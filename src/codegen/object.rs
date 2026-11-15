use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use cranelift_codegen::ir::AbiParam;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_module::{default_libcall_names, DataDescription, Linkage, Module};
use cranelift_native::builder as native_builder;
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::ast::{StaticInitVal, Type, TypedProgram, Visibility};
use crate::cli::CrateType;
use crate::codegen::ctx::ProgramMeta;
use crate::codegen::func::compile_func;
use crate::codegen::layout::{
    abi_signature_for_fn, array_stride, find_struct_layout, size_and_align, tuple_field_offsets,
};
use crate::sanal::StructLayout;

pub const RUNTIME_C_SOURCE: &str = include_str!("runtime.c");

fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        hash ^= b as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn ensure_runtime_object() -> Result<PathBuf, String> {
    let temp_dir = std::env::temp_dir();
    let hash = hash_bytes(RUNTIME_C_SOURCE.as_bytes());
    let runtime_obj_path = temp_dir.join(format!("gdrs_runtime_{:016x}.o", hash));

    if runtime_obj_path.exists() {
        return Ok(runtime_obj_path);
    }

    let runtime_c_path = temp_dir.join(format!("gdrs_runtime_{:016x}.c", hash));
    fs::write(&runtime_c_path, RUNTIME_C_SOURCE)
        .map_err(|e| format!("Failed to write runtime C source: {}", e))?;

    let tmp_obj = temp_dir.join(format!("gdrs_runtime_{:016x}_{}.o.tmp", hash, std::process::id()));
    let compile_out = Command::new("clang")
        .args([
            "-c",
            "-O2",
            runtime_c_path.to_str().unwrap(),
            "-o",
            tmp_obj.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("Failed to execute clang for runtime: {}", e))?;

    let _ = fs::remove_file(&runtime_c_path);

    if !compile_out.status.success() {
        let _ = fs::remove_file(&tmp_obj);
        return Err(format!(
            "Failed to compile GDRS runtime:\n{}",
            String::from_utf8_lossy(&compile_out.stderr)
        ));
    }

    let _ = fs::rename(&tmp_obj, &runtime_obj_path);
    Ok(runtime_obj_path)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OptLevel {
    #[default]
    None,
    Speed,
    SpeedAndSize,
}

impl OptLevel {
    pub fn as_cranelift_str(self) -> &'static str {
        match self {
            OptLevel::None => "none",
            OptLevel::Speed => "speed",
            OptLevel::SpeedAndSize => "speed_and_size",
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct CompileOptions {
    pub opt_level: OptLevel,
    pub crate_type: CrateType,
    pub extra_objects: Vec<(String, Vec<u8>)>,
}

pub fn compile_program_to_object_bytes(
    program: &TypedProgram,
    struct_layouts: &HashMap<String, StructLayout>,
    source_map: &crate::loader::SourceMap,
) -> Result<Vec<u8>, String> {
    compile_program_to_object_bytes_with_options(
        program,
        struct_layouts,
        source_map,
        &CompileOptions::default(),
    )
}

pub fn compile_program_to_object_bytes_with_options(
    program: &TypedProgram,
    struct_layouts: &HashMap<String, StructLayout>,
    source_map: &crate::loader::SourceMap,
    opts: &CompileOptions,
) -> Result<Vec<u8>, String> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("opt_level", opts.opt_level.as_cranelift_str())
        .map_err(|e| format!("Setting opt_level error: {}", e))?;
    flag_builder
        .set("is_pic", "true")
        .map_err(|e| format!("Setting is_pic error: {}", e))?;
    flag_builder
        .set("enable_verifier", "true")
        .map_err(|e| format!("Setting enable_verifier error: {}", e))?;
    let isa_builder = native_builder().map_err(|e| format!("Host target architecture error: {}", e))?;
    let target_isa = isa_builder
        .finish(Flags::new(flag_builder))
        .map_err(|e| format!("Target ISA error: {}", e))?;

    let object_builder = ObjectBuilder::new(target_isa, "gdrs_app", default_libcall_names())
        .map_err(|e| format!("ObjectBuilder error: {}", e))?;

    let mut module = ObjectModule::new(object_builder);
    let mut ctx = module.make_context();
    let mut builder_context = cranelift_frontend::FunctionBuilderContext::new();
    let mut meta = ProgramMeta::from_program(program, struct_layouts, source_map);

    emit_static_data_objects(program, &meta, &mut module)?;

    // Forward-declare all program functions before compiling bodies so mutually
    // recursive or out-of-order calls use Export rather than Import linkage.
    let call_conv = module.isa().default_call_conv();
    for func in &program.functions {
        let export_name = if opts.crate_type == CrateType::Bin && func.name == "main" {
            "gdrs_main"
        } else {
            &func.name
        };
        let is_extern_import = program.extern_import_fns.contains(&func.name);
        let linkage = if is_extern_import {
            Linkage::Import
        } else if opts.crate_type == CrateType::Bin {
            if func.name == "main" {
                Linkage::Export
            } else {
                Linkage::Local
            }
        } else if func.name.starts_with("std_") {
            Linkage::Local
        } else {
            Linkage::Export
        };
        if module.get_name(export_name).is_none() {
            let param_tys: Vec<Type> = func.params.iter().map(|p| p.ty).collect();
            let (mut sig, _) = abi_signature_for_fn(
                call_conv,
                &param_tys,
                &func.return_type,
                func.name.ends_with("_drop"),
                &meta.struct_layouts,
                meta.enum_layouts,
            );
            if func.is_track_caller {
                use cranelift_codegen::ir::types;
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
            }
            module
                .declare_function(export_name, linkage, &sig)
                .map_err(|e| format!("Failed to declare '{}': {}", export_name, e))?;
        }
    }

    for func in &program.functions {
        if program.extern_import_fns.contains(&func.name) {
            continue;
        }
        compile_func(
            func,
            &mut meta,
            &mut module,
            &mut ctx,
            &mut builder_context,
        );
    }

    let product = module.finish();
    product
        .emit()
        .map_err(|e| format!("Failed to emit object bytes: {}", e))
}

pub fn compile_program_to_binary(
    program: &TypedProgram,
    struct_layouts: &HashMap<String, StructLayout>,
    output_binary_path: &str,
    lib_dirs: &[String],
    libs: &[String],
    source_map: &crate::loader::SourceMap,
) -> Result<(), String> {
    compile_program_to_binary_with_options(
        program,
        struct_layouts,
        output_binary_path,
        lib_dirs,
        libs,
        source_map,
        &CompileOptions::default(),
    )
}

pub fn compile_program_to_binary_with_options(
    program: &TypedProgram,
    struct_layouts: &HashMap<String, StructLayout>,
    output_binary_path: &str,
    lib_dirs: &[String],
    libs: &[String],
    source_map: &crate::loader::SourceMap,
    opts: &CompileOptions,
) -> Result<(), String> {
    let object_bytes =
        compile_program_to_object_bytes_with_options(program, struct_layouts, source_map, opts)?;

    let temp_dir = std::env::temp_dir();
    let pid = std::process::id();
    let obj_path = temp_dir.join(format!("gdrs_main_{}.o", pid));
    fs::write(&obj_path, object_bytes).map_err(|e| format!("Failed to write object file: {}", e))?;

    let mut extra_obj_paths = Vec::new();
    for (idx, (crate_name, ext_bytes)) in opts.extra_objects.iter().enumerate() {
        let ext_path = temp_dir.join(format!("gdrs_extern_{}_{}_{}.o", crate_name, pid, idx));
        if let Err(e) = fs::write(&ext_path, ext_bytes) {
            let _ = fs::remove_file(&obj_path);
            for p in &extra_obj_paths {
                let _ = fs::remove_file(p);
            }
            return Err(format!(
                "Failed to write temporary extern object for `{}`: {}",
                crate_name, e
            ));
        }
        extra_obj_paths.push(ext_path);
    }

    let runtime_obj_path = match ensure_runtime_object() {
        Ok(p) => p,
        Err(e) => {
            let _ = fs::remove_file(&obj_path);
            for p in &extra_obj_paths {
                let _ = fs::remove_file(p);
            }
            return Err(e);
        }
    };

    let mut clang_args = vec![obj_path.to_str().unwrap().to_string()];
    for ext_p in &extra_obj_paths {
        clang_args.push(ext_p.to_str().unwrap().to_string());
    }
    clang_args.push(runtime_obj_path.to_str().unwrap().to_string());
    clang_args.push("-o".to_string());
    clang_args.push(output_binary_path.to_string());
    for dir in lib_dirs {
        clang_args.push(format!("-L{}", dir));
    }
    for lib in libs {
        clang_args.push(format!("-l{}", lib));
    }
    clang_args.push("-lm".to_string());
    clang_args.push("-lpthread".to_string());

    let clang_output = Command::new("clang").args(&clang_args).output();

    let _ = fs::remove_file(&obj_path);
    for p in &extra_obj_paths {
        let _ = fs::remove_file(p);
    }

    let clang_output = clang_output.map_err(|e| format!("Failed to execute clang linker: {}", e))?;
    if !clang_output.status.success() {
        return Err(format!(
            "clang linking failed:\n{}",
            String::from_utf8_lossy(&clang_output.stderr)
        ));
    }

    Ok(())
}

pub fn write_staticlib_archive(object_bytes: &[u8], crate_name: &str, output_path: &str) -> Result<(), String> {
    let temp_dir = std::env::temp_dir();
    let obj_path = temp_dir.join(format!("gdrs_staticlib_{}_{}.o", crate_name, std::process::id()));
    fs::write(&obj_path, object_bytes)
        .map_err(|e| format!("Failed to write temporary staticlib object: {}", e))?;
    let _ = fs::remove_file(output_path);
    let ar_out = Command::new("ar")
        .args(["rcs", output_path, obj_path.to_str().unwrap()])
        .output();
    let _ = fs::remove_file(&obj_path);
    let ar_out = ar_out.map_err(|e| format!("Failed to execute `ar` archiver: {}", e))?;
    if !ar_out.status.success() {
        return Err(format!(
            "`ar` staticlib creation failed:\n{}",
            String::from_utf8_lossy(&ar_out.stderr)
        ));
    }
    Ok(())
}

fn emit_static_data_objects<M: Module>(
    program: &TypedProgram,
    meta: &ProgramMeta<'_>,
    module: &mut M,
) -> Result<(), String> {
    static STATIC_STR_COUNTER: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);

    #[allow(clippy::too_many_arguments)]
    fn write_static_init<M: Module>(
        init: &StaticInitVal,
        ty: Type,
        base_off: usize,
        buf: &mut [u8],
        relocs: &mut Vec<(usize, String)>,
        meta: &ProgramMeta<'_>,
        module: &mut M,
    ) -> Result<(), String> {
        match (init, ty) {
            (StaticInitVal::Int(v), Type::I8 | Type::U8) => {
                buf[base_off] = *v as u8;
            }
            (StaticInitVal::Int(v), Type::I16 | Type::U16) => {
                buf[base_off..base_off + 2].copy_from_slice(&(*v as i16).to_ne_bytes());
            }
            (StaticInitVal::Int(v), Type::I32 | Type::U32) => {
                buf[base_off..base_off + 4].copy_from_slice(&(*v as i32).to_ne_bytes());
            }
            (StaticInitVal::Int(v), Type::Int | Type::U64 | Type::Ptr(_)) => {
                buf[base_off..base_off + 8].copy_from_slice(&v.to_ne_bytes());
            }
            (StaticInitVal::Float(f), Type::F32) => {
                buf[base_off..base_off + 4].copy_from_slice(&(*f as f32).to_ne_bytes());
            }
            (StaticInitVal::Float(f), Type::Float) => {
                buf[base_off..base_off + 8].copy_from_slice(&f.to_ne_bytes());
            }
            (StaticInitVal::Bool(b), Type::Bool) => {
                buf[base_off] = u8::from(*b);
            }
            (StaticInitVal::Str(raw_s), Type::Str) => {
                let s = crate::ast::unescape_string_literal(raw_s);
                let id_num = STATIC_STR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                let str_sym = format!("__gdrs_static_str_{id_num}");
                let mut str_desc = DataDescription::new();
                let mut bytes = s.into_bytes();
                bytes.push(0);
                str_desc.define(bytes.into_boxed_slice());
                let str_id = module
                    .declare_data(&str_sym, Linkage::Local, false, false)
                    .map_err(|e| format!("Failed to declare static string '{}': {}", str_sym, e))?;
                module
                    .define_data(str_id, &str_desc)
                    .map_err(|e| format!("Failed to define static string '{}': {}", str_sym, e))?;
                relocs.push((base_off, str_sym));
            }
            (StaticInitVal::Array(elems), Type::Array(elem_ty, _)) => {
                let stride = array_stride(elem_ty, &meta.struct_layouts, meta.enum_layouts) as usize;
                for (i, elem) in elems.iter().enumerate() {
                    write_static_init(
                        elem,
                        *elem_ty,
                        base_off + i * stride,
                        buf,
                        relocs,
                        meta,
                        module,
                    )?;
                }
            }
            (StaticInitVal::Tuple(elems), Type::Tuple(tys)) => {
                let (_, _, offsets) =
                    tuple_field_offsets(tys, &meta.struct_layouts, meta.enum_layouts);
                for ((elem, ty), off) in elems.iter().zip(tys.iter()).zip(offsets.iter()) {
                    write_static_init(
                        elem,
                        *ty,
                        base_off + (*off as usize),
                        buf,
                        relocs,
                        meta,
                        module,
                    )?;
                }
            }
            (StaticInitVal::Struct(sname, fields), Type::Obj(_)) => {
                if let Some(layout) = find_struct_layout(&meta.struct_layouts, sname) {
                    for (fname, fval) in fields {
                        if let Some((foff, fty)) = layout.field_offsets.get(fname) {
                            write_static_init(
                                fval,
                                *fty,
                                base_off + (*foff as usize),
                                buf,
                                relocs,
                                meta,
                                module,
                            )?;
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    for st in &program.statics {
        if st
            .module_path
            .first()
            .is_some_and(|c| program.extern_crate_names.contains(c))
        {
            continue;
        }
        let (size, align) = size_and_align(&st.ty, &meta.struct_layouts, meta.enum_layouts);
        let alloc_size = size.max(1) as usize;
        let mut buf = vec![0u8; alloc_size];
        let mut relocs = Vec::new();
        write_static_init(&st.init, st.ty, 0, &mut buf, &mut relocs, meta, module)?;

        let mut data_ctx = DataDescription::new();
        data_ctx.define(buf.into_boxed_slice());
        data_ctx.set_align(align.max(1) as u64);
        for (off, target_sym) in relocs {
            let target_id = module
                .declare_data(&target_sym, Linkage::Local, false, false)
                .map_err(|e| format!("Failed to declare reloc target '{}': {}", target_sym, e))?;
            let gv = module.declare_data_in_data(target_id, &mut data_ctx);
            data_ctx.write_data_addr(off as u32, gv, 0);
        }

        let linkage = if st.vis == Visibility::Pub {
            Linkage::Export
        } else {
            Linkage::Local
        };
        let data_id = module
            .declare_data(&st.name, linkage, st.is_mut, false)
            .map_err(|e| format!("Failed to declare static '{}': {}", st.name, e))?;
        module
            .define_data(data_id, &data_ctx)
            .map_err(|e| format!("Failed to define static '{}': {}", st.name, e))?;
    }
    Ok(())
}
