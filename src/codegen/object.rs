use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use cranelift_codegen::ir::AbiParam;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_module::{default_libcall_names, Linkage, Module};
use cranelift_native::builder as native_builder;
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::ast::{Type, TypedProgram};
use crate::codegen::ctx::ProgramMeta;
use crate::codegen::func::compile_func;
use crate::codegen::layout::abi_signature_for_fn;
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

pub fn compile_program_to_binary(
    program: &TypedProgram,
    struct_layouts: &HashMap<String, StructLayout>,
    output_binary_path: &str,
    lib_dirs: &[String],
    libs: &[String],
    source_map: &crate::loader::SourceMap,
) -> Result<(), String> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("is_pic", "true")
        .map_err(|e| format!("Setting is_pic error: {}", e))?;
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

    // Forward-declare all program functions before compiling bodies so mutually
    // recursive or out-of-order calls use Export rather than Import linkage.
    let call_conv = module.isa().default_call_conv();
    for func in &program.functions {
        let export_name = if func.name == "main" {
            "gdrs_main"
        } else {
            &func.name
        };
        if module.get_name(export_name).is_none() {
            let param_tys: Vec<Type> = func.params.iter().map(|p| p.ty).collect();
            let (sig, _) = abi_signature_for_fn(
                call_conv,
                &param_tys,
                &func.return_type,
                func.name.ends_with("_drop"),
                &meta.struct_layouts,
                meta.enum_layouts,
            );
            module
                .declare_function(export_name, Linkage::Export, &sig)
                .map_err(|e| format!("Failed to declare '{}': {}", export_name, e))?;
        }
    }

    for func in &program.functions {
        compile_func(
            func,
            &mut meta,
            &mut module,
            &mut ctx,
            &mut builder_context,
        );
    }

    let product = module.finish();
    let object_bytes = product
        .emit()
        .map_err(|e| format!("Failed to emit object bytes: {}", e))?;

    let temp_dir = std::env::temp_dir();
    let obj_path = temp_dir.join(format!("gdrs_main_{}.o", std::process::id()));
    fs::write(&obj_path, object_bytes).map_err(|e| format!("Failed to write object file: {}", e))?;

    let runtime_obj_path = match ensure_runtime_object() {
        Ok(p) => p,
        Err(e) => {
            let _ = fs::remove_file(&obj_path);
            return Err(e);
        }
    };

    let mut clang_args = vec![
        obj_path.to_str().unwrap().to_string(),
        runtime_obj_path.to_str().unwrap().to_string(),
        "-o".to_string(),
        output_binary_path.to_string(),
    ];
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

    let clang_output = clang_output.map_err(|e| format!("Failed to execute clang linker: {}", e))?;
    if !clang_output.status.success() {
        return Err(format!(
            "clang linking failed:\n{}",
            String::from_utf8_lossy(&clang_output.stderr)
        ));
    }

    Ok(())
}
