//! codegen/drops.rs
//! Cranelift Drop Flag allocation, LIFO scope drop emission, and Drop Glue calls
//! (including synthesized recursive field drops for user structs without custom `Drop`).

use std::collections::{HashMap, HashSet};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, StackSlot, StackSlotData, StackSlotKind, types, Value};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{FuncId, Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::expr::cranelift_type_of;
use crate::codegen::layout::{
    array_stride, enum_variant_offsets, find_struct_layout, is_aggregate_type, tuple_field_offsets,
};
use crate::sanal::StructLayout;

pub type EnumLayoutMap = HashMap<String, Vec<(String, i64, Vec<Type>)>>;

#[inline]
pub fn is_npo_enum(name: &str) -> bool {
    name.starts_with("std_core_Option_ptr")
        || name.starts_with("std_core_Option_void")
        || name.contains("_ptr_")
        || name.contains("_void")
}

pub fn find_enum_layout<'a>(
    name: &str,
    enum_layouts: &'a EnumLayoutMap,
) -> Option<&'a Vec<(String, i64, Vec<Type>)>> {
    enum_layouts.get(name).or_else(|| {
        enum_layouts
            .iter()
            .find(|(k, _)| **k == name || k.ends_with(&format!("_{name}")))
            .map(|(_, v)| v)
    })
}

fn explicit_drop_fn_name(ty: &Type, known_drop_fns: &HashSet<String>) -> Option<String> {
    match ty {
        Type::String | Type::Obj("String") | Type::Obj("std_string_String") => {
            Some("std_string_String_drop".to_string())
        }
        Type::Vec(_) | Type::Obj("Vec") | Type::Obj("std_vec_Vec") => {
            Some("std_vec_Vec_drop".to_string())
        }
        Type::Obj(name) if name.starts_with("std_vec_Vec_") => {
            Some("std_vec_Vec_drop".to_string())
        }
        Type::Rc(_) => Some("intrinsic_rc_drop".to_string()),
        Type::Arc(_) => Some("intrinsic_arc_drop".to_string()),
        Type::Obj(name) => {
            let candidate = format!("{name}_drop");
            if known_drop_fns.contains(&candidate) {
                Some(candidate)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn find_layout<'a>(
    name: &str,
    struct_layouts: &'a HashMap<String, StructLayout>,
) -> Option<&'a StructLayout> {
    struct_layouts.get(name).or_else(|| {
        struct_layouts
            .iter()
            .find(|(k, _)| **k == name || k.ends_with(&format!("_{name}")))
            .map(|(_, v)| v)
    })
}

fn has_drop_glue_inner(
    ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    visited: &mut HashSet<String>,
) -> bool {
    if explicit_drop_fn_name(ty, known_drop_fns).is_some() {
        return true;
    }
    if matches!(ty, Type::DynTrait(_)) {
        return true;
    }
    if let Type::Array(elem, len) = ty {
        return *len > 0
            && has_drop_glue_inner(elem, known_drop_fns, struct_layouts, enum_layouts, visited);
    }
    if let Type::Tuple(elems) = ty {
        return elems
            .iter()
            .any(|e| has_drop_glue_inner(e, known_drop_fns, struct_layouts, enum_layouts, visited));
    }
    if let Type::Enum(name) = ty {
        if is_npo_enum(name) {
            return false;
        }
        let key = format!("enum:{name}");
        if !visited.insert(key.clone()) {
            return false;
        }
        let has = if let Some(variants) = find_enum_layout(name, enum_layouts) {
            variants.iter().any(|(_, _, p_tys)| {
                p_tys.iter().any(|p_ty| {
                    has_drop_glue_inner(p_ty, known_drop_fns, struct_layouts, enum_layouts, visited)
                })
            })
        } else {
            false
        };
        visited.remove(&key);
        return has;
    }
    if let Type::Obj(name) = ty {
        if !visited.insert((*name).to_string()) {
            return false;
        }
        let has = if let Some(layout) = find_layout(name, struct_layouts) {
            layout.field_offsets.values().any(|(_, f_ty)| {
                has_drop_glue_inner(f_ty, known_drop_fns, struct_layouts, enum_layouts, visited)
            })
        } else {
            false
        };
        visited.remove(*name);
        return has;
    }
    false
}

pub fn has_drop_glue(
    ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> bool {
    let mut visited = HashSet::new();
    has_drop_glue_inner(ty, known_drop_fns, struct_layouts, enum_layouts, &mut visited)
}

fn emit_free_call<M: Module>(builder: &mut FunctionBuilder, ptr_val: Value, module: &mut M) {
    let mut free_sig = module.make_signature();
    free_sig.params.push(AbiParam::new(types::I64));
    let free_id = module
        .declare_function("free", Linkage::Import, &free_sig)
        .unwrap();
    let local_free = module.declare_func_in_func(free_id, builder.func);
    builder.ins().call(local_free, &[ptr_val]);
}

fn resolve_or_synthesize_drop_fn<M: Module>(
    ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Option<FuncId> {
    if matches!(ty, Type::Rc(_) | Type::Arc(_)) {
        let drop_fn_name = explicit_drop_fn_name(ty, known_drop_fns)?;
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(cranelift_type_of(ty)));
        return match module.get_name(&drop_fn_name) {
            Some(cranelift_module::FuncOrDataId::Func(id)) => Ok(id),
            _ => module.declare_function(&drop_fn_name, Linkage::Import, &sig),
        }
        .ok();
    }

    if matches!(ty, Type::DynTrait(_)) {
        let synth_name = "__gdrs_drop_dyn";
        if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(synth_name) {
            return Some(id);
        }
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(synth_name, Linkage::Export, &sig)
            .ok()?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.append_block_params_for_function_params(entry);
            let ptr_val = builder.block_params(entry)[0];

            let drop_body = builder.create_block();
            let call_dtor_blk = builder.create_block();
            let free_blk = builder.create_block();
            let exit_block = builder.create_block();

            builder.ins().brif(ptr_val, drop_body, &[], exit_block, &[]);

            builder.switch_to_block(drop_body);
            builder.seal_block(drop_body);
            let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_val, 0);
            let dtor_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_val, 16);
            builder.ins().brif(dtor_ptr, call_dtor_blk, &[], free_blk, &[]);

            builder.switch_to_block(call_dtor_blk);
            builder.seal_block(call_dtor_blk);
            let mut dtor_sig = module.make_signature();
            dtor_sig.params.push(AbiParam::new(types::I64));
            let sig_ref = builder.import_signature(dtor_sig);
            builder.ins().call_indirect(sig_ref, dtor_ptr, &[data_ptr]);
            builder.ins().jump(free_blk, &[]);

            builder.switch_to_block(free_blk);
            builder.seal_block(free_blk);
            emit_free_call(&mut builder, ptr_val, module);
            builder.ins().jump(exit_block, &[]);

            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize();
        }
        let _ = module.define_function(func_id, &mut ctx);
        module.clear_context(&mut ctx);
        return Some(func_id);
    }

    if matches!(
        ty,
        Type::String | Type::Obj("String") | Type::Obj("std_string_String")
    ) {
        let synth_name = "__gdrs_drop_string";
        if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(synth_name) {
            return Some(id);
        }
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(synth_name, Linkage::Export, &sig)
            .ok()?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig.clone();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.append_block_params_for_function_params(entry);
            let ptr_val = builder.block_params(entry)[0];

            let drop_body = builder.create_block();
            let exit_block = builder.create_block();
            builder.ins().brif(ptr_val, drop_body, &[], exit_block, &[]);

            builder.switch_to_block(drop_body);
            builder.seal_block(drop_body);

            let drop_fn = match module.get_name("std_string_String_drop") {
                Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                _ => module
                    .declare_function("std_string_String_drop", Linkage::Import, &sig)
                    .ok()?,
            };
            let local_drop = module.declare_func_in_func(drop_fn, builder.func);
            builder.ins().call(local_drop, &[ptr_val]);
            builder.ins().jump(exit_block, &[]);

            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize();
        }
        let _ = module.define_function(func_id, &mut ctx);
        module.clear_context(&mut ctx);
        return Some(func_id);
    }

    let vec_elem_opt: Option<Option<Type>> = match ty {
        Type::Vec(elem) => Some(Some(**elem)),
        Type::Obj("Vec") | Type::Obj("std_vec_Vec") => Some(None),
        Type::Obj(name) if name.starts_with("std_vec_Vec_") => Some(
            crate::sanal::mono::lookup_mangled(name).and_then(|(_, args)| args.first().copied()),
        ),
        _ => None,
    };
    if let Some(elem_opt) = vec_elem_opt {
        let synth_name = format!("__gdrs_drop_{}", crate::sanal::mono::type_suffix(ty));
        if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
            return Some(id);
        }
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(&synth_name, Linkage::Export, &sig)
            .ok()?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig.clone();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.append_block_params_for_function_params(entry);
            let ptr_val = builder.block_params(entry)[0];

            let drop_body = builder.create_block();
            let exit_block = builder.create_block();
            builder.ins().brif(ptr_val, drop_body, &[], exit_block, &[]);

            builder.switch_to_block(drop_body);
            builder.seal_block(drop_body);

            if let Some(elem_ty) = elem_opt {
                if has_drop_glue(&elem_ty, known_drop_fns, struct_layouts, enum_layouts) {
                    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_val, 0);
                    let len_val = builder.ins().load(types::I64, MemFlags::new(), ptr_val, 8);
                    let zero = builder.ins().iconst(types::I64, 0);
                    let has_data = builder.ins().icmp_imm(IntCC::NotEqual, data_ptr, 0);
                    let has_len = builder.ins().icmp_imm(IntCC::SignedGreaterThan, len_val, 0);
                    let should_loop = builder.ins().band(has_data, has_len);

                    let loop_start = builder.create_block();
                    let loop_hdr = builder.create_block();
                    let loop_body = builder.create_block();
                    let after_loop = builder.create_block();
                    builder.ins().brif(should_loop, loop_start, &[], after_loop, &[]);

                    builder.switch_to_block(loop_start);
                    builder.seal_block(loop_start);
                    let idx_var = Variable::from_u32(0);
                    builder.declare_var(idx_var, types::I64);
                    builder.def_var(idx_var, zero);
                    builder.ins().jump(loop_hdr, &[]);

                    builder.switch_to_block(loop_hdr);
                    let cur_idx = builder.use_var(idx_var);
                    let cond = builder.ins().icmp(IntCC::SignedLessThan, cur_idx, len_val);
                    builder.ins().brif(cond, loop_body, &[], after_loop, &[]);

                    builder.switch_to_block(loop_body);
                    builder.seal_block(loop_body);
                    let elem_bytes = array_stride(&elem_ty, struct_layouts, enum_layouts).max(1) as i64;
                    let stride = builder.ins().iconst(types::I64, elem_bytes);
                    let off = builder.ins().imul(cur_idx, stride);
                    let elem_addr = builder.ins().iadd(data_ptr, off);
                    let drop_arg = if is_aggregate_type(&elem_ty, struct_layouts, enum_layouts) {
                        elem_addr
                    } else {
                        builder.ins().load(
                            cranelift_type_of(&elem_ty),
                            MemFlags::new(),
                            elem_addr,
                            0,
                        )
                    };
                    emit_drop_for_value(
                        &mut builder,
                        drop_arg,
                        &elem_ty,
                        known_drop_fns,
                        struct_layouts,
                        enum_layouts,
                        module,
                    );
                    let next_idx = builder.ins().iadd_imm(cur_idx, 1);
                    builder.def_var(idx_var, next_idx);
                    builder.ins().jump(loop_hdr, &[]);
                    builder.seal_block(loop_hdr);

                    builder.switch_to_block(after_loop);
                    builder.seal_block(after_loop);
                }
            }

            let vec_drop_id = match module.get_name("std_vec_Vec_drop") {
                Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                _ => module
                    .declare_function("std_vec_Vec_drop", Linkage::Import, &sig)
                    .ok()?,
            };
            let local_vec_drop = module.declare_func_in_func(vec_drop_id, builder.func);
            builder.ins().call(local_vec_drop, &[ptr_val]);
            builder.ins().jump(exit_block, &[]);

            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize();
        }
        let _ = module.define_function(func_id, &mut ctx);
        module.clear_context(&mut ctx);
        return Some(func_id);
    }

    if let Type::Array(elem_ty, len) = ty {
        let elem_ty = **elem_ty;
        let len = *len;
        if len == 0 || !has_drop_glue(&elem_ty, known_drop_fns, struct_layouts, enum_layouts) {
            return None;
        }
        let synth_name = format!("__gdrs_drop_{}", crate::sanal::mono::type_suffix(ty));
        if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
            return Some(id);
        }

        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(&synth_name, Linkage::Export, &sig)
            .ok()?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.append_block_params_for_function_params(entry);
            let ptr_val = builder.block_params(entry)[0];

            let drop_body = builder.create_block();
            let exit_block = builder.create_block();
            builder.ins().brif(ptr_val, drop_body, &[], exit_block, &[]);

            builder.switch_to_block(drop_body);
            builder.seal_block(drop_body);

            let idx_var = Variable::from_u32(0);
            builder.declare_var(idx_var, types::I64);
            let zero = builder.ins().iconst(types::I64, 0);
            builder.def_var(idx_var, zero);

            let loop_hdr = builder.create_block();
            let loop_body = builder.create_block();
            let after_loop = builder.create_block();

            builder.ins().jump(loop_hdr, &[]);
            builder.switch_to_block(loop_hdr);
            let cur_idx = builder.use_var(idx_var);
            let limit = builder.ins().iconst(types::I64, len as i64);
            let cond = builder.ins().icmp(IntCC::SignedLessThan, cur_idx, limit);
            builder.ins().brif(cond, loop_body, &[], after_loop, &[]);

            builder.switch_to_block(loop_body);
            builder.seal_block(loop_body);
            let elem_bytes = array_stride(&elem_ty, struct_layouts, enum_layouts).max(1) as i64;
            let stride = builder.ins().iconst(types::I64, elem_bytes);
            let off = builder.ins().imul(cur_idx, stride);
            let elem_addr = builder.ins().iadd(ptr_val, off);
            let drop_arg = if is_aggregate_type(&elem_ty, struct_layouts, enum_layouts) {
                elem_addr
            } else {
                builder
                    .ins()
                    .load(cranelift_type_of(&elem_ty), MemFlags::new(), elem_addr, 0)
            };
            emit_drop_for_value(
                &mut builder,
                drop_arg,
                &elem_ty,
                known_drop_fns,
                struct_layouts,
                enum_layouts,
                module,
            );
            let next_idx = builder.ins().iadd_imm(cur_idx, 1);
            builder.def_var(idx_var, next_idx);
            builder.ins().jump(loop_hdr, &[]);
            builder.seal_block(loop_hdr);

            builder.switch_to_block(after_loop);
            builder.seal_block(after_loop);

            builder.ins().jump(exit_block, &[]);

            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize();
        }

        let _ = module.define_function(func_id, &mut ctx);
        module.clear_context(&mut ctx);
        return Some(func_id);
    }

    if let Type::Enum(name) = ty {
        if is_npo_enum(name) {
            return None;
        }
        let variants = find_enum_layout(name, enum_layouts)?;
        let droppable_variants: Vec<(i64, Vec<(u32, Type)>)> = variants
            .iter()
            .filter_map(|(_, v_tag, p_tys)| {
                let (_, _, offsets) = enum_variant_offsets(p_tys, struct_layouts, enum_layouts);
                let mut fields: Vec<(u32, Type)> = p_tys
                    .iter()
                    .zip(offsets.into_iter())
                    .filter(|(p_ty, _)| {
                        has_drop_glue(p_ty, known_drop_fns, struct_layouts, enum_layouts)
                    })
                    .map(|(p_ty, off)| (off, *p_ty))
                    .collect();
                if fields.is_empty() {
                    None
                } else {
                    fields.sort_by(|a, b| b.0.cmp(&a.0));
                    Some((*v_tag, fields))
                }
            })
            .collect();
        if droppable_variants.is_empty() {
            return None;
        }

        let synth_name = format!("__gdrs_drop_enum_{name}");
        if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
            return Some(id);
        }
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(&synth_name, Linkage::Export, &sig)
            .ok()?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.append_block_params_for_function_params(entry);
            let ptr_val = builder.block_params(entry)[0];

            let drop_body = builder.create_block();
            let exit_block = builder.create_block();
            builder.ins().brif(ptr_val, drop_body, &[], exit_block, &[]);

            builder.switch_to_block(drop_body);
            builder.seal_block(drop_body);

            let tag_val = builder.ins().load(types::I64, MemFlags::new(), ptr_val, 0);
            let after_payloads = builder.create_block();
            for (v_tag, fields) in droppable_variants {
                let match_blk = builder.create_block();
                let next_blk = builder.create_block();
                let is_tag = builder.ins().icmp_imm(IntCC::Equal, tag_val, v_tag);
                builder.ins().brif(is_tag, match_blk, &[], next_blk, &[]);

                builder.switch_to_block(match_blk);
                builder.seal_block(match_blk);
                for (off, p_ty) in fields {
                    let drop_arg = if is_aggregate_type(&p_ty, struct_layouts, enum_layouts) {
                        builder.ins().iadd_imm(ptr_val, off as i64)
                    } else {
                        builder.ins().load(
                            cranelift_type_of(&p_ty),
                            MemFlags::new(),
                            ptr_val,
                            off as i32,
                        )
                    };
                    emit_drop_for_value(
                        &mut builder,
                        drop_arg,
                        &p_ty,
                        known_drop_fns,
                        struct_layouts,
                        enum_layouts,
                        module,
                    );
                }
                builder.ins().jump(after_payloads, &[]);

                builder.switch_to_block(next_blk);
                builder.seal_block(next_blk);
            }
            builder.ins().jump(after_payloads, &[]);
            builder.switch_to_block(after_payloads);
            builder.seal_block(after_payloads);

            builder.ins().jump(exit_block, &[]);

            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize();
        }

        let _ = module.define_function(func_id, &mut ctx);
        module.clear_context(&mut ctx);
        return Some(func_id);
    }

    if let Type::Tuple(elems) = ty {
        let (_, _, offsets) = tuple_field_offsets(elems, struct_layouts, enum_layouts);
        let mut droppable_fields: Vec<(u32, Type)> = elems
            .iter()
            .copied()
            .zip(offsets)
            .filter(|(f_ty, _)| has_drop_glue(f_ty, known_drop_fns, struct_layouts, enum_layouts))
            .map(|(f_ty, off)| (off, f_ty))
            .collect();
        if droppable_fields.is_empty() {
            return None;
        }
        droppable_fields.sort_by(|a, b| b.0.cmp(&a.0));

        let synth_name = format!("__gdrs_drop_{}", crate::sanal::mono::type_suffix(ty));
        if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
            return Some(id);
        }
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(&synth_name, Linkage::Export, &sig)
            .ok()?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.append_block_params_for_function_params(entry);
            let ptr_val = builder.block_params(entry)[0];

            let drop_body = builder.create_block();
            let exit_block = builder.create_block();
            builder.ins().brif(ptr_val, drop_body, &[], exit_block, &[]);

            builder.switch_to_block(drop_body);
            builder.seal_block(drop_body);

            for (offset, f_ty) in droppable_fields {
                let drop_arg = if is_aggregate_type(&f_ty, struct_layouts, enum_layouts) {
                    builder.ins().iadd_imm(ptr_val, offset as i64)
                } else {
                    builder.ins().load(
                        cranelift_type_of(&f_ty),
                        MemFlags::new(),
                        ptr_val,
                        offset as i32,
                    )
                };
                emit_drop_for_value(
                    &mut builder,
                    drop_arg,
                    &f_ty,
                    known_drop_fns,
                    struct_layouts,
                    enum_layouts,
                    module,
                );
            }

            builder.ins().jump(exit_block, &[]);
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize();
        }
        let _ = module.define_function(func_id, &mut ctx);
        module.clear_context(&mut ctx);
        return Some(func_id);
    }

    let Type::Obj(name) = ty else {
        return None;
    };
    let custom_drop = explicit_drop_fn_name(ty, known_drop_fns);
    let layout_opt = find_struct_layout(struct_layouts, name).or_else(|| find_layout(name, struct_layouts));

    let mut droppable_fields: Vec<(u32, Type)> = layout_opt
        .map(|layout| {
            layout
                .field_offsets
                .values()
                .filter(|(_, f_ty)| has_drop_glue(f_ty, known_drop_fns, struct_layouts, enum_layouts))
                .copied()
                .collect()
        })
        .unwrap_or_default();
    if custom_drop.is_none() && droppable_fields.is_empty() {
        return None;
    }
    // Drop fields in reverse offset order
    droppable_fields.sort_by(|a, b| b.0.cmp(&a.0));

    let struct_id = layout_opt.map(|l| l.name.as_str()).unwrap_or(name);
    let synth_name = format!("__gdrs_drop_{struct_id}");
    if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
        return Some(id);
    }

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    let func_id = module
        .declare_function(&synth_name, Linkage::Export, &sig)
        .ok()?;

    let mut ctx = module.make_context();
    ctx.func.signature = sig.clone();
    let mut builder_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = builder.create_block();
        builder.switch_to_block(entry);
        builder.append_block_params_for_function_params(entry);
        let ptr_val = builder.block_params(entry)[0];

        let drop_body = builder.create_block();
        let exit_block = builder.create_block();
        builder.ins().brif(ptr_val, drop_body, &[], exit_block, &[]);

        builder.switch_to_block(drop_body);
        builder.seal_block(drop_body);

        if let Some(custom_fn) = custom_drop {
            let mut drop_sig = module.make_signature();
            drop_sig.params.push(AbiParam::new(types::I64));
            let drop_id = match module.get_name(&custom_fn) {
                Some(cranelift_module::FuncOrDataId::Func(id)) => Some(id),
                _ => module
                    .declare_function(&custom_fn, Linkage::Import, &drop_sig)
                    .ok(),
            };
            if let Some(did) = drop_id {
                let local_did = module.declare_func_in_func(did, builder.func);
                builder.ins().call(local_did, &[ptr_val]);
            }
        }

        for (offset, f_ty) in droppable_fields {
            let drop_arg = if is_aggregate_type(&f_ty, struct_layouts, enum_layouts) {
                builder.ins().iadd_imm(ptr_val, offset as i64)
            } else {
                builder.ins().load(
                    cranelift_type_of(&f_ty),
                    MemFlags::new(),
                    ptr_val,
                    offset as i32,
                )
            };
            emit_drop_for_value(
                &mut builder,
                drop_arg,
                &f_ty,
                known_drop_fns,
                struct_layouts,
                enum_layouts,
                module,
            );
        }

        builder.ins().jump(exit_block, &[]);

        builder.switch_to_block(exit_block);
        builder.seal_block(exit_block);
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();
    }

    let _ = module.define_function(func_id, &mut ctx);
    module.clear_context(&mut ctx);
    Some(func_id)
}

pub fn allocate_drop_flag(builder: &mut FunctionBuilder) -> StackSlot {
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        1,
        0,
    ));
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().stack_store(one, slot, 0);
    slot
}

pub fn mark_drop_flag_moved(builder: &mut FunctionBuilder, slot: StackSlot) {
    let zero = builder.ins().iconst(types::I8, 0);
    builder.ins().stack_store(zero, slot, 0);
}

pub fn mark_drop_flag_active(builder: &mut FunctionBuilder, slot: StackSlot) {
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().stack_store(one, slot, 0);
}

pub fn emit_drop_for_value<M: Module>(
    builder: &mut FunctionBuilder,
    val: Value,
    ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) {
    let Some(callee) = resolve_or_synthesize_drop_fn(ty, known_drop_fns, struct_layouts, enum_layouts, module) else {
        return;
    };
    let local_callee = module.declare_func_in_func(callee, builder.func);
    builder.ins().call(local_callee, &[val]);
}

pub fn emit_drop_fn_ptr<M: Module>(
    builder: &mut FunctionBuilder,
    inner_ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Value {
    match resolve_or_synthesize_drop_fn(inner_ty, known_drop_fns, struct_layouts, enum_layouts, module) {
        Some(id) => {
            let local_callee = module.declare_func_in_func(id, builder.func);
            builder.ins().func_addr(types::I64, local_callee)
        }
        None => builder.ins().iconst(types::I64, 0),
    }
}

/// Emits a destructor function pointer for heap-boxed aggregates (`rc[T]`, `arc[T]`, `dyn Trait`),
/// running `in_place` drop (if any) and then `free(ptr)` on the heap box.
pub fn emit_heap_drop_fn_ptr<M: Module>(
    builder: &mut FunctionBuilder,
    inner_ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Value {
    if !is_aggregate_type(inner_ty, struct_layouts, enum_layouts) {
        return emit_drop_fn_ptr(builder, inner_ty, known_drop_fns, struct_layouts, enum_layouts, module);
    }

    let in_place_id =
        resolve_or_synthesize_drop_fn(inner_ty, known_drop_fns, struct_layouts, enum_layouts, module);
    let Some(drop_id) = in_place_id else {
        let mut free_sig = module.make_signature();
        free_sig.params.push(AbiParam::new(types::I64));
        let free_id = module
            .declare_function("free", Linkage::Import, &free_sig)
            .unwrap();
        let local_free = module.declare_func_in_func(free_id, builder.func);
        return builder.ins().func_addr(types::I64, local_free);
    };

    let synth_name = format!("__gdrs_heap_drop_{}", crate::sanal::mono::type_suffix(inner_ty));
    let heap_fn_id = if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
        id
    } else {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function(&synth_name, Linkage::Export, &sig)
            .unwrap();
        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut fbuilder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = fbuilder.create_block();
            fbuilder.switch_to_block(entry);
            fbuilder.append_block_params_for_function_params(entry);
            let ptr_val = fbuilder.block_params(entry)[0];

            let drop_body = fbuilder.create_block();
            let exit_blk = fbuilder.create_block();
            fbuilder.ins().brif(ptr_val, drop_body, &[], exit_blk, &[]);

            fbuilder.switch_to_block(drop_body);
            fbuilder.seal_block(drop_body);
            let local_drop = module.declare_func_in_func(drop_id, fbuilder.func);
            fbuilder.ins().call(local_drop, &[ptr_val]);
            emit_free_call(&mut fbuilder, ptr_val, module);
            fbuilder.ins().jump(exit_blk, &[]);

            fbuilder.switch_to_block(exit_blk);
            fbuilder.seal_block(exit_blk);
            fbuilder.ins().return_(&[]);
            fbuilder.seal_all_blocks();
            fbuilder.finalize();
        }
        let _ = module.define_function(fid, &mut ctx);
        module.clear_context(&mut ctx);
        fid
    };
    let local_callee = module.declare_func_in_func(heap_fn_id, builder.func);
    builder.ins().func_addr(types::I64, local_callee)
}

pub fn emit_conditional_drop<M: Module>(
    builder: &mut FunctionBuilder,
    var: Variable,
    ty: &Type,
    slot: StackSlot,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) {
    if !has_drop_glue(ty, known_drop_fns, struct_layouts, enum_layouts) || builder.is_unreachable() {
        return;
    }

    let flag = builder.ins().stack_load(types::I8, slot, 0);
    let drop_block = builder.create_block();
    let cont_block = builder.create_block();

    builder.ins().brif(flag, drop_block, &[], cont_block, &[]);

    builder.switch_to_block(drop_block);
    builder.seal_block(drop_block);

    // Mark as dropped (flag = 0) to prevent double drop
    mark_drop_flag_moved(builder, slot);

    // Emit the drop glue execution using the exact Variable captured at binding time
    let val = builder.use_var(var);
    emit_drop_for_value(builder, val, ty, known_drop_fns, struct_layouts, enum_layouts, module);

    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}
