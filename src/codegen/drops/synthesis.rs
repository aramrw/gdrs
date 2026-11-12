//! codegen/drops/synthesis.rs
//! Recursive drop function synthesis for aggregates, enums, vecs, and custom Drop implementations.

use std::collections::{HashMap, HashSet};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{FuncId, Linkage, Module};

use crate::ast::Type;
use crate::codegen::drops::{
    explicit_drop_fn_name, find_enum_layout, find_layout, flags::emit_drop_for_value, has_drop_glue,
    is_npo_enum, EnumLayoutMap,
};
use crate::codegen::expr::cranelift_type_of;
use crate::codegen::layout::{
    array_stride, enum_variant_offsets, find_struct_layout, is_aggregate_type, tuple_field_offsets,
};
use crate::sanal::StructLayout;

pub(crate) fn emit_free_call<M: Module>(builder: &mut FunctionBuilder, ptr_val: Value, module: &mut M) {
    let mut free_sig = module.make_signature();
    free_sig.params.push(AbiParam::new(types::I64));
    let free_id = module
        .declare_function("free", Linkage::Import, &free_sig)
        .unwrap();
    let local_free = module.declare_func_in_func(free_id, builder.func);
    builder.ins().call(local_free, &[ptr_val]);
}

pub fn resolve_or_synthesize_drop_fn<M: Module>(
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
