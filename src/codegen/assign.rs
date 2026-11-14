use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr, TypedStructPattern, TypedTuplePattern};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{emit_conditional_drop, emit_drop_for_value, has_drop_glue, mark_drop_flag_active};
use crate::codegen::expr::{coerce_typed_val, compile_expr, cranelift_type_of};
use crate::codegen::layout::{
    alloc_stack_slot, emit_memcpy_bytes, find_struct_layout, is_aggregate_type, size_and_align,
    tuple_field_offsets,
};

pub fn compile_let<M: Module>(
    builder: &mut FunctionBuilder,
    value: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
    name: &str,
) -> Value {
    let val = compile_expr(builder, value, cg, module);
    cg.cancel_temp(val);

    // Transfer ownership if moving from an existing droppable variable
    if let TypedExpr::Ident(src_name, src_ty, _) = value {
        if !src_ty.is_copy() {
            cg.mark_moved(builder, src_name);
        }
    }

    let var = Variable::from_u32(cg.var_counter as u32);
    cg.var_counter += 1;

    let is_str_to_string = matches!(
        ty,
        Type::String | Type::Obj("String") | Type::Obj("std_string_String")
    ) && value.ty() == Type::Str;

    let stored_val = if is_str_to_string {
        builder.declare_var(var, types::I64);
        let (_, dst_ptr) = alloc_stack_slot(builder, 24, 8);
        builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().store(MemFlags::new(), zero, dst_ptr, 8);
        builder.ins().store(MemFlags::new(), zero, dst_ptr, 16);
        dst_ptr
    } else if let (Type::Vec(elem_ty), Type::Array(_, arr_len)) = (ty, value.ty()) {
        builder.declare_var(var, types::I64);
        if let TypedExpr::Ident(src_name, _, _) = value {
            cg.mark_moved(builder, src_name);
        }
        crate::codegen::arrays::alloc_stack_vec_header_from_array(
            builder,
            val,
            elem_ty,
            arr_len,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        )
    } else if let (
        Type::Slice(_) | Type::Ref(Type::Slice(_)) | Type::MutRef(Type::Slice(_)),
        Type::Array(_, arr_len)
        | Type::Ref(&Type::Array(_, arr_len))
        | Type::MutRef(&Type::Array(_, arr_len)),
    ) = (ty, value.ty())
    {
        builder.declare_var(var, types::I64);
        crate::codegen::arrays::alloc_stack_slice_header(builder, val, arr_len)
    } else if is_aggregate_type(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        builder.declare_var(var, types::I64);
        let (size, align) = size_and_align(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
        let (_, dst_addr) = alloc_stack_slot(builder, size, align);
        emit_memcpy_bytes(builder, module, dst_addr, val, size);
        dst_addr
    } else {
        let cranelift_ty = cranelift_type_of(ty);
        builder.declare_var(var, cranelift_ty);
        coerce_typed_val(builder, val, &value.ty(), cranelift_ty)
    };

    builder.def_var(var, stored_val);
    cg.bind_var(name, var, *ty);
    if !is_aggregate_type(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        let cranelift_ty = cranelift_type_of(ty);
        cg.track_addr_taken_slot(builder, name, ty, cranelift_ty, stored_val);
    }
    cg.track_var_if_droppable(builder, name, ty, true);

    stored_val
}

fn drop_value_at_addr<M: Module>(
    builder: &mut FunctionBuilder,
    ty: &Type,
    src_addr: Value,
    cg: &CodegenCtx,
    module: &mut M,
) {
    if has_drop_glue(
        ty,
        &cg.meta.known_drop_fns,
        &cg.meta.struct_layouts,
        cg.meta.enum_layouts,
    ) {
        let drop_arg = if is_aggregate_type(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            src_addr
        } else {
            builder
                .ins()
                .load(cranelift_type_of(ty), MemFlags::new(), src_addr, 0)
        };
        emit_drop_for_value(
            builder,
            drop_arg,
            ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        );
    }
}

fn bind_value_from_addr<M: Module>(
    builder: &mut FunctionBuilder,
    name: &str,
    ty: &Type,
    src_addr: Value,
    cg: &mut CodegenCtx,
    module: &mut M,
) {
    if name == "_" {
        drop_value_at_addr(builder, ty, src_addr, cg, module);
        return;
    }
    let var = Variable::from_u32(cg.var_counter as u32);
    cg.var_counter += 1;
    if is_aggregate_type(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        let (size, align) = size_and_align(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
        let (_, dst_addr) = alloc_stack_slot(builder, size, align);
        emit_memcpy_bytes(builder, module, dst_addr, src_addr, size);
        builder.declare_var(var, types::I64);
        builder.def_var(var, dst_addr);
        cg.bind_var(name, var, *ty);
        cg.track_var_if_droppable(builder, name, ty, true);
    } else {
        let cl_ty = cranelift_type_of(ty);
        let loaded = if *ty == Type::Unit || *ty == Type::Void {
            builder.ins().iconst(types::I64, 0)
        } else {
            builder.ins().load(cl_ty, MemFlags::new(), src_addr, 0)
        };
        builder.declare_var(var, cl_ty);
        builder.def_var(var, loaded);
        cg.bind_var(name, var, *ty);
        cg.track_addr_taken_slot(builder, name, ty, cl_ty, loaded);
        cg.track_var_if_droppable(builder, name, ty, true);
    }
}

fn bind_compiled_tuple_pattern<M: Module>(
    builder: &mut FunctionBuilder,
    pat: &TypedTuplePattern,
    src_addr: Value,
    cg: &mut CodegenCtx,
    module: &mut M,
) {
    match pat {
        TypedTuplePattern::Ident { name, ty, .. } => {
            bind_value_from_addr(builder, name, ty, src_addr, cg, module);
        }
        TypedTuplePattern::Tuple(subpats, tup_ty, _) => {
            let elem_tys: Vec<Type> = match tup_ty {
                Type::Tuple(elems) => elems.to_vec(),
                _ => Vec::new(),
            };
            let (_, _, offsets) =
                tuple_field_offsets(&elem_tys, &cg.meta.struct_layouts, cg.meta.enum_layouts);
            for (i, sub) in subpats.iter().enumerate() {
                let off = offsets.get(i).copied().unwrap_or((i * 8) as u32);
                let sub_addr = if off == 0 {
                    src_addr
                } else {
                    builder.ins().iadd_imm(src_addr, off as i64)
                };
                bind_compiled_tuple_pattern(builder, sub, sub_addr, cg, module);
            }
        }
    }
}

pub fn compile_let_tuple<M: Module>(
    builder: &mut FunctionBuilder,
    pat: &TypedTuplePattern,
    rhs: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let val = compile_expr(builder, rhs, cg, module);
    cg.cancel_temp(val);
    if let TypedExpr::Ident(src_name, src_ty, _) = rhs {
        if !src_ty.is_copy() {
            cg.mark_moved(builder, src_name);
        }
    }
    bind_compiled_tuple_pattern(builder, pat, val, cg, module);
    builder.ins().iconst(types::I64, 0)
}

pub fn compile_let_struct<M: Module>(
    builder: &mut FunctionBuilder,
    pat: &TypedStructPattern,
    rhs: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let val = compile_expr(builder, rhs, cg, module);
    cg.cancel_temp(val);
    if let TypedExpr::Ident(src_name, src_ty, _) = rhs {
        if !src_ty.is_copy() {
            cg.mark_moved(builder, src_name);
        }
    }

    let layout = find_struct_layout(&cg.meta.struct_layouts, &pat.struct_name).cloned();
    let offset_of = |fname: &str, fallback: u32| -> u32 {
        layout
            .as_ref()
            .and_then(|l| l.field_offsets.get(fname).map(|(off, _)| *off))
            .unwrap_or(fallback)
    };

    for field in &pat.bindings {
        let off = offset_of(&field.field_name, field.offset);
        let src_addr = if off == 0 {
            val
        } else {
            builder.ins().iadd_imm(val, off as i64)
        };
        bind_value_from_addr(builder, &field.binding_name, &field.ty, src_addr, cg, module);
    }

    for (fname, fty, fallback_off) in &pat.dropped_fields {
        let off = offset_of(fname, *fallback_off);
        let src_addr = if off == 0 {
            val
        } else {
            builder.ins().iadd_imm(val, off as i64)
        };
        drop_value_at_addr(builder, fty, src_addr, cg, module);
    }

    builder.ins().iconst(types::I64, 0)
}

pub fn compile_assign<M: Module>(
    builder: &mut FunctionBuilder,
    value: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
    name: &str,
) -> Value {
    let raw_val = compile_expr(builder, value, cg, module);
    cg.cancel_temp(raw_val);

    if let TypedExpr::Ident(src_name, src_ty, _) = value {
        if !src_ty.is_copy() {
            cg.mark_moved(builder, src_name);
        }
    }

    let var = cg.vars.get(name).copied().expect("Undefined variable during codegen");
    let dest_ptr = builder.use_var(var);
    let target_ty = cg.var_types.get(name).copied().unwrap_or_else(|| value.ty());

    let val = if let (Type::Vec(elem_ty), Type::Array(_, arr_len)) = (target_ty, value.ty()) {
        crate::codegen::arrays::alloc_stack_vec_header_from_array(
            builder,
            raw_val,
            elem_ty,
            arr_len,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        )
    } else if let (
        Type::Slice(_) | Type::Ref(Type::Slice(_)) | Type::MutRef(Type::Slice(_)),
        Type::Array(_, arr_len)
        | Type::Ref(&Type::Array(_, arr_len))
        | Type::MutRef(&Type::Array(_, arr_len)),
    ) = (target_ty, value.ty())
    {
        crate::codegen::arrays::alloc_stack_slice_header(builder, raw_val, arr_len)
    } else {
        raw_val
    };

    if is_aggregate_type(&target_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        if let Some(&slot) = cg.drop_flags.get(name) {
            if has_drop_glue(
                &target_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
            ) {
                let is_diff = builder.ins().icmp(IntCC::NotEqual, dest_ptr, val);
                let drop_old = builder.create_block();
                let cont = builder.create_block();
                builder.ins().brif(is_diff, drop_old, &[], cont, &[]);
                builder.switch_to_block(drop_old);
                builder.seal_block(drop_old);
                emit_conditional_drop(
                    builder,
                    var,
                    &target_ty,
                    slot,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
                builder.ins().jump(cont, &[]);
                builder.switch_to_block(cont);
                builder.seal_block(cont);
            }
        }

        let (size, _) = size_and_align(&target_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
        emit_memcpy_bytes(builder, module, dest_ptr, val, size);
        if let Some(&slot) = cg.drop_flags.get(name) {
            mark_drop_flag_active(builder, slot);
        }
        dest_ptr
    } else {
        if let Some(&slot) = cg.drop_flags.get(name) {
            emit_conditional_drop(
                builder,
                var,
                &target_ty,
                slot,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
                module,
            );
        }

        let final_val = if let Some(&(slot, slot_ty)) = cg.var_slots.get(name) {
            let v = coerce_typed_val(builder, val, &value.ty(), slot_ty);
            builder.ins().stack_store(v, slot, 0);
            v
        } else {
            let var_ty = builder.func.dfg.value_type(dest_ptr);
            let v = coerce_typed_val(builder, val, &value.ty(), var_ty);
            builder.def_var(var, v);
            v
        };

        if let Some(&slot) = cg.drop_flags.get(name) {
            mark_drop_flag_active(builder, slot);
        }
        final_val
    }
}
