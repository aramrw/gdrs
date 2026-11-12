//! codegen/objects.rs
//! Codegen for stack-backed struct/object initialization, field access/assignment, and enum construction.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{emit_drop_for_value, find_enum_layout, has_drop_glue, is_npo_enum};
use crate::codegen::expr::{coerce_typed_val, compile_expr, cranelift_type_of};
use crate::codegen::layout::{
    alloc_stack_slot, emit_memcpy_bytes, enum_variant_offsets, find_struct_layout,
    is_aggregate_type, repr_kind, size_and_align, tuple_field_offsets, ReprKind,
};

fn target_struct_name(target_ty: &Type) -> Option<&'static str> {
    match target_ty {
        Type::Obj(struct_name) => Some(struct_name),
        Type::Vec(_) => Some("std_vec_Vec"),
        Type::String => Some("std_string_String"),
        Type::Ref(inner) | Type::MutRef(inner) => target_struct_name(inner),
        _ => None,
    }
}

pub fn compile_obj_init<M: Module>(
    builder: &mut FunctionBuilder,
    struct_name: &str,
    fields: &[(String, TypedExpr)],
    obj_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let layout_opt = find_struct_layout(&cg.meta.struct_layouts, struct_name).cloned();
    let (size, align) = if layout_opt.is_some() {
        size_and_align(obj_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts)
    } else {
        ((fields.len() as u32) * 8, 8)
    };
    let (_, base_ptr) = alloc_stack_slot(builder, size, align);

    for (i, (field_name, field_expr)) in fields.iter().enumerate() {
        let raw_val = compile_expr(builder, field_expr, cg, module);
        cg.cancel_temp(raw_val);
        if let TypedExpr::Ident(v_name, v_ty, _) = field_expr {
            if !v_ty.is_copy() {
                cg.mark_moved(builder, v_name);
            }
        }
        let (offset, field_ty) = if let Some(layout) = &layout_opt {
            if let Some((off, ty)) = layout.field_offsets.get(field_name) {
                (*off as i32, *ty)
            } else {
                ((i * 8) as i32, field_expr.ty())
            }
        } else {
            ((i * 8) as i32, field_expr.ty())
        };

        if matches!(field_ty, Type::Slice(_)) {
            if let Type::Array(_, arr_len) = field_expr.ty() {
                let slice_addr = crate::codegen::arrays::alloc_stack_slice_header(
                    builder,
                    raw_val,
                    arr_len,
                );
                let dst = builder.ins().iadd_imm(base_ptr, offset as i64);
                emit_memcpy_bytes(builder, module, dst, slice_addr, 16);
                continue;
            }
        }
        if matches!(field_ty, Type::Vec(_)) {
            if let Type::Array(elem_ty, arr_len) = field_expr.ty() {
                let vec_addr = crate::codegen::arrays::alloc_stack_vec_header_from_array(
                    builder,
                    raw_val,
                    &elem_ty,
                    arr_len,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
                let dst = builder.ins().iadd_imm(base_ptr, offset as i64);
                emit_memcpy_bytes(builder, module, dst, vec_addr, 24);
                continue;
            }
        }

        match repr_kind(&field_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            ReprKind::Zst => {}
            ReprKind::Aggregate { size: f_size, .. } => {
                let dst = if offset == 0 {
                    base_ptr
                } else {
                    builder.ins().iadd_imm(base_ptr, offset as i64)
                };
                emit_memcpy_bytes(builder, module, dst, raw_val, f_size);
            }
            ReprKind::Scalar(target_cl_ty) => {
                let val = coerce_typed_val(builder, raw_val, &field_expr.ty(), target_cl_ty);
                builder.ins().store(MemFlags::new(), val, base_ptr, offset);
            }
        }
    }

    base_ptr
}

pub fn compile_tuple_init<M: Module>(
    builder: &mut FunctionBuilder,
    elems: &[TypedExpr],
    tup_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    if elems.is_empty() {
        return builder.ins().iconst(types::I64, 0);
    }
    let elem_tys: Vec<Type> = match tup_ty {
        Type::Tuple(ts) => ts.to_vec(),
        _ => elems.iter().map(|e| e.ty()).collect(),
    };
    let (size, align, offsets) =
        tuple_field_offsets(&elem_tys, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    if size == 0 {
        return builder.ins().iconst(types::I64, 0);
    }
    let (_, base_ptr) = alloc_stack_slot(builder, size, align);

    for (i, elem) in elems.iter().enumerate() {
        let raw_val = compile_expr(builder, elem, cg, module);
        cg.cancel_temp(raw_val);
        if let TypedExpr::Ident(v_name, v_ty, _) = elem {
            if !v_ty.is_copy() {
                cg.mark_moved(builder, v_name);
            }
        }
        let field_ty = elem_tys.get(i).copied().unwrap_or_else(|| elem.ty());
        let offset = offsets.get(i).copied().unwrap_or((i * 8) as u32) as i32;
        match repr_kind(&field_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            ReprKind::Zst => {}
            ReprKind::Aggregate { size: f_size, .. } => {
                let dst = if offset == 0 {
                    base_ptr
                } else {
                    builder.ins().iadd_imm(base_ptr, offset as i64)
                };
                emit_memcpy_bytes(builder, module, dst, raw_val, f_size);
            }
            ReprKind::Scalar(target_cl_ty) => {
                let val = coerce_typed_val(builder, raw_val, &elem.ty(), target_cl_ty);
                builder.ins().store(MemFlags::new(), val, base_ptr, offset);
            }
        }
    }

    base_ptr
}

pub fn compile_field_access<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    field_name: &str,
    field_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let base_ptr = compile_expr(builder, target, cg, module);
    let mut offset = 0i32;

    let unwrapped_target = match target.ty() {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };
    if let Type::Tuple(elems) = unwrapped_target {
        if let Ok(idx) = field_name.parse::<usize>() {
            let (_, _, offsets) =
                tuple_field_offsets(elems, &cg.meta.struct_layouts, cg.meta.enum_layouts);
            offset = offsets.get(idx).copied().unwrap_or(0) as i32;
        }
    } else if let Some(struct_name) = target_struct_name(&target.ty()) {
        if let Some(layout) = find_struct_layout(&cg.meta.struct_layouts, struct_name) {
            if let Some((f_offset, _)) = layout.field_offsets.get(field_name) {
                offset = *f_offset as i32;
            }
        }
    }

    match repr_kind(field_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        ReprKind::Zst => builder.ins().iconst(types::I64, 0),
        ReprKind::Aggregate { .. } => {
            if offset == 0 {
                base_ptr
            } else {
                builder.ins().iadd_imm(base_ptr, offset as i64)
            }
        }
        ReprKind::Scalar(cl_ty) => builder.ins().load(cl_ty, MemFlags::new(), base_ptr, offset),
    }
}

pub fn compile_field_assign<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    field_name: &str,
    val: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let base_ptr = compile_expr(builder, target, cg, module);
    let mut new_val = compile_expr(builder, val, cg, module);
    cg.cancel_temp(new_val);
    if let TypedExpr::Ident(v_name, v_ty, _) = val {
        if !v_ty.is_copy() {
            cg.mark_moved(builder, v_name);
        }
    }
    let mut offset = 0i32;
    let mut field_ty = val.ty();

    let unwrapped_target = match target.ty() {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };
    if let Type::Tuple(elems) = unwrapped_target {
        if let Ok(idx) = field_name.parse::<usize>() {
            let (_, _, offsets) =
                tuple_field_offsets(elems, &cg.meta.struct_layouts, cg.meta.enum_layouts);
            offset = offsets.get(idx).copied().unwrap_or(0) as i32;
            if let Some(&fty) = elems.get(idx) {
                field_ty = fty;
            }
        }
    } else if let Some(struct_name) = target_struct_name(&target.ty()) {
        if let Some(layout) = find_struct_layout(&cg.meta.struct_layouts, struct_name) {
            if let Some((f_offset, f_ty)) = layout.field_offsets.get(field_name) {
                offset = *f_offset as i32;
                field_ty = *f_ty;
            }
        }
    }

    match repr_kind(&field_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        ReprKind::Zst => builder.ins().iconst(types::I64, 0),
        ReprKind::Aggregate { size: f_size, .. } => {
            let dst_addr = if offset == 0 {
                base_ptr
            } else {
                builder.ins().iadd_imm(base_ptr, offset as i64)
            };
            if has_drop_glue(
                &field_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
            ) {
                let is_diff = builder.ins().icmp(IntCC::NotEqual, dst_addr, new_val);
                let drop_blk = builder.create_block();
                let cont_blk = builder.create_block();
                builder.ins().brif(is_diff, drop_blk, &[], cont_blk, &[]);
                builder.switch_to_block(drop_blk);
                builder.seal_block(drop_blk);
                emit_drop_for_value(
                    builder,
                    dst_addr,
                    &field_ty,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
                builder.ins().jump(cont_blk, &[]);
                builder.switch_to_block(cont_blk);
                builder.seal_block(cont_blk);
            }
            emit_memcpy_bytes(builder, module, dst_addr, new_val, f_size);
            dst_addr
        }
        ReprKind::Scalar(target_cl_ty) => {
            new_val = coerce_typed_val(builder, new_val, &val.ty(), target_cl_ty);
            if has_drop_glue(
                &field_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
            ) {
                let old_val = builder.ins().load(target_cl_ty, MemFlags::new(), base_ptr, offset);
                let non_null = builder.ins().icmp_imm(IntCC::NotEqual, old_val, 0);
                let is_diff = builder.ins().icmp(IntCC::NotEqual, old_val, new_val);
                let should_drop = builder.ins().band(non_null, is_diff);
                let drop_blk = builder.create_block();
                let cont_blk = builder.create_block();
                builder.ins().brif(should_drop, drop_blk, &[], cont_blk, &[]);
                builder.switch_to_block(drop_blk);
                builder.seal_block(drop_blk);
                emit_drop_for_value(
                    builder,
                    old_val,
                    &field_ty,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
                builder.ins().jump(cont_blk, &[]);
                builder.switch_to_block(cont_blk);
                builder.seal_block(cont_blk);
            }
            builder.ins().store(MemFlags::new(), new_val, base_ptr, offset);
            new_val
        }
    }
}

pub fn compile_enum_construct<M: Module>(
    builder: &mut FunctionBuilder,
    enum_name: &str,
    variant_name: &str,
    disc: &usize,
    payload_exprs: &[TypedExpr],
    enum_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    if is_npo_enum(enum_name) {
        if variant_name.ends_with("None") || *disc == 1 || payload_exprs.is_empty() {
            return builder.ins().iconst(types::I64, 0);
        } else {
            let p_val = compile_expr(builder, &payload_exprs[0], cg, module);
            cg.cancel_temp(p_val);
            return p_val;
        }
    }

    let (total_size, align) = size_and_align(enum_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    let (_, base_ptr) = alloc_stack_slot(builder, total_size, align);

    let disc_val = builder.ins().iconst(types::I64, *disc as i64);
    builder.ins().store(MemFlags::new(), disc_val, base_ptr, 0);

    let payload_tys: Vec<Type> = find_enum_layout(enum_name, cg.meta.enum_layouts)
        .and_then(|vs| {
            vs.iter()
                .find(|(_, tag, _)| *tag == (*disc as i64))
                .map(|(_, _, pts)| pts.clone())
        })
        .unwrap_or_else(|| payload_exprs.iter().map(|p| p.ty()).collect());
    let (_, _, offsets) =
        enum_variant_offsets(&payload_tys, &cg.meta.struct_layouts, cg.meta.enum_layouts);

    for (i, payload) in payload_exprs.iter().enumerate() {
        let p_ty = payload_tys.get(i).copied().unwrap_or_else(|| payload.ty());
        let off = offsets.get(i).copied().unwrap_or(((i + 1) * 8) as u32);
        let val = compile_expr(builder, payload, cg, module);
        cg.cancel_temp(val);
        if let TypedExpr::Ident(v_name, v_ty, _) = payload {
            if !v_ty.is_copy() {
                cg.mark_moved(builder, v_name);
            }
        }
        if is_aggregate_type(&p_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            let (p_size, _) = size_and_align(&p_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
            let dst = builder.ins().iadd_imm(base_ptr, off as i64);
            emit_memcpy_bytes(builder, module, dst, val, p_size);
        } else {
            let target_cl_ty = cranelift_type_of(&p_ty);
            let coerced = coerce_typed_val(builder, val, &payload.ty(), target_cl_ty);
            builder
                .ins()
                .store(MemFlags::new(), coerced, base_ptr, off as i32);
        }
    }

    base_ptr
}
