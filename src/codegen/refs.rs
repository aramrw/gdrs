use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{emit_drop_for_value, has_drop_glue};
use crate::codegen::expr::{coerce_typed_val, compile_expr, cranelift_type_of};
use crate::codegen::layout::{
    emit_memcpy_bytes, find_struct_layout, is_aggregate_type, size_and_align, tuple_field_offsets,
};

fn store_scalar_in_temp_slot(builder: &mut FunctionBuilder, val: Value) -> Value {
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        8,
        0,
    ));
    let ptr = builder.ins().stack_addr(types::I64, slot, 0);
    builder.ins().store(MemFlags::new(), val, ptr, 0);
    ptr
}

fn is_ref_passthrough_ty(
    ty: &Type,
    struct_layouts: &std::collections::HashMap<String, crate::sanal::StructLayout>,
    enum_layouts: &std::collections::HashMap<String, Vec<(String, i64, Vec<Type>)>>,
) -> bool {
    is_aggregate_type(ty, struct_layouts, enum_layouts)
        || matches!(
            ty,
            Type::Obj(_)
                | Type::Enum(_)
                | Type::String
                | Type::Vec(_)
                | Type::Slice(_)
                | Type::Array(_, _)
                | Type::Ref(_)
                | Type::MutRef(_)
                | Type::DynTrait(_)
        )
}

pub fn compile_ref<M: Module>(
    builder: &mut FunctionBuilder,
    inner_expr: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    match inner_expr {
        TypedExpr::StaticRef(name, _, _) => {
            let is_mut = cg
                .meta
                .static_globals
                .get(name)
                .map(|(_, m)| *m)
                .unwrap_or(false);
            crate::codegen::expr::emit_static_addr(builder, name, is_mut, module)
        }
        TypedExpr::Ident(name, ty, _) => {
            if matches!(ty, Type::DynTrait(_)) {
                return compile_expr(builder, inner_expr, cg, module);
            }
            if let Some(&(slot, _)) = cg.var_slots.get(name) {
                return builder.ins().stack_addr(types::I64, slot, 0);
            }
            let val = compile_expr(builder, inner_expr, cg, module);
            if is_ref_passthrough_ty(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                val
            } else {
                store_scalar_in_temp_slot(builder, val)
            }
        }
        TypedExpr::FieldAccess(target, field_name, field_ty, _) => {
            if is_ref_passthrough_ty(field_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                return compile_expr(builder, inner_expr, cg, module);
            }
            let (base_ptr, unwrapped_target) =
                crate::codegen::objects::unwrap_struct_base_ptr(builder, target, cg, module);
            let mut offset = 0i32;
            if let Type::Tuple(elems) = unwrapped_target {
                if let Ok(idx) = field_name.parse::<usize>() {
                    let (_, _, offsets) =
                        tuple_field_offsets(elems, &cg.meta.struct_layouts, cg.meta.enum_layouts);
                    offset = offsets.get(idx).copied().unwrap_or(0) as i32;
                }
            } else {
                let target_struct_name = match unwrapped_target {
                    Type::Obj(struct_name) => Some(struct_name),
                    Type::Vec(_) => Some("std_vec_Vec"),
                    Type::String => Some("std_string_String"),
                    _ => None,
                };
                if let Some(struct_name) = target_struct_name {
                    if let Some(layout) = find_struct_layout(&cg.meta.struct_layouts, struct_name) {
                        if let Some((f_offset, _)) = layout.field_offsets.get(field_name) {
                            offset = *f_offset as i32;
                        }
                    }
                }
            }
            if offset == 0 {
                base_ptr
            } else {
                builder.ins().iadd_imm(base_ptr, offset as i64)
            }
        }
        TypedExpr::IndexAccess(target, idx, elem_ty, _) => {
            if matches!(idx.as_ref(), TypedExpr::Range(..))
                || matches!(elem_ty, Type::Slice(_) | Type::Str)
            {
                compile_expr(builder, inner_expr, cg, module)
            } else {
                crate::codegen::arrays::compile_index_addr(builder, target, idx, elem_ty, cg, module)
                    .0
            }
        }
        TypedExpr::Deref(ptr_expr, deref_ty, _) => {
            let ptr_val = compile_expr(builder, ptr_expr, cg, module);
            if matches!(ptr_expr.ty(), Type::Rc(_) | Type::Arc(_)) {
                if is_aggregate_type(deref_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                    builder.ins().load(types::I64, MemFlags::new(), ptr_val, 8)
                } else {
                    builder.ins().iadd_imm(ptr_val, 8)
                }
            } else {
                ptr_val
            }
        }
        _ => {
            let ty = inner_expr.ty();
            let val = compile_expr(builder, inner_expr, cg, module);
            if is_ref_passthrough_ty(&ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                val
            } else {
                store_scalar_in_temp_slot(builder, val)
            }
        }
    }
}

pub fn compile_deref<M: Module>(
    builder: &mut FunctionBuilder,
    inner_expr: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    if matches!(inner_expr.ty(), Type::Box(_)) && !ty.is_copy() {
        let ptr_val = compile_expr(builder, inner_expr, cg, module);
        cg.cancel_temp(ptr_val);
        let res_val = if is_aggregate_type(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            let (size, align) = size_and_align(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
            let (_, dst_addr) = crate::codegen::layout::alloc_stack_slot(builder, size, align);
            emit_memcpy_bytes(builder, module, dst_addr, ptr_val, size);
            dst_addr
        } else {
            let load_ty = cranelift_type_of(ty);
            builder.ins().load(load_ty, MemFlags::new(), ptr_val, 0)
        };
        crate::codegen::drops::synthesis::emit_free_call(builder, ptr_val, module);
        if let TypedExpr::Ident(b_name, _, _) = inner_expr {
            cg.mark_moved(builder, b_name);
        }
        return res_val;
    }

    let ptr_val = compile_expr(builder, inner_expr, cg, module);
    let is_rc_arc = matches!(inner_expr.ty(), Type::Rc(_) | Type::Arc(_));
    if is_aggregate_type(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        if is_rc_arc {
            builder.ins().load(types::I64, MemFlags::new(), ptr_val, 8)
        } else {
            ptr_val
        }
    } else {
        let offset = if is_rc_arc { 8 } else { 0 };
        let load_ty = cranelift_type_of(ty);
        builder.ins().load(load_ty, MemFlags::new(), ptr_val, offset)
    }
}

pub fn compile_deref_assign<M: Module>(
    builder: &mut FunctionBuilder,
    ptr_expr: &TypedExpr,
    val_expr: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let ptr_val = compile_expr(builder, ptr_expr, cg, module);
    let val = compile_expr(builder, val_expr, cg, module);
    cg.cancel_temp(val);
    if let TypedExpr::Ident(v_name, v_ty, _) = val_expr {
        if !v_ty.is_copy() {
            cg.mark_moved(builder, v_name);
        }
    }

    let (is_rc_arc, inner_ty, drop_inner) = match ptr_expr.ty() {
        Type::Rc(inner) | Type::Arc(inner) => (true, *inner, Some(*inner)),
        Type::Box(inner) => (false, *inner, Some(*inner)),
        Type::Ptr(inner) => (false, *inner, None),
        Type::MutRef(inner) => (false, *inner, Some(*inner)),
        _ => (false, val_expr.ty(), None),
    };

    if is_aggregate_type(&inner_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        let dst_ptr = if is_rc_arc {
            builder.ins().load(types::I64, MemFlags::new(), ptr_val, 8)
        } else {
            ptr_val
        };
        if let Some(d_ty) = drop_inner {
            if has_drop_glue(
                &d_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
            ) {
                let is_diff = builder.ins().icmp(IntCC::NotEqual, dst_ptr, val);
                let drop_blk = builder.create_block();
                let cont_blk = builder.create_block();
                builder.ins().brif(is_diff, drop_blk, &[], cont_blk, &[]);
                builder.switch_to_block(drop_blk);
                builder.seal_block(drop_blk);
                emit_drop_for_value(
                    builder,
                    dst_ptr,
                    &d_ty,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
                builder.ins().jump(cont_blk, &[]);
                builder.switch_to_block(cont_blk);
                builder.seal_block(cont_blk);
            }
        }
        let (size, _) = size_and_align(&inner_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
        emit_memcpy_bytes(builder, module, dst_ptr, val, size);
        return builder.ins().iconst(types::I64, 0);
    }

    let offset = if is_rc_arc { 8 } else { 0 };
    let target_cranelift_ty = cranelift_type_of(&inner_ty);
    let stored_val = coerce_typed_val(builder, val, &val_expr.ty(), target_cranelift_ty);

    if let Some(d_ty) = drop_inner {
        if has_drop_glue(
            &d_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
        ) {
            let old_val = builder
                .ins()
                .load(target_cranelift_ty, MemFlags::new(), ptr_val, offset);
            let non_null = builder.ins().icmp_imm(IntCC::NotEqual, old_val, 0);
            let is_diff = builder.ins().icmp(IntCC::NotEqual, old_val, stored_val);
            let should_drop = builder.ins().band(non_null, is_diff);
            let drop_blk = builder.create_block();
            let cont_blk = builder.create_block();
            builder.ins().brif(should_drop, drop_blk, &[], cont_blk, &[]);
            builder.switch_to_block(drop_blk);
            builder.seal_block(drop_blk);
            emit_drop_for_value(
                builder,
                old_val,
                &d_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
                module,
            );
            builder.ins().jump(cont_blk, &[]);
            builder.switch_to_block(cont_blk);
            builder.seal_block(cont_blk);
        }
    }

    builder
        .ins()
        .store(MemFlags::new(), stored_val, ptr_val, offset);
    builder.ins().iconst(types::I64, 0)
}
