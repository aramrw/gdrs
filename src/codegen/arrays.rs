//! codegen/arrays.rs
//! Codegen for stack arrays `[T; N]`, stack slice/Vec headers, index access/assignment, and ranges.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{Linkage, Module};

use crate::ast::{normalize_type_name, Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{emit_drop_for_value, has_drop_glue, EnumLayoutMap};
use crate::codegen::expr::{coerce_typed_val, coerce_val, compile_expr, cranelift_type_of};
use crate::codegen::layout::{
    alloc_stack_slot, array_stride, emit_memcpy_bytes, is_aggregate_type, size_and_align,
};
use crate::sanal::StructLayout;

fn emit_malloc<M: Module>(builder: &mut FunctionBuilder, module: &mut M, bytes_val: Value) -> Value {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("malloc", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(local_callee, &[bytes_val]);
    builder.inst_results(call_inst)[0]
}

pub fn compile_array_init<M: Module>(
    builder: &mut FunctionBuilder,
    elems: &[TypedExpr],
    arr_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    if let Type::Vec(inner_elem) = arr_ty {
        let elem_ty = **inner_elem;
        let stride = array_stride(&elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts).max(1);
        let (_, vec_ptr) = alloc_stack_slot(builder, 24, 8);
        let zero = builder.ins().iconst(types::I64, 0);

        if elems.is_empty() {
            builder.ins().store(MemFlags::new(), zero, vec_ptr, 0);
            builder.ins().store(MemFlags::new(), zero, vec_ptr, 8);
            builder.ins().store(MemFlags::new(), zero, vec_ptr, 16);
            return vec_ptr;
        }

        let cap = elems.len().max(4);
        let alloc_bytes = builder.ins().iconst(types::I64, (cap as i64) * (stride as i64));
        let buf_ptr = emit_malloc(builder, module, alloc_bytes);
        let len_val = builder.ins().iconst(types::I64, elems.len() as i64);
        let cap_val = builder.ins().iconst(types::I64, cap as i64);
        builder.ins().store(MemFlags::new(), buf_ptr, vec_ptr, 0);
        builder.ins().store(MemFlags::new(), len_val, vec_ptr, 8);
        builder.ins().store(MemFlags::new(), cap_val, vec_ptr, 16);

        let is_agg = is_aggregate_type(&elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
        for (i, elem) in elems.iter().enumerate() {
            let raw_val = compile_expr(builder, elem, cg, module);
            cg.cancel_temp(raw_val);
            if let TypedExpr::Ident(v_name, v_ty, _) = elem {
                if !v_ty.is_copy() {
                    cg.mark_moved(builder, v_name);
                }
            }
            let offset = (i as u32 * stride) as i32;
            if is_agg {
                let (esize, _) = size_and_align(&elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
                let dst = builder.ins().iadd_imm(buf_ptr, offset as i64);
                emit_memcpy_bytes(builder, module, dst, raw_val, esize);
            } else {
                let stored_ty = cranelift_type_of(&elem_ty);
                let val = coerce_typed_val(builder, raw_val, &elem.ty(), stored_ty);
                builder.ins().store(MemFlags::new(), val, buf_ptr, offset);
            }
        }
        return vec_ptr;
    }

    let target_elem_ty = match arr_ty {
        Type::Array(elem_ty, _) | Type::Slice(elem_ty) => **elem_ty,
        _ => elems.first().map(|e| e.ty()).unwrap_or(Type::Int),
    };
    let (_, elem_align) =
        size_and_align(&target_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    let stride = array_stride(&target_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    let total_bytes = stride * (elems.len() as u32);
    let (_, base_ptr) = alloc_stack_slot(builder, total_bytes, elem_align);

    let is_agg = is_aggregate_type(&target_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    for (i, elem) in elems.iter().enumerate() {
        let raw_val = compile_expr(builder, elem, cg, module);
        cg.cancel_temp(raw_val);
        if let TypedExpr::Ident(v_name, v_ty, _) = elem {
            if !v_ty.is_copy() {
                cg.mark_moved(builder, v_name);
            }
        }
        let offset = (i as u32 * stride) as i32;
        if is_agg {
            let (esize, _) =
                size_and_align(&target_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
            let dst = if offset == 0 {
                base_ptr
            } else {
                builder.ins().iadd_imm(base_ptr, offset as i64)
            };
            emit_memcpy_bytes(builder, module, dst, raw_val, esize);
        } else {
            let stored_ty = cranelift_type_of(&target_elem_ty);
            let val = coerce_typed_val(builder, raw_val, &elem.ty(), stored_ty);
            builder.ins().store(MemFlags::new(), val, base_ptr, offset);
        }
    }

    if matches!(arr_ty, Type::Slice(_)) {
        alloc_stack_slice_header(builder, base_ptr, elems.len())
    } else {
        base_ptr
    }
}

fn get_element_type(target_ty: &Type, fallback: &Type) -> Type {
    let resolved = match target_ty {
        Type::Vec(inner) | Type::Slice(inner) | Type::Array(inner, _) => **inner,
        Type::Ref(inner) | Type::MutRef(inner) => return get_element_type(inner, fallback),
        Type::Obj(s) => {
            if let Some((_, t_args)) = crate::sanal::mono::lookup_mangled(s) {
                if let Some(first) = t_args.first() {
                    return *first;
                }
            }
            let normalized = normalize_type_name(s);
            if matches!(normalized.as_str(), "f64" | "f32" | "float") {
                if s.contains("f32") || s.contains("F32") {
                    Type::F32
                } else {
                    Type::Float
                }
            } else {
                *fallback
            }
        }
        _ => *fallback,
    };

    if matches!(resolved, Type::Generic(_)) {
        *fallback
    } else {
        resolved
    }
}

fn emit_bounds_check<M: Module>(
    builder: &mut FunctionBuilder,
    idx_val: Value,
    len_val: Value,
    module: &mut M,
) {
    let in_bounds = builder.ins().icmp(IntCC::UnsignedLessThan, idx_val, len_val);
    let ok_blk = builder.create_block();
    let panic_blk = builder.create_block();
    builder.ins().brif(in_bounds, ok_blk, &[], panic_blk, &[]);

    builder.switch_to_block(panic_blk);
    builder.seal_block(panic_blk);
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("intrinsic_bounds_panic", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    builder.ins().call(local_callee, &[idx_val, len_val]);
    builder
        .ins()
        .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());

    builder.switch_to_block(ok_blk);
    builder.seal_block(ok_blk);
}

fn load_indexable_buffer_and_len(
    builder: &mut FunctionBuilder,
    base_ptr: Value,
    raw_target_ty: &Type,
) -> (Value, Option<Value>) {
    let target_ty = match raw_target_ty {
        Type::Ref(inner) | Type::MutRef(inner) => **inner,
        other => *other,
    };
    match target_ty {
        Type::Array(_, arr_len) => {
            let len_val = builder.ins().iconst(types::I64, arr_len as i64);
            (base_ptr, Some(len_val))
        }
        Type::Slice(_) | Type::Vec(_) => {
            let buf_ptr = builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0);
            let len_val = builder.ins().load(types::I64, MemFlags::new(), base_ptr, 8);
            (buf_ptr, Some(len_val))
        }
        Type::Obj(s)
            if s.contains("Vec")
                || s.contains("vec")
                || s.contains("Slice")
                || s.contains("slice") =>
        {
            let buf_ptr = builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0);
            let len_val = builder.ins().load(types::I64, MemFlags::new(), base_ptr, 8);
            (buf_ptr, Some(len_val))
        }
        _ => (base_ptr, None),
    }
}

pub fn compile_index_addr<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    idx: &TypedExpr,
    elem_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> (Value, Type) {
    let base_ptr = compile_expr(builder, target, cg, module);
    let (buffer_ptr, opt_len) = load_indexable_buffer_and_len(builder, base_ptr, &target.ty());
    let raw_idx_val = compile_expr(builder, idx, cg, module);
    let idx_val = coerce_val(builder, raw_idx_val, types::I64);
    if let Some(len_val) = opt_len {
        emit_bounds_check(builder, idx_val, len_val, module);
    }

    let actual_elem_ty = get_element_type(&target.ty(), elem_ty);
    let stride = array_stride(&actual_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) as i64;
    let elem_size = builder.ins().iconst(types::I64, stride);
    let offset = builder.ins().imul(idx_val, elem_size);
    (builder.ins().iadd(buffer_ptr, offset), actual_elem_ty)
}

pub fn compile_index_access<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    idx: &TypedExpr,
    elem_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let (elem_addr, actual_elem_ty) =
        compile_index_addr(builder, target, idx, elem_ty, cg, module);

    if is_aggregate_type(&actual_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        elem_addr
    } else {
        let cranelift_ty = cranelift_type_of(&actual_elem_ty);
        builder.ins().load(cranelift_ty, MemFlags::new(), elem_addr, 0)
    }
}

pub fn compile_index_assign<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    idx: &TypedExpr,
    val: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let base_ptr = compile_expr(builder, target, cg, module);
    let (buffer_ptr, opt_len) = load_indexable_buffer_and_len(builder, base_ptr, &target.ty());
    let raw_idx_val = compile_expr(builder, idx, cg, module);
    let idx_val = coerce_val(builder, raw_idx_val, types::I64);
    if let Some(len_val) = opt_len {
        emit_bounds_check(builder, idx_val, len_val, module);
    }
    let new_val = compile_expr(builder, val, cg, module);
    cg.cancel_temp(new_val);
    if let TypedExpr::Ident(v_name, v_ty, _) = val {
        if !v_ty.is_copy() {
            cg.mark_moved(builder, v_name);
        }
    }

    let actual_elem_ty = get_element_type(&target.ty(), &val.ty());
    let stride = array_stride(&actual_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) as i64;
    let elem_size_val = builder.ins().iconst(types::I64, stride);
    let offset = builder.ins().imul(idx_val, elem_size_val);
    let elem_addr = builder.ins().iadd(buffer_ptr, offset);

    if is_aggregate_type(&actual_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        let (esize, _) = size_and_align(&actual_elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
        if has_drop_glue(
            &actual_elem_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
        ) {
            let is_diff = builder.ins().icmp(IntCC::NotEqual, elem_addr, new_val);
            let drop_blk = builder.create_block();
            let cont_blk = builder.create_block();
            builder.ins().brif(is_diff, drop_blk, &[], cont_blk, &[]);
            builder.switch_to_block(drop_blk);
            builder.seal_block(drop_blk);
            emit_drop_for_value(
                builder,
                elem_addr,
                &actual_elem_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
                module,
            );
            builder.ins().jump(cont_blk, &[]);
            builder.switch_to_block(cont_blk);
            builder.seal_block(cont_blk);
        }
        emit_memcpy_bytes(builder, module, elem_addr, new_val, esize);
        elem_addr
    } else {
        let cranelift_ty = cranelift_type_of(&actual_elem_ty);
        let coerced_val = coerce_typed_val(builder, new_val, &val.ty(), cranelift_ty);

        if has_drop_glue(
            &actual_elem_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
        ) {
            let old_val = builder.ins().load(cranelift_ty, MemFlags::new(), elem_addr, 0);
            let non_null = builder.ins().icmp_imm(IntCC::NotEqual, old_val, 0);
            let is_diff = builder.ins().icmp(IntCC::NotEqual, old_val, coerced_val);
            let should_drop = builder.ins().band(non_null, is_diff);
            let drop_blk = builder.create_block();
            let cont_blk = builder.create_block();
            builder.ins().brif(should_drop, drop_blk, &[], cont_blk, &[]);
            builder.switch_to_block(drop_blk);
            builder.seal_block(drop_blk);
            emit_drop_for_value(
                builder,
                old_val,
                &actual_elem_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
                module,
            );
            builder.ins().jump(cont_blk, &[]);
            builder.switch_to_block(cont_blk);
            builder.seal_block(cont_blk);
        }

        builder.ins().store(MemFlags::new(), coerced_val, elem_addr, 0);
        coerced_val
    }
}

/// Allocates a 16-byte stack-backed slice fat pointer `{ ptr, len }` without heap allocation.
pub fn alloc_stack_slice_header(
    builder: &mut FunctionBuilder,
    data_ptr: Value,
    arr_len: usize,
) -> Value {
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        16,
        3,
    ));
    let ptr_addr = builder.ins().stack_addr(types::I64, slot, 0);
    builder.ins().store(MemFlags::new(), data_ptr, ptr_addr, 0);
    let len_val = builder.ins().iconst(types::I64, arr_len as i64);
    builder.ins().store(MemFlags::new(), len_val, ptr_addr, 8);
    ptr_addr
}

/// Allocates a 24-byte stack-backed `Vec` header `{ data_ptr, len, cap }`, copying `arr_len`
/// elements from a stack `[T; N]` array into an owned heap data buffer.
pub fn alloc_stack_vec_header_from_array<M: Module>(
    builder: &mut FunctionBuilder,
    src_data_ptr: Value,
    elem_ty: &Type,
    arr_len: usize,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Value {
    let (_, hdr_ptr) = alloc_stack_slot(builder, 24, 8);
    let zero = builder.ins().iconst(types::I64, 0);
    if arr_len == 0 {
        builder.ins().store(MemFlags::new(), zero, hdr_ptr, 0);
        builder.ins().store(MemFlags::new(), zero, hdr_ptr, 8);
        builder.ins().store(MemFlags::new(), zero, hdr_ptr, 16);
        return hdr_ptr;
    }

    let stride = array_stride(elem_ty, struct_layouts, enum_layouts).max(1);
    let total_bytes = (arr_len as u32) * stride;
    let size_val = builder.ins().iconst(types::I64, total_bytes as i64);
    let heap_buf = emit_malloc(builder, module, size_val);
    emit_memcpy_bytes(builder, module, heap_buf, src_data_ptr, total_bytes);

    let len_val = builder.ins().iconst(types::I64, arr_len as i64);
    builder.ins().store(MemFlags::new(), heap_buf, hdr_ptr, 0);
    builder.ins().store(MemFlags::new(), len_val, hdr_ptr, 8);
    builder.ins().store(MemFlags::new(), len_val, hdr_ptr, 16);
    hdr_ptr
}

/// Allocates a stack-backed `[start, end]` range pair for standalone `Range` expressions.
pub fn compile_range<M: Module>(
    builder: &mut FunctionBuilder,
    start_expr: &TypedExpr,
    end_expr: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let start = compile_expr(builder, start_expr, cg, module);
    let end = compile_expr(builder, end_expr, cg, module);

    let (_, slot_ptr) = alloc_stack_slot(builder, 16, 8);
    builder.ins().store(MemFlags::new(), start, slot_ptr, 0);
    builder.ins().store(MemFlags::new(), end, slot_ptr, 8);
    slot_ptr
}
