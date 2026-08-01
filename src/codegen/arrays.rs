//! codegen/arrays.rs
//! Codegen for array/vector initialization, index access, index assignment, and ranges.

use std::collections::HashMap;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, types, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::expr::{coerce_val, compile_expr, cranelift_type_of};
use crate::sanal::StructLayout;

pub fn compile_array_init<M: Module>(
    builder: &mut FunctionBuilder,
    elems: &[TypedExpr],
    arr_ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    if matches!(arr_ty, Type::Vec(_)) {
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module
            .declare_function("intrinsic_vec_new", Linkage::Import, &sig)
            .unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let call_inst = builder.ins().call(local_callee, &[]);
        let vec_ptr = builder.inst_results(call_inst)[0];

        for elem in elems {
            let raw_elem_val = compile_expr(builder, elem, vars, var_counter, module, struct_layouts);
            let elem_val = coerce_val(builder, raw_elem_val, types::I64);
            let mut sig_push = module.make_signature();
            sig_push.params.push(AbiParam::new(types::I64));
            sig_push.params.push(AbiParam::new(types::I64));
            let callee_push = module
                .declare_function("intrinsic_vec_push", Linkage::Import, &sig_push)
                .unwrap();
            let local_push = module.declare_func_in_func(callee_push, builder.func);
            builder.ins().call(local_push, &[vec_ptr, elem_val]);
        }

        vec_ptr
    } else {
        let slot_bytes = (elems.len() * 8) as u32;
        let slot = builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            if slot_bytes == 0 { 8 } else { slot_bytes },
            0,
        ));
        let base_ptr = builder.ins().stack_addr(types::I64, slot, 0);

        for (i, elem) in elems.iter().enumerate() {
            let val = compile_expr(builder, elem, vars, var_counter, module, struct_layouts);
            let offset = (i * 8) as i32;
            builder.ins().store(MemFlags::new(), val, base_ptr, offset);
        }

        base_ptr
    }
}

pub fn compile_index_access<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    idx: &TypedExpr,
    elem_ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
    let buffer_ptr = match target.ty() {
        Type::Slice(_) | Type::Vec(_) => {
            builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0)
        }
        Type::Obj(s) if s.contains("Vec") => {
            builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0)
        }
        _ => base_ptr,
    };
    let raw_idx_val = compile_expr(builder, idx, vars, var_counter, module, struct_layouts);
    let idx_val = coerce_val(builder, raw_idx_val, types::I64);
    let elem_size = builder.ins().iconst(types::I64, 8);
    let offset = builder.ins().imul(idx_val, elem_size);
    let elem_addr = builder.ins().iadd(buffer_ptr, offset);

    let cranelift_ty = cranelift_type_of(elem_ty);

    builder
        .ins()
        .load(cranelift_ty, MemFlags::new(), elem_addr, 0)
}

pub fn compile_index_assign<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    idx: &TypedExpr,
    val: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
    let buffer_ptr = match target.ty() {
        Type::Slice(_) | Type::Vec(_) => {
            builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0)
        }
        Type::Obj(s) if s.contains("Vec") => {
            builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0)
        }
        _ => base_ptr,
    };
    let raw_idx_val = compile_expr(builder, idx, vars, var_counter, module, struct_layouts);
    let idx_val = coerce_val(builder, raw_idx_val, types::I64);
    let new_val = compile_expr(builder, val, vars, var_counter, module, struct_layouts);

    let elem_size = builder.ins().iconst(types::I64, 8);
    let offset = builder.ins().imul(idx_val, elem_size);
    let elem_addr = builder.ins().iadd(buffer_ptr, offset);

    builder.ins().store(MemFlags::new(), new_val, elem_addr, 0);
    new_val
}

pub fn compile_range<M: Module>(
    builder: &mut FunctionBuilder,
    start_expr: &TypedExpr,
    end_expr: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let start = compile_expr(
        builder,
        start_expr,
        vars,
        var_counter,
        module,
        struct_layouts,
    );
    let end = compile_expr(builder, end_expr, vars, var_counter, module, struct_layouts);

    let mut malloc_sig = module.make_signature();
    malloc_sig.params.push(AbiParam::new(types::I64));
    malloc_sig.returns.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("malloc", Linkage::Import, &malloc_sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let size_val = builder.ins().iconst(types::I64, 16);
    let call_inst = builder.ins().call(local_callee, &[size_val]);
    let heap_ptr = builder.inst_results(call_inst)[0];

    builder.ins().store(MemFlags::new(), start, heap_ptr, 0);
    builder.ins().store(MemFlags::new(), end, heap_ptr, 8);
    heap_ptr
}
