//! codegen/drops.rs
//! Cranelift Drop Flag allocation, LIFO scope drop emission, and Drop Glue calls.

use std::collections::HashMap;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, StackSlot, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::Type;
use crate::codegen::expr::cranelift_type_of;
use crate::sanal::StructLayout;

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

pub fn emit_drop_for_var<M: Module>(
    builder: &mut FunctionBuilder,
    var_name: &str,
    ty: &Type,
    vars: &HashMap<String, Variable>,
    module: &mut M,
) {
    let var = match vars.get(var_name) {
        Some(v) => *v,
        None => return,
    };
    let val = builder.use_var(var);

    // Determine the drop function name based on Type
    let drop_fn_name = match ty {
        Type::String | Type::Obj("String") | Type::Obj("std_string_String") => {
            "std_string_String_drop".to_string()
        }
        Type::Vec(_) | Type::Obj("Vec") | Type::Obj("std_vec_Vec") => {
            "std_vec_Vec_drop".to_string()
        }
        Type::Obj(name) => format!("{name}_drop"),
        _ => return,
    };

    // Declare function if needed and call drop
    let mut sig = module.make_signature();
    sig.params.push(cranelift_codegen::ir::AbiParam::new(cranelift_type_of(ty)));

    if let Ok(callee) = module.declare_function(&drop_fn_name, Linkage::Import, &sig) {
        let local_callee = module.declare_func_in_func(callee, builder.func);
        builder.ins().call(local_callee, &[val]);
    }
}

pub fn has_drop_glue(ty: &Type) -> bool {
    match ty {
        Type::String | Type::Obj("String") | Type::Obj("std_string_String") => true,
        Type::Vec(_) | Type::Obj("Vec") | Type::Obj("std_vec_Vec") => true,
        Type::Obj(_) => true,
        _ => false,
    }
}

pub fn emit_conditional_drop<M: Module>(
    builder: &mut FunctionBuilder,
    var_name: &str,
    ty: &Type,
    slot: StackSlot,
    vars: &HashMap<String, Variable>,
    module: &mut M,
) {
    if !has_drop_glue(ty) || builder.is_unreachable() {
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

    // Emit the drop glue execution
    emit_drop_for_var(builder, var_name, ty, vars, module);

    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}
