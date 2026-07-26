//! codegen/objects.rs
//! Codegen for struct/object initialization, field access, and field assignment.

use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, Value, types};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{Linkage, Module};
use std::collections::HashMap;

use crate::ast::{Type, TypedExpr};
use crate::codegen::expr::{coerce_val, compile_expr, cranelift_type_of};
use crate::sanal::StructLayout;

pub fn compile_obj_init<M: Module>(
    builder: &mut FunctionBuilder,
    fields: &[(String, TypedExpr)],
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let slot_size = (fields.len() * 8) as i64;
    let size_val = builder
        .ins()
        .iconst(types::I64, if slot_size == 0 { 8 } else { slot_size });

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("malloc", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(local_callee, &[size_val]);
    let base_ptr = builder.inst_results(call_inst)[0];

    for (i, (_field_name, field_expr)) in fields.iter().enumerate() {
        let val = compile_expr(
            builder,
            field_expr,
            vars,
            var_counter,
            module,
            struct_layouts,
        );
        let offset = (i * 8) as i32;
        builder.ins().store(MemFlags::new(), val, base_ptr, offset);
    }

    base_ptr
}

pub fn compile_field_access<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    field_name: &str,
    field_ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
    let mut offset = 0i32;

    let target_struct_name = match target.ty() {
        Type::Obj(struct_name) => Some(struct_name),
        Type::Ref(inner) | Type::MutRef(inner) => match *inner {
            Type::Obj(struct_name) => Some(struct_name),
            _ => None,
        },
        _ => None,
    };

    if let Some(struct_name) = target_struct_name {
        if let Some(layout) = struct_layouts.get(struct_name) {
            if let Some((f_offset, _)) = layout.field_offsets.get(field_name) {
                offset = *f_offset as i32;
            }
        }
    }

    let field_cranelift_ty = cranelift_type_of(field_ty);

    builder
        .ins()
        .load(field_cranelift_ty, MemFlags::new(), base_ptr, offset)
}

pub fn compile_field_assign<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    field_name: &str,
    val: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
    let new_val = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
    let mut offset = 0i32;

    let target_struct_name = match target.ty() {
        Type::Obj(struct_name) => Some(struct_name),
        Type::Ref(inner) | Type::MutRef(inner) => match *inner {
            Type::Obj(struct_name) => Some(struct_name),
            _ => None,
        },
        _ => None,
    };

    if let Some(struct_name) = target_struct_name {
        if let Some(layout) = struct_layouts.get(struct_name) {
            if let Some((f_offset, _)) = layout.field_offsets.get(field_name) {
                offset = *f_offset as i32;
            }
        }
    }

    builder
        .ins()
        .store(MemFlags::new(), new_val, base_ptr, offset);
    new_val
}

pub fn compile_enum_construct<M: Module>(
    builder: &mut FunctionBuilder,
    _enum_name: &String,
    _variant_name: &String,
    disc: &usize,
    payload_exprs: &Vec<TypedExpr>,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    use cranelift_codegen::ir::AbiParam;
    let total_bytes = ((1 + payload_exprs.len()) * 8) as i64;
    let size_val = builder
        .ins()
        .iconst(types::I64, if total_bytes == 0 { 8 } else { total_bytes });

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("malloc", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(local_callee, &[size_val]);
    let base_ptr = builder.inst_results(call_inst)[0];

    // Store discriminant tag at offset 0
    let disc_val = builder.ins().iconst(types::I64, *disc as i64);
    builder.ins().store(MemFlags::new(), disc_val, base_ptr, 0);

    // Store payload fields at offsets 8, 16, ...
    for (i, expr) in payload_exprs.iter().enumerate() {
        let val = compile_expr(builder, expr, vars, var_counter, module, struct_layouts);
        let val_i64 = coerce_val(builder, val, types::I64);
        let offset = ((i + 1) * 8) as i32;
        builder
            .ins()
            .store(MemFlags::new(), val_i64, base_ptr, offset);
    }

    base_ptr
}
