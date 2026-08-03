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
        Type::Vec(_) => Some("Vec"),
        Type::String => Some("String"),
        Type::Ref(inner) | Type::MutRef(inner) => match *inner {
            Type::Obj(struct_name) => Some(struct_name),
            Type::Vec(_) => Some("Vec"),
            Type::String => Some("String"),
            _ => None,
        },
        _ => None,
    };

    if let Some(struct_name) = target_struct_name {
        let layout_opt = struct_layouts.get(struct_name).cloned().or_else(|| {
            struct_layouts
                .iter()
                .find(|(k, _)| {
                    **k == struct_name
                        || struct_name.starts_with(k.as_str())
                        || struct_name.contains(k.as_str())
                        || k.contains(&format!("{struct_name}_"))
                        || k.starts_with(&format!("{struct_name}_"))
                        || k.ends_with(&format!("_{struct_name}"))
                        || k.ends_with(struct_name)
                })
                .map(|(_, v)| v.clone())
        });
        if let Some(layout) = layout_opt {
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
    let mut new_val = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
    let mut offset = 0i32;

    let target_struct_name = match target.ty() {
        Type::Obj(struct_name) => Some(struct_name),
        Type::Vec(_) => Some("Vec"),
        Type::String => Some("String"),
        Type::Ref(inner) | Type::MutRef(inner) => match *inner {
            Type::Obj(struct_name) => Some(struct_name),
            Type::Vec(_) => Some("Vec"),
            Type::String => Some("String"),
            _ => None,
        },
        _ => None,
    };

    if let Some(struct_name) = target_struct_name {
        let layout_opt = struct_layouts.get(struct_name).cloned().or_else(|| {
            struct_layouts
                .iter()
                .find(|(k, _)| {
                    **k == struct_name
                        || struct_name.starts_with(k.as_str())
                        || struct_name.contains(k.as_str())
                        || k.contains(&format!("{struct_name}_"))
                        || k.starts_with(&format!("{struct_name}_"))
                        || k.ends_with(&format!("_{struct_name}"))
                        || k.ends_with(struct_name)
                })
                .map(|(_, v)| v.clone())
        });
        if let Some(layout) = layout_opt {
            if let Some((f_offset, f_ty)) = layout.field_offsets.get(field_name) {
                offset = *f_offset as i32;
                let target_cranelift_ty = crate::codegen::expr::cranelift_type_of(f_ty);
                new_val = crate::codegen::expr::coerce_val(builder, new_val, target_cranelift_ty);
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
    let is_npo = _enum_name.starts_with("std_core_Option_ptr")
        || _enum_name.starts_with("std_core_Option_void")
        || _enum_name.contains("_ptr_")
        || _enum_name.contains("_void");
    if is_npo {
        if _variant_name.ends_with("None") || *disc == 1 || payload_exprs.is_empty() {
            return builder.ins().iconst(types::I64, 0);
        } else {
            return compile_expr(builder, &payload_exprs[0], vars, var_counter, module, struct_layouts);
        }
    }

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
