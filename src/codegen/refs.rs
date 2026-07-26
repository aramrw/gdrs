use std::collections::HashMap;

use cranelift_codegen::ir::{InstBuilder, StackSlotData, StackSlotKind, Value};
use cranelift_codegen::ir::{MemFlags, types};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr, TypedMatchArm};
use crate::codegen::expr::{coerce_val, compile_expr, cranelift_type_of};
use crate::sanal::StructLayout;

pub fn compile_ref<M: Module>(
    builder: &mut FunctionBuilder,
    inner_expr: &Box<TypedExpr>,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    match inner_expr.as_ref() {
        TypedExpr::Ident(_name, ty, _) => {
            let val = compile_expr(
                builder,
                inner_expr,
                vars,
                var_counter,
                module,
                struct_layouts,
            );
            match ty {
                Type::Obj(_)
                | Type::Str
                | Type::String
                | Type::Vec(_)
                | Type::Array(_, _)
                | Type::Ref(_)
                | Type::MutRef(_) => val,
                _ => {
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        8,
                        0,
                    ));
                    let ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    builder.ins().store(MemFlags::new(), val, ptr, 0);
                    ptr
                }
            }
        }
        TypedExpr::FieldAccess(target, field_name, _, _) => {
            let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
            let mut offset = 0i32;
            let target_struct_name = match target.ty() {
                crate::ast::Type::Obj(struct_name) => Some(struct_name),
                crate::ast::Type::Ref(inner) | crate::ast::Type::MutRef(inner) => match *inner {
                    crate::ast::Type::Obj(struct_name) => Some(struct_name),
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
            builder.ins().iadd_imm(base_ptr, offset as i64)
        }
        TypedExpr::Deref(ptr_expr, _, _) => {
            compile_expr(builder, ptr_expr, vars, var_counter, module, struct_layouts)
        }
        _ => compile_expr(
            builder,
            inner_expr,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),
    }
}

pub fn compile_deref<M: Module>(
    builder: &mut FunctionBuilder,
    inner_expr: &Box<TypedExpr>,
    _ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let ptr_val = compile_expr(
        builder,
        inner_expr,
        vars,
        var_counter,
        module,
        struct_layouts,
    );
    let offset = match inner_expr.ty() {
        Type::Rc(_) | Type::Arc(_) => 8,
        _ => 0,
    };
    let load_ty = cranelift_type_of(_ty);
    builder
        .ins()
        .load(load_ty, MemFlags::new(), ptr_val, offset)
}

pub fn compile_deref_assign<M: Module>(
    builder: &mut FunctionBuilder,
    ptr_expr: &Box<TypedExpr>,
    val_expr: &Box<TypedExpr>,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let ptr_val = compile_expr(builder, ptr_expr, vars, var_counter, module, struct_layouts);
    let val = compile_expr(builder, val_expr, vars, var_counter, module, struct_layouts);
    let offset = match ptr_expr.ty() {
        Type::Rc(_) | Type::Arc(_) => 8,
        _ => 0,
    };
    builder.ins().store(MemFlags::new(), val, ptr_val, offset);
    builder.ins().iconst(types::I64, 0)
}
