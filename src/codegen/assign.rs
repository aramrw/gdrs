use std::collections::HashMap;

use cranelift_codegen::ir::{InstBuilder, MemFlags, Value};
use cranelift_codegen::ir::{StackSlotData, StackSlotKind, types};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr};
use crate::codegen::expr::{coerce_val, compile_expr, cranelift_type_of};
use crate::sanal::StructLayout;

pub fn compile_let<M: Module>(
    builder: &mut FunctionBuilder,
    value: &Box<TypedExpr>,
    ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
    name: &String,
) -> Value {
    let val = compile_expr(builder, value, vars, var_counter, module, struct_layouts);

    let var = Variable::from_u32(*var_counter as u32);
    *var_counter += 1;

    // Map gdrs Type to the precise Cranelift type
    let cranelift_ty = cranelift_type_of(ty);

    builder.declare_var(var, cranelift_ty);

    let val = coerce_val(builder, val, cranelift_ty);

    // 3. Handle stack slot layouts for composite types (Obj, Str, Vec, etc.)
    let stored_val = match ty {
        Type::Obj(_) => val,
        Type::Str => val,

        Type::String => {
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                24,
                0,
            ));
            let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);
            builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
            let zero = builder.ins().iconst(types::I64, 0);
            builder.ins().store(MemFlags::new(), zero, dst_ptr, 8);
            builder.ins().store(MemFlags::new(), zero, dst_ptr, 16);
            dst_ptr
        }
        Type::Slice(_) => {
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                16,
                0,
            ));
            let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);
            builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
            let len_val = match value.as_ref() {
                TypedExpr::ArrayInit(elems, _, _) => {
                    builder.ins().iconst(types::I64, elems.len() as i64)
                }
                _ => builder.ins().iconst(types::I64, 0),
            };
            builder.ins().store(MemFlags::new(), len_val, dst_ptr, 8);
            dst_ptr
        }
        Type::Vec(_) => {
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                24,
                0,
            ));
            let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);
            builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
            let len_val = match value.as_ref() {
                TypedExpr::ArrayInit(elems, _, _) => {
                    builder.ins().iconst(types::I64, elems.len() as i64)
                }
                _ => builder.ins().iconst(types::I64, 0),
            };
            builder.ins().store(MemFlags::new(), len_val, dst_ptr, 8);
            let zero = builder.ins().iconst(types::I64, 0);
            builder.ins().store(MemFlags::new(), zero, dst_ptr, 16);
            dst_ptr
        }
        _ => val,
    };

    builder.def_var(var, stored_val);
    vars.insert(name.clone(), var);

    stored_val
}

pub fn compile_assign<M: Module>(
    builder: &mut FunctionBuilder,
    value: &Box<TypedExpr>,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
    name: &String,
) -> Value {
    let mut val = compile_expr(builder, value, vars, var_counter, module, struct_layouts);
    let var = vars.get(name).expect("Undefined variable during codegen");
    let dest_ptr = builder.use_var(*var);

    if let Type::Obj(struct_name) = value.ty() {
        if let Some(layout) = struct_layouts.get(struct_name) {
            for i in 0..(layout.total_size / 8) {
                let offset = (i * 8) as i32;
                let field_val = builder.ins().load(types::I64, MemFlags::new(), val, offset);
                builder
                    .ins()
                    .store(MemFlags::new(), field_val, dest_ptr, offset);
            }
        }
    } else {
        // Use dest_ptr (Value) with value_type() instead of *var (Variable)
        let var_ty = builder.func.dfg.value_type(dest_ptr);
        let val_ty = builder.func.dfg.value_type(val);

        if val_ty != var_ty {
            val = match (val_ty, var_ty) {
                (types::I64, types::I32) => builder.ins().ireduce(types::I32, val),
                (types::I32, types::I64) => builder.ins().sextend(types::I64, val),
                (types::F64, types::F32) => builder.ins().fdemote(types::F32, val),
                (types::F32, types::F64) => builder.ins().fpromote(types::F64, val),
                _ => val,
            };
        }

        builder.def_var(*var, val);
    }
    val
}
