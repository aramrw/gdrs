use std::collections::HashMap;

use cranelift_codegen::ir::{MemFlags, types};
use cranelift_codegen::ir::{InstBuilder, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr, TypedMatchArm};
use crate::codegen::expr::{coerce_val, compile_expr, cranelift_type_of};
use crate::sanal::StructLayout;

pub fn compile_if<M: Module>(
    builder: &mut FunctionBuilder,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
    cond: &Box<TypedExpr>,
    body: &Box<TypedExpr>,
) -> Value {
    let then_block = builder.create_block();
    let exit_block = builder.create_block();

    let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
    builder
        .ins()
        .brif(cond_val, then_block, &[], exit_block, &[]);

    // THEN BLOCK
    builder.switch_to_block(then_block);
    builder.seal_block(then_block);
    compile_expr(builder, body, vars, var_counter, module, struct_layouts);
    if !builder.is_unreachable() {
        builder.ins().jump(exit_block, &[]);
    }

    // EXIT BLOCK
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    builder.ins().iconst(types::I64, 0)
}

pub fn compile_if_else<M: Module>(
    builder: &mut FunctionBuilder,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    ty: &Type,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
    cond: &Box<TypedExpr>,
    then_b: &Box<TypedExpr>,
    else_b: &Box<TypedExpr>,
) -> Value {
    let then_block = builder.create_block();
    let else_block = builder.create_block();
    let exit_block = builder.create_block();

    let is_unit = *ty == Type::Unit;
    let cranelift_ty = cranelift_type_of(ty);

    // Only expect a block parameter if this expression yields a non-unit value
    if !is_unit {
        builder.append_block_param(exit_block, cranelift_ty);
    }

    let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
    builder
        .ins()
        .brif(cond_val, then_block, &[], else_block, &[]);

    // THEN
    builder.switch_to_block(then_block);
    builder.seal_block(then_block);
    let then_val = compile_expr(builder, then_b, vars, var_counter, module, struct_layouts);
    let then_term = builder.is_unreachable();
    if !then_term {
        if is_unit {
            builder.ins().jump(exit_block, &[]);
        } else {
            let coerced = coerce_val(builder, then_val, cranelift_ty);
            builder.ins().jump(exit_block, &[coerced]);
        }
    }

    // ELSE
    builder.switch_to_block(else_block);
    builder.seal_block(else_block);
    let else_val = compile_expr(builder, else_b, vars, var_counter, module, struct_layouts);
    let else_term = builder.is_unreachable();
    if !else_term {
        if is_unit {
            builder.ins().jump(exit_block, &[]);
        } else {
            let coerced = coerce_val(builder, else_val, cranelift_ty);
            builder.ins().jump(exit_block, &[coerced]);
        }
    }

    // EXIT
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    if then_term && else_term {
        let dummy = match cranelift_ty {
            types::F32 => builder.ins().f32const(0.0),
            types::F64 => builder.ins().f64const(0.0),
            _ => builder.ins().iconst(cranelift_ty, 0),
        };
        builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
        dummy
    } else if is_unit {
        builder.ins().iconst(types::I64, 0)
    } else {
        builder.block_params(exit_block)[0]
    }
}

pub fn compile_match<M: Module>(
    builder: &mut FunctionBuilder,
    target: &Box<TypedExpr>,
    arms: &Vec<TypedMatchArm>,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    ty: &Type,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    use cranelift_codegen::ir::condcodes::IntCC;

    let is_unit = *ty == Type::Unit;
    let cranelift_ty = cranelift_type_of(ty);

    let target_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
    let tag_val = builder
        .ins()
        .load(types::I64, MemFlags::new(), target_ptr, 0);

    let exit_block = builder.create_block();
    if !is_unit {
        builder.append_block_param(exit_block, cranelift_ty);
    }

    for arm in arms {
        let arm_block = builder.create_block();
        let next_check_block = builder.create_block();

        if arm.tag == -1 {
            builder.ins().jump(arm_block, &[]);
        } else {
            let expected_tag = builder.ins().iconst(types::I64, arm.tag);
            let is_match = builder.ins().icmp(IntCC::Equal, tag_val, expected_tag);
            builder
                .ins()
                .brif(is_match, arm_block, &[], next_check_block, &[]);
        }

        // Compile Arm Block
        builder.switch_to_block(arm_block);
        builder.seal_block(arm_block);

        for (idx, (b_name, _b_ty)) in arm.bindings.iter().enumerate() {
            if b_name != "_" {
                let offset = ((idx + 1) * 8) as i32;
                let payload_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::new(), target_ptr, offset);
                let var = cranelift_frontend::Variable::from_u32(*var_counter as u32);
                *var_counter += 1;
                builder.declare_var(var, types::I64);
                builder.def_var(var, payload_val);
                vars.insert(b_name.clone(), var);
            }
        }

        let mut arm_val = builder.ins().iconst(types::I64, 0);
        for stmt in &arm.body {
            arm_val = compile_expr(builder, stmt, vars, var_counter, module, struct_layouts);
        }

        if !builder.is_unreachable() {
            if is_unit {
                builder.ins().jump(exit_block, &[]);
            } else {
                let coerced = coerce_val(builder, arm_val, cranelift_ty);
                builder.ins().jump(exit_block, &[coerced]);
            }
        }

        // Switch to Next Check Block
        builder.switch_to_block(next_check_block);
        builder.seal_block(next_check_block);
    }

    if !builder.is_unreachable() {
        builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
    }

    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    if is_unit {
        builder.ins().iconst(types::I64, 0)
    } else {
        builder.block_params(exit_block)[0]
    }
}
