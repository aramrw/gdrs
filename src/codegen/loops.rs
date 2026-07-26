use std::collections::HashMap;

use cranelift_codegen::ir::{InstBuilder, Value};
use cranelift_codegen::ir::types;
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr, TypedMatchArm};
use crate::codegen::expr::compile_expr;
use crate::sanal::StructLayout;

pub fn compile_while<M: Module>(
    builder: &mut FunctionBuilder,
    cond: &Box<TypedExpr>,
    body: &Box<TypedExpr>,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let header_block = builder.create_block();
    let body_block = builder.create_block();
    let exit_block = builder.create_block();

    builder.ins().jump(header_block, &[]);

    // 1. HEADER BLOCK
    builder.switch_to_block(header_block);
    let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
    builder
        .ins()
        .brif(cond_val, body_block, &[], exit_block, &[]);

    // 2. BODY BLOCK
    builder.switch_to_block(body_block);
    builder.seal_block(body_block);
    compile_expr(builder, body, vars, var_counter, module, struct_layouts);
    builder.ins().jump(header_block, &[]);

    builder.seal_block(header_block);

    // 3. EXIT BLOCK
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    builder.ins().iconst(types::I64, 0)
}
