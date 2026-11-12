use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{InstBuilder, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::ast::TypedExpr;
use crate::codegen::branching::expr_is_terminator;
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::expr::compile_expr;

pub fn compile_while<M: Module>(
    builder: &mut FunctionBuilder,
    cond: &TypedExpr,
    body: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let header_block = builder.create_block();
    let body_block = builder.create_block();
    let exit_block = builder.create_block();

    builder.ins().jump(header_block, &[]);

    // 1. HEADER BLOCK
    builder.switch_to_block(header_block);
    cg.push_temp_scope();
    let cond_val = compile_expr(builder, cond, cg, module);
    cg.pop_temp_scope_and_drop(builder, module);
    builder
        .ins()
        .brif(cond_val, body_block, &[], exit_block, &[]);

    // 2. BODY BLOCK
    builder.switch_to_block(body_block);
    builder.seal_block(body_block);

    let loop_scope_depth = cg.scopes.len();
    let loop_temp_depth = cg.temp_scopes.len();
    cg.loop_stack.push((header_block, exit_block, loop_scope_depth, loop_temp_depth));
    cg.push_scope();
    cg.push_temp_scope();
    let _body_val = compile_expr(builder, body, cg, module);
    if !builder.is_unreachable() && !expr_is_terminator(body) {
        cg.pop_temp_scope_and_drop(builder, module);
        cg.pop_scope_and_drop(builder, module);
        builder.ins().jump(header_block, &[]);
    } else {
        cg.pop_temp_scope_without_drop();
        cg.pop_scope_without_drop();
    }
    cg.loop_stack.pop();

    builder.seal_block(header_block);

    // 3. EXIT BLOCK
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    builder.ins().iconst(types::I64, 0)
}
