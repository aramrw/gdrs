use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{InstBuilder, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr};
use crate::codegen::branching::expr_is_terminator;
use crate::codegen::ctx::{CodegenCtx, LoopTarget};
use crate::codegen::expr::compile_expr;
use crate::codegen::layout::{alloc_stack_slot, repr_kind, ReprKind};

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
    cg.loop_stack.push(LoopTarget {
        header_block,
        exit_block,
        scope_depth: loop_scope_depth,
        temp_depth: loop_temp_depth,
        result_repr: None,
    });
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

pub fn compile_loop<M: Module>(
    builder: &mut FunctionBuilder,
    body: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let header_block = builder.create_block();
    let exit_block = builder.create_block();

    let is_diverging = *ty == Type::Void;
    let res_repr = repr_kind(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    let out_addr_opt = if is_diverging {
        None
    } else {
        match res_repr {
            ReprKind::Aggregate { size, align } => Some(alloc_stack_slot(builder, size, align).1),
            ReprKind::Scalar(cl_ty) => {
                builder.append_block_param(exit_block, cl_ty);
                None
            }
            ReprKind::Zst => None,
        }
    };

    builder.ins().jump(header_block, &[]);
    builder.switch_to_block(header_block);

    let loop_scope_depth = cg.scopes.len();
    let loop_temp_depth = cg.temp_scopes.len();
    cg.loop_stack.push(LoopTarget {
        header_block,
        exit_block,
        scope_depth: loop_scope_depth,
        temp_depth: loop_temp_depth,
        result_repr: if is_diverging {
            None
        } else {
            Some((res_repr, out_addr_opt))
        },
    });
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
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    if is_diverging || builder.is_unreachable() {
        let dummy = match res_repr {
            ReprKind::Scalar(types::F32) => builder.ins().f32const(0.0),
            ReprKind::Scalar(types::F64) => builder.ins().f64const(0.0),
            ReprKind::Scalar(cl_ty) => builder.ins().iconst(cl_ty, 0),
            ReprKind::Aggregate { .. } | ReprKind::Zst => builder.ins().iconst(types::I64, 0),
        };
        builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
        dummy
    } else if let Some(out_addr) = out_addr_opt {
        out_addr
    } else if matches!(res_repr, ReprKind::Zst) {
        builder.ins().iconst(types::I64, 0)
    } else {
        builder.block_params(exit_block)[0]
    }
}
