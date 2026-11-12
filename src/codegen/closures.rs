//! codegen/closures.rs
//! Codegen for closure expressions.

use cranelift_codegen::ir::{types, InstBuilder, Value};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::Module;

use crate::ast::{Span, Type, TypedExpr};
use crate::codegen::ctx::ProgramMeta;

pub fn compile_closure<M: Module>(
    builder: &mut FunctionBuilder,
    closure_name: &str,
    params: &[(String, Type)],
    body: &TypedExpr,
    ret_ty: &Type,
    span: &Span,
    meta: &mut ProgramMeta,
    module: &mut M,
) -> Value {
    let callee = match module.get_name(closure_name) {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        _ => {
            let func_params = params
                .iter()
                .map(|(p_name, p_ty)| crate::ast::Param {
                    name: p_name.clone(),
                    is_mutable: false,
                    ty: *p_ty,
                    span: span.clone(),
                })
                .collect();

            let func_decl = crate::ast::TypedFuncDecl {
                name: closure_name.to_string(),
                params: func_params,
                return_type: *ret_ty,
                where_clause: None,
                body: vec![body.clone()],
            };

            let mut new_ctx = module.make_context();
            let mut new_builder_ctx = FunctionBuilderContext::new();

            crate::codegen::func::compile_func(
                &func_decl,
                meta,
                module,
                &mut new_ctx,
                &mut new_builder_ctx,
            )
            .expect("compile_func failed to return FuncId for closure")
        }
    };

    let local_callee = module.declare_func_in_func(callee, builder.func);
    builder.ins().func_addr(types::I64, local_callee)
}
