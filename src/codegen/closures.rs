//! codegen/closures.rs
//! Codegen for closure expressions.

use std::collections::HashMap;
use cranelift_codegen::ir::{types, InstBuilder, Value};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::{Span, Type, TypedExpr};
use crate::sanal::StructLayout;

pub fn compile_closure<M: Module>(
    builder: &mut FunctionBuilder,
    closure_name: &str,
    params: &[(String, Type)],
    body: &TypedExpr,
    ret_ty: &Type,
    span: &Span,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let mut sig = module.make_signature();
    for _ in params {
        sig.params
            .push(cranelift_codegen::ir::AbiParam::new(types::I64));
    }
    if *ret_ty != Type::Unit {
        sig.returns
            .push(cranelift_codegen::ir::AbiParam::new(types::I64));
    }

    let (callee, is_new) = match module.get_name(closure_name) {
        Some(cranelift_module::FuncOrDataId::Func(id)) => (id, false),
        _ => (
            module
                .declare_function(closure_name, Linkage::Export, &sig)
                .unwrap(),
            true,
        ),
    };

    if is_new {
        let mut func_params = Vec::new();
        for (p_name, p_ty) in params {
            func_params.push(crate::ast::Param {
                name: p_name.clone(),
                is_mutable: false,
                ty: *p_ty,
                span: span.clone(),
            });
        }

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
            struct_layouts,
            module,
            &mut new_ctx,
            &mut new_builder_ctx,
        );
    }

    let local_callee = module.declare_func_in_func(callee, builder.func);
    builder.ins().func_addr(types::I64, local_callee)
}
