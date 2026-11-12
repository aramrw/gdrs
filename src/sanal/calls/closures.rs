//! sanal/calls/closures.rs
//! Closure type checking and non-capturing closure construction.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn build_non_capturing_closure<'a>(
    outer_scopes: &ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    params: &[String],
    param_ty: Type,
    body: &Expr,
    span: &Span,
) -> TypedExpr {
    static CLOSURE_COUNTER: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);
    let closure_name = format!(
        "__closure_{}",
        CLOSURE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    );

    // Closures compile as standalone non-capturing function pointers.
    // Type-checking against a fresh ScopeStack blocks outer captures and reports E0434.
    let mut closure_scopes = ScopeStack::new();
    let mut typed_params = Vec::new();
    for p in params {
        closure_scopes.declare(p.clone(), false, param_ty);
        typed_params.push((p.clone(), param_ty));
    }

    let mut closure_errors = Vec::new();
    let t_body = type_check_expr(&mut closure_scopes, &mut closure_errors, type_ctx, body)
        .unwrap_or(TypedExpr::Int(0, span.clone()));
    for mut err in closure_errors {
        if err.code == "E0425" {
            if let Some(var_name) = err
                .message
                .strip_prefix("Undefined variable '")
                .and_then(|s| s.strip_suffix('\''))
                .or_else(|| {
                    err.message
                        .strip_prefix("Cannot assign to undefined variable '")
                        .and_then(|s| s.strip_suffix('\''))
                })
            {
                if outer_scopes.lookup(var_name).is_some() {
                    err = SemanticError {
                        code: "E0434",
                        message: format!(
                            "Cannot capture outer variable `{var_name}` in a non-capturing closure"
                        ),
                        label: "Outer variable captured here".to_string(),
                        secondary_label: None,
                        help: Some(
                            "Pass state explicitly as closure arguments or via `arc.new(...)`"
                                .to_string(),
                        ),
                        span: err.span,
                    };
                }
            }
        }
        errors.push(err);
    }
    let ret_ty = t_body.ty();

    TypedExpr::Closure(
        closure_name,
        typed_params,
        Box::new(t_body),
        ret_ty,
        span.clone(),
    )
}

pub fn type_check_closure<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    params: &[String],
    body: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    Some(build_non_capturing_closure(
        scopes,
        errors,
        type_ctx,
        params,
        Type::Int,
        body,
        span,
    ))
}
