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

    let expected_fn_sig = type_ctx.current_expected_type.and_then(|exp| {
        let resolved = type_ctx.infer.borrow_mut().probe(exp);
        if let Type::FnPtr(p_tys, r_ty) = resolved {
            Some((p_tys.to_vec(), *r_ty))
        } else {
            None
        }
    });

    // Closures compile as standalone non-capturing function pointers.
    // Type-checking against a fresh ScopeStack blocks outer captures and reports E0434.
    let mut closure_scopes = ScopeStack::new();
    let mut typed_params = Vec::new();
    for (i, raw_p) in params.iter().enumerate() {
        let (p_name, explicit_p_ty) = if let Some((n, t_str)) = raw_p.split_once(':') {
            let resolved_t = type_ctx.resolve_type_annotation(Type::Obj(crate::ast::intern_str(t_str)));
            (n.to_string(), Some(resolved_t))
        } else {
            (raw_p.clone(), None)
        };
        let p_ty = explicit_p_ty
            .or_else(|| {
                expected_fn_sig
                    .as_ref()
                    .and_then(|(ps, _)| ps.get(i).copied())
            })
            .unwrap_or(param_ty);
        closure_scopes.declare(p_name.clone(), false, p_ty);
        typed_params.push((p_name, p_ty));
    }

    let mut body_ctx = type_ctx.clone();
    body_ctx.current_expected_type = expected_fn_sig.as_ref().map(|(_, r)| *r);
    if let Some((_, exp_r)) = &expected_fn_sig {
        body_ctx.current_return_type = Some(*exp_r);
    }

    let mut closure_errors = Vec::new();
    let t_body = type_check_expr(&mut closure_scopes, &mut closure_errors, &body_ctx, body)
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
                            "Pass state explicitly as closure arguments or via `Arc::new(...)`"
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
    if let Some((_, exp_r)) = &expected_fn_sig {
        let _ = type_ctx.infer.borrow_mut().unify(*exp_r, ret_ty);
    }
    let resolved_ret_ty = type_ctx.infer.borrow_mut().resolve(ret_ty);
    if crate::sanal::type_contains_ref(&resolved_ret_ty) {
        errors.push(SemanticError {
            code: "E0106",
            message: "Closure cannot return a reference (`&T` / `&mut T`)".to_string(),
            label: "References cannot escape a closure".to_string(),
            secondary_label: None,
            help: Some("Return an owned value, `Rc<T>`, or `Arc<T>` instead".to_string()),
            span: t_body.span(),
        });
    }
    crate::sanal::control_flow::lifetimes::check_block_escape_lifetime(
        &closure_scopes,
        &t_body,
        errors,
    );

    TypedExpr::Closure(
        closure_name,
        typed_params,
        Box::new(t_body),
        resolved_ret_ty,
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
