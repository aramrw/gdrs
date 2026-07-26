//! sanal/refs.rs
//! Type checking for references (&, &mut) and dereferencing (*, *ptr = val).

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_ref<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    inner: &Expr,
    is_mut: bool,
    span: &Span,
) -> Option<TypedExpr> {
    let t_inner = type_check_expr(scopes, errors, type_ctx, inner)?;
    let inner_ty = t_inner.ty();
    let ref_ty = if is_mut {
        Type::MutRef(crate::ast::intern_type(inner_ty))
    } else {
        Type::Ref(crate::ast::intern_type(inner_ty))
    };
    Some(TypedExpr::Ref(
        Box::new(t_inner),
        is_mut,
        ref_ty,
        span.clone(),
    ))
}

pub fn type_check_deref<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    inner: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_inner = type_check_expr(scopes, errors, type_ctx, inner)?;
    match t_inner.ty() {
        Type::Rc(inner_ty) | Type::Arc(inner_ty) | Type::Ref(inner_ty) | Type::MutRef(inner_ty) => {
            Some(TypedExpr::Deref(Box::new(t_inner), *inner_ty, span.clone()))
        }
        Type::Int | Type::I32 => {
            Some(TypedExpr::Deref(Box::new(t_inner), Type::Int, span.clone()))
        }
        other => {
            errors.push(SemanticError {
                message: format!("Cannot dereference type `{:?}`", other),
                label: "Type cannot be dereferenced".to_string(),
                help: Some("Use rc.new(val) or arc.new(val) or raw pointer".to_string()),
                span: span.clone(),
            });
            Some(TypedExpr::Deref(
                Box::new(t_inner),
                Type::Unit,
                span.clone(),
            ))
        }
    }
}

pub fn type_check_deref_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    ptr: &Expr,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_ptr = type_check_expr(scopes, errors, type_ctx, ptr)?;
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;
    match t_ptr.ty() {
        Type::Rc(inner_ty) | Type::Arc(inner_ty) | Type::Ref(inner_ty) | Type::MutRef(inner_ty) => {
            if t_val.ty() != *inner_ty {
                errors.push(SemanticError {
                    message: format!(
                        "Mismatched type in dereference assignment. Pointer holds `{:?}`, found `{:?}`",
                        *inner_ty,
                        t_val.ty()
                    ),
                    label: format!("Expected `{:?}`", *inner_ty),
                    help: None,
                    span: span.clone(),
                });
            }
            Some(TypedExpr::DerefAssign(
                Box::new(t_ptr),
                Box::new(t_val),
                span.clone(),
            ))
        }
        other => {
            errors.push(SemanticError {
                message: format!("Cannot dereference assign type `{:?}`", other),
                label: "Type cannot be dereferenced".to_string(),
                help: None,
                span: span.clone(),
            });
            Some(TypedExpr::DerefAssign(
                Box::new(t_ptr),
                Box::new(t_val),
                span.clone(),
            ))
        }
    }
}
