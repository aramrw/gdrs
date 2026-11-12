//! sanal/control_flow/blocks.rs
//! Block expressions, unsafe blocks, and return statements.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{consume_tail_expr, is_type_compatible, mark_expr_moved_if_ident},
        control_flow::lifetimes::{check_block_escape_lifetime, check_return_ref_lifetime},
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_block<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    stmts: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    scopes.push_scope();
    let mut typed_stmts = Vec::new();
    let mut inner_ctx = type_ctx.clone();
    inner_ctx.current_expected_type = None;
    for (idx, stmt) in stmts.iter().enumerate() {
        let ctx_for_stmt = if idx + 1 == stmts.len() { type_ctx } else { &inner_ctx };
        if let Some(t_stmt) = type_check_expr(scopes, errors, ctx_for_stmt, stmt) {
            typed_stmts.push(t_stmt);
        }
    }
    if let Some(last) = typed_stmts.last() {
        consume_tail_expr(scopes, errors, type_ctx, last);
        check_block_escape_lifetime(scopes, last, errors);
    }
    scopes.pop_scope();
    let block_ty = typed_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
    Some(TypedExpr::Block(typed_stmts, block_ty, span.clone()))
}

pub fn type_check_unsafe<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    stmts: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    scopes.push_scope();
    let mut unsafe_ctx = type_ctx.clone();
    unsafe_ctx.is_unsafe = true;
    let mut inner_ctx = unsafe_ctx.clone();
    inner_ctx.current_expected_type = None;
    let mut typed_stmts = Vec::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        let ctx_for_stmt = if idx + 1 == stmts.len() { &unsafe_ctx } else { &inner_ctx };
        if let Some(t_stmt) = type_check_expr(scopes, errors, ctx_for_stmt, stmt) {
            typed_stmts.push(t_stmt);
        }
    }
    if let Some(last) = typed_stmts.last() {
        consume_tail_expr(scopes, errors, &unsafe_ctx, last);
        check_block_escape_lifetime(scopes, last, errors);
    }
    scopes.pop_scope();
    let block_ty = typed_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
    Some(TypedExpr::Unsafe(typed_stmts, block_ty, span.clone()))
}


pub fn type_check_return<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    opt_expr: Option<&Expr>,
    span: &Span,
) -> Option<TypedExpr> {
    let mut ret_ctx = type_ctx.clone();
    ret_ctx.current_expected_type = type_ctx.current_return_type;
    let mut t_opt = match opt_expr {
        Some(e) => {
            let te = type_check_expr(scopes, errors, &ret_ctx, e)?;
            type_ctx.check_not_moved_from_projection(&te, errors);
            mark_expr_moved_if_ident(scopes, errors, &te);
            Some(Box::new(te))
        }
        None => None,
    };

    if let Some(expected_ret) = type_ctx.current_return_type {
        match &mut t_opt {
            None if expected_ret != Type::Unit => {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Empty `return` in function expecting `{:?}`",
                        expected_ret
                    ),
                    label: format!("Expected return value of type `{:?}`", expected_ret),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
            Some(ret_expr) => {
                if matches!(expected_ret, Type::Ref(_) | Type::MutRef(_)) {
                    check_return_ref_lifetime(scopes, ret_expr, errors);
                }
                let unify_res = type_ctx.infer.borrow_mut().unify(expected_ret, ret_expr.ty());
                let found_ty = type_ctx.infer.borrow_mut().resolve(ret_expr.ty());
                if let Type::DynTrait(trait_name) = expected_ret {
                    if !matches!(found_ty, Type::DynTrait(_)) {
                        type_ctx.validate_dyn_coercion(&found_ty, trait_name, &ret_expr.span(), errors);
                        let inner = *ret_expr.clone();
                        **ret_expr = TypedExpr::CoerceToDyn(Box::new(inner), trait_name, span.clone());
                    }
                }
                if expected_ret == Type::Unit && found_ty != Type::Unit && found_ty != Type::Void {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Cannot return value of type `{:?}` from a unit function",
                            found_ty
                        ),
                        label: "Unexpected return value".into(),
                        secondary_label: None,
                        help: None,
                        span: ret_expr.span(),
                    });
                } else if unify_res.is_err() && !is_type_compatible(&expected_ret, &found_ty) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Mismatched return type: expected `{:?}`, found `{:?}`",
                            expected_ret, found_ty
                        ),
                        label: format!("Expected `{:?}`", expected_ret),
                        secondary_label: None,
                        help: None,
                        span: ret_expr.span(),
                    });
                }
            }
            _ => {}
        }
    }

    Some(TypedExpr::Return(t_opt, span.clone()))
}
