//! sanal/control_flow/loops.rs
//! Loop constructs (while, break, continue) type checking.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        compat::is_diverging_expr,
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_while<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    cond: &Expr,
    body: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let pre_loop_moves = scopes.snapshot_moves();
    let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
    let mut loop_ctx = type_ctx.clone();
    loop_ctx.loop_depth += 1;
    let t_body = type_check_expr(scopes, errors, &loop_ctx, body)?;

    if !is_diverging_expr(&t_body) {
        let post_iter_moves = scopes.snapshot_moves();
        let moved_across_iter = pre_loop_moves.iter().zip(post_iter_moves.iter()).any(|(pre, post)| {
            pre.iter().any(|(k, &was_moved)| !was_moved && post.get(k).copied().unwrap_or(false))
        });
        if moved_across_iter {
            let mut iter2_errors = Vec::new();
            let _ = type_check_expr(scopes, &mut iter2_errors, type_ctx, cond);
            let _ = type_check_expr(scopes, &mut iter2_errors, &loop_ctx, body);
            for err in iter2_errors {
                if err.code == "E0382" {
                    errors.push(err);
                }
            }
            scopes.restore_moves(&post_iter_moves);
        }
    }

    if t_cond.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("`while` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
            label: "Expected boolean condition".into(),
            secondary_label: None,
            help: None,
            span: t_cond.span().clone(),
        });
    }

    Some(TypedExpr::While(
        Box::new(t_cond),
        Box::new(t_body),
        span.clone(),
    ))
}

pub fn type_check_break<'a>(
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) -> Option<TypedExpr> {
    if type_ctx.loop_depth == 0 {
        errors.push(SemanticError {
            code: "E0268",
            message: "`break` outside of a loop".to_string(),
            label: "Cannot `break` outside of a `while` or `for` loop".to_string(),
            secondary_label: None,
            help: Some("Move `break` inside a loop body".to_string()),
            span: span.clone(),
        });
    }
    Some(TypedExpr::Break(span.clone()))
}

pub fn type_check_continue<'a>(
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) -> Option<TypedExpr> {
    if type_ctx.loop_depth == 0 {
        errors.push(SemanticError {
            code: "E0268",
            message: "`continue` outside of a loop".to_string(),
            label: "Cannot `continue` outside of a `while` or `for` loop".to_string(),
            secondary_label: None,
            help: Some("Move `continue` inside a loop body".to_string()),
            span: span.clone(),
        });
    }
    Some(TypedExpr::Continue(span.clone()))
}

