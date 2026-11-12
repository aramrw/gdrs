//! sanal/control_flow/branching.rs
//! Conditional branching (if, if-else) type checking.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{consume_tail_expr, is_diverging_expr, is_type_compatible},
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_if<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    cond: &Expr,
    body: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
    let pre_if_moves = scopes.snapshot_moves();
    let t_body = type_check_expr(scopes, errors, type_ctx, body)?;
    if is_diverging_expr(&t_body) {
        scopes.restore_moves(&pre_if_moves);
    }

    if t_cond.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("`if` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
            label: "Expected boolean expression".into(),
            secondary_label: None,
            help: Some("Try using a comparison operator like ==, <, or >".into()),
            span: t_cond.span().clone(),
        });
    }

    Some(TypedExpr::If(
        Box::new(t_cond),
        Box::new(t_body),
        span.clone(),
    ))
}

pub fn type_check_if_else<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    cond: &Expr,
    then_b: &Expr,
    else_b: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
    let pre_branch_moves = scopes.snapshot_moves();
    let t_then = type_check_expr(scopes, errors, type_ctx, then_b)?;
    let then_diverges = is_diverging_expr(&t_then);
    if !then_diverges {
        consume_tail_expr(scopes, errors, type_ctx, &t_then);
    }
    let then_moves = scopes.snapshot_moves();

    scopes.restore_moves(&pre_branch_moves);
    let t_else = type_check_expr(scopes, errors, type_ctx, else_b)?;
    let else_diverges = is_diverging_expr(&t_else);
    if !else_diverges {
        consume_tail_expr(scopes, errors, type_ctx, &t_else);
    }
    let else_moves = scopes.snapshot_moves();

    scopes.restore_moves(&pre_branch_moves);
    if !then_diverges {
        scopes.merge_moves(&then_moves);
    }
    if !else_diverges {
        scopes.merge_moves(&else_moves);
    }

    if t_cond.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("`if` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
            label: "Expected boolean expression".into(),
            secondary_label: None,
            help: None,
            span: t_cond.span().clone(),
        });
    }

    let then_diverges = is_diverging_expr(&t_then);
    let else_diverges = is_diverging_expr(&t_else);

    let res_ty = if then_diverges && else_diverges {
        Type::Void
    } else if then_diverges {
        type_ctx.infer.borrow_mut().resolve(t_else.ty())
    } else if else_diverges {
        type_ctx.infer.borrow_mut().resolve(t_then.ty())
    } else {
        let unify_res = type_ctx
            .infer
            .borrow_mut()
            .unify_branches(t_then.ty(), t_else.ty());
        let resolved_then = type_ctx.infer.borrow_mut().resolve(t_then.ty());
        let resolved_else = type_ctx.infer.borrow_mut().resolve(t_else.ty());
        if unify_res.is_err()
            && !is_type_compatible(&resolved_then, &resolved_else)
            && !is_type_compatible(&resolved_else, &resolved_then)
        {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "`if` and `else` branches have incompatible types (`{:?}` vs `{:?}`)",
                    resolved_then,
                    resolved_else
                ),
                label: format!("Expected `{:?}` because of `if` branch", resolved_then),
                secondary_label: Some((
                    t_then.span().clone(),
                    format!("`if` branch evaluated to type `{:?}`", resolved_then),
                )),
                help: Some(
                    "Both branches of an if/else expression must yield compatible types".into(),
                ),
                span: t_else.span().clone(),
            });
        }
        resolved_then
    };

    Some(TypedExpr::IfElse(
        Box::new(t_cond),
        Box::new(t_then),
        Box::new(t_else),
        res_ty,
        span.clone(),
    ))
}

