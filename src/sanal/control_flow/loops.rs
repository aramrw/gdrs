//! sanal/control_flow/loops.rs
//! Loop constructs (while, break, continue) type checking.

use std::{cell::RefCell, rc::Rc};

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{is_diverging_expr, is_type_compatible},
        types::{type_check_expr, LoopBreakTracker, TypeCtx},
        ScopeStack, SemanticError,
    },
};

fn check_second_loop_iteration<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    loop_ctx: &TypeCtx<'a>,
    pre_loop_moves: &[std::collections::HashMap<String, bool>],
    cond: Option<&Expr>,
    body: &Expr,
    cond_ctx: &TypeCtx<'a>,
) {
    let post_iter_moves = scopes.snapshot_moves();
    let moved_across_iter = pre_loop_moves.iter().zip(post_iter_moves.iter()).any(|(pre, post)| {
        pre.iter()
            .any(|(k, &was_moved)| !was_moved && post.get(k).copied().unwrap_or(false))
    });
    if moved_across_iter {
        let mut iter2_errors = Vec::new();
        if let Some(c) = cond {
            let _ = type_check_expr(scopes, &mut iter2_errors, cond_ctx, c);
        }
        let _ = type_check_expr(scopes, &mut iter2_errors, loop_ctx, body);
        for err in iter2_errors {
            if err.code == "E0382" {
                errors.push(err);
            }
        }
        scopes.restore_moves(&post_iter_moves);
    }
}

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
    loop_ctx.current_loop_breaks = Some(Rc::new(RefCell::new(LoopBreakTracker {
        allow_value: false,
        expected_ty: None,
        seen_types: Vec::new(),
    })));
    loop_ctx.current_expected_type = None;
    let t_body = type_check_expr(scopes, errors, &loop_ctx, body)?;

    if !is_diverging_expr(&t_body) {
        check_second_loop_iteration(
            scopes,
            errors,
            &loop_ctx,
            &pre_loop_moves,
            Some(cond),
            body,
            type_ctx,
        );
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

pub fn type_check_loop<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    body: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let pre_loop_moves = scopes.snapshot_moves();
    let tracker = Rc::new(RefCell::new(LoopBreakTracker {
        allow_value: true,
        expected_ty: type_ctx.current_expected_type,
        seen_types: Vec::new(),
    }));
    let mut loop_ctx = type_ctx.clone();
    loop_ctx.loop_depth += 1;
    loop_ctx.current_loop_breaks = Some(tracker.clone());
    loop_ctx.current_expected_type = None;

    let t_body = type_check_expr(scopes, errors, &loop_ctx, body)?;

    if !is_diverging_expr(&t_body) {
        check_second_loop_iteration(
            scopes,
            errors,
            &loop_ctx,
            &pre_loop_moves,
            None,
            body,
            type_ctx,
        );
    }

    let seen = tracker.borrow().seen_types.clone();
    let result_ty = if seen.is_empty() {
        Type::Void
    } else {
        let mut acc = seen[0].0;
        for (b_ty, b_span) in seen.iter().skip(1) {
            if acc == Type::Void {
                acc = *b_ty;
            } else if *b_ty != Type::Void && !is_type_compatible(&acc, b_ty) {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "`loop` has incompatible `break` types: expected `{:?}`, found `{:?}`",
                        acc, b_ty
                    ),
                    label: "Incompatible `break` value type".into(),
                    secondary_label: None,
                    help: Some("All `break` expressions inside a `loop` must yield the same type".into()),
                    span: b_span.clone(),
                });
            }
        }
        acc
    };

    Some(TypedExpr::Loop(Box::new(t_body), result_ty, span.clone()))
}

pub fn type_check_break<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    opt_val: Option<&Expr>,
    span: &Span,
) -> Option<TypedExpr> {
    if type_ctx.loop_depth == 0 {
        errors.push(SemanticError {
            code: "E0268",
            message: "`break` outside of a loop".to_string(),
            label: "Cannot `break` outside of a `while`, `loop`, or `for` loop".to_string(),
            secondary_label: None,
            help: Some("Move `break` inside a loop body".to_string()),
            span: span.clone(),
        });
    }

    let expected_for_val = type_ctx
        .current_loop_breaks
        .as_ref()
        .and_then(|t| if t.borrow().allow_value { t.borrow().expected_ty } else { None });

    let typed_val = if let Some(val_expr) = opt_val {
        let mut val_ctx = type_ctx.clone();
        val_ctx.current_expected_type = expected_for_val;
        let tv = type_check_expr(scopes, errors, &val_ctx, val_expr)?;
        if let Some(tracker) = &type_ctx.current_loop_breaks {
            if !tracker.borrow().allow_value {
                errors.push(SemanticError {
                    code: "E0571",
                    message: "`break` with a value can only be used inside a `loop`".to_string(),
                    label: "Can only `break` with a value in a `loop` expression".to_string(),
                    secondary_label: None,
                    help: Some("Use `loop:` instead of `while` or `for`, or omit the value after `break`".to_string()),
                    span: span.clone(),
                });
            } else {
                if let Some(exp) = expected_for_val {
                    if !is_type_compatible(&exp, &tv.ty()) && tv.ty() != Type::Void {
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "mismatched types in `break`: expected `{:?}`, found `{:?}`",
                                exp,
                                tv.ty()
                            ),
                            label: "Unexpected `break` value type".into(),
                            secondary_label: None,
                            help: None,
                            span: tv.span().clone(),
                        });
                    }
                }
                let mut tr = tracker.borrow_mut();
                if tr.expected_ty.is_none() && tv.ty() != Type::Void {
                    tr.expected_ty = Some(tv.ty());
                }
                tr.seen_types.push((tv.ty(), tv.span().clone()));
            }
        }
        Some(Box::new(tv))
    } else {
        if let Some(tracker) = &type_ctx.current_loop_breaks {
            if tracker.borrow().allow_value {
                if let Some(exp) = expected_for_val {
                    if !is_type_compatible(&exp, &Type::Unit) {
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "mismatched types in `break`: expected `{:?}`, found `()`",
                                exp
                            ),
                            label: "`break` without a value yields `()`".into(),
                            secondary_label: None,
                            help: None,
                            span: span.clone(),
                        });
                    }
                }
                tracker.borrow_mut().seen_types.push((Type::Unit, span.clone()));
            }
        }
        None
    };

    Some(TypedExpr::Break(typed_val, span.clone()))
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

