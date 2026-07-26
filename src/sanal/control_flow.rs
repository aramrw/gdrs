//! sanal/control_flow.rs
//! Type checking for control flow: block, unsafe, match, try, while, if, if-else, return.

use crate::{
    ast::{Expr, MatchArm, Span, Type, TypedExpr},
    sanal::{
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
    for stmt in stmts {
        if let Some(t_stmt) = type_check_expr(scopes, errors, type_ctx, stmt) {
            typed_stmts.push(t_stmt);
        }
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
    let mut typed_stmts = Vec::new();
    for stmt in stmts {
        if let Some(t_stmt) = type_check_expr(scopes, errors, &unsafe_ctx, stmt) {
            typed_stmts.push(t_stmt);
        }
    }
    scopes.pop_scope();
    let block_ty = typed_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
    Some(TypedExpr::Unsafe(typed_stmts, block_ty, span.clone()))
}

pub fn type_check_match<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target_expr: &Expr,
    arms: &[MatchArm],
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target_expr)?;
    let enum_name = match t_target.ty() {
        Type::Enum(name) => name,
        Type::Obj(name) if type_ctx.enum_map.contains_key(name) => name,
        other => {
            errors.push(SemanticError {
                message: format!("`match` target must be an `enum`, found `{:?}`", other),
                label: "Expected enum type".into(),
                help: None,
                span: target_expr.span().clone(),
            });
            return None;
        }
    };

    let variant_info = type_ctx.enum_map.get(enum_name).cloned();
    let mut typed_arms = Vec::new();
    let mut arm_types = Vec::new();

    for arm in arms {
        scopes.push_scope();
        let mut typed_bindings = Vec::new();
        let tag = if arm.variant_name == "_" {
            -1
        } else {
            let short_v_name = arm
                .variant_name
                .split("::")
                .last()
                .unwrap_or(&arm.variant_name);
            if let Some((_, v_map)) = &variant_info {
                if let Some((v_tag, p_types)) = v_map.get(short_v_name) {
                    for (b_name, p_ty) in arm.bindings.iter().zip(p_types.iter()) {
                        if b_name != "_" {
                            scopes.declare(b_name.clone(), false, *p_ty);
                        }
                        typed_bindings.push((b_name.clone(), *p_ty));
                    }
                    *v_tag
                } else {
                    errors.push(SemanticError {
                        message: format!(
                            "Unknown variant `{}` for enum `{}`",
                            arm.variant_name, enum_name
                        ),
                        label: "Unknown variant".into(),
                        help: None,
                        span: arm.span.clone(),
                    });
                    -1
                }
            } else {
                -1
            }
        };

        let mut typed_arm_stmts = Vec::new();
        for stmt in &arm.body {
            if let Some(t_stmt) = type_check_expr(scopes, errors, type_ctx, stmt) {
                typed_arm_stmts.push(t_stmt);
            }
        }
        scopes.pop_scope();

        let arm_ty = typed_arm_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
        arm_types.push(arm_ty);

        typed_arms.push(crate::ast::TypedMatchArm {
            variant_name: arm.variant_name.clone(),
            tag,
            bindings: typed_bindings,
            body: typed_arm_stmts,
            span: arm.span.clone(),
        });
    }

    let match_ty = arm_types.first().cloned().unwrap_or(Type::Unit);
    Some(TypedExpr::Match(
        Box::new(t_target),
        typed_arms,
        match_ty,
        span.clone(),
    ))
}

pub fn type_check_try<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    inner_expr: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_inner = type_check_expr(scopes, errors, type_ctx, inner_expr)?;
    let inner_ty = t_inner.ty();
    let enum_name_opt = match inner_ty {
        Type::Enum(name) | Type::Obj(name) if name.ends_with("Option") => {
            Some("std_core_Option".to_string())
        }
        _ => None,
    };
    let enum_name_res = match inner_ty {
        Type::Enum(name) | Type::Obj(name) if name.ends_with("Result") => {
            Some("std_core_Result".to_string())
        }
        _ => None,
    };

    if let Some(enum_name) = enum_name_opt {
        let match_expr = Expr::Match(
            Box::new(inner_expr.clone()),
            vec![
                MatchArm {
                    variant_name: format!("{enum_name}::Some"),
                    bindings: vec!["val".to_string()],
                    body: vec![Expr::Ident("val".to_string(), span.clone())],
                    span: span.clone(),
                },
                MatchArm {
                    variant_name: format!("{enum_name}::None"),
                    bindings: vec![],
                    body: vec![Expr::Return(
                        Some(Box::new(Expr::Ident(
                            format!("{enum_name}_None"),
                            span.clone(),
                        ))),
                        span.clone(),
                    )],
                    span: span.clone(),
                },
            ],
            span.clone(),
        );
        type_check_expr(scopes, errors, type_ctx, &match_expr)
    } else if let Some(enum_name) = enum_name_res {
        let match_expr = Expr::Match(
            Box::new(inner_expr.clone()),
            vec![
                MatchArm {
                    variant_name: format!("{enum_name}::Ok"),
                    bindings: vec!["val".to_string()],
                    body: vec![Expr::Ident("val".to_string(), span.clone())],
                    span: span.clone(),
                },
                MatchArm {
                    variant_name: format!("{enum_name}::Err"),
                    bindings: vec!["err".to_string()],
                    body: vec![Expr::Return(
                        Some(Box::new(Expr::Call(
                            format!("{enum_name}_Err"),
                            vec![Expr::Ident("err".to_string(), span.clone())],
                            span.clone(),
                        ))),
                        span.clone(),
                    )],
                    span: span.clone(),
                },
            ],
            span.clone(),
        );
        type_check_expr(scopes, errors, type_ctx, &match_expr)
    } else {
        errors.push(SemanticError {
            message: format!(
                "The `?` operator can only be applied to `Option` or `Result`, found `{:?}`",
                inner_ty
            ),
            label: "Cannot apply `?` operator".into(),
            help: Some("Ensure expression returns an Option or Result type".into()),
            span: span.clone(),
        });
        None
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
    let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
    let t_body = type_check_expr(scopes, errors, type_ctx, body)?;

    if t_cond.ty() != Type::Bool {
        errors.push(SemanticError {
            message: format!("`while` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
            label: "Expected boolean condition".into(),
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

pub fn type_check_if<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    cond: &Expr,
    body: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
    let t_body = type_check_expr(scopes, errors, type_ctx, body)?;

    if t_cond.ty() != Type::Bool {
        errors.push(SemanticError {
            message: format!("`if` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
            label: "Expected boolean expression".into(),
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
    let t_then = type_check_expr(scopes, errors, type_ctx, then_b)?;
    let t_else = type_check_expr(scopes, errors, type_ctx, else_b)?;

    if t_cond.ty() != Type::Bool {
        errors.push(SemanticError {
            message: format!("`if` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
            label: "Expected boolean expression".into(),
            help: None,
            span: t_cond.span().clone(),
        });
    }

    if t_then.ty() != t_else.ty() {
        errors.push(SemanticError {
            message: format!(
                "`if` and `else` branches have incompatible types (`{:?}` vs `{:?}`)",
                t_then.ty(),
                t_else.ty()
            ),
            label: format!("Expected `{:?}` because of `if` branch", t_then.ty()),
            help: Some(
                "Both branches of an if/else expression must yield the exact same type".into(),
            ),
            span: t_else.span().clone(),
        });
    }

    let res_ty = t_then.ty();
    Some(TypedExpr::IfElse(
        Box::new(t_cond),
        Box::new(t_then),
        Box::new(t_else),
        res_ty,
        span.clone(),
    ))
}

pub fn type_check_return<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    opt_expr: Option<&Expr>,
    span: &Span,
) -> Option<TypedExpr> {
    let t_opt = match opt_expr {
        Some(e) => Some(Box::new(type_check_expr(scopes, errors, type_ctx, e)?)),
        None => None,
    };
    Some(TypedExpr::Return(t_opt, span.clone()))
}
