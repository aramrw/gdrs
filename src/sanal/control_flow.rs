//! sanal/control_flow.rs
//! Type checking for control flow: block, unsafe, match, try, while, if, if-else, return.

use crate::{
    ast::{Expr, MatchArm, Span, Type, TypedExpr, TypedMatchArm},
    sanal::{
        compat::{
            consume_tail_expr, extract_root_ident_with_ty, extract_root_var, is_diverging_expr,
            is_type_compatible, mark_expr_moved_if_ident,
        },
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn check_return_ref_lifetime(
    scopes: &ScopeStack,
    expr: &TypedExpr,
    errors: &mut Vec<SemanticError>,
) {
    match expr {
        TypedExpr::Ref(inner, _, _, span) => match extract_root_ident_with_ty(inner) {
            None => errors.push(SemanticError {
                code: "E0515",
                message: "Cannot return reference to temporary value".to_string(),
                label: "Returns a reference to data owned by the current function".to_string(),
                secondary_label: None,
                help: Some("Return an owned value instead of a reference".to_string()),
                span: span.clone(),
            }),
            Some((root, root_ty)) => {
                let valid_caller_origin = matches!(root_ty, Type::Ref(_) | Type::MutRef(_))
                    && scopes.lookup(root).is_some_and(|info| info.from_caller);
                if !valid_caller_origin {
                    errors.push(SemanticError {
                        code: "E0515",
                        message: format!("Cannot return reference to local variable `{root}`"),
                        label: "Returns a reference to data owned by the current function"
                            .to_string(),
                        secondary_label: None,
                        help: Some("Return an owned value instead of a reference".to_string()),
                        span: span.clone(),
                    });
                }
            }
        },
        TypedExpr::Ident(name, ty, span) => {
            if matches!(ty, Type::Ref(_) | Type::MutRef(_))
                && !scopes.lookup(name).is_some_and(|info| info.from_caller)
            {
                errors.push(SemanticError {
                    code: "E0515",
                    message: format!(
                        "Cannot return reference `{name}` that borrows from a local variable"
                    ),
                    label: "Returns a reference to data owned by the current function"
                        .to_string(),
                    secondary_label: None,
                    help: Some("Return an owned value instead of a reference".to_string()),
                    span: span.clone(),
                });
            }
        }
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            if let Some(last) = stmts.last() {
                check_return_ref_lifetime(scopes, last, errors);
            }
        }
        TypedExpr::IfElse(_, then_b, else_b, _, _) => {
            if !is_diverging_expr(then_b) {
                check_return_ref_lifetime(scopes, then_b, errors);
            }
            if !is_diverging_expr(else_b) {
                check_return_ref_lifetime(scopes, else_b, errors);
            }
        }
        TypedExpr::Match(_, arms, _, _) => {
            for arm in arms {
                if !crate::sanal::compat::definitely_returns(&arm.body) {
                    if let Some(last) = arm.body.last() {
                        check_return_ref_lifetime(scopes, last, errors);
                    }
                }
            }
        }
        TypedExpr::Call(_, args, _, _) => {
            for arg in args {
                if matches!(arg.ty(), Type::Ref(_) | Type::MutRef(_)) {
                    check_return_ref_lifetime(scopes, arg, errors);
                }
            }
        }
        _ => {}
    }
}

fn check_block_escape_lifetime(
    scopes: &ScopeStack,
    expr: &TypedExpr,
    errors: &mut Vec<SemanticError>,
) {
    match expr {
        TypedExpr::Ref(inner, _, _, span) => {
            if let Some(root) = extract_root_var(inner) {
                if scopes.current_scope_contains(root) {
                    errors.push(SemanticError {
                        code: "E0597",
                        message: format!(
                            "`{root}` does not live long enough; dropped at end of block while borrowed"
                        ),
                        label: "Borrowed value does not live long enough".to_string(),
                        secondary_label: None,
                        help: Some("Bind the value outside this block before borrowing it".to_string()),
                        span: span.clone(),
                    });
                }
            }
        }
        TypedExpr::Ident(name, ty, span) if matches!(ty, Type::Ref(_) | Type::MutRef(_)) => {
            if let Some(target) = scopes.borrow_target(name) {
                if scopes.current_scope_contains(&target) {
                    errors.push(SemanticError {
                        code: "E0597",
                        message: format!(
                            "`{target}` does not live long enough; dropped at end of block while borrowed"
                        ),
                        label: "Borrowed value does not live long enough".to_string(),
                        secondary_label: None,
                        help: Some("Bind the value outside this block before borrowing it".to_string()),
                        span: span.clone(),
                    });
                }
            }
        }
        _ => {}
    }
}

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

pub fn type_check_match<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target_expr: &Expr,
    arms: &[MatchArm],
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target_expr)?;
    let resolved_target_ty = type_ctx.infer.borrow_mut().resolve(t_target.ty());
    let is_ref_target = matches!(resolved_target_ty, Type::Ref(_) | Type::MutRef(_));
    let unwrapped_target_ty = match resolved_target_ty {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };
    let enum_name = match unwrapped_target_ty {
        Type::Enum(name) => name,
        Type::Obj(name) if type_ctx.contains_enum(name) => name,
        other => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("`match` target must be an `enum`, found `{:?}`", other),
                label: "Expected enum type".into(),
                secondary_label: None,
                help: None,
                span: target_expr.span().clone(),
            });
            return None;
        }
    };

    let variant_info = type_ctx.get_enum(enum_name);
    let can_move_target = !is_ref_target
        && match &t_target {
            TypedExpr::Ident(name, _, _) if name != "self" => true,
            _ => false,
        };
    if can_move_target {
        mark_expr_moved_if_ident(scopes, errors, &t_target);
    } else if !is_ref_target {
        type_ctx.check_not_moved_from_projection(&t_target, errors);
    }
    let pre_match_moves = scopes.snapshot_moves();
    let mut non_diverging_moves = Vec::new();
    let mut typed_arms = Vec::new();
    let mut non_diverging_arm: Option<(Type, Span)> = None;
    let mut all_diverging = !arms.is_empty();
    let mut has_wildcard = false;
    let mut covered_variants = std::collections::HashSet::new();

    for arm in arms {
        scopes.restore_moves(&pre_match_moves);
        scopes.push_scope();
        let mut typed_bindings = Vec::new();
        let tag = if arm.variant_name == "_" {
            has_wildcard = true;
            -1
        } else {
            let short_v_name = arm
                .variant_name
                .split("::")
                .last()
                .unwrap_or(&arm.variant_name);
            covered_variants.insert(short_v_name.to_string());
            if let Some((_, v_map)) = &variant_info {
                if let Some((v_tag, p_types)) = v_map.get(short_v_name) {
                    for (b_name, p_ty) in arm.bindings.iter().zip(p_types.iter()) {
                        let mut bound_ty = *p_ty;
                        // Fallback for unmonomorphized VecIter::next returning Option<i64>
                        if short_v_name == "Some" && (*p_ty == Type::Int || matches!(*p_ty, Type::Generic(_))) {
                            if let TypedExpr::Call(name, args, _, _) = &t_target {
                                if (name == "next" || name.ends_with("_next")) && !args.is_empty() {
                                    if let TypedExpr::Ident(iter_var_name, _, _) = &args[0] {
                                        if let Some(info) = scopes.lookup(iter_var_name) {
                                            if let Type::Vec(elem_ty) = info.ty {
                                                bound_ty = *elem_ty;
                                            } else if let Type::Obj(obj_name) = info.ty {
                                                if let Some((_, t_args)) = crate::sanal::mono::lookup_mangled(obj_name) {
                                                    if let Some(first_t) = t_args.first() {
                                                        bound_ty = *first_t;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if b_name != "_" {
                            if is_ref_target && type_ctx.has_drop_ownership(&bound_ty) {
                                errors.push(SemanticError {
                                    code: "E0507",
                                    message: format!(
                                        "Cannot move out of borrowed enum payload `{b_name}` of type `{bound_ty:?}`"
                                    ),
                                    label: "Cannot move out of borrowed enum".to_string(),
                                    secondary_label: None,
                                    help: Some(
                                        "Match on the owned enum by value or ignore the payload with `_`"
                                            .to_string(),
                                    ),
                                    span: arm.span.clone(),
                                });
                            }
                            scopes.declare(b_name.clone(), false, bound_ty);
                        }
                        typed_bindings.push((b_name.clone(), bound_ty));
                    }
                    *v_tag
                } else {
                    errors.push(SemanticError {
                        code: "E0004",
                        message: format!(
                            "Unknown variant `{}` for enum `{}`",
                            arm.variant_name, enum_name
                        ),
                        label: "Unknown variant".into(),
                        secondary_label: None,
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
        let mut arm_stmt_ctx = type_ctx.clone();
        arm_stmt_ctx.current_expected_type = None;
        for (idx, stmt) in arm.body.iter().enumerate() {
            let ctx_for_stmt = if idx + 1 == arm.body.len() { type_ctx } else { &arm_stmt_ctx };
            if let Some(t_stmt) = type_check_expr(scopes, errors, ctx_for_stmt, stmt) {
                typed_arm_stmts.push(t_stmt);
            }
        }
        let arm_diverges = crate::sanal::compat::definitely_returns(&typed_arm_stmts);
        if !arm_diverges {
            if let Some(last) = typed_arm_stmts.last() {
                consume_tail_expr(scopes, errors, type_ctx, last);
                check_block_escape_lifetime(scopes, last, errors);
            }
        }
        scopes.pop_scope();

        if !arm_diverges {
            non_diverging_moves.push(scopes.snapshot_moves());
            all_diverging = false;
        let arm_ty = match typed_arm_stmts.last() {
            Some(TypedExpr::Let(..)) | Some(TypedExpr::LetTuple(..)) | None => Type::Unit,
            Some(last) => last.ty(),
        };
            if let Some((expected_ty, first_span)) = &non_diverging_arm {
                let unify_res = type_ctx.infer.borrow_mut().unify_branches(*expected_ty, arm_ty);
                let resolved_expected = type_ctx.infer.borrow_mut().resolve(*expected_ty);
                let resolved_arm = type_ctx.infer.borrow_mut().resolve(arm_ty);
                if unify_res.is_err()
                    && !is_type_compatible(&resolved_expected, &resolved_arm)
                    && !is_type_compatible(&resolved_arm, &resolved_expected)
                {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "`match` arms have incompatible types: expected `{:?}`, found `{:?}`",
                            resolved_expected, resolved_arm
                        ),
                        label: format!("Expected `{:?}`", resolved_expected),
                        secondary_label: Some((
                            first_span.clone(),
                            format!("First arm has type `{:?}`", resolved_expected),
                        )),
                        help: Some("All non-diverging match arms must produce compatible types".into()),
                        span: arm.span.clone(),
                    });
                }
            } else {
                non_diverging_arm = Some((arm_ty, arm.span.clone()));
            }
        }

        typed_arms.push(TypedMatchArm {
            variant_name: arm.variant_name.clone(),
            tag,
            bindings: typed_bindings,
            body: typed_arm_stmts,
            span: arm.span.clone(),
        });
    }

    scopes.restore_moves(&pre_match_moves);
    for br in non_diverging_moves {
        scopes.merge_moves(&br);
    }

    if !has_wildcard {
        if let Some((_, v_map)) = &variant_info {
            let mut missing: Vec<&str> = v_map
                .keys()
                .filter(|v| !covered_variants.contains(v.as_str()))
                .map(|v| v.as_str())
                .collect();
            missing.sort();
            if !missing.is_empty() {
                errors.push(SemanticError {
                    code: "E0004",
                    message: format!(
                        "Non-exhaustive `match` on enum `{enum_name}`: missing variant(s) {}",
                        missing.join(", ")
                    ),
                    label: format!("Missing pattern(s): {}", missing.join(", ")),
                    secondary_label: None,
                    help: Some("Add arms for all variants or a catch-all `_ => ...` arm".into()),
                    span: span.clone(),
                });
            }
        }
    }

    let match_ty = if all_diverging {
        Type::Void
    } else {
        non_diverging_arm
            .map(|(t, _)| type_ctx.infer.borrow_mut().resolve(t))
            .unwrap_or(Type::Unit)
    };
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

    let (is_option, is_result, enum_name) = match inner_ty {
        Type::Enum(name) | Type::Obj(name) => (
            name.contains("Option"),
            name.contains("Result"),
            name.to_string(),
        ),
        _ => (false, false, String::new()),
    };

    if !is_option && !is_result {
        errors.push(SemanticError {
            code: "E0308",
            message: format!(
                "The `?` operator can only be applied to `Option` or `Result`, found `{:?}`",
                inner_ty
            ),
            label: "Cannot apply `?` operator".into(),
            secondary_label: None,
            help: Some("Ensure expression returns an Option or Result type".into()),
            span: span.clone(),
        });
        return None;
    }

    let ret_enum_name = match type_ctx.current_return_type {
        Some(Type::Enum(ret_name)) | Some(Type::Obj(ret_name)) => {
            let compatible_kind = (is_option && ret_name.contains("Option"))
                || (is_result && ret_name.contains("Result"));
            if !compatible_kind {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Cannot use `?` on `{enum_name}` inside a function returning `{ret_name}`"
                    ),
                    label: "Incompatible enclosing return type for `?`".into(),
                    secondary_label: None,
                    help: Some(if is_option {
                        "Function must return `Option<...>` to propagate `Option` with `?`".into()
                    } else {
                        "Function must return `Result<...>` to propagate `Result` with `?`".into()
                    }),
                    span: span.clone(),
                });
            }
            ret_name.to_string()
        }
        Some(other) => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot use `?` inside a function returning `{:?}`",
                    other
                ),
                label: "Enclosing function cannot propagate errors with `?`".into(),
                secondary_label: None,
                help: Some(if is_option {
                    "Change the function return type to `Option<...>`".into()
                } else {
                    "Change the function return type to `Result<...>`".into()
                }),
                span: span.clone(),
            });
            enum_name.clone()
        }
        None => enum_name.clone(),
    };

    let variant_info = type_ctx.get_enum(&enum_name);
    let ret_variant_info = type_ctx.get_enum(&ret_enum_name);

    if is_option {
        let (some_tag, payload_ty) = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("Some"))
            .map(|(tag, p)| (*tag, p.first().copied().unwrap_or(Type::Int)))
            .unwrap_or((0, Type::Int));
        let none_tag = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("None"))
            .map(|(tag, _)| *tag)
            .unwrap_or(1);
        let (ret_static, ret_none_disc) = ret_variant_info
            .as_ref()
            .map(|(static_name, v_map)| {
                let d = v_map.get("None").map(|(tag, _)| *tag as usize).unwrap_or(1);
                (*static_name, d)
            })
            .unwrap_or((crate::ast::intern_str(&ret_enum_name), 1));

        let arm_some = TypedMatchArm {
            variant_name: format!("{enum_name}::Some"),
            tag: some_tag,
            bindings: vec![("__try_val".to_string(), payload_ty)],
            body: vec![TypedExpr::Ident("__try_val".to_string(), payload_ty, span.clone())],
            span: span.clone(),
        };
        let arm_none = TypedMatchArm {
            variant_name: format!("{enum_name}::None"),
            tag: none_tag,
            bindings: vec![],
            body: vec![TypedExpr::Return(
                Some(Box::new(TypedExpr::EnumConstruct(
                    ret_static.to_string(),
                    "None".to_string(),
                    ret_none_disc,
                    vec![],
                    Type::Enum(ret_static),
                    span.clone(),
                ))),
                span.clone(),
            )],
            span: span.clone(),
        };
        Some(TypedExpr::Match(
            Box::new(t_inner),
            vec![arm_some, arm_none],
            payload_ty,
            span.clone(),
        ))
    } else {
        let (ok_tag, payload_ty) = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("Ok"))
            .map(|(tag, p)| (*tag, p.first().copied().unwrap_or(Type::Int)))
            .unwrap_or((0, Type::Int));
        let (err_tag, err_ty) = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("Err"))
            .map(|(tag, p)| (*tag, p.first().copied().unwrap_or(Type::Int)))
            .unwrap_or((1, Type::Int));
        let (ret_static, ret_err_disc) = ret_variant_info
            .as_ref()
            .map(|(static_name, v_map)| {
                let d = v_map.get("Err").map(|(tag, _)| *tag as usize).unwrap_or(1);
                (*static_name, d)
            })
            .unwrap_or((crate::ast::intern_str(&ret_enum_name), 1));

        let arm_ok = TypedMatchArm {
            variant_name: format!("{enum_name}::Ok"),
            tag: ok_tag,
            bindings: vec![("__try_val".to_string(), payload_ty)],
            body: vec![TypedExpr::Ident("__try_val".to_string(), payload_ty, span.clone())],
            span: span.clone(),
        };
        let arm_err = TypedMatchArm {
            variant_name: format!("{enum_name}::Err"),
            tag: err_tag,
            bindings: vec![("__try_err".to_string(), err_ty)],
            body: vec![TypedExpr::Return(
                Some(Box::new(TypedExpr::EnumConstruct(
                    ret_static.to_string(),
                    "Err".to_string(),
                    ret_err_disc,
                    vec![TypedExpr::Ident("__try_err".to_string(), err_ty, span.clone())],
                    Type::Enum(ret_static),
                    span.clone(),
                ))),
                span.clone(),
            )],
            span: span.clone(),
        };
        Some(TypedExpr::Match(
            Box::new(t_inner),
            vec![arm_ok, arm_err],
            payload_ty,
            span.clone(),
        ))
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
