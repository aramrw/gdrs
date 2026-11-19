//! sanal/control_flow/patterns.rs
//! Match expression and pattern matching type checking.

use crate::{
    ast::{Expr, MatchArm, Span, TuplePattern, Type, TypedExpr, TypedMatchArm},
    sanal::{
        compat::{consume_tail_expr, is_type_compatible, mark_expr_moved_if_ident},
        control_flow::lifetimes::check_block_escape_lifetime,
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

#[derive(Clone)]
enum MatchTargetKind<'a> {
    Enum {
        enum_name: &'a str,
        variant_info: Option<(&'static str, std::collections::HashMap<String, (i64, Vec<Type>)>)>,
        is_ref_target: bool,
    },
    Bool,
    Int(Type),
}

fn parse_scalar_lit_tag(
    pat: &str,
    target_kind: &MatchTargetKind<'_>,
    errors: &mut Vec<SemanticError>,
    span: &Span,
) -> Option<i64> {
    match target_kind {
        MatchTargetKind::Bool => {
            if let Some(b) = pat.strip_prefix("__lit_bool:") {
                Some(if b == "true" { 1 } else { 0 })
            } else {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!("Mismatched pattern `{}` for `bool` match target", pat.trim_start_matches("__lit_int:")),
                    label: "Expected `true`, `false`, or `_`".into(),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
                None
            }
        }
        MatchTargetKind::Int(ity) => {
            if let Some(num_str) = pat.strip_prefix("__lit_int:") {
                if let Ok(v) = num_str.parse::<i64>() {
                    return Some(v);
                }
                if let Ok(v) = num_str.parse::<u64>() {
                    return Some(v as i64);
                }
            }
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Mismatched pattern `{}` for integer type `{ity:?}`", pat.trim_start_matches("__lit_bool:")),
                label: "Expected integer literal or `_`".into(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
            None
        }
        MatchTargetKind::Enum { enum_name, .. } => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Cannot match literal pattern against enum `{enum_name}`"),
                label: "Expected enum variant or `_`".into(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
            None
        }
    }
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

    let target_kind = match unwrapped_target_ty {
        Type::Enum(name) => {
            let variant_info = type_ctx.get_enum(name).or_else(|| {
                if name.starts_with("std_core_Option") || name.starts_with("Option") {
                    type_ctx.get_enum("std_core_Option").or_else(|| type_ctx.get_enum("Option"))
                } else {
                    None
                }
            });
            MatchTargetKind::Enum { enum_name: name, variant_info, is_ref_target }
        }
        Type::Obj(name) if type_ctx.contains_enum(name) => {
            let variant_info = type_ctx.get_enum(name);
            MatchTargetKind::Enum { enum_name: name, variant_info, is_ref_target }
        }
        Type::Bool => MatchTargetKind::Bool,
        Type::Int
        | Type::I8
        | Type::U8
        | Type::I16
        | Type::U16
        | Type::I32
        | Type::U32
        | Type::U64 => MatchTargetKind::Int(unwrapped_target_ty),
        other => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "`match` target must be an `enum`, integer, or `bool`, found `{:?}`",
                    other
                ),
                label: "Unsupported `match` target type".into(),
                secondary_label: None,
                help: None,
                span: target_expr.span().clone(),
            });
            return None;
        }
    };

    let can_move_target = matches!(target_kind, MatchTargetKind::Enum { is_ref_target: false, .. })
        && match &t_target {
            TypedExpr::Ident(name, _, _) => {
                !scopes.lookup(name).is_some_and(|i| i.is_borrowed_self)
            }
            _ => false,
        };
    if can_move_target {
        mark_expr_moved_if_ident(scopes, errors, &t_target);
    } else if !is_ref_target {
        type_ctx.check_not_moved_from_projection(&t_target, errors);
    }
    let pre_match_moves = scopes.snapshot_moves();
    let mut non_diverging_moves = Vec::new();
    let target_from_caller = crate::sanal::compat::extract_root_var(&t_target).is_some_and(|root| {
        scopes.lookup(root).is_some_and(|i| i.from_caller)
            || scopes
                .borrow_target(root)
                .is_some_and(|bt| scopes.lookup(&bt).is_some_and(|i| i.from_caller))
    });
    let mut typed_arms = Vec::new();
    let mut non_diverging_arm: Option<(Type, Span)> = None;
    let mut all_diverging = !arms.is_empty();
    let mut has_wildcard = false;
    let mut covered_variants = std::collections::HashSet::new();
    let mut covered_bools = [false, false];

    for arm in arms {
        scopes.restore_moves(&pre_match_moves);
        scopes.push_scope();
        let mut typed_bindings: Vec<(String, Type)> = Vec::new();
        let mut alt_tags: Vec<i64> = Vec::new();
        let mut arm_is_wildcard = false;
        let is_unguarded = arm.guard.is_none();

        let all_pats = std::iter::once((&arm.variant_name, &arm.bindings))
            .chain(arm.alt_patterns.iter().map(|(v, b)| (v, b)));

        let mut primary_tag = -1i64;
        for (pat_idx, (pat_name, pat_bindings)) in all_pats.enumerate() {
            if pat_name == "_" {
                arm_is_wildcard = true;
                if is_unguarded {
                    has_wildcard = true;
                }
                if !pat_bindings.is_empty() {
                    errors.push(SemanticError {
                        code: "E0023",
                        message: "Wildcard pattern `_` does not accept bindings".into(),
                        label: "Unexpected bindings".into(),
                        secondary_label: None,
                        help: None,
                        span: arm.span.clone(),
                    });
                }
                continue;
            }

            if pat_name.starts_with("__lit_") {
                let lit_tag = parse_scalar_lit_tag(pat_name, &target_kind, errors, &arm.span)
                    .unwrap_or(0);
                if matches!(target_kind, MatchTargetKind::Bool) && is_unguarded {
                    if lit_tag == 0 {
                        covered_bools[0] = true;
                    } else {
                        covered_bools[1] = true;
                    }
                }
                if pat_idx == 0 {
                    primary_tag = lit_tag;
                } else {
                    alt_tags.push(lit_tag);
                }
                continue;
            }

            match &target_kind {
                MatchTargetKind::Enum { enum_name, variant_info, is_ref_target } => {
                    let short_v_name = pat_name.split("::").last().unwrap_or(pat_name);
                    if is_unguarded {
                        covered_variants.insert(short_v_name.to_string());
                    }
                    if let Some((_, v_map)) = variant_info {
                        if let Some((v_tag, p_types)) = v_map.get(short_v_name) {
                            let mut cur_bindings: Vec<(String, Type)> = Vec::new();
                            for (b_name, p_ty) in pat_bindings.iter().zip(p_types.iter()) {
                                let mut bound_ty = *p_ty;
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
                                                                bound_ty = if obj_name.contains("VecRefIter") {
                                                                    Type::Ref(crate::ast::intern_type(*first_t))
                                                                } else {
                                                                    *first_t
                                                                };
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                if pat_idx == 0 && b_name != "_" {
                                    if *is_ref_target && type_ctx.has_drop_ownership(&bound_ty) {
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
                                    scopes.declare_with_caller(
                                        b_name.clone(),
                                        false,
                                        bound_ty,
                                        target_from_caller,
                                    );
                                }
                                cur_bindings.push((b_name.clone(), bound_ty));
                            }
                            if pat_idx == 0 {
                                typed_bindings = cur_bindings;
                                primary_tag = *v_tag;
                            } else {
                                fn non_wild(bs: &[(String, Type)]) -> Vec<(usize, &str, Type)> {
                                    bs.iter()
                                        .enumerate()
                                        .filter(|(_, (n, _))| n != "_")
                                        .map(|(i, (n, t))| (i, n.as_str(), *t))
                                        .collect()
                                }
                                if non_wild(&cur_bindings) != non_wild(&typed_bindings) {
                                    errors.push(SemanticError {
                                        code: "E0408",
                                        message: format!(
                                            "Or-pattern alternative `{pat_name}` must bind the same variables and types as the primary pattern"
                                        ),
                                        label: "Mismatched bindings in `|` pattern".into(),
                                        secondary_label: None,
                                        help: Some("Ensure every `|` branch binds identical names with matching payload types".into()),
                                        span: arm.span.clone(),
                                    });
                                }
                                alt_tags.push(*v_tag);
                            }
                        } else {
                            errors.push(SemanticError {
                                code: "E0004",
                                message: format!("Unknown variant `{pat_name}` for enum `{enum_name}`"),
                                label: "Unknown variant".into(),
                                secondary_label: None,
                                help: None,
                                span: arm.span.clone(),
                            });
                        }
                    }
                }
                MatchTargetKind::Bool | MatchTargetKind::Int(_) => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Pattern `{pat_name}` cannot match non-enum type `{unwrapped_target_ty:?}`"
                        ),
                        label: "Expected literal pattern or `_`".into(),
                        secondary_label: None,
                        help: None,
                        span: arm.span.clone(),
                    });
                }
            }
        }
        let tag = primary_tag;

        let mut typed_guard: Option<Box<TypedExpr>> = None;
        if let Some(guard_expr) = &arm.guard {
            let mut guard_ctx = type_ctx.clone();
            guard_ctx.current_expected_type = None;
            if let Some(t_guard) = type_check_expr(scopes, errors, &guard_ctx, guard_expr) {
                let g_ty = type_ctx.infer.borrow_mut().resolve(t_guard.ty());
                if g_ty != Type::Bool && !matches!(g_ty, Type::Infer(_)) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!("Match guard must evaluate to `bool`, found `{g_ty:?}`"),
                        label: "Expected `bool`".into(),
                        secondary_label: None,
                        help: None,
                        span: guard_expr.span().clone(),
                    });
                }
                typed_guard = Some(Box::new(t_guard));
            }
        }

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
                Some(TypedExpr::Let(..))
                | Some(TypedExpr::LetTuple(..))
                | Some(TypedExpr::LetStruct(..))
                | None => Type::Unit,
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
            alt_tags,
            is_wildcard: arm_is_wildcard,
            bindings: typed_bindings,
            guard: typed_guard,
            body: typed_arm_stmts,
            span: arm.span.clone(),
        });
    }

    scopes.restore_moves(&pre_match_moves);
    for br in non_diverging_moves {
        scopes.merge_moves(&br);
    }

    if !has_wildcard {
        match &target_kind {
            MatchTargetKind::Enum { enum_name, variant_info, .. } => {
                if let Some((_, v_map)) = variant_info {
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
            MatchTargetKind::Bool => {
                let mut missing = Vec::new();
                if !covered_bools[0] {
                    missing.push("false");
                }
                if !covered_bools[1] {
                    missing.push("true");
                }
                if !missing.is_empty() {
                    errors.push(SemanticError {
                        code: "E0004",
                        message: format!(
                            "Non-exhaustive `match` on `bool`: missing {}",
                            missing.join(", ")
                        ),
                        label: format!("Missing pattern(s): {}", missing.join(", ")),
                        secondary_label: None,
                        help: Some("Cover both `true` and `false` or add `_ => ...`".into()),
                        span: span.clone(),
                    });
                }
            }
            MatchTargetKind::Int(ity) => {
                errors.push(SemanticError {
                    code: "E0004",
                    message: format!(
                        "Non-exhaustive `match` on integer type `{ity:?}`: missing catch-all `_ => ...` arm"
                    ),
                    label: "Integer `match` requires a catch-all `_` arm".into(),
                    secondary_label: None,
                    help: Some("Add an unguarded `_ => ...` arm".into()),
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

/// Type-checks `let Pat = expr else: <diverging block>` by lowering through `type_check_match`,
/// enforcing divergence on the `else` branch, and binding extracted payload variables into the
/// enclosing scope with their declared mutability.
pub fn type_check_let_else<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    variant_name: &str,
    bindings: &[(String, bool)],
    target: &Expr,
    else_body: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    let mut match_arm0_bindings = Vec::with_capacity(bindings.len());
    let mut bound_vars: Vec<(String, bool, String)> = Vec::new();
    for (idx, (b_name, is_mut)) in bindings.iter().enumerate() {
        if b_name == "_" {
            match_arm0_bindings.push("_".to_string());
        } else {
            let tmp = format!("__le_{}_{idx}", span.start);
            match_arm0_bindings.push(tmp.clone());
            bound_vars.push((b_name.clone(), *is_mut, tmp));
        }
    }

    let arm0_body = if bound_vars.is_empty() {
        vec![Expr::TupleInit(Vec::new(), span.clone())]
    } else if bound_vars.len() == 1 {
        vec![Expr::Ident(bound_vars[0].2.clone(), span.clone())]
    } else {
        vec![Expr::TupleInit(
            bound_vars
                .iter()
                .map(|(_, _, tmp)| Expr::Ident(tmp.clone(), span.clone()))
                .collect(),
            span.clone(),
        )]
    };

    let match_arms = vec![
        MatchArm::simple(
            variant_name.to_string(),
            match_arm0_bindings,
            arm0_body,
            span.clone(),
        ),
        MatchArm::simple(
            "_".to_string(),
            Vec::new(),
            else_body.to_vec(),
            span.clone(),
        ),
    ];

    let typed_match = type_check_match(scopes, errors, type_ctx, target, &match_arms, span)?;

    if let TypedExpr::Match(_, typed_arms, match_ty, _) = &typed_match {
        if let Some(else_arm) = typed_arms.get(1) {
            if !crate::sanal::compat::definitely_returns(&else_arm.body) {
                errors.push(SemanticError {
                    code: "E0308",
                    message: "`else` clause of `let ... else` must diverge".to_string(),
                    label: "Expected diverging control flow in `else` block".to_string(),
                    secondary_label: None,
                    help: Some(
                        "End the `else` block with `return`, `break`, `continue`, or `panic!(...)`"
                            .to_string(),
                    ),
                    span: else_arm.span.clone(),
                });
            }
        }

        if bound_vars.is_empty() {
            return Some(typed_match);
        } else if bound_vars.len() == 1 {
            let (user_name, is_mut, _) = &bound_vars[0];
            let val_ty = *match_ty;
            scopes.declare(user_name.clone(), *is_mut, val_ty);
            return Some(TypedExpr::Let(
                user_name.clone(),
                *is_mut,
                Box::new(typed_match),
                val_ty,
                span.clone(),
            ));
        } else {
            let pat = TuplePattern::Tuple(
                bound_vars
                    .iter()
                    .map(|(name, is_mut, _)| TuplePattern::Ident {
                        name: name.clone(),
                        is_mutable: *is_mut,
                        span: span.clone(),
                    })
                    .collect(),
                span.clone(),
            );
            let val_ty = *match_ty;
            let typed_pat =
                crate::sanal::vars::bind_tuple_pattern(scopes, errors, type_ctx, &pat, val_ty);
            return Some(TypedExpr::LetTuple(
                typed_pat,
                val_ty,
                Box::new(typed_match),
                span.clone(),
            ));
        }
    }

    Some(typed_match)
}

