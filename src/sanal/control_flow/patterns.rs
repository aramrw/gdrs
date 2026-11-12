//! sanal/control_flow/patterns.rs
//! Match expression and pattern matching type checking.

use crate::{
    ast::{Expr, MatchArm, Span, Type, TypedExpr, TypedMatchArm},
    sanal::{
        compat::{consume_tail_expr, is_type_compatible, mark_expr_moved_if_ident},
        control_flow::lifetimes::check_block_escape_lifetime,
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

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

