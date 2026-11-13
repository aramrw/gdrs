//! sanal/vars.rs
//! Type checking for variable lookup, let bindings, and assignments.

use crate::{
    ast::{intern_str, Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{extract_root_var, is_type_compatible, mark_expr_moved_if_ident},
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_ident<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    name: &str,
    span: &Span,
) -> Option<TypedExpr> {
    if let Some(info) = scopes.lookup(name) {
        if info.is_moved {
            errors.push(SemanticError {
                code: "E0382",
                message: format!("Use of moved value '{name}'"),
                label: "Value used here after move".to_string(),
                secondary_label: None,
                help: Some("Value was moved in a previous assignment or function call".to_string()),
                span: span.clone(),
            });
        }
        if let Some((true, holder)) = scopes.active_borrow(name) {
            errors.push(SemanticError {
                code: "E0502",
                message: format!(
                    "Cannot use `{name}` because it is mutably borrowed by `{holder}`"
                ),
                label: format!("Use of `{name}` while mutably borrowed"),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        let info_ty = info.ty;
        let resolved_ty = type_ctx.infer.borrow_mut().resolve(info_ty);
        if resolved_ty != info_ty {
            if let Some(m_info) = scopes.lookup_mut(name) {
                m_info.ty = resolved_ty;
            }
        }
        Some(TypedExpr::Ident(name.to_string(), resolved_ty, span.clone()))
    } else if let Some((enum_part, variant_part)) = name.split_once("::") {
        let normalized_enum = match enum_part {
            "Opt" | "Option" => "std_core_Option",
            "Res" | "Result" => "std_core_Result",
            other => other,
        };
        if let Some(te) = super::objects::type_check_enum_construct(
            scopes,
            errors,
            type_ctx,
            normalized_enum,
            variant_part,
            &[],
            span,
        ) {
            if matches!(te, TypedExpr::EnumConstruct(..)) {
                return Some(te);
            }
        }
        let normalized = name.replace("::", "_");
        let found_struct = type_ctx.get_struct(&normalized);
        let found_enum = type_ctx.get_enum(&normalized);
        if let Some(layout) = found_struct {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Obj(intern_str(&layout.name)),
                span.clone(),
            ))
        } else if let Some((mangled_enum, _)) = found_enum {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Enum(mangled_enum),
                span.clone(),
            ))
        } else if name == "rc"
            || name == "arc"
            || type_ctx.fn_map.borrow().contains_key(name)
            || type_ctx.fn_map.borrow().contains_key(&normalized)
        {
            Some(TypedExpr::Ident(name.to_string(), Type::Int, span.clone()))
        } else {
            errors.push(SemanticError {
                code: "E0425",
                message: format!("Undefined variable '{name}'"),
                label: "Variable does not exist in this scope".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
            None
        }
    } else {
        if name == "None" {
            if let Some(te) = super::objects::type_check_enum_construct(
                scopes,
                errors,
                type_ctx,
                "std_core_Option",
                name,
                &[],
                span,
            ) {
                if matches!(te, TypedExpr::EnumConstruct(..)) {
                    return Some(te);
                }
            }
        }
        let normalized = name.replace("::", "_");
        if let Some((enum_part, variant_part)) = normalized.rsplit_once('_') {
            let norm_enum = match enum_part {
                "Opt" | "Option" => "std_core_Option",
                "Res" | "Result" => "std_core_Result",
                other => other,
            };
            let is_zero_arg_variant = type_ctx
                .get_enum(norm_enum)
                .and_then(|(_, v)| v.get(variant_part).map(|(_, pts)| pts.is_empty()))
                .unwrap_or_else(|| {
                    let mono = type_ctx.mono.borrow();
                    mono.enum_templates
                        .get(norm_enum)
                        .or_else(|| {
                            mono.enum_templates
                                .iter()
                                .find(|(k, _)| k.as_str() == norm_enum || k.ends_with(&format!("_{norm_enum}")))
                                .map(|(_, d)| d)
                        })
                        .and_then(|d| d.variants.iter().find(|v| v.name == variant_part))
                        .map(|v| v.payload_types.is_empty())
                        .unwrap_or(false)
                });
            if is_zero_arg_variant {
                if let Some(te) = super::objects::type_check_enum_construct(
                    scopes,
                    errors,
                    type_ctx,
                    norm_enum,
                    variant_part,
                    &[],
                    span,
                ) {
                    if matches!(te, TypedExpr::EnumConstruct(..)) {
                        return Some(te);
                    }
                }
            }
        }
        let found_struct = type_ctx.get_struct(&normalized).or_else(|| {
            let mono = type_ctx.mono.borrow();
            mono.struct_templates
                .get(&normalized)
                .or_else(|| {
                    mono.struct_templates
                        .iter()
                        .find(|(k, _)| k.as_str() == normalized || k.ends_with(&format!("_{normalized}")))
                        .map(|(_, v)| v)
                })
                .map(|decl| crate::sanal::StructLayout {
                    name: decl.name.clone(),
                    total_size: 0,
                    field_offsets: std::collections::HashMap::new(),
                    vis: decl.vis,
                    module_path: decl.module_path.clone(),
                    field_vis: decl
                        .fields
                        .iter()
                        .map(|f| (f.name.clone(), f.vis))
                        .collect(),
                })
        });
        let found_enum = type_ctx.get_enum(&normalized);
        if let Some(layout) = found_struct {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Obj(intern_str(&layout.name)),
                span.clone(),
            ))
        } else if let Some((mangled_enum, _)) = found_enum {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Enum(mangled_enum),
                span.clone(),
            ))
        } else if name == "rc"
            || name == "arc"
            || type_ctx.fn_map.borrow().contains_key(name)
            || type_ctx.fn_map.borrow().contains_key(&normalized)
        {
            Some(TypedExpr::Ident(name.to_string(), Type::Int, span.clone()))
        } else {
            errors.push(SemanticError {
                code: "E0425",
                message: format!("Undefined variable '{name}'"),
                label: "Variable does not exist in this scope".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
            None
        }
    }
}

/// Validates a reference assignment/binding (`name = expr`) and returns `(Option<(target_var, is_mut)>, from_caller)`.
fn resolve_ref_borrow_info(
    scopes: &ScopeStack,
    errors: &mut Vec<SemanticError>,
    holder_name: &str,
    dest_ty: &Type,
    typed_val: &TypedExpr,
    span: &Span,
    is_assign: bool,
) -> (Option<(String, bool)>, bool) {
    let temp_err = |errors: &mut Vec<SemanticError>, err_span: &Span| {
        let action = if is_assign { "assignment to" } else { "binding" };
        errors.push(SemanticError {
            code: "E0716",
            message: format!(
                "Temporary value dropped while borrowed in {action} `{holder_name}`"
            ),
            label: "Creates a dangling reference to a temporary".to_string(),
            secondary_label: None,
            help: Some("Bind the value to a `let` variable before borrowing it".to_string()),
            span: err_span.clone(),
        });
    };

    match typed_val {
        TypedExpr::Ref(inner, ref_is_mut, _, _) => {
            if let Some(target_var) = extract_root_var(inner) {
                let target_owned = target_var.to_string();
                let from_caller = scopes.lookup(&target_owned).is_some_and(|i| i.from_caller);
                (Some((target_owned, *ref_is_mut)), from_caller)
            } else {
                temp_err(errors, span);
                (None, false)
            }
        }
        TypedExpr::Call(fn_name, call_args, _, call_span)
            if crate::sanal::control_flow::lifetimes::is_borrowed_view_call(fn_name) =>
        {
            if let Some(root) =
                crate::sanal::control_flow::lifetimes::borrowed_view_root(fn_name, call_args)
            {
                let target_owned = match scopes.lookup(root).map(|i| i.ty) {
                    Some(Type::Ref(_) | Type::MutRef(_))
                        if !scopes.lookup(root).is_some_and(|i| i.from_caller) =>
                    {
                        scopes.borrow_target(root).unwrap_or_else(|| root.to_string())
                    }
                    _ => root.to_string(),
                };
                let from_caller = scopes.lookup(&target_owned).is_some_and(|i| i.from_caller);
                (Some((target_owned, false)), from_caller)
            } else {
                temp_err(errors, call_span);
                (None, false)
            }
        }
        TypedExpr::Ident(src_name, _, _)
            if matches!(dest_ty, Type::Ref(_) | Type::MutRef(_) | Type::Str)
                || matches!(dest_ty, Type::Obj(s) if s.contains("VecIter")) =>
        {
            let from_caller = scopes.lookup(src_name).is_some_and(|i| i.from_caller);
            let inherited = scopes
                .borrow_target(src_name)
                .map(|tgt| (tgt, matches!(dest_ty, Type::MutRef(_))));
            (inherited, from_caller)
        }
        _ => (None, false),
    }
}

/// Checks if assigning a compound expression (`IfElse` / `Match` / `Block`) could let an inner
/// borrow outlive the assignment target `holder_name`.
fn check_compound_assign_borrow_depths(
    scopes: &ScopeStack,
    errors: &mut Vec<SemanticError>,
    holder_name: &str,
    holder_depth: usize,
    expr: &TypedExpr,
    span: &Span,
) {
    let check_target = |errors: &mut Vec<SemanticError>, target: &str| {
        let from_caller = scopes.lookup(target).is_some_and(|i| i.from_caller);
        if !from_caller && scopes.scope_depth(target).is_some_and(|d| d > holder_depth) {
            errors.push(SemanticError {
                code: "E0597",
                message: format!(
                    "`{target}` does not live long enough for assignment to `{holder_name}`"
                ),
                label: "Borrowed value does not live long enough".to_string(),
                secondary_label: None,
                help: Some("Bind the value in an outer scope before borrowing it".to_string()),
                span: span.clone(),
            });
        }
    };

    match expr {
        TypedExpr::Ref(inner, _, _, _) => {
            if let Some(root) = extract_root_var(inner) {
                check_target(errors, root);
            }
        }
        TypedExpr::Call(fn_name, call_args, _, _)
            if crate::sanal::control_flow::lifetimes::is_borrowed_view_call(fn_name) =>
        {
            if let Some(root) =
                crate::sanal::control_flow::lifetimes::borrowed_view_root(fn_name, call_args)
            {
                check_target(errors, root);
            }
        }
        TypedExpr::Ident(src, ty, _)
            if matches!(ty, Type::Ref(_) | Type::MutRef(_) | Type::Str)
                || matches!(ty, Type::Obj(s) if s.contains("VecIter")) =>
        {
            if let Some(target) = scopes.borrow_target(src) {
                check_target(errors, &target);
            }
        }
        TypedExpr::IfElse(_, then_b, else_b, _, _) => {
            check_compound_assign_borrow_depths(scopes, errors, holder_name, holder_depth, then_b, span);
            check_compound_assign_borrow_depths(scopes, errors, holder_name, holder_depth, else_b, span);
        }
        TypedExpr::Match(_, arms, _, _) => {
            for arm in arms {
                if let Some(last) = arm.body.last() {
                    check_compound_assign_borrow_depths(
                        scopes,
                        errors,
                        holder_name,
                        holder_depth,
                        last,
                        span,
                    );
                }
            }
        }
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            if let Some(last) = stmts.last() {
                check_compound_assign_borrow_depths(
                    scopes,
                    errors,
                    holder_name,
                    holder_depth,
                    last,
                    span,
                );
            }
        }
        _ => {}
    }
}

pub fn type_check_let<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    name: &str,
    explicit_ty: Option<&Type>,
    is_mutable: bool,
    value: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let resolved_explicit = explicit_ty.map(|t| type_ctx.resolve_type_annotation(*t));
    let mut let_ctx = type_ctx.clone();
    if resolved_explicit.is_some() {
        let_ctx.current_expected_type = resolved_explicit;
    }
    let mut typed_val = type_check_expr(scopes, errors, &let_ctx, value)?;
    if let Some(Type::Vec(expected_elem)) = resolved_explicit {
        if let TypedExpr::ArrayInit(elems, Type::Array(elem_var, 0), arr_span) = typed_val {
            let _ = type_ctx.infer.borrow_mut().unify(*expected_elem, *elem_var);
            typed_val = TypedExpr::ArrayInit(elems, Type::Vec(expected_elem), arr_span);
        }
    } else if resolved_explicit.is_none() && is_mutable {
        if let TypedExpr::ArrayInit(elems, Type::Array(elem_ty, 0), arr_span) = typed_val {
            typed_val = TypedExpr::ArrayInit(elems, Type::Vec(elem_ty), arr_span);
        }
    }
    let inferred_ty = type_ctx.infer.borrow_mut().resolve(typed_val.ty());

    let final_ty = if let Some(ref annotated) = resolved_explicit {
        let unify_res = type_ctx.infer.borrow_mut().unify(*annotated, inferred_ty);
        let resolved_inferred = type_ctx.infer.borrow_mut().resolve(inferred_ty);
        let resolved_annotated = type_ctx.infer.borrow_mut().resolve(*annotated);
        if let Type::DynTrait(t_name) = resolved_annotated {
            if !matches!(resolved_inferred, Type::DynTrait(_)) {
                type_ctx.validate_dyn_coercion(&resolved_inferred, t_name, span, errors);
                typed_val = TypedExpr::CoerceToDyn(Box::new(typed_val), t_name, span.clone());
            }
        }
        if unify_res.is_err() && !is_type_compatible(&resolved_annotated, &resolved_inferred) {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot assign value of type `{resolved_inferred:?}` to variable '{name}' declared as `{resolved_annotated:?}`"
                ),
                label: "Type mismatch in let binding".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        resolved_annotated
    } else {
        inferred_ty
    };

    let (borrow_info, from_caller) = resolve_ref_borrow_info(
        scopes,
        errors,
        name,
        &final_ty,
        &typed_val,
        span,
        false,
    );
    if let Some((target_owned, ref_is_mut)) = borrow_info {
        scopes.add_borrow(name.to_string(), target_owned, ref_is_mut);
    }

    type_ctx.check_not_moved_from_projection(&typed_val, errors);
    mark_expr_moved_if_ident(scopes, errors, &typed_val);

    scopes.declare_with_caller(name.to_string(), is_mutable, final_ty.clone(), from_caller);

    Some(TypedExpr::Let(
        name.to_string(),
        is_mutable,
        Box::new(typed_val),
        final_ty,
        span.clone(),
    ))
}

fn bind_tuple_pattern(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'_>,
    pat: &crate::ast::TuplePattern,
    ty: Type,
) -> crate::ast::TypedTuplePattern {
    let resolved_ty = type_ctx.infer.borrow_mut().resolve(ty);
    match pat {
        crate::ast::TuplePattern::Ident {
            name,
            is_mutable,
            span,
        } => {
            if name != "_" {
                scopes.declare(name.clone(), *is_mutable, resolved_ty);
            }
            crate::ast::TypedTuplePattern::Ident {
                name: name.clone(),
                is_mutable: *is_mutable,
                ty: resolved_ty,
                span: span.clone(),
            }
        }
        crate::ast::TuplePattern::Tuple(subpats, span) => {
            let elem_tys: Vec<Type> = match resolved_ty {
                Type::Tuple(elems) => {
                    if elems.len() != subpats.len() {
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "Mismatched tuple destructuring arity: expected {} element(s), found {}",
                                subpats.len(),
                                elems.len()
                            ),
                            label: "Mismatched tuple length".to_string(),
                            secondary_label: None,
                            help: None,
                            span: span.clone(),
                        });
                    }
                    elems.to_vec()
                }
                Type::Unit if subpats.is_empty() => Vec::new(),
                Type::Infer(_) => {
                    let vars: Vec<Type> = subpats
                        .iter()
                        .enumerate()
                        .map(|(i, p)| {
                            let sp = match p {
                                crate::ast::TuplePattern::Ident { span, .. }
                                | crate::ast::TuplePattern::Tuple(_, span) => span.clone(),
                            };
                            type_ctx
                                .infer
                                .borrow_mut()
                                .fresh(sp, &format!("tuple pattern element {i}"))
                        })
                        .collect();
                    let tup = Type::Tuple(crate::ast::intern_tuple(&vars));
                    let _ = type_ctx.infer.borrow_mut().unify(resolved_ty, tup);
                    vars
                }
                other => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Mismatched types in tuple destructuring: expected a tuple, found `{other:?}`"
                        ),
                        label: "Expected tuple type".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                    vec![Type::Int; subpats.len()]
                }
            };

            let mut typed_subs = Vec::with_capacity(subpats.len());
            for (i, sub) in subpats.iter().enumerate() {
                let ety = elem_tys.get(i).copied().unwrap_or(Type::Int);
                typed_subs.push(bind_tuple_pattern(scopes, errors, type_ctx, sub, ety));
            }
            crate::ast::TypedTuplePattern::Tuple(typed_subs, resolved_ty, span.clone())
        }
    }
}

pub fn type_check_let_tuple<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    pat: &crate::ast::TuplePattern,
    explicit_ty: Option<&Type>,
    value: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let resolved_explicit = explicit_ty.map(|t| type_ctx.resolve_type_annotation(*t));
    let mut let_ctx = type_ctx.clone();
    if resolved_explicit.is_some() {
        let_ctx.current_expected_type = resolved_explicit;
    }
    let typed_val = type_check_expr(scopes, errors, &let_ctx, value)?;
    let inferred_ty = type_ctx.infer.borrow_mut().resolve(typed_val.ty());

    let final_ty = if let Some(annotated) = resolved_explicit {
        let unify_res = type_ctx.infer.borrow_mut().unify(annotated, inferred_ty);
        let resolved_inferred = type_ctx.infer.borrow_mut().resolve(inferred_ty);
        let resolved_annotated = type_ctx.infer.borrow_mut().resolve(annotated);
        if unify_res.is_err() && !is_type_compatible(&resolved_annotated, &resolved_inferred) {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot destructure value of type `{resolved_inferred:?}` as `{resolved_annotated:?}`"
                ),
                label: "Type mismatch in tuple let binding".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        resolved_annotated
    } else {
        inferred_ty
    };

    type_ctx.check_not_moved_from_projection(&typed_val, errors);
    mark_expr_moved_if_ident(scopes, errors, &typed_val);

    let typed_pat = bind_tuple_pattern(scopes, errors, type_ctx, pat, final_ty);

    Some(TypedExpr::LetTuple(
        typed_pat,
        final_ty,
        Box::new(typed_val),
        span.clone(),
    ))
}

pub fn type_check_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    name: &str,
    value: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let mut typed_val = type_check_expr(scopes, errors, type_ctx, value)?;

    type_ctx.check_not_moved_from_projection(&typed_val, errors);
    mark_expr_moved_if_ident(scopes, errors, &typed_val);

    let info_opt = scopes.lookup(name).map(|i| (i.is_mutable, i.ty));
    if let Some((is_mutable, mut var_ty)) = info_opt {
        if let Some((_, holder)) = scopes.active_borrow(name) {
            errors.push(SemanticError {
                code: "E0506",
                message: format!(
                    "Cannot assign to `{name}` because it is borrowed by `{holder}`"
                ),
                label: format!("Assignment to `{name}` occurs here while borrowed"),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        scopes.mark_active(name);
        if !is_mutable {
            errors.push(SemanticError {
                code: "E0382",
                message: format!("Cannot reassign immutable variable '{name}'"),
                label: format!("Variable '{name}' is immutable"),
                secondary_label: None,
                help: Some(format!(
                    "Consider declaring this variable as mutable: 'let mut {name}'"
                )),
                span: span.clone(),
            });
        }

        let val_ty = type_ctx.infer.borrow_mut().resolve(typed_val.ty());

        if let Type::Vec(elem_ty) = &val_ty {
            let _ = type_ctx.infer.borrow_mut().unify(var_ty, Type::Vec(*elem_ty));
            var_ty = type_ctx.infer.borrow_mut().resolve(var_ty);
        } else if let TypedExpr::Call(c_name, c_args, _, _) = &typed_val {
            if c_name.ends_with("push") && c_args.len() >= 2 {
                let pushed_ty = c_args[1].ty();
                let _ = type_ctx
                    .infer
                    .borrow_mut()
                    .unify(var_ty, Type::Vec(crate::ast::intern_type(pushed_ty)));
                var_ty = type_ctx.infer.borrow_mut().resolve(var_ty);
            }
        } else if let Type::Obj(s) = &val_ty {
            let clean = s.split('_').last().unwrap_or(s);
            if clean == "Vec" || clean.starts_with("Vec_") {
                if let Type::Vec(elem_ty) = var_ty {
                    var_ty = Type::Vec(elem_ty);
                }
            }
        }

        if let Type::DynTrait(t_name) = var_ty {
            if !matches!(val_ty, Type::DynTrait(_)) {
                type_ctx.validate_dyn_coercion(&val_ty, t_name, &typed_val.span(), errors);
                typed_val = TypedExpr::CoerceToDyn(Box::new(typed_val), t_name, span.clone());
            }
        }
        let unify_res = type_ctx.infer.borrow_mut().unify(var_ty, val_ty);
        let resolved_var = type_ctx.infer.borrow_mut().resolve(var_ty);
        let resolved_val = type_ctx.infer.borrow_mut().resolve(val_ty);

        if unify_res.is_err() && !is_type_compatible(&resolved_var, &resolved_val) {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot assign type `{:?}` to variable '{name}' of type `{:?}`",
                    resolved_val, resolved_var
                ),
                label: "Type mismatch".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }

        let (borrow_info, from_caller) =
            resolve_ref_borrow_info(scopes, errors, name, &var_ty, &typed_val, span, true);
        if let Some(holder_depth) = scopes.scope_depth(name) {
            if let Some((ref target_owned, _)) = borrow_info {
                if !from_caller
                    && scopes
                        .scope_depth(target_owned)
                        .is_some_and(|target_depth| target_depth > holder_depth)
                {
                    errors.push(SemanticError {
                        code: "E0597",
                        message: format!(
                            "`{target_owned}` does not live long enough for assignment to `{name}`"
                        ),
                        label: "Borrowed value does not live long enough".to_string(),
                        secondary_label: None,
                        help: Some("Bind the value in an outer scope before borrowing it".to_string()),
                        span: span.clone(),
                    });
                }
            } else {
                check_compound_assign_borrow_depths(
                    scopes,
                    errors,
                    name,
                    holder_depth,
                    &typed_val,
                    span,
                );
            }
        }
        scopes.remove_borrow(name);
        if let Some((target_owned, ref_is_mut)) = borrow_info {
            scopes.add_borrow(name.to_string(), target_owned, ref_is_mut);
        }
        if let Some(info) = scopes.lookup_mut(name) {
            info.from_caller = from_caller;
        }
    } else {
        errors.push(SemanticError {
            code: "E0425",
            message: format!("Cannot assign to undefined variable '{name}'"),
            label: format!("Variable '{name}' does not exist in this scope"),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
    }

    Some(TypedExpr::Assign(
        name.to_string(),
        Box::new(typed_val),
        span.clone(),
    ))
}
