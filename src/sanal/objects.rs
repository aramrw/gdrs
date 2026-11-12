//! sanal/objects.rs
//! Type checking for structs, field access/assignment, enum construction, arrays, and indexing.

use crate::{
    ast::{intern_str, Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{is_type_compatible, mark_expr_moved_if_ident},
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError, StructLayout,
    },
};

fn lookup_struct_layout_for_type<'a>(
    type_ctx: &TypeCtx<'a>,
    target_ty: Type,
) -> Option<(String, StructLayout)> {
    let struct_name = match target_ty {
        Type::Obj(s) => Some(s),
        Type::Vec(_) => Some(crate::ast::intern_str("std_vec_Vec")),
        Type::String => Some(crate::ast::intern_str("std_string_String")),
        Type::Ref(inner) | Type::MutRef(inner) => match *inner {
            Type::Obj(s) => Some(s),
            Type::Vec(_) => Some(crate::ast::intern_str("std_vec_Vec")),
            Type::String => Some(crate::ast::intern_str("std_string_String")),
            _ => None,
        },
        _ => None,
    }?;

    let layout = type_ctx.get_struct(struct_name).or_else(|| {
        let mono = type_ctx.mono.borrow();
        mono.struct_templates
            .get(struct_name)
            .or_else(|| {
                mono.struct_templates
                    .iter()
                    .find(|(k, _)| k.as_str() == struct_name || k.ends_with(&format!("_{struct_name}")))
                    .map(|(_, v)| v)
            })
            .map(|decl| {
                let mut field_offsets = std::collections::HashMap::new();
                for f in &decl.fields {
                    field_offsets.insert(f.name.clone(), (0, f.ty));
                }
                StructLayout {
                    name: decl.name.clone(),
                    total_size: 0,
                    field_offsets,
                }
            })
    })?;

    Some((struct_name.to_string(), layout))
}

pub fn type_check_array_init<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    elems: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    let mut typed_elems = Vec::new();
    for e in elems {
        if let Some(te) = type_check_expr(scopes, errors, type_ctx, e) {
            type_ctx.check_not_moved_from_projection(&te, errors);
            mark_expr_moved_if_ident(scopes, errors, &te);
            typed_elems.push(te);
        }
    }

    let elem_ty = if !typed_elems.is_empty() {
        typed_elems[0].ty()
    } else {
        type_ctx
            .infer
            .borrow_mut()
            .fresh(span.clone(), "element type of array")
    };

    for (i, elem) in typed_elems.iter().enumerate().skip(1) {
        let unify_res = type_ctx.infer.borrow_mut().unify(elem_ty, elem.ty());
        if unify_res.is_err() && !is_type_compatible(&elem_ty, &elem.ty()) {
            let resolved_expected = type_ctx.infer.borrow_mut().resolve(elem_ty);
            let resolved_found = type_ctx.infer.borrow_mut().resolve(elem.ty());
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Array elements must all have the same type. Expected `{:?}`, element {} has type `{:?}`",
                    resolved_expected,
                    i + 1,
                    resolved_found
                ),
                label: format!("Expected `{:?}`", resolved_expected),
                secondary_label: None,
                help: Some("Arrays are homogeneous and cannot hold mixed types".into()),
                span: elem.span().clone(),
            });
        }
    }

    let resolved_elem = type_ctx.infer.borrow_mut().resolve(elem_ty);
    let arr_ty = Type::Array(crate::ast::intern_type(resolved_elem), typed_elems.len());
    Some(TypedExpr::ArrayInit(typed_elems, arr_ty, span.clone()))
}

pub fn type_check_tuple_init<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    elems: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    if elems.is_empty() {
        return Some(TypedExpr::TupleInit(Vec::new(), Type::Unit, span.clone()));
    }

    let expected_elems = type_ctx.current_expected_type.and_then(|exp| {
        let resolved = type_ctx.infer.borrow_mut().probe(exp);
        if let Type::Tuple(tys) = resolved {
            Some(tys.to_vec())
        } else {
            None
        }
    });

    let mut typed_elems = Vec::with_capacity(elems.len());
    let mut elem_tys = Vec::with_capacity(elems.len());
    for (i, e) in elems.iter().enumerate() {
        let mut elem_ctx = type_ctx.clone();
        elem_ctx.current_expected_type = expected_elems.as_ref().and_then(|v| v.get(i).copied());
        if let Some(te) = type_check_expr(scopes, errors, &elem_ctx, e) {
            type_ctx.check_not_moved_from_projection(&te, errors);
            mark_expr_moved_if_ident(scopes, errors, &te);
            let resolved_ty = type_ctx.infer.borrow_mut().resolve(te.ty());
            elem_tys.push(resolved_ty);
            typed_elems.push(te);
        }
    }
    let tuple_ty = Type::Tuple(crate::ast::intern_tuple(&elem_tys));
    Some(TypedExpr::TupleInit(typed_elems, tuple_ty, span.clone()))
}

pub fn type_check_index_access<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    idx: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;

    let resolved_idx_ty = type_ctx.infer.borrow_mut().probe(t_idx.ty());
    if matches!(resolved_idx_ty, Type::Infer(_)) {
        let _ = type_ctx.infer.borrow_mut().unify(Type::Int, resolved_idx_ty);
    } else if !matches!(resolved_idx_ty, Type::Int | Type::I32) {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Array index must be an `Int`, found `{:?}`", resolved_idx_ty),
            label: "Invalid index type".into(),
            secondary_label: None,
            help: None,
            span: t_idx.span().clone(),
        });
    }

    let resolved_target = type_ctx.infer.borrow_mut().resolve(t_target.ty());
    let target_ty = match resolved_target {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };

    let elem_ty = match target_ty {
        Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => *e_ty,
        Type::Obj(s) => {
            if let Some((_, t_args)) = crate::sanal::mono::lookup_mangled(s) {
                t_args.first().copied().unwrap_or(Type::Int)
            } else {
                Type::Int
            }
        }
        other_ty => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Cannot index into non-array type `{:?}`", other_ty),
                label: "Not an array".into(),
                secondary_label: None,
                help: None,
                span: t_target.span().clone(),
            });
            Type::Int
        }
    };

    Some(TypedExpr::IndexAccess(
        Box::new(t_target),
        Box::new(t_idx),
        elem_ty,
        span.clone(),
    ))
}

pub fn type_check_index_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    idx: &Expr,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;
    type_ctx.check_not_moved_from_projection(&t_val, errors);
    mark_expr_moved_if_ident(scopes, errors, &t_val);

    let mut curr = target;
    while let Expr::FieldAccess(inner, _, _) | Expr::IndexAccess(inner, _, _) | Expr::Deref(inner, _) = curr {
        curr = inner.as_ref();
    }
    if let Expr::Ident(var_name, _) = curr {
        if let Some((_, holder)) = scopes.active_borrow(var_name) {
            errors.push(SemanticError {
                code: "E0506",
                message: format!(
                    "Cannot assign to element of `{var_name}` because `{var_name}` is borrowed by `{holder}`"
                ),
                label: "Indexed assignment while borrowed".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        if let Some(info) = scopes.lookup(var_name) {
            if matches!(info.ty, Type::Ref(_)) {
                errors.push(SemanticError {
                    code: "E0594",
                    message: format!("Cannot mutate element through immutable reference '{var_name}'"),
                    label: "Reference is immutable".to_string(),
                    secondary_label: None,
                    help: Some("Use `&mut` or an owned mutable binding `let mut`".to_string()),
                    span: span.clone(),
                });
            } else if !info.is_mutable && !matches!(info.ty, Type::MutRef(_) | Type::Ptr(_)) {
                errors.push(SemanticError {
                    code: "E0596",
                    message: format!("Cannot assign to element of immutable variable '{var_name}'"),
                    label: "Variable is immutable".to_string(),
                    secondary_label: None,
                    help: Some(format!("Declare as mutable: `let mut {var_name}`")),
                    span: span.clone(),
                });
            }
        }
    }

    let resolved_idx_ty = type_ctx.infer.borrow_mut().probe(t_idx.ty());
    if matches!(resolved_idx_ty, Type::Infer(_)) {
        let _ = type_ctx.infer.borrow_mut().unify(Type::Int, resolved_idx_ty);
    } else if !matches!(resolved_idx_ty, Type::Int | Type::I32) {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Array index must be an `Int`, found `{:?}`", resolved_idx_ty),
            label: "Invalid index type".into(),
            secondary_label: None,
            help: None,
            span: t_idx.span().clone(),
        });
    }

    let resolved_target = type_ctx.infer.borrow_mut().resolve(t_target.ty());
    let clean_target_ty = match resolved_target {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };
    let opt_elem_ty = match clean_target_ty {
        Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => Some(*e_ty),
        Type::Obj(s) => crate::sanal::mono::lookup_mangled(s)
            .and_then(|(_, t_args)| t_args.first().copied()),
        _ => None,
    };
    if let Some(elem_ty) = opt_elem_ty {
        let unify_res = type_ctx.infer.borrow_mut().unify(elem_ty, t_val.ty());
        let resolved_elem = type_ctx.infer.borrow_mut().resolve(elem_ty);
        let resolved_val = type_ctx.infer.borrow_mut().resolve(t_val.ty());
        if unify_res.is_err() && !is_type_compatible(&resolved_elem, &resolved_val) {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot assign type `{:?}` to array holding `{:?}`",
                    resolved_val,
                    resolved_elem
                ),
                label: "Type mismatch".into(),
                secondary_label: None,
                help: None,
                span: t_val.span().clone(),
            });
        }
    }

    Some(TypedExpr::IndexAssign(
        Box::new(t_target),
        Box::new(t_idx),
        Box::new(t_val),
        span.clone(),
    ))
}

pub fn type_check_obj_init<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    raw_name: &str,
    fields: &[(String, Expr)],
    span: &Span,
) -> Option<TypedExpr> {
    let name = &raw_name.replace("::", "_");
    let mut typed_fields = Vec::new();
    for (f_name, f_expr) in fields {
        let t_expr = type_check_expr(scopes, errors, type_ctx, f_expr)?;
        type_ctx.check_not_moved_from_projection(&t_expr, errors);
        mark_expr_moved_if_ident(scopes, errors, &t_expr);
        typed_fields.push((f_name.clone(), t_expr));
    }

    let mut found_struct = type_ctx.get_struct(name);

    if found_struct.is_none() {
        let opt_template = {
            let mono = type_ctx.mono.borrow();
            crate::sanal::mono::find_struct_template(&mono, name)
        };

        if let Some(decl) = opt_template {
            let generic_params =
                crate::sanal::mono::extract_generic_params_struct(&decl, type_ctx.mono);
            let (param_env, param_tys) = {
                let mut infer = type_ctx.infer.borrow_mut();
                infer.instantiate_params(&generic_params, span, &decl.name)
            };

            let infer_mangled = crate::sanal::mono::mangle_name(&decl.name, &param_tys);
            let self_infer_ty = Type::Obj(intern_str(&infer_mangled));
            if let Some(exp_ty) = type_ctx.current_expected_type {
                let _ = type_ctx.infer.borrow_mut().unify(exp_ty, self_infer_ty);
            }

            for (f_name, f_expr) in &typed_fields {
                if let Some(f_decl) = decl.fields.iter().find(|f| f.name == *f_name) {
                    let expected_field_ty =
                        crate::sanal::mono::substitute_type(f_decl.ty, &param_env);
                    let _ = type_ctx
                        .infer
                        .borrow_mut()
                        .unify(expected_field_ty, f_expr.ty());
                }
            }

            let resolved_params: Vec<Type> = {
                let mut infer = type_ctx.infer.borrow_mut();
                param_tys.into_iter().map(|t| infer.resolve(t)).collect()
            };

            let has_unresolved = resolved_params.iter().any(|t| {
                crate::sanal::compat::type_contains_infer(t)
                    || crate::sanal::compat::type_contains_generic(t)
            });

            if !has_unresolved {
                if let Some(mangled) = crate::sanal::mono::monomorphize_struct(
                    type_ctx.mono,
                    &decl.name,
                    &resolved_params,
                    type_ctx.struct_map,
                    type_ctx.enum_map,
                    type_ctx.fn_map,
                    type_ctx.worklist,
                ) {
                    found_struct = type_ctx.get_struct(&mangled);
                }
            } else {
                let partial_mangled = crate::sanal::mono::mangle_name(&decl.name, &resolved_params);
                found_struct = type_ctx.get_struct(&partial_mangled);
            }
        }
    }

    let obj_ty_name = if let Some(layout) = found_struct {
        for (expected_field, (_, expected_ty)) in &layout.field_offsets {
            if !typed_fields.iter().any(|(f, _)| f == expected_field) {
                errors.push(SemanticError {
                    code: "E0063",
                    message: format!(
                        "Missing field '{expected_field}' in struct initialization of '{name}'"
                    ),
                    label: format!("Field '{expected_field}: {expected_ty:?}' is missing"),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
        }

        for (f_name, f_expr) in &typed_fields {
            if let Some((_, expected_ty)) = layout.field_offsets.get(f_name) {
                let unify_res = type_ctx
                    .infer
                    .borrow_mut()
                    .unify(*expected_ty, f_expr.ty());
                let resolved_expected = type_ctx.infer.borrow_mut().resolve(*expected_ty);
                let resolved_found = type_ctx.infer.borrow_mut().resolve(f_expr.ty());
                if unify_res.is_err() && !is_type_compatible(&resolved_expected, &resolved_found) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Field '{f_name}' in struct '{name}' expects type `{:?}`, found `{:?}`",
                            resolved_expected,
                            resolved_found
                        ),
                        label: format!("Expected `{:?}`", resolved_expected),
                        secondary_label: None,
                        help: None,
                        span: f_expr.span().clone(),
                    });
                }
            } else {
                errors.push(SemanticError {
                    code: "E0599",
                    message: format!("Struct '{name}' has no field named '{f_name}'"),
                    label: "Unknown field".into(),
                    secondary_label: None,
                    help: None,
                    span: f_expr.span().clone(),
                });
            }
        }
        layout.name
    } else {
        errors.push(SemanticError {
            code: "E0425",
            message: format!("Undefined struct '{name}'"),
            label: "Struct does not exist".into(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
        name.to_string()
    };

    let obj_ty = type_ctx
        .infer
        .borrow_mut()
        .resolve(Type::Obj(intern_str(&obj_ty_name)));
    let final_obj_name = match obj_ty {
        Type::Obj(s) => s.to_string(),
        _ => obj_ty_name,
    };
    Some(TypedExpr::ObjInit(
        final_obj_name,
        typed_fields,
        obj_ty,
        span.clone(),
    ))
}

pub fn type_check_field_access<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    field_name: &str,
    span: &Span,
) -> Option<TypedExpr> {
    if let Expr::Ident(ref enum_name, _) = *target {
        if let Some((static_enum_name, variants)) = type_ctx.get_enum(enum_name) {
            if let Some((disc, _)) = variants.get(field_name) {
                return Some(TypedExpr::EnumConstruct(
                    enum_name.clone(),
                    field_name.to_string(),
                    *disc as usize,
                    vec![],
                    Type::Enum(static_enum_name),
                    span.clone(),
                ));
            }
        } else {
            let is_template_enum = {
                let mono = type_ctx.mono.borrow();
                crate::sanal::mono::find_enum_template(&mono, enum_name).is_some()
            };
            if is_template_enum {
                if let Some(te) = type_check_enum_construct(
                    scopes, errors, type_ctx, enum_name, field_name, &[], span,
                ) {
                    return Some(te);
                }
            }
        }
    }

    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let mut field_ty = Type::Int;

    let target_ty = type_ctx.infer.borrow_mut().resolve(t_target.ty());
    let unwrapped_tuple = match target_ty {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };
    if let Type::Tuple(elems) = unwrapped_tuple {
        if let Ok(idx) = field_name.parse::<usize>() {
            if let Some(&elem_ty) = elems.get(idx) {
                field_ty = elem_ty;
            } else {
                errors.push(SemanticError {
                    code: "E0609",
                    message: format!("No field `{field_name}` on tuple type `{target_ty:?}`"),
                    label: "Tuple index out of bounds".to_string(),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
        } else {
            errors.push(SemanticError {
                code: "E0609",
                message: format!("No field `{field_name}` on tuple type `{target_ty:?}`"),
                label: "Unknown tuple field".to_string(),
                secondary_label: None,
                help: Some("Tuples are indexed numerically, e.g. `t.0` or `t.1`".to_string()),
                span: span.clone(),
            });
        }
    } else if let Some((struct_name, layout)) = lookup_struct_layout_for_type(type_ctx, target_ty) {
        if let Some((_, fty)) = layout.field_offsets.get(field_name) {
            field_ty = match fty {
                Type::Generic(g) => {
                    if let Some((base_name, t_args)) = crate::sanal::mono::lookup_mangled(&struct_name) {
                        let mono = type_ctx.mono.borrow();
                        if let Some(decl) = mono.struct_templates.get(&base_name) {
                            let gp = crate::sanal::mono::extract_generic_params_struct(decl, type_ctx.mono);
                            gp.iter()
                                .position(|p| p == g.trim_start_matches('$'))
                                .and_then(|idx| t_args.get(idx).copied())
                                .unwrap_or(Type::Int)
                        } else {
                            Type::Int
                        }
                    } else {
                        Type::Int
                    }
                }
                other => *other,
            };
        } else {
            errors.push(SemanticError {
                code: "E0599",
                message: format!("Struct '{struct_name}' has no field '{field_name}'"),
                label: "Field not found".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
    } else if field_name == "len" {
        let clean_ty = match t_target.ty() {
            Type::Ref(inner) | Type::MutRef(inner) => *inner,
            other => other,
        };
        if matches!(clean_ty, Type::Vec(_) | Type::Slice(_) | Type::Array(_, _) | Type::String) || match &clean_ty { Type::Obj(s) => s.contains("Vec"), _ => false } {
            return crate::sanal::calls::type_check_call(scopes, errors, type_ctx, "len", &[target.clone()], span);
        }
        errors.push(SemanticError {
            code: "E0599",
            message: format!("Cannot access field on non-object type {:?}", t_target.ty()),
            label: "Not a struct object".to_string(),
            secondary_label: None,
            help: Some("Did you mean to call a method like `.len()` with parentheses?".to_string()),
            span: span.clone(),
        });
    } else {
        errors.push(SemanticError {
            code: "E0599",
            message: format!("Cannot access field on non-object type {:?}", t_target.ty()),
            label: "Not a struct object".to_string(),
            secondary_label: None,
            help: Some("Did you mean to call a method like `.len()` with parentheses?".to_string()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::FieldAccess(
        Box::new(t_target),
        field_name.to_string(),
        field_ty,
        span.clone(),
    ))
}

pub fn type_check_field_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    field_name: &str,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;
    type_ctx.check_not_moved_from_projection(&t_val, errors);
    mark_expr_moved_if_ident(scopes, errors, &t_val);

    let mut curr = target;
    while let Expr::FieldAccess(inner, _, _)
    | Expr::IndexAccess(inner, _, _)
    | Expr::Deref(inner, _) = curr
    {
        curr = inner.as_ref();
    }
    if let Expr::Ident(var_name, _) = curr {
        if let Some((_, holder)) = scopes.active_borrow(var_name) {
            errors.push(SemanticError {
                code: "E0506",
                message: format!(
                    "Cannot assign to `{var_name}.{field_name}` because `{var_name}` is borrowed by `{holder}`"
                ),
                label: "Field assignment while borrowed".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        if let Some(info) = scopes.lookup(var_name) {
            if matches!(info.ty, Type::Ref(_)) {
                errors.push(SemanticError {
                    code: "E0594",
                    message: format!("Cannot mutate field through immutable reference '{var_name}'"),
                    label: "Reference is immutable".to_string(),
                    secondary_label: None,
                    help: Some("Use `&mut` or an owned mutable binding `let mut`".to_string()),
                    span: span.clone(),
                });
            } else {
                let is_mut_ref = matches!(info.ty, Type::MutRef(_) | Type::Ptr(_));
                if !info.is_mutable && !is_mut_ref {
                    errors.push(SemanticError {
                        code: "E0382",
                        message: format!("Cannot mutate field of immutable object '{var_name}'"),
                        label: "Object is immutable".to_string(),
                        secondary_label: None,
                        help: Some(format!("Declare as mutable: 'let mut {var_name}'")),
                        span: span.clone(),
                    });
                }
            }
        }
    }

    let resolved_target_ty = type_ctx.infer.borrow_mut().resolve(t_target.ty());
    let unwrapped_tuple_assign = match resolved_target_ty {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };
    if let Type::Tuple(elems) = unwrapped_tuple_assign {
        if let Ok(idx) = field_name.parse::<usize>() {
            if let Some(&expected_ty) = elems.get(idx) {
                let unify_res = type_ctx.infer.borrow_mut().unify(expected_ty, t_val.ty());
                let resolved_expected = type_ctx.infer.borrow_mut().resolve(expected_ty);
                let resolved_found = type_ctx.infer.borrow_mut().resolve(t_val.ty());
                if unify_res.is_err() && !is_type_compatible(&resolved_expected, &resolved_found) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Mismatched type assigning to tuple field `.{idx}`: expected `{:?}`, found `{:?}`",
                            resolved_expected, resolved_found
                        ),
                        label: format!("Expected `{:?}`", resolved_expected),
                        secondary_label: None,
                        help: None,
                        span: t_val.span(),
                    });
                }
            } else {
                errors.push(SemanticError {
                    code: "E0609",
                    message: format!("No field `{field_name}` on tuple type `{resolved_target_ty:?}`"),
                    label: "Tuple index out of bounds".to_string(),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
        } else {
            errors.push(SemanticError {
                code: "E0609",
                message: format!("No field `{field_name}` on tuple type `{resolved_target_ty:?}`"),
                label: "Unknown tuple field".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
    } else if let Some((struct_name, layout)) = lookup_struct_layout_for_type(type_ctx, resolved_target_ty) {
        if let Some((_, expected_ty)) = layout.field_offsets.get(field_name) {
            let unify_res = type_ctx.infer.borrow_mut().unify(*expected_ty, t_val.ty());
            let resolved_expected = type_ctx.infer.borrow_mut().resolve(*expected_ty);
            let resolved_found = type_ctx.infer.borrow_mut().resolve(t_val.ty());
            if unify_res.is_err() && !is_type_compatible(&resolved_expected, &resolved_found) {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched type assigning to field `{struct_name}.{field_name}`: expected `{:?}`, found `{:?}`",
                        resolved_expected,
                        resolved_found
                    ),
                    label: format!("Expected `{:?}`", resolved_expected),
                    secondary_label: None,
                    help: None,
                    span: t_val.span(),
                });
            }
        } else {
            errors.push(SemanticError {
                code: "E0599",
                message: format!("Struct '{struct_name}' has no field '{field_name}'"),
                label: "Field not found".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
    }

    Some(TypedExpr::FieldAssign(
        Box::new(t_target),
        field_name.to_string(),
        Box::new(t_val),
        span.clone(),
    ))
}

pub fn type_check_enum_construct<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    enum_name: &str,
    variant_name: &str,
    args: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    let mut typed_args = Vec::new();
    for a in args {
        if let Some(ta) = type_check_expr(scopes, errors, type_ctx, a) {
            type_ctx.check_not_moved_from_projection(&ta, errors);
            mark_expr_moved_if_ident(scopes, errors, &ta);
            typed_args.push(ta);
        }
    }

    let mut found_enum = type_ctx.get_enum(enum_name);

    if found_enum.is_none() {
        let template_name = if enum_name.starts_with("std_core_Option") || enum_name.starts_with("Opt") || enum_name.starts_with("Option") {
            "std_core_Option"
        } else if enum_name.starts_with("std_core_Result") || enum_name.starts_with("Res") || enum_name.starts_with("Result") {
            "std_core_Result"
        } else {
            enum_name.split('_').next().unwrap_or(enum_name)
        };

        let opt_template = {
            let mono = type_ctx.mono.borrow();
            mono.enum_templates
                .get(template_name)
                .or_else(|| mono.enum_templates.get(enum_name))
                .or_else(|| {
                    mono.enum_templates
                        .iter()
                        .find(|(k, _)| k.as_str() == enum_name || k.ends_with(&format!("_{enum_name}")))
                        .map(|(_, v)| v)
                })
                .cloned()
        };

        if let Some(decl) = opt_template {
            let generic_params = crate::sanal::mono::extract_generic_params_enum(&decl);
            let (param_env, param_tys) = {
                let mut infer = type_ctx.infer.borrow_mut();
                infer.instantiate_params(&generic_params, span, &decl.name)
            };

            let infer_mangled = crate::sanal::mono::mangle_name(&decl.name, &param_tys);
            let self_infer_ty = Type::Enum(intern_str(&infer_mangled));
            if let Some(exp_ty) = type_ctx.current_expected_type {
                let _ = type_ctx.infer.borrow_mut().unify(exp_ty, self_infer_ty);
            }

            if let Some(v_decl) = decl.variants.iter().find(|v| v.name == variant_name) {
                for (pt, ta) in v_decl.payload_types.iter().zip(typed_args.iter()) {
                    let expected_pt = crate::sanal::mono::substitute_type(*pt, &param_env);
                    let _ = type_ctx.infer.borrow_mut().unify(expected_pt, ta.ty());
                }
            }

            let resolved_params: Vec<Type> = {
                let mut infer = type_ctx.infer.borrow_mut();
                param_tys.into_iter().map(|t| infer.resolve(t)).collect()
            };

            // Preserve 1-arg `Result<T>` shorthand when `expected_type` explicitly has 1 arg.
            let mono_params: Vec<Type> = if decl.name.ends_with("Result")
                && resolved_params.len() == 2
                && crate::sanal::compat::type_contains_infer(&resolved_params[1])
                && type_ctx
                    .current_expected_type
                    .and_then(|t| match t {
                        Type::Enum(n) | Type::Obj(n) => crate::sanal::mono::lookup_mangled(n),
                        _ => None,
                    })
                    .is_some_and(|(b, args)| b.ends_with("Result") && args.len() == 1)
            {
                vec![resolved_params[0]]
            } else {
                resolved_params
            };

            let has_unresolved = mono_params.iter().any(|t| {
                crate::sanal::compat::type_contains_infer(t)
                    || crate::sanal::compat::type_contains_generic(t)
            });

            if !has_unresolved {
                if let Some(mangled) = crate::sanal::mono::monomorphize_enum(
                    type_ctx.mono,
                    &decl.name,
                    &mono_params,
                    type_ctx.enum_map,
                    type_ctx.fn_map,
                    type_ctx.worklist,
                ) {
                    found_enum = type_ctx.get_enum(&mangled);
                }
            } else {
                let partial_mangled = crate::sanal::mono::mangle_name(&decl.name, &mono_params);
                found_enum = type_ctx.get_enum(&partial_mangled);
            }
        }
    }

    if let Some((static_name, variants)) = found_enum {
        if let Some((d, payload_tys)) = variants.get(variant_name) {
            if typed_args.len() != payload_tys.len() {
                errors.push(SemanticError {
                    code: "E0061",
                    message: format!(
                        "Enum variant `{static_name}::{variant_name}` expects {} argument(s), found {}",
                        payload_tys.len(),
                        typed_args.len()
                    ),
                    label: format!("Expected {} argument(s)", payload_tys.len()),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            } else {
                for (arg, expected_ty) in typed_args.iter().zip(payload_tys.iter()) {
                    let unify_res = type_ctx
                        .infer
                        .borrow_mut()
                        .unify(*expected_ty, arg.ty());
                    let resolved_expected = type_ctx.infer.borrow_mut().resolve(*expected_ty);
                    let resolved_found = type_ctx.infer.borrow_mut().resolve(arg.ty());
                    if unify_res.is_err() && !is_type_compatible(&resolved_expected, &resolved_found) {
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "Enum variant `{static_name}::{variant_name}` expects `{:?}`, found `{:?}`",
                                resolved_expected,
                                resolved_found
                            ),
                            label: format!("Expected `{:?}`", resolved_expected),
                            secondary_label: None,
                            help: None,
                            span: arg.span(),
                        });
                    }
                }
            }
            let resolved_enum_ty = type_ctx
                .infer
                .borrow_mut()
                .resolve(Type::Enum(static_name));
            let final_enum_name = match resolved_enum_ty {
                Type::Enum(s) => s.to_string(),
                _ => static_name.to_string(),
            };
            return Some(TypedExpr::EnumConstruct(
                final_enum_name,
                variant_name.to_string(),
                *d as usize,
                typed_args,
                resolved_enum_ty,
                span.clone(),
            ));
        }
    }

    None
}
