//! sanal/objects/fields.rs
//! Type checking for field access and field assignment expressions.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{is_type_compatible, mark_expr_moved_if_ident},
        objects::construction::{lookup_struct_layout_for_type, type_check_enum_construct},
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

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
        let is_slice_len = matches!(
            unwrapped_tuple,
            Type::Slice(_) | Type::Array(_, _) | Type::Vec(_)
        ) && field_name == "len";
        if !is_slice_len {
            if let Some(&f_vis) = layout.field_vis.get(field_name) {
                if !crate::ast::is_visible(f_vis, &layout.module_path, &type_ctx.current_module) {
                    errors.push(SemanticError {
                        code: "E0616",
                        message: format!("Field `{field_name}` of struct `{struct_name}` is private"),
                        label: "Private field".to_string(),
                        secondary_label: None,
                        help: Some(format!("Mark `{field_name}` with `pub` if it should be accessible outside its module")),
                        span: span.clone(),
                    });
                }
            }
        }
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

