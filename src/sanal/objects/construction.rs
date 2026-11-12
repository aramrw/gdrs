//! sanal/objects/construction.rs
//! Struct layout lookup, struct instantiation, and enum variant construction.

use crate::{
    ast::{intern_str, Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{is_type_compatible, mark_expr_moved_if_ident},
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError, StructLayout,
    },
};

pub(crate) fn lookup_struct_layout_for_type<'a>(
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
                let mut field_vis = std::collections::HashMap::new();
                for f in &decl.fields {
                    field_offsets.insert(f.name.clone(), (0, f.ty));
                    field_vis.insert(f.name.clone(), f.vis);
                }
                StructLayout {
                    name: decl.name.clone(),
                    total_size: 0,
                    field_offsets,
                    vis: decl.vis,
                    module_path: decl.module_path.clone(),
                    field_vis,
                }
            })
    })?;

    Some((struct_name.to_string(), layout))
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
        if !crate::ast::is_visible(layout.vis, &layout.module_path, &type_ctx.current_module) {
            errors.push(SemanticError {
                code: "E0603",
                message: format!("Struct `{name}` is private"),
                label: "Private struct".to_string(),
                secondary_label: None,
                help: Some(format!("Mark `{name}` with `pub` if it should be accessible outside its module")),
                span: span.clone(),
            });
        }
        for (f_name, f_vis) in &layout.field_vis {
            if !crate::ast::is_visible(*f_vis, &layout.module_path, &type_ctx.current_module) {
                errors.push(SemanticError {
                    code: "E0603",
                    message: format!("Cannot construct `{name}` directly because field `{f_name}` is private"),
                    label: "Private field in struct literal".to_string(),
                    secondary_label: None,
                    help: Some(format!("Use a public constructor function on `{name}`, or mark `{f_name}` as `pub`")),
                    span: span.clone(),
                });
                break;
            }
        }
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


pub fn type_check_enum_construct<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    enum_name: &str,
    variant_name: &str,
    args: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    let expected_payloads: Option<Vec<Type>> = type_ctx
        .get_enum(enum_name)
        .and_then(|(_, variants)| variants.get(variant_name).map(|(_, tys)| tys.clone()));

    let mut typed_args = Vec::new();
    for (i, a) in args.iter().enumerate() {
        let mut arg_ctx = type_ctx.clone();
        arg_ctx.current_expected_type = expected_payloads.as_ref().and_then(|v| v.get(i).copied());
        if let Some(ta) = type_check_expr(scopes, errors, &arg_ctx, a) {
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
