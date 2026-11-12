//! sanal/calls/mod.rs
//! Type checking for function calls, method calls, macro calls, and closures.

pub mod closures;
pub mod helpers;
pub mod macros;
pub mod validation;

pub use closures::{build_non_capturing_closure, type_check_closure};
pub use helpers::build_substituted_method;
pub use macros::type_check_macro_call;
pub use validation::validate_call_arguments;

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};
pub fn type_check_call<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    raw_name_arg: &str,
    args: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    let is_method_syntax = raw_name_arg.starts_with('.');
    let raw_name = raw_name_arg.strip_prefix('.').unwrap_or(raw_name_arg);

    if args.len() == 2 {
        if let Expr::Ident(ref smart_ptr, _) = args[0] {
            if (smart_ptr == "rc" || smart_ptr == "arc")
                && scopes.lookup(smart_ptr).is_none()
                && raw_name == "new"
            {
                if let Some(t_val) = type_check_expr(scopes, errors, type_ctx, &args[1]) {
                    type_ctx.check_not_moved_from_projection(&t_val, errors);
                    crate::sanal::compat::mark_expr_moved_if_ident(scopes, errors, &t_val);
                    let inner_ty = crate::ast::intern_type(t_val.ty());
                    let ret_ty = if smart_ptr == "rc" {
                        Type::Rc(inner_ty)
                    } else {
                        Type::Arc(inner_ty)
                    };
                    return Some(TypedExpr::Call(
                        format!("{smart_ptr}_new"),
                        vec![t_val],
                        ret_ty,
                        span.clone(),
                    ));
                }
            }
        }
    }

    if !args.is_empty() {
        if let Expr::Ident(ref type_name, _) = args[0] {
            if scopes.lookup(type_name).is_none() {
                if let Some((_, variants)) = type_ctx.get_enum(type_name) {
                    if variants.contains_key(raw_name) {
                        if let Some(te) = super::objects::type_check_enum_construct(
                            scopes,
                            errors,
                            type_ctx,
                            type_name,
                            raw_name,
                            &args[1..],
                            span,
                        ) {
                            return Some(te);
                        }
                    }
                } else {
                    let is_enum_variant = {
                        let mono = type_ctx.mono.borrow();
                        crate::sanal::mono::find_enum_template(&mono, type_name)
                            .is_some_and(|decl| decl.variants.iter().any(|v| v.name == raw_name))
                    };
                    if is_enum_variant {
                        if let Some(te) = super::objects::type_check_enum_construct(
                            scopes,
                            errors,
                            type_ctx,
                            type_name,
                            raw_name,
                            &args[1..],
                            span,
                        ) {
                            return Some(te);
                        }
                    }
                }
            }
        }
    }

    if !args.is_empty() {
        if let Expr::Ident(ref struct_name, _) = args[0] {
            if scopes.lookup(struct_name).is_none() {
                let is_known_type =
                    type_ctx.contains_struct(struct_name) || type_ctx.contains_enum(struct_name);
                let is_template_method = {
                    let mono = type_ctx.mono.borrow();
                    crate::sanal::mono::find_struct_template(&mono, struct_name)
                        .and_then(|d| crate::sanal::mono::find_impl_method(&mono, &d.name, raw_name))
                        .is_some()
                        || crate::sanal::mono::find_enum_template(&mono, struct_name)
                            .and_then(|d| {
                                crate::sanal::mono::find_impl_method(&mono, &d.name, raw_name)
                            })
                            .is_some()
                };
                if is_known_type || is_template_method {
                    let static_name = format!("{struct_name}::{raw_name}");
                    let mangled = format!("{struct_name}_{raw_name}");
                    if is_template_method
                        || type_ctx.contains_fn(&mangled)
                        || type_ctx.contains_fn(&static_name)
                    {
                        return type_check_call(
                            scopes,
                            errors,
                            type_ctx,
                            &static_name,
                            &args[1..],
                            span,
                        );
                    }
                }
            }
        }
    }

    let mut typed_args = Vec::new();
    if !args.is_empty() {
        if let Some(first_arg) = type_check_expr(scopes, errors, type_ctx, &args[0]) {
            let first_ty = first_arg.ty();
            typed_args.push(first_arg);

            let elem_ty = match &first_ty {
                Type::Vec(inner) => Some((**inner).clone()),
                Type::Ref(inner) | Type::MutRef(inner) => match &**inner {
                    Type::Vec(elem) => Some((**elem).clone()),
                    _ => None,
                },
                _ => None,
            };

            for arg in &args[1..] {
                if let (Some(closure_elem_ty), Expr::Closure(params, body, c_span)) =
                    (elem_ty.clone(), arg)
                {
                    typed_args.push(build_non_capturing_closure(
                        scopes,
                        errors,
                        type_ctx,
                        params,
                        closure_elem_ty,
                        body,
                        c_span,
                    ));
                } else if let Some(t_arg) = type_check_expr(scopes, errors, type_ctx, arg) {
                    typed_args.push(t_arg);
                }
            }

            if raw_name.ends_with("push") && typed_args.len() >= 2 {
                let recv_ty = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
                let recv_elem_opt = match recv_ty {
                    Type::Vec(inner) => Some(*inner),
                    Type::Ref(inner) | Type::MutRef(inner) => match *inner {
                        Type::Vec(elem) => Some(*elem),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(recv_elem) = recv_elem_opt {
                    let pushed_ty = type_ctx.infer.borrow_mut().resolve(typed_args[1].ty());
                    let unify_ok = type_ctx
                        .infer
                        .borrow_mut()
                        .unify(recv_elem, pushed_ty)
                        .is_ok();
                    if unify_ok {
                        let updated_recv = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
                        if let Expr::Ident(vec_var_name, _) = &args[0] {
                            if let Some(info) = scopes.lookup_mut(vec_var_name) {
                                info.ty = updated_recv;
                            }
                        }
                        match &mut typed_args[0] {
                            TypedExpr::Ident(_, t_ty, _)
                            | TypedExpr::FieldAccess(_, _, t_ty, _)
                            | TypedExpr::Deref(_, t_ty, _) => {
                                *t_ty = updated_recv;
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    let is_enum_candidate = raw_name.contains("::")
        || matches!(raw_name, "Some" | "None" | "Ok" | "Err")
        || raw_name.starts_with("Opt_")
        || raw_name.starts_with("Res_")
        || raw_name.starts_with("std_core_")
        || raw_name
            .rsplit_once('_')
            .is_some_and(|(e, _)| type_ctx.contains_enum(e));

    if is_enum_candidate {
        let prefer_std_option = matches!(
            type_ctx.current_return_type,
            Some(Type::Enum(r)) | Some(Type::Obj(r)) if r.starts_with("std_core_Option")
        );
        let prefer_std_result = matches!(
            type_ctx.current_return_type,
            Some(Type::Enum(r)) | Some(Type::Obj(r)) if r.starts_with("std_core_Result")
        );
        let has_local_option = !prefer_std_option && type_ctx.enum_map.borrow().contains_key("Option");
        let has_local_result = !prefer_std_result && type_ctx.enum_map.borrow().contains_key("Result");

        let normalized_name = match raw_name {
            "Some" | "Option::Some" | "Option_Some" => {
                if has_local_option {
                    "Option_Some".to_string()
                } else {
                    "std_core_Option_Some".to_string()
                }
            }
            "None" | "Option::None" | "Option_None" => {
                if has_local_option {
                    "Option_None".to_string()
                } else {
                    "std_core_Option_None".to_string()
                }
            }
            "Ok" | "Result::Ok" | "Result_Ok" => {
                if has_local_result {
                    "Result_Ok".to_string()
                } else {
                    "std_core_Result_Ok".to_string()
                }
            }
            "Err" | "Result::Err" | "Result_Err" => {
                if has_local_result {
                    "Result_Err".to_string()
                } else {
                    "std_core_Result_Err".to_string()
                }
            }
            _ => {
                let n = raw_name.replace("::", "_");
                if n.starts_with("Opt_") {
                    n.replacen("Opt_", "std_core_Option_", 1)
                } else if n.starts_with("Res_") {
                    n.replacen("Res_", "std_core_Result_", 1)
                } else {
                    n
                }
            }
        };
        if let Some((enum_name, variant_name)) = normalized_name.rsplit_once('_') {
            if type_ctx.contains_enum(enum_name)
                || enum_name.starts_with("std_core_")
                || enum_name == "Opt"
                || enum_name == "Res"
            {
                if let Some(te) = super::objects::type_check_enum_construct(
                    scopes, errors, type_ctx, enum_name, variant_name, args, span,
                ) {
                    if matches!(te, TypedExpr::EnumConstruct(..)) {
                        return Some(te);
                    }
                }
            }
        }
    }

    let name = raw_name.replace("::", "_");

    // Handle .clone() on rc<T> / arc<T> smart pointers
    if raw_name == "clone" && typed_args.len() == 1 {
        let first_ty = typed_args[0].ty();
        if matches!(first_ty, Type::Rc(_) | Type::Arc(_)) {
            let fn_name = if matches!(first_ty, Type::Rc(_)) {
                "rc_clone"
            } else {
                "arc_clone"
            };
            return Some(TypedExpr::Call(
                fn_name.to_string(),
                typed_args,
                first_ty,
                span.clone(),
            ));
        }
    }

    let mut resolved_name = name.clone();
    let is_direct_concrete_fn = !is_method_syntax
        && (type_ctx.extern_signatures.contains_key(&name)
            || type_ctx.fn_map.borrow().get(&name).is_some_and(|f| {
                !f.params
                    .iter()
                    .any(|p| crate::sanal::compat::type_contains_generic(&p.ty))
                    && !crate::sanal::compat::type_contains_generic(&f.return_type)
            }));

    // 1. Check if first argument is a receiver target for method lookup `target.method(...)`
    if !is_direct_concrete_fn && !typed_args.is_empty() {
        let target_ty = typed_args[0].ty();
        let type_name = match &target_ty {
            Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
            Type::Ref(inner) | Type::MutRef(inner) => match &**inner {
                Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
                _ => None,
            },
            _ => None,
        };

        if let Some(tn) = type_name {
            let mangled = format!("{tn}_{name}");
            if let Some(target_func) = type_ctx.get_fn(&mangled) {
                resolved_name = target_func.name;
            } else if type_ctx.contains_struct(&tn) {
                let _ = type_ctx.get_struct(&tn);
                if let Some(target_func) = type_ctx.get_fn(&mangled) {
                    resolved_name = target_func.name;
                }
            }
        }
    }

    let is_generic_fn = type_ctx
        .get_fn(&resolved_name)
        .map(|f| {
            f.params
                .iter()
                .any(|p| crate::sanal::compat::type_contains_generic(&p.ty))
        })
        .unwrap_or(false);

    if !typed_args.is_empty() {
        let t0 = match typed_args[0].ty() {
            Type::Ref(inner) | Type::MutRef(inner) => *inner,
            other => other,
        };
        if let Type::DynTrait(trait_name) = t0 {
            let m_name = raw_name
                .rsplit('.')
                .next()
                .unwrap_or(&name)
                .rsplit("::")
                .next()
                .unwrap_or(&name)
                .to_string();
            let methods_opt = type_ctx.trait_methods.get(trait_name).or_else(|| {
                type_ctx
                    .trait_methods
                    .iter()
                    .find(|(k, _)| k.ends_with(&format!("_{trait_name}")))
                    .map(|(_, v)| v)
            });
            if let Some(methods) = methods_opt {
                if let Some((_, _, ret_ty)) = methods.iter().find(|(m, _, _)| m == &m_name) {
                    let recv = typed_args.remove(0);
                    return Some(TypedExpr::DynCall(
                        Box::new(recv),
                        m_name,
                        typed_args,
                        *ret_ty,
                        span.clone(),
                    ));
                }
            }
        }
    }

    let mut deferred_target_func: Option<crate::ast::FuncDecl> = None;

    // 2. Auto-monomorphize static method calls like `Vec2_new(1.0, 2.0)` or `Vec3_new(1.0, 2.0, 3.0)`
    if !is_direct_concrete_fn && (resolved_name == name || !type_ctx.contains_fn(&resolved_name) || is_generic_fn) {
        let target_type = if !typed_args.is_empty() {
            let t0 = match typed_args[0].ty() {
                Type::Ref(inner) | Type::MutRef(inner) => *inner,
                other => other,
            };
            match t0 {
                Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
                Type::Vec(_) => Some("Vec".to_string()),
                Type::String => Some("String".to_string()),
                _ => None,
            }
        } else {
            None
        };

        let (mut base_struct, method_name) = if name.starts_with("std_vec_Vec_") {
            ("std_vec_Vec".to_string(), name["std_vec_Vec_".len()..].to_string())
        } else if let Some(ref tt) = target_type {
            let mn = if name.starts_with(&format!("{tt}_")) {
                name[tt.len() + 1..].to_string()
            } else {
                name.clone()
            };
            (tt.clone(), mn)
        } else if let Some((bs, mn)) = {
            let mono = type_ctx.mono.borrow();
            let mut found = None;
            for (idx, _) in name.match_indices('_') {
                let candidate = &name[..idx];
                let is_known = type_ctx.struct_map.borrow().contains_key(candidate)
                    || type_ctx.enum_map.borrow().contains_key(candidate)
                    || mono.struct_templates.contains_key(candidate)
                    || mono.enum_templates.contains_key(candidate)
                    || mono.struct_templates.iter().any(|(k, _)| k.ends_with(&format!("_{candidate}")))
                    || mono.enum_templates.iter().any(|(k, _)| k.ends_with(&format!("_{candidate}")));
                if is_known {
                    found = Some((candidate.to_string(), name[idx + 1..].to_string()));
                }
            }
            found.or_else(|| {
                if raw_name.contains("::") {
                    raw_name.rsplit_once("::").map(|(b, m)| (b.replace("::", "_"), m.to_string()))
                } else {
                    name.split_once('_').map(|(b, m)| (b.to_string(), m.to_string()))
                }
            })
        } {
            (bs, mn)
        } else {
            (String::new(), String::new())
        };

        if base_struct.ends_with("_t") || base_struct.ends_with("_T") {
            base_struct = base_struct[..base_struct.len() - 2].to_string();
        }
        if base_struct == "VecIter" || base_struct == "std_vec_VecIter" || base_struct.starts_with("std_vec_VecIter_") {
            base_struct = "std_vec_VecIter".to_string();
        } else if base_struct == "Vec" || base_struct == "std_vec_Vec" || base_struct.starts_with("std_vec_Vec_") {
            base_struct = "std_vec_Vec".to_string();
        } else if base_struct == "String" || base_struct == "std_string_String" || base_struct.starts_with("std_string_String_") {
            base_struct = "std_string_String".to_string();
        } else if base_struct.contains("Option") {
            base_struct = if type_ctx.mono.borrow().enum_templates.contains_key("Option") || type_ctx.enum_map.borrow().contains_key("Option") {
                "Option".to_string()
            } else {
                "std_core_Option".to_string()
            };
        } else if base_struct.contains("Result") {
            base_struct = if type_ctx.mono.borrow().enum_templates.contains_key("Result") || type_ctx.enum_map.borrow().contains_key("Result") {
                "Result".to_string()
            } else {
                "std_core_Result".to_string()
            };
        } else if base_struct.starts_with("std_") {
            if let Some((clean, _)) = base_struct.rsplit_once('_') {
                if type_ctx.struct_map.borrow().contains_key(clean) || type_ctx.enum_map.borrow().contains_key(clean) {
                    base_struct = clean.to_string();
                }
            }
        }

        if !type_ctx.struct_map.borrow().contains_key(&base_struct)
            && !type_ctx.enum_map.borrow().contains_key(&base_struct)
            && !type_ctx.mono.borrow().struct_templates.contains_key(&base_struct)
            && !type_ctx.mono.borrow().enum_templates.contains_key(&base_struct)
        {
            if let Some(clean) = base_struct.strip_prefix("std_core_").or_else(|| base_struct.strip_prefix("std_vec_")).or_else(|| base_struct.strip_prefix("std_string_")) {
                if type_ctx.mono.borrow().enum_templates.contains_key(clean) || type_ctx.enum_map.borrow().contains_key(clean) {
                    base_struct = clean.to_string();
                } else if type_ctx.mono.borrow().struct_templates.contains_key(clean) || type_ctx.struct_map.borrow().contains_key(clean) {
                    base_struct = clean.to_string();
                }
            }
            if let Some(k) = type_ctx.mono.borrow().struct_templates.keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            } else if let Some(k) = type_ctx.struct_map.borrow().keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            } else if let Some(k) = type_ctx.mono.borrow().enum_templates.keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            } else if let Some(k) = type_ctx.enum_map.borrow().keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            }
        }

        let is_struct_or_enum = type_ctx.struct_map.borrow().contains_key(&base_struct)
            || type_ctx.enum_map.borrow().contains_key(&base_struct)
            || type_ctx.mono.borrow().struct_templates.contains_key(&base_struct)
            || type_ctx.mono.borrow().enum_templates.contains_key(&base_struct);

        if !base_struct.is_empty() && is_struct_or_enum {
            let mut resolved_mangled = false;
            if !typed_args.is_empty() {
                let arg_ty = match typed_args[0].ty() {
                    Type::Ref(inner) | Type::MutRef(inner) => *inner,
                    other => other,
                };
                if let Type::Enum(mangled_enum) | Type::Obj(mangled_enum) = arg_ty {
                    let mangled_fn = format!("{mangled_enum}_{method_name}");
                    if type_ctx.contains_fn(&mangled_fn) {
                        resolved_name = mangled_fn;
                        resolved_mangled = true;
                    } else if mangled_enum.starts_with("std_core_")
                        || type_ctx.mono.borrow().enum_templates.contains_key(mangled_enum)
                    {
                        let base_e = if mangled_enum.contains("Option") { "Option" } else { "Result" };
                        let alt_base_e = if mangled_enum.contains("Option") { "std_core_Option" } else { "std_core_Result" };
                        let cache = type_ctx.mono.borrow().enum_cache.clone();
                        let cached_args = cache.iter()
                            .find(|(_, m)| *m == mangled_enum || mangled_enum.ends_with(m.as_str()) || m.ends_with(&format!("_{mangled_enum}")))
                            .map(|(k, _)| k.type_args.clone());

                        let type_args = cached_args
                            .or_else(|| crate::sanal::mono::lookup_mangled(mangled_enum).map(|(_, a)| a))
                            .unwrap_or_else(|| vec![Type::Int, Type::Int]);

                        if type_args.iter().any(|t| {
                            crate::sanal::compat::type_contains_infer(t)
                                || crate::sanal::compat::type_contains_generic(t)
                        }) {
                            let enum_tpl = {
                                let mono = type_ctx.mono.borrow();
                                crate::sanal::mono::find_enum_template(&mono, base_e)
                                    .or_else(|| crate::sanal::mono::find_enum_template(&mono, alt_base_e))
                                    .and_then(|d| {
                                        crate::sanal::mono::find_impl_method(&mono, &d.name, &method_name)
                                            .map(|m| (d, m))
                                    })
                            };
                            if let Some((tpl_decl, tpl_method)) = enum_tpl {
                                let gen_params =
                                    crate::sanal::mono::extract_generic_params_enum(&tpl_decl);
                                let self_ty = Type::Enum(crate::ast::intern_str(
                                    &crate::sanal::mono::mangle_name(&tpl_decl.name, &type_args),
                                ));
                                let placeholder = type_ctx.infer.borrow_mut().register_deferred_call(
                                    crate::sanal::infer::DeferredCall::EnumMethod {
                                        base_enum: tpl_decl.name.clone(),
                                        method_name: method_name.clone(),
                                        type_args: type_args.clone(),
                                    },
                                );
                                resolved_name = placeholder.clone();
                                deferred_target_func = Some(build_substituted_method(
                                    &tpl_decl.name,
                                    &gen_params,
                                    &tpl_method,
                                    &type_args,
                                    self_ty,
                                    placeholder,
                                ));
                                resolved_mangled = true;
                            }
                        } else {
                            let mangled = crate::sanal::mono::monomorphize_enum(
                                type_ctx.mono,
                                base_e,
                                &type_args,
                                type_ctx.enum_map,
                                type_ctx.fn_map,
                                type_ctx.worklist,
                            ).or_else(|| crate::sanal::mono::monomorphize_enum(
                                type_ctx.mono,
                                alt_base_e,
                                &type_args,
                                type_ctx.enum_map,
                                type_ctx.fn_map,
                                type_ctx.worklist,
                            ));

                            if let Some(m) = mangled {
                                let try_fn = format!("{m}_{method_name}");
                                if type_ctx.contains_fn(&try_fn) {
                                    resolved_name = try_fn;
                                    resolved_mangled = true;
                                }
                            }
                        }
                    }
                }
            }

            if !resolved_mangled {
                let mut type_args = Vec::new();
                if !typed_args.is_empty() {
                    let recv_ty = match typed_args[0].ty() {
                        Type::Ref(inner) | Type::MutRef(inner) => *inner,
                        other => other,
                    };
                    if let Type::Vec(inner) = recv_ty {
                        type_args.push(*inner);
                    }
                }
                if type_args.is_empty() && !typed_args.is_empty() {
                    let recv_ty = match typed_args[0].ty() {
                        Type::Ref(inner) | Type::MutRef(inner) => *inner,
                        other => other,
                    };
                    if let Type::Obj(obj_name) = recv_ty {
                        let name_str = obj_name.to_string();
                        if name_str.contains("Vec") && typed_args.len() >= 2 {
                            let elem_ty = typed_args[1].ty();
                            if !matches!(elem_ty, Type::Generic(_)) {
                                type_args.push(elem_ty);
                            }
                        } else if let Some((_, mangled_args)) = crate::sanal::mono::lookup_mangled(&name_str) {
                            type_args.extend(mangled_args);
                        } else if let Some((_, suffix)) = name_str.rsplit_once('_') {
                            if type_ctx.contains_struct(suffix) || type_ctx.contains_enum(suffix) {
                                type_args.push(Type::Obj(crate::ast::intern_str(suffix)));
                            }
                        }
                    }
                }
                if type_args.is_empty() {
                    let is_struct_tpl_static = {
                        let mono = type_ctx.mono.borrow();
                        crate::sanal::mono::find_struct_template(&mono, &base_struct)
                            .and_then(|d| {
                                crate::sanal::mono::find_impl_method(&mono, &d.name, &method_name)
                                    .map(|m| (d, m))
                            })
                    };
                    if let Some((tpl_decl, tpl_method)) = is_struct_tpl_static {
                        let gen_params = crate::sanal::mono::extract_generic_params_struct(
                            &tpl_decl,
                            type_ctx.mono,
                        );
                        if !gen_params.is_empty() {
                            let (p_env, mut p_tys) = type_ctx.infer.borrow_mut().instantiate_params(
                                &gen_params,
                                span,
                                &tpl_decl.name,
                            );
                            let self_obj = if tpl_decl.name == "std_vec_Vec" {
                                Type::Vec(crate::ast::intern_type(p_tys[0]))
                            } else {
                                Type::Obj(crate::ast::intern_str(&crate::sanal::mono::mangle_name(
                                    &tpl_decl.name,
                                    &p_tys,
                                )))
                            };
                            let mut sub_params = Vec::new();
                            for p in &tpl_method.params {
                                let p_ty = match p.ty {
                                    Type::Unit if p.name == "self" => self_obj,
                                    Type::Ref(inner) if *inner == Type::Unit && p.name == "self" => {
                                        Type::Ref(crate::ast::intern_type(self_obj))
                                    }
                                    Type::MutRef(inner) if *inner == Type::Unit && p.name == "self" => {
                                        Type::MutRef(crate::ast::intern_type(self_obj))
                                    }
                                    other => {
                                        let sub = crate::sanal::mono::substitute_type(other, &p_env);
                                        if let Type::Obj(tn) = sub {
                                            if tn == tpl_decl.name {
                                                self_obj
                                            } else {
                                                sub
                                            }
                                        } else {
                                            sub
                                        }
                                    }
                                };
                                sub_params.push(p_ty);
                            }
                            for (p_ty, arg) in sub_params.iter().zip(typed_args.iter()) {
                                let _ = type_ctx.infer.borrow_mut().unify(*p_ty, arg.ty());
                            }
                            let mut ret_sub = crate::sanal::mono::substitute_type(tpl_method.return_type, &p_env);
                            if let Type::Obj(tn) = ret_sub {
                                let short = tpl_decl.name.rsplit_once('_').map(|(_, s)| s).unwrap_or(&tpl_decl.name);
                                if tn == tpl_decl.name || tn == short {
                                    ret_sub = self_obj;
                                }
                            }
                            if let Some(exp) = type_ctx.current_expected_type {
                                let _ = type_ctx.infer.borrow_mut().unify(exp, ret_sub);
                            }
                            for t in &mut p_tys {
                                *t = type_ctx.infer.borrow_mut().resolve(*t);
                            }
                            type_args = p_tys;
                        }
                    }
                }
                if type_args.is_empty() {
                    let actual_args = if !typed_args.is_empty()
                        && matches!(
                            typed_args[0].ty(),
                            Type::Obj(_) | Type::Enum(_) | Type::Ref(_) | Type::MutRef(_)
                        )
                    {
                        &typed_args[1..]
                    } else {
                        &typed_args[..]
                    };
                    for a in actual_args {
                        let mut t = a.ty();
                        if let Type::Array(elem_ty, _) | Type::Slice(elem_ty) = t {
                            t = *elem_ty;
                        }
                        if !matches!(t, Type::Unit) && !type_args.contains(&t) {
                            type_args.push(t);
                        }
                    }
                }
                for t in &mut type_args {
                    *t = type_ctx.infer.borrow_mut().resolve(*t);
                }
                let direct_method = format!("{base_struct}_{method_name}");
                let clean_base = base_struct.strip_prefix("std_core_")
                    .or_else(|| base_struct.strip_prefix("std_vec_"))
                    .or_else(|| base_struct.strip_prefix("std_string_"))
                    .or_else(|| base_struct.strip_prefix("std_fs_"))
                    .unwrap_or(&base_struct);

                let is_generic_template = type_ctx.get_fn(&direct_method).map(|f| {
                    f.params.iter().any(|p| matches!(p.ty, Type::Generic(_))) || matches!(f.return_type, Type::Generic(_))
                }).unwrap_or(false)
                    || type_ctx.mono.borrow().struct_templates.contains_key(&base_struct)
                    || type_ctx.mono.borrow().struct_templates.contains_key(clean_base)
                    || type_ctx.mono.borrow().enum_templates.contains_key(&base_struct)
                    || type_ctx.mono.borrow().enum_templates.contains_key(clean_base);

                if !typed_args.is_empty() {
                    let arg_ty = match typed_args[0].ty() {
                        Type::Ref(inner) | Type::MutRef(inner) => *inner,
                        other => other,
                    };
                    if let Type::Enum(mangled_enum) = arg_ty {
                        let try_fn = format!("{mangled_enum}_{method_name}");
                        if type_ctx.contains_fn(&try_fn) {
                            resolved_name = try_fn;
                        }
                    }
                }

                if resolved_name == name && !type_args.is_empty() {
                    let has_infer = type_args.iter().any(|t| {
                        crate::sanal::compat::type_contains_infer(t)
                            || crate::sanal::compat::type_contains_generic(t)
                    });
                    if has_infer {
                        if base_struct == "std_vec_Vec" && method_name == "new" {
                            resolved_name = "std_vec_Vec_new".to_string();
                        } else {
                            let tpl_opt = {
                                let mono = type_ctx.mono.borrow();
                                crate::sanal::mono::find_struct_template(&mono, &base_struct)
                                    .and_then(|d| {
                                        crate::sanal::mono::find_impl_method(&mono, &d.name, &method_name)
                                            .map(|m| (d, m))
                                    })
                            };
                            if let Some((tpl_decl, tpl_method)) = tpl_opt {
                                let gen_params = crate::sanal::mono::extract_generic_params_struct(
                                    &tpl_decl,
                                    type_ctx.mono,
                                );
                                let self_obj = if tpl_decl.name == "std_vec_Vec" {
                                    Type::Vec(crate::ast::intern_type(type_args[0]))
                                } else {
                                    Type::Obj(crate::ast::intern_str(
                                        &crate::sanal::mono::mangle_name(&tpl_decl.name, &type_args),
                                    ))
                                };
                                let placeholder = type_ctx.infer.borrow_mut().register_deferred_call(
                                    crate::sanal::infer::DeferredCall::StructMethod {
                                        base_struct: tpl_decl.name.clone(),
                                        method_name: method_name.clone(),
                                        type_args: type_args.clone(),
                                    },
                                );
                                resolved_name = placeholder.clone();
                                deferred_target_func = Some(build_substituted_method(
                                    &tpl_decl.name,
                                    &gen_params,
                                    &tpl_method,
                                    &type_args,
                                    self_obj,
                                    placeholder,
                                ));
                            }
                        }
                    } else {
                        let lookup_base = base_struct.clone();
                        if let Some(mangled_struct) = crate::sanal::mono::monomorphize_struct(
                            type_ctx.mono,
                            &lookup_base,
                            &type_args,
                            type_ctx.struct_map,
                            type_ctx.enum_map,
                            type_ctx.fn_map,
                            type_ctx.worklist,
                        ) {
                            let mangled_fn = format!("{mangled_struct}_{method_name}");
                            resolved_name = mangled_fn;
                        } else if !is_generic_template && type_ctx.contains_fn(&direct_method) {
                            resolved_name = direct_method;
                        }
                    }
                } else if resolved_name == name && !is_generic_template && type_ctx.contains_fn(&direct_method) {
                    resolved_name = direct_method;
                }
            }
        }
    }

    // 3. Fallback to direct fn_map lookup if not already resolved to a method
    if resolved_name == name && !type_ctx.extern_signatures.contains_key(&name) && !type_ctx.extern_fn_names.contains(&name) {
        if let Some(target_func) = type_ctx.get_fn(&name) {
            resolved_name = target_func.name;
        }
    }

    // 4. Monomorphize standalone generic functions (and generic methods on non-generic types)
    let needs_fn_mono = deferred_target_func.is_none()
        && type_ctx.get_fn(&resolved_name).is_some_and(|f| {
            f.params
                .iter()
                .any(|p| crate::sanal::compat::type_contains_generic(&p.ty))
                || crate::sanal::compat::type_contains_generic(&f.return_type)
        });
    if needs_fn_mono {
        let arg_types: Vec<Type> = typed_args
            .iter()
            .map(|a| type_ctx.infer.borrow_mut().resolve(a.ty()))
            .collect();
        let has_infer = arg_types
            .iter()
            .any(crate::sanal::compat::type_contains_infer);
        if has_infer {
            if let Some(tpl_fn) = type_ctx.get_fn(&resolved_name) {
                let mut gen_params = Vec::new();
                for p in &tpl_fn.params {
                    if let Type::Generic(g) = p.ty {
                        let clean = g.trim_start_matches('$').to_string();
                        if !gen_params.contains(&clean) {
                            gen_params.push(clean);
                        }
                    }
                }
                if let Type::Generic(g) = tpl_fn.return_type {
                    let clean = g.trim_start_matches('$').to_string();
                    if !gen_params.contains(&clean) {
                        gen_params.push(clean);
                    }
                }
                let (p_env, _) = type_ctx.infer.borrow_mut().instantiate_params(
                    &gen_params,
                    span,
                    &tpl_fn.name,
                );
                let sub_params: Vec<crate::ast::Param> = tpl_fn
                    .params
                    .iter()
                    .map(|p| crate::ast::Param {
                        name: p.name.clone(),
                        is_mutable: p.is_mutable,
                        ty: crate::sanal::mono::substitute_type(p.ty, &p_env),
                        span: p.span.clone(),
                    })
                    .collect();
                let ret_sub = crate::sanal::mono::substitute_type(tpl_fn.return_type, &p_env);
                for (p, a) in sub_params.iter().zip(arg_types.iter()) {
                    let _ = type_ctx.infer.borrow_mut().unify(p.ty, *a);
                }
                let placeholder = type_ctx.infer.borrow_mut().register_deferred_call(
                    crate::sanal::infer::DeferredCall::GenericFn {
                        base_fn: resolved_name.clone(),
                        type_args: Vec::new(),
                    },
                );
                resolved_name = placeholder.clone();
                deferred_target_func = Some(crate::ast::FuncDecl {
                    name: placeholder,
                    params: sub_params,
                    return_type: ret_sub,
                    where_clause: tpl_fn.where_clause.clone(),
                    body: Vec::new(),
                    is_track_caller: tpl_fn.is_track_caller,
                    vis: tpl_fn.vis,
                    module_path: tpl_fn.module_path.clone(),
                    is_trait_impl: tpl_fn.is_trait_impl,
                });
            }
        } else if let Some(mangled_fn) = crate::sanal::mono::monomorphize_fn(
            type_ctx.mono,
            &resolved_name,
            &arg_types,
            type_ctx.fn_map,
            type_ctx.struct_map,
            type_ctx.enum_map,
            type_ctx.worklist,
        ) {
            resolved_name = mangled_fn;
        }
    }

    if (raw_name.ends_with(".push") || raw_name.ends_with("::push") || raw_name == "push") && typed_args.len() >= 2 {
        let elem_ty = type_ctx.infer.borrow_mut().resolve(typed_args[1].ty());
        if let TypedExpr::Ident(vec_var_name, _, _) = &typed_args[0] {
            if let Some(info) = scopes.lookup_mut(vec_var_name) {
                let _ = type_ctx
                    .infer
                    .borrow_mut()
                    .unify(info.ty, Type::Vec(crate::ast::intern_type(elem_ty)));
                info.ty = type_ctx.infer.borrow_mut().resolve(info.ty);
            }
        }
    }

    if raw_name == "std::mem::drop" || raw_name == "mem::drop" || raw_name == "std_mem_drop" {
        if typed_args.len() != 1 {
            errors.push(SemanticError {
                code: "E0061",
                message: format!("`std::mem::drop` expects 1 argument, found {}", typed_args.len()),
                label: "Expected 1 argument".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        } else {
            type_ctx.check_not_moved_from_projection(&typed_args[0], errors);
            if let TypedExpr::Ident(arg_name, arg_ty, arg_span) = &typed_args[0] {
                if !arg_ty.is_copy() {
                    crate::sanal::compat::check_not_borrowed_on_move(
                        scopes, errors, arg_name, arg_span,
                    );
                    scopes.mark_moved(arg_name);
                }
            }
        }
        return Some(TypedExpr::Call(
            "std_mem_drop".to_string(),
            typed_args,
            Type::Unit,
            span.clone(),
        ));
    }

    if raw_name.ends_with(".drop") || (raw_name == "drop" && !typed_args.is_empty()) {
        errors.push(SemanticError {
            code: "E0040",
            message: "Explicit call to Drop::drop is forbidden; use std::mem::drop() instead".to_string(),
            label: "Explicit call to Drop::drop is forbidden".to_string(),
            secondary_label: None,
            help: Some("Use std::mem::drop() to drop a value early".to_string()),
            span: span.clone(),
        });
    }

    if type_ctx.extern_fn_names.contains(&resolved_name) && !type_ctx.is_unsafe {
        errors.push(SemanticError {
            code: "E0133",
            message: format!(
                "Call to extern C function '{resolved_name}' requires an 'unsafe:' block"
            ),
            label: "Foreign C function call requires 'unsafe:' block".to_string(),
            secondary_label: None,
            help: Some("Wrap this call inside an 'unsafe:' block".to_string()),
            span: span.clone(),
        });
    }

    let target_func_opt = if is_method_syntax && resolved_name == name {
        None
    } else {
        deferred_target_func.or_else(|| type_ctx.get_fn(&resolved_name))
    };
    let ret_ty = if let Some(target_func) = target_func_opt {
        if !target_func.is_trait_impl
            && !crate::ast::is_visible(
                target_func.vis,
                &target_func.module_path,
                &type_ctx.current_module,
            )
        {
            let clean_name = name.trim_start_matches('.');
            if is_method_syntax {
                errors.push(SemanticError {
                    code: "E0624",
                    message: format!("Method `{clean_name}` is private"),
                    label: "Private method".to_string(),
                    secondary_label: None,
                    help: Some(format!("Mark `{clean_name}` with `pub fn` if it should be callable outside its module")),
                    span: span.clone(),
                });
            } else {
                errors.push(SemanticError {
                    code: "E0603",
                    message: format!("Function `{clean_name}` is private"),
                    label: "Private function".to_string(),
                    secondary_label: None,
                    help: Some(format!("Mark `{clean_name}` with `pub fn` if it should be callable outside its module")),
                    span: span.clone(),
                });
            }
        }
        validate_call_arguments(
            &target_func,
            &mut typed_args,
            is_method_syntax,
            &resolved_name,
            scopes,
            errors,
            type_ctx,
            span,
        );
        let mut ret_ty = if matches!(target_func.return_type, Type::Generic(_)) {
            Type::Int
        } else {
            target_func.return_type
        };

        if (resolved_name == "std_vec_Vec_into_iter"
            || resolved_name == "std_vec_Vec_iter"
            || (resolved_name.starts_with("std_vec_Vec")
                && (resolved_name.ends_with("_into_iter") || resolved_name.ends_with("_iter"))))
            && !typed_args.is_empty()
        {
            fn vec_elem_from_ty(t: Type) -> Option<Type> {
                match t {
                    Type::Vec(e) => Some(*e),
                    Type::Obj(s) => crate::sanal::mono::lookup_mangled(s)
                        .and_then(|(_, args)| args.first().copied()),
                    Type::Ref(inner) | Type::MutRef(inner) => vec_elem_from_ty(*inner),
                    _ => None,
                }
            }
            let inner_opt = vec_elem_from_ty(typed_args[0].ty());
            if let Some(elem_ty) = inner_opt {
                if let Some(mangled_iter) = crate::sanal::mono::monomorphize_struct(
                    type_ctx.mono,
                    "std_vec_VecIter",
                    &[elem_ty],
                    type_ctx.struct_map,
                    type_ctx.enum_map,
                    type_ctx.fn_map,
                    type_ctx.worklist,
                ) {
                    ret_ty = Type::Obj(crate::ast::intern_str(&mangled_iter));
                }
            }
        }

        if resolved_name.ends_with("from_slice") && !typed_args.is_empty() {
            let arg_ty = typed_args[0].ty();
            let elem_ty = match arg_ty {
                Type::Slice(e) | Type::Vec(e) | Type::Array(e, _) => *e,
                _ => Type::Float,
            };
            ret_ty = Type::Vec(crate::ast::intern_type(elem_ty));
        }
        if resolved_name == "std_vec_Vec_new" {
            let elem_var = type_ctx
                .infer
                .borrow_mut()
                .fresh(span.clone(), "element type of `Vec`");
            let vec_ty = Type::Vec(crate::ast::intern_type(elem_var));
            if let Some(exp) = type_ctx.current_expected_type {
                let _ = type_ctx.infer.borrow_mut().unify(exp, vec_ty);
            }
            ret_ty = type_ctx.infer.borrow_mut().resolve(vec_ty);
        }
        type_ctx.infer.borrow_mut().resolve(ret_ty)
    } else if let Some((param_decl_types, ext_ret_ty)) =
        type_ctx.extern_signatures.get(&resolved_name)
    {
        if let Some((ext_vis, ext_mod)) = type_ctx.extern_vis.get(&resolved_name) {
            if !crate::ast::is_visible(*ext_vis, ext_mod, &type_ctx.current_module) {
                errors.push(SemanticError {
                    code: "E0603",
                    message: format!("Extern function `{resolved_name}` is private"),
                    label: "Private extern function".to_string(),
                    secondary_label: None,
                    help: Some(format!("Mark `{resolved_name}` with `pub fn` if it should be callable outside its module")),
                    span: span.clone(),
                });
            }
        }
        if param_decl_types.len() != typed_args.len() {
            errors.push(SemanticError {
                code: "E0061",
                message: format!(
                    "Extern C function '{resolved_name}' expects {} argument(s), found {}",
                    param_decl_types.len(),
                    typed_args.len()
                ),
                label: format!("Expected {} argument(s)", param_decl_types.len()),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        } else {
            for (param_ty, arg) in param_decl_types.iter().zip(typed_args.iter_mut()) {
                match (param_ty, arg.ty()) {
                    (
                        Type::F32,
                        Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_),
                    ) => {
                        if arg.ty() != Type::F32 {
                            *arg = TypedExpr::CastF32(Box::new(arg.clone()), span.clone());
                        }
                    }
                    (
                        Type::I32,
                        Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_),
                    ) => {
                        if arg.ty() != Type::I32 {
                            *arg = TypedExpr::CastI32(Box::new(arg.clone()), span.clone());
                        }
                    }
                    _ => {}
                }
                if !crate::sanal::compat::is_type_compatible(param_ty, &arg.ty()) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Mismatched argument in call to extern C function `{resolved_name}`: expected `{:?}`, found `{:?}`",
                            param_ty,
                            arg.ty()
                        ),
                        label: format!("Expected `{:?}`", param_ty),
                        secondary_label: None,
                        help: None,
                        span: arg.span(),
                    });
                }
            }
        }
        *ext_ret_ty
    } else if scopes.lookup(&resolved_name).is_some() {
        Type::Int
    } else if is_method_syntax && !typed_args.is_empty() {
        if typed_args[0].ty() != Type::Error {
            errors.push(SemanticError {
                code: "E0599",
                message: format!(
                    "No method named `{}` found for type `{}`",
                    raw_name,
                    crate::sanal::compat::format_type(&typed_args[0].ty())
                ),
                label: format!("Method `{}` not found on this type", raw_name),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        Type::Error
    } else {
        errors.push(SemanticError {
            code: "E0425",
            message: format!("Undefined function '{resolved_name}' (raw: '{raw_name}')"),
            label: "Function does not exist".to_string(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
        Type::Error
    };

    let call_target = if type_ctx.extern_signatures.contains_key(&resolved_name) {
        type_ctx
            .extern_c_names
            .get(&resolved_name)
            .cloned()
            .unwrap_or(resolved_name)
    } else {
        resolved_name
    };

    Some(TypedExpr::Call(
        call_target,
        typed_args,
        ret_ty,
        span.clone(),
    ))
}

