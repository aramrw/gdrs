//! sanal/calls/mod.rs
//! Type checking for function calls, method calls, macro calls, and closures.

pub mod closures;
pub mod helpers;
pub mod macros;
pub mod resolution;
pub mod validation;

pub use closures::{build_non_capturing_closure, type_check_closure};
pub use helpers::build_substituted_method;
pub use macros::type_check_macro_call;
pub use resolution::resolve_call_target;
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
                if let Some((_, param_tys, ret_ty)) = methods.iter().find(|(m, _, _)| m == &m_name) {
                    let recv = typed_args.remove(0);
                    let synthetic_params: Vec<crate::ast::Param> = param_tys
                        .iter()
                        .skip(1)
                        .enumerate()
                        .map(|(i, p_ty)| crate::ast::Param {
                            name: format!("arg{i}"),
                            is_mutable: false,
                            ty: *p_ty,
                            span: span.clone(),
                        })
                        .collect();
                    let synthetic_fn = crate::ast::FuncDecl {
                        name: format!("{trait_name}::{m_name}"),
                        params: synthetic_params,
                        return_type: *ret_ty,
                        where_clause: None,
                        is_track_caller: false,
                        vis: crate::ast::Visibility::Pub,
                        module_path: Vec::new(),
                        is_trait_impl: false,
                        body: Vec::new(),
                    };
                    validate_call_arguments(
                        &synthetic_fn,
                        &mut typed_args,
                        false,
                        &synthetic_fn.name,
                        scopes,
                        errors,
                        type_ctx,
                        span,
                    );
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

    let (mut resolved_name, deferred_target_func) = resolve_call_target(
        raw_name,
        &name,
        resolved_name,
        is_direct_concrete_fn,
        is_generic_fn,
        &typed_args,
        type_ctx,
        span,
    );

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
            if let Some(raw_elem_ty) = inner_opt {
                let elem_ty = type_ctx.infer.borrow_mut().resolve(raw_elem_ty);
                if !elem_ty.is_copy() && !matches!(elem_ty, Type::Infer(_) | Type::Error) {
                    errors.push(SemanticError {
                        code: "E0507",
                        message: format!(
                            "Cannot iterate by value over `Vec<{elem_ty:?}>` because `{elem_ty:?}` is not `Copy`"
                        ),
                        label: "Would copy non-Copy element out of borrowed Vec".to_string(),
                        secondary_label: None,
                        help: Some(
                            "Iterate by index (`for i in 0..v.len():`) and borrow elements (`&v[i]`) instead"
                                .to_string(),
                        ),
                        span: span.clone(),
                    });
                } else if let Some(mangled_iter) = crate::sanal::mono::monomorphize_struct(
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
    } else if let Some(var_info) = scopes.lookup(&resolved_name) {
        let var_ty = type_ctx.infer.borrow_mut().resolve(var_info.ty);
        errors.push(SemanticError {
            code: "E0618",
            message: format!(
                "Expected function, found local variable `{resolved_name}` of type `{:?}`",
                var_ty
            ),
            label: "Not callable".to_string(),
            secondary_label: None,
            help: Some("Only named functions, methods, and inline closures are callable".to_string()),
            span: span.clone(),
        });
        Type::Error
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

