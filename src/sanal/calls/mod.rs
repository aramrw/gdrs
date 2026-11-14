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

    // Handle Box::new / Rc::new / Arc::new (both `::new(x)` and `.new(x)`)
    let smart_new_kind: Option<(&str, &Expr)> = if args.len() == 1 {
        match raw_name {
            "Box::new"
            | "std_boxed_Box::new"
            | "std_boxed_Box_new"
            | "Box_new"
            | "box::new" => Some(("box", &args[0])),
            "Rc::new" | "std_rc_Rc::new" | "std_rc_Rc_new" | "Rc_new" | "rc::new" => {
                Some(("rc", &args[0]))
            }
            "Arc::new" | "std_sync_Arc::new" | "std_sync_Arc_new" | "Arc_new" | "arc::new" => {
                Some(("arc", &args[0]))
            }
            _ => None,
        }
    } else if args.len() == 2 && raw_name == "new" {
        if let Expr::Ident(ref smart_ptr, _) = args[0] {
            if scopes.lookup(smart_ptr).is_none() {
                match smart_ptr.as_str() {
                    "Box" | "box" | "std_boxed_Box" => Some(("box", &args[1])),
                    "Rc" | "rc" | "std_rc_Rc" => Some(("rc", &args[1])),
                    "Arc" | "arc" | "std_sync_Arc" => Some(("arc", &args[1])),
                    _ => None,
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    if let Some((kind, val_expr)) = smart_new_kind {
        let mut inner_ctx = type_ctx.clone();
        inner_ctx.current_expected_type = type_ctx.current_expected_type.and_then(|exp| {
            let resolved = type_ctx.infer.borrow_mut().probe(exp);
            match resolved {
                Type::Box(inner) | Type::Rc(inner) | Type::Arc(inner) => Some(*inner),
                _ => None,
            }
        });
        if let Some(t_val) = type_check_expr(scopes, errors, &inner_ctx, val_expr) {
            type_ctx.check_not_moved_from_projection(&t_val, errors);
            crate::sanal::compat::mark_expr_moved_if_ident(scopes, errors, &t_val);
            let inner_ty = crate::ast::intern_type(type_ctx.infer.borrow_mut().resolve(t_val.ty()));
            let ret_ty = match kind {
                "box" => Type::Box(inner_ty),
                "rc" => Type::Rc(inner_ty),
                _ => Type::Arc(inner_ty),
            };
            return Some(TypedExpr::Call(
                format!("{kind}_new"),
                vec![t_val],
                ret_ty,
                span.clone(),
            ));
        }
    }

    // Handle Rc::clone(&r), Arc::clone(&a), Box::clone(&b)
    let smart_clone_arg: Option<(&str, &Expr)> = if args.len() == 1 {
        match raw_name {
            "Box::clone" | "std_boxed_Box::clone" | "std_boxed_Box_clone" | "Box_clone" => {
                Some(("box", &args[0]))
            }
            "Rc::clone" | "std_rc_Rc::clone" | "std_rc_Rc_clone" | "Rc_clone" | "rc::clone" => {
                Some(("rc", &args[0]))
            }
            "Arc::clone"
            | "std_sync_Arc::clone"
            | "std_sync_Arc_clone"
            | "Arc_clone"
            | "arc::clone" => Some(("arc", &args[0])),
            _ => None,
        }
    } else if args.len() == 2 && raw_name == "clone" {
        if let Expr::Ident(ref smart_ptr, _) = args[0] {
            if scopes.lookup(smart_ptr).is_none() {
                match smart_ptr.as_str() {
                    "Box" | "box" | "std_boxed_Box" => Some(("box", &args[1])),
                    "Rc" | "rc" | "std_rc_Rc" => Some(("rc", &args[1])),
                    "Arc" | "arc" | "std_sync_Arc" => Some(("arc", &args[1])),
                    _ => None,
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    if let Some((_kind, arg_expr)) = smart_clone_arg {
        if let Some(t_arg) = type_check_expr(scopes, errors, type_ctx, arg_expr) {
            let resolved_arg = type_ctx.infer.borrow_mut().resolve(t_arg.ty());
            let (unwrapped_expr, ptr_ty) = match resolved_arg {
                Type::Ref(inner) | Type::MutRef(inner) => match t_arg {
                    TypedExpr::Ref(inner_e, _, _, _) => (*inner_e, *inner),
                    other => (
                        TypedExpr::Deref(Box::new(other), *inner, span.clone()),
                        *inner,
                    ),
                },
                other => (t_arg, other),
            };
            match ptr_ty {
                Type::Rc(_) => {
                    return Some(TypedExpr::Call(
                        "rc_clone".to_string(),
                        vec![unwrapped_expr],
                        ptr_ty,
                        span.clone(),
                    ));
                }
                Type::Arc(_) => {
                    return Some(TypedExpr::Call(
                        "arc_clone".to_string(),
                        vec![unwrapped_expr],
                        ptr_ty,
                        span.clone(),
                    ));
                }
                Type::Box(inner) => {
                    return Some(TypedExpr::Call(
                        "box_clone".to_string(),
                        vec![unwrapped_expr],
                        Type::Box(inner),
                        span.clone(),
                    ));
                }
                _ => {}
            }
        }
    }

    // Handle Rc::strong_count(&r) / Arc::strong_count(&a)
    let smart_count_arg: Option<(&str, &Expr)> = if args.len() == 1 {
        match raw_name {
            "Rc::strong_count"
            | "std_rc_Rc::strong_count"
            | "std_rc_Rc_strong_count"
            | "Rc_strong_count"
            | "rc::strong_count" => Some(("rc", &args[0])),
            "Arc::strong_count"
            | "std_sync_Arc::strong_count"
            | "std_sync_Arc_strong_count"
            | "Arc_strong_count"
            | "arc::strong_count" => Some(("arc", &args[0])),
            _ => None,
        }
    } else if args.len() == 2 && raw_name == "strong_count" {
        if let Expr::Ident(ref smart_ptr, _) = args[0] {
            if scopes.lookup(smart_ptr).is_none() {
                match smart_ptr.as_str() {
                    "Rc" | "rc" | "std_rc_Rc" => Some(("rc", &args[1])),
                    "Arc" | "arc" | "std_sync_Arc" => Some(("arc", &args[1])),
                    _ => None,
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    if let Some((kind, arg_expr)) = smart_count_arg {
        if let Some(t_arg) = type_check_expr(scopes, errors, type_ctx, arg_expr) {
            let resolved_arg = type_ctx.infer.borrow_mut().resolve(t_arg.ty());
            let (unwrapped_expr, _) = match resolved_arg {
                Type::Ref(inner) | Type::MutRef(inner) => match t_arg {
                    TypedExpr::Ref(inner_e, _, _, _) => (*inner_e, *inner),
                    other => (
                        TypedExpr::Deref(Box::new(other), *inner, span.clone()),
                        *inner,
                    ),
                },
                other => (t_arg, other),
            };
            return Some(TypedExpr::Call(
                format!("{kind}_strong_count"),
                vec![unwrapped_expr],
                Type::Int,
                span.clone(),
            ));
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
        let pre_call_param_tys: Option<Vec<Type>> = if !is_method_syntax && raw_name != "__call_fn_ptr" {
            let norm = raw_name.replace("::", "_");
            if let Some(info) = scopes.lookup(raw_name).or_else(|| scopes.lookup(&norm)) {
                let resolved = type_ctx.infer.borrow_mut().resolve(info.ty);
                if let Type::FnPtr(ps, _) = resolved {
                    Some(ps.to_vec())
                } else {
                    None
                }
            } else {
                type_ctx
                    .get_fn(&norm)
                    .or_else(|| type_ctx.get_fn(raw_name))
                    .map(|f| f.params.iter().map(|p| p.ty).collect())
            }
        } else {
            None
        };

        let mut arg0_ctx = type_ctx.clone();
        if let Some(ref ps) = pre_call_param_tys {
            if let Some(&p0) = ps.first() {
                if !crate::sanal::compat::type_contains_generic(&p0) {
                    arg0_ctx.current_expected_type = Some(p0);
                }
            }
        }

        if let Some(first_arg) = type_check_expr(scopes, errors, &arg0_ctx, &args[0]) {
            let first_ty = type_ctx.infer.borrow_mut().resolve(first_arg.ty());
            typed_args.push(first_arg);

            let mut unwrapped_first = first_ty;
            while let Type::Ref(inner)
            | Type::MutRef(inner)
            | Type::Box(inner)
            | Type::Rc(inner)
            | Type::Arc(inner) = unwrapped_first
            {
                unwrapped_first = *inner;
            }

            let elem_ty = match &unwrapped_first {
                Type::Vec(inner) | Type::Slice(inner) | Type::Array(inner, _) => {
                    Some((**inner).clone())
                }
                _ => None,
            };

            let method_param_tys: Option<Vec<Type>> = if raw_name == "__call_fn_ptr" {
                if let Type::FnPtr(ps, _) = unwrapped_first {
                    let mut v = vec![first_ty];
                    v.extend_from_slice(ps);
                    Some(v)
                } else {
                    None
                }
            } else if pre_call_param_tys.is_some() {
                pre_call_param_tys
            } else if let Type::Obj(tn) | Type::Enum(tn) = unwrapped_first {
                let clean_m = raw_name.replace("::", "_");
                let mangled = format!("{tn}_{clean_m}");
                type_ctx
                    .get_fn(&mangled)
                    .map(|f| f.params.iter().map(|p| p.ty).collect())
            } else {
                None
            };

            for (idx, arg) in args[1..].iter().enumerate() {
                let expected_arg_ty = method_param_tys
                    .as_ref()
                    .and_then(|ps| ps.get(idx + 1).copied())
                    .filter(|t| !crate::sanal::compat::type_contains_generic(t));

                let mut arg_ctx = type_ctx.clone();
                arg_ctx.current_expected_type = expected_arg_ty;

                if let Expr::Closure(params, body, c_span) = arg {
                    let fallback_param_ty = match expected_arg_ty {
                        Some(Type::FnPtr(ps, _)) => ps.first().copied().unwrap_or(Type::Int),
                        _ => elem_ty.clone().unwrap_or(Type::Int),
                    };
                    typed_args.push(build_non_capturing_closure(
                        scopes,
                        errors,
                        &arg_ctx,
                        params,
                        fallback_param_ty,
                        body,
                        c_span,
                    ));
                } else if let Some(t_arg) = type_check_expr(scopes, errors, &arg_ctx, arg) {
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

    // Handle indirect function pointer call `(expr)(args...)` lowered to `__call_fn_ptr`
    if raw_name == "__call_fn_ptr" && !typed_args.is_empty() {
        let callee_ty = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
        if let Type::FnPtr(param_tys, ret_ty) = callee_ty {
            let supplied = typed_args.len() - 1;
            if supplied != param_tys.len() {
                errors.push(SemanticError {
                    code: "E0061",
                    message: format!(
                        "Function pointer expects {} argument(s), found {}",
                        param_tys.len(),
                        supplied
                    ),
                    label: format!("Expected {} argument(s)", param_tys.len()),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            } else {
                for (param_ty, arg) in param_tys.iter().zip(typed_args.iter_mut().skip(1)) {
                    if !param_ty.is_copy() && !matches!(param_ty, Type::Ref(_) | Type::MutRef(_)) {
                        type_ctx.check_not_moved_from_projection(arg, errors);
                        crate::sanal::compat::mark_expr_moved_if_ident(scopes, errors, arg);
                    }
                    let unify_res = type_ctx.infer.borrow_mut().unify(*param_ty, arg.ty());
                    let resolved_param = type_ctx.infer.borrow_mut().resolve(*param_ty);
                    let resolved_arg = type_ctx.infer.borrow_mut().resolve(arg.ty());
                    if unify_res.is_err()
                        && !crate::sanal::compat::is_type_compatible(&resolved_param, &resolved_arg)
                    {
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "Mismatched argument in function pointer call: expected `{:?}`, found `{:?}`",
                                resolved_param, resolved_arg
                            ),
                            label: format!("Expected `{:?}`", resolved_param),
                            secondary_label: None,
                            help: None,
                            span: arg.span(),
                        });
                    }
                }
            }
            let resolved_ret = type_ctx.infer.borrow_mut().resolve(*ret_ty);
            return Some(TypedExpr::Call(
                "__call_fn_ptr".to_string(),
                typed_args,
                resolved_ret,
                span.clone(),
            ));
        } else if callee_ty != Type::Error {
            errors.push(SemanticError {
                code: "E0618",
                message: format!("Expected function, found `{:?}`", callee_ty),
                label: "Not callable".to_string(),
                secondary_label: None,
                help: None,
                span: typed_args[0].span(),
            });
            return Some(TypedExpr::Call(
                "__call_fn_ptr".to_string(),
                typed_args,
                Type::Error,
                span.clone(),
            ));
        }
    }

    // Handle .clone() and .strong_count() on Box<T> / Rc<T> / Arc<T> smart pointers
    if (raw_name == "clone" || raw_name == "strong_count") && typed_args.len() == 1 {
        let first_ty = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
        let (unwrapped_arg, inner_ptr_ty) = match first_ty {
            Type::Ref(inner) | Type::MutRef(inner)
                if matches!(*inner, Type::Rc(_) | Type::Arc(_) | Type::Box(_)) =>
            {
                let orig = typed_args.remove(0);
                let derefed = match orig {
                    TypedExpr::Ref(inner_e, _, _, _) => *inner_e,
                    other => TypedExpr::Deref(Box::new(other), *inner, span.clone()),
                };
                (Some(derefed), *inner)
            }
            other => (None, other),
        };
        if let Some(u) = unwrapped_arg {
            typed_args.insert(0, u);
        }
        if raw_name == "clone" {
            match inner_ptr_ty {
                Type::Rc(_) => {
                    return Some(TypedExpr::Call(
                        "rc_clone".to_string(),
                        typed_args,
                        inner_ptr_ty,
                        span.clone(),
                    ));
                }
                Type::Arc(_) => {
                    return Some(TypedExpr::Call(
                        "arc_clone".to_string(),
                        typed_args,
                        inner_ptr_ty,
                        span.clone(),
                    ));
                }
                Type::Box(inner) => {
                    return Some(TypedExpr::Call(
                        "box_clone".to_string(),
                        typed_args,
                        Type::Box(inner),
                        span.clone(),
                    ));
                }
                _ => {}
            }
        } else if raw_name == "strong_count" {
            match inner_ptr_ty {
                Type::Rc(_) => {
                    return Some(TypedExpr::Call(
                        "rc_strong_count".to_string(),
                        typed_args,
                        Type::Int,
                        span.clone(),
                    ));
                }
                Type::Arc(_) => {
                    return Some(TypedExpr::Call(
                        "arc_strong_count".to_string(),
                        typed_args,
                        Type::Int,
                        span.clone(),
                    ));
                }
                _ => {}
            }
        }
    }

    // Handle built-in .len() and .is_empty() on slices, arrays, and str
    if (raw_name == "len" || raw_name == "is_empty") && typed_args.len() == 1 {
        let mut clean_ty = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
        while let Type::Ref(inner)
        | Type::MutRef(inner)
        | Type::Box(inner)
        | Type::Rc(inner)
        | Type::Arc(inner) = clean_ty
        {
            clean_ty = *inner;
        }
        if matches!(clean_ty, Type::Slice(_) | Type::Array(_, _) | Type::Str) {
            let ret_ty = if raw_name == "len" {
                Type::Int
            } else {
                Type::Bool
            };
            return Some(TypedExpr::Call(
                format!("__builtin_{raw_name}"),
                typed_args,
                ret_ty,
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
        let mut target_ty = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
        while let Type::Ref(inner)
        | Type::MutRef(inner)
        | Type::Box(inner)
        | Type::Rc(inner)
        | Type::Arc(inner) = target_ty
        {
            target_ty = *inner;
        }
        let type_name = match &target_ty {
            Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
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
        let mut t0 = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
        while let Type::Ref(inner)
        | Type::MutRef(inner)
        | Type::Box(inner)
        | Type::Rc(inner)
        | Type::Arc(inner) = t0
        {
            t0 = *inner;
        }
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
                    let recv_is_ref = matches!(recv.ty(), Type::Ref(_) | Type::MutRef(_));
                    let trait_self_ty = param_tys.first().copied().unwrap_or(Type::Unit);
                    let self_is_ref = matches!(trait_self_ty, Type::Ref(_) | Type::MutRef(_));
                    let self_is_non_consuming = m_name == "fmt"
                        || m_name == "to_string"
                        || (*ret_ty != Type::Unit && ret_ty.is_copy());

                    if !self_is_ref && !self_is_non_consuming {
                        if recv_is_ref {
                            errors.push(SemanticError {
                                code: "E0507",
                                message: format!("Cannot invoke consuming method `{m_name}` through a borrowed reference to `dyn {trait_name}`"),
                                label: "Cannot move out of borrowed `dyn` trait object".to_string(),
                                secondary_label: None,
                                help: Some("Bind an owned `dyn` object or change the trait method to take `&self`".to_string()),
                                span: recv.span(),
                            });
                        } else {
                            type_ctx.check_not_moved_from_projection(&recv, errors);
                            crate::sanal::compat::mark_expr_moved_if_ident(scopes, errors, &recv);
                        }
                    } else if matches!(trait_self_ty, Type::MutRef(_)) {
                        if let Some(root_var) = crate::sanal::compat::extract_root_var(&recv) {
                            if let Some((was_mut, holder)) = scopes.active_borrow(root_var) {
                                errors.push(SemanticError {
                                    code: if was_mut { "E0499" } else { "E0502" },
                                    message: format!("Cannot mutably borrow `{root_var}` for `{m_name}` while already borrowed by `{holder}`"),
                                    label: "Conflicting borrow on trait object".to_string(),
                                    secondary_label: None,
                                    help: None,
                                    span: recv.span(),
                                });
                            }
                        }
                    } else if let Some(root_var) = crate::sanal::compat::extract_root_var(&recv) {
                        if let Some((true, holder)) = scopes.active_borrow(root_var) {
                            errors.push(SemanticError {
                                code: "E0502",
                                message: format!("Cannot borrow `{root_var}` for `{m_name}` because it is mutably borrowed by `{holder}`"),
                                label: "Conflicting borrow on trait object".to_string(),
                                secondary_label: None,
                                help: None,
                                span: recv.span(),
                            });
                        }
                    }

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
                    Type::Vec(e) | Type::Slice(e) | Type::Array(e, _) => Some(*e),
                    Type::Obj(s) => crate::sanal::mono::lookup_mangled(s)
                        .and_then(|(_, args)| args.first().copied()),
                    Type::Ref(inner)
                    | Type::MutRef(inner)
                    | Type::Box(inner)
                    | Type::Rc(inner)
                    | Type::Arc(inner) => vec_elem_from_ty(*inner),
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
                    let _ = crate::sanal::mono::monomorphize_enum(
                        type_ctx.mono,
                        "std_core_Option",
                        &[elem_ty],
                        type_ctx.enum_map,
                        type_ctx.fn_map,
                        type_ctx.worklist,
                    );
                    ret_ty = Type::Obj(crate::ast::intern_str(&mangled_iter));
                }
            }
        }

        if resolved_name.ends_with("from_slice") && !typed_args.is_empty() {
            let mut arg_ty = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
            while let Type::Ref(inner) | Type::MutRef(inner) = arg_ty {
                arg_ty = *inner;
            }
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
        if let Type::FnPtr(param_tys, fn_ret_ty) = var_ty {
            if param_tys.len() != typed_args.len() {
                errors.push(SemanticError {
                    code: "E0061",
                    message: format!(
                        "Function pointer `{resolved_name}` expects {} argument(s), found {}",
                        param_tys.len(),
                        typed_args.len()
                    ),
                    label: format!("Expected {} argument(s)", param_tys.len()),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            } else {
                for (param_ty, arg) in param_tys.iter().zip(typed_args.iter_mut()) {
                    if !param_ty.is_copy() && !matches!(param_ty, Type::Ref(_) | Type::MutRef(_)) {
                        type_ctx.check_not_moved_from_projection(arg, errors);
                        crate::sanal::compat::mark_expr_moved_if_ident(scopes, errors, arg);
                    }
                    let unify_res = type_ctx.infer.borrow_mut().unify(*param_ty, arg.ty());
                    let resolved_param = type_ctx.infer.borrow_mut().resolve(*param_ty);
                    let resolved_arg = type_ctx.infer.borrow_mut().resolve(arg.ty());
                    if unify_res.is_err()
                        && !crate::sanal::compat::is_type_compatible(&resolved_param, &resolved_arg)
                    {
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "Mismatched argument in call to `{resolved_name}`: expected `{:?}`, found `{:?}`",
                                resolved_param, resolved_arg
                            ),
                            label: format!("Expected `{:?}`", resolved_param),
                            secondary_label: None,
                            help: None,
                            span: arg.span(),
                        });
                    }
                }
            }
            type_ctx.infer.borrow_mut().resolve(*fn_ret_ty)
        } else {
            errors.push(SemanticError {
                code: "E0618",
                message: format!(
                    "Expected function, found local variable `{resolved_name}` of type `{:?}`",
                    var_ty
                ),
                label: "Not callable".to_string(),
                secondary_label: None,
                help: Some("Only named functions, methods, function pointers, and inline closures are callable".to_string()),
                span: span.clone(),
            });
            Type::Error
        }
    } else if is_method_syntax && !typed_args.is_empty() {
        let recv_ty = type_ctx.infer.borrow_mut().resolve(typed_args[0].ty());
        if let Some((_, layout)) =
            crate::sanal::objects::construction::lookup_struct_layout_for_type(type_ctx, recv_ty)
        {
            if let Some((_, f_ty)) = layout.field_offsets.get(raw_name) {
                let resolved_f_ty = type_ctx.infer.borrow_mut().resolve(*f_ty);
                if let Type::FnPtr(param_tys, fn_ret_ty) = resolved_f_ty {
                    let recv_expr = typed_args.remove(0);
                    let field_callee = TypedExpr::FieldAccess(
                        Box::new(recv_expr),
                        raw_name.to_string(),
                        resolved_f_ty,
                        span.clone(),
                    );
                    if param_tys.len() != typed_args.len() {
                        errors.push(SemanticError {
                            code: "E0061",
                            message: format!(
                                "Function pointer field `{raw_name}` expects {} argument(s), found {}",
                                param_tys.len(),
                                typed_args.len()
                            ),
                            label: format!("Expected {} argument(s)", param_tys.len()),
                            secondary_label: None,
                            help: None,
                            span: span.clone(),
                        });
                    } else {
                        for (param_ty, arg) in param_tys.iter().zip(typed_args.iter_mut()) {
                            if !param_ty.is_copy()
                                && !matches!(param_ty, Type::Ref(_) | Type::MutRef(_))
                            {
                                type_ctx.check_not_moved_from_projection(arg, errors);
                                crate::sanal::compat::mark_expr_moved_if_ident(
                                    scopes, errors, arg,
                                );
                            }
                            let unify_res = type_ctx.infer.borrow_mut().unify(*param_ty, arg.ty());
                            let resolved_param = type_ctx.infer.borrow_mut().resolve(*param_ty);
                            let resolved_arg = type_ctx.infer.borrow_mut().resolve(arg.ty());
                            if unify_res.is_err()
                                && !crate::sanal::compat::is_type_compatible(
                                    &resolved_param,
                                    &resolved_arg,
                                )
                            {
                                errors.push(SemanticError {
                                    code: "E0308",
                                    message: format!(
                                        "Mismatched argument in call to field `{raw_name}`: expected `{:?}`, found `{:?}`",
                                        resolved_param, resolved_arg
                                    ),
                                    label: format!("Expected `{:?}`", resolved_param),
                                    secondary_label: None,
                                    help: None,
                                    span: arg.span(),
                                });
                            }
                        }
                    }
                    typed_args.insert(0, field_callee);
                    let resolved_ret = type_ctx.infer.borrow_mut().resolve(*fn_ret_ty);
                    return Some(TypedExpr::Call(
                        "__call_fn_ptr".to_string(),
                        typed_args,
                        resolved_ret,
                        span.clone(),
                    ));
                }
            }
        }
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

