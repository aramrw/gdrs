//! sanal/calls.rs
//! Type checking for function calls, method calls, macro calls, and closures.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_macro_call<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    name: &str,
    args: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    if (name == "thread" || name == "spawn") && args.len() == 2 {
        if let Expr::Closure(params, body, c_span) = &args[0] {
            if let Some(t_arg1) = type_check_expr(scopes, errors, type_ctx, &args[1]) {
                static CLOSURE_COUNTER: std::sync::atomic::AtomicUsize =
                    std::sync::atomic::AtomicUsize::new(0);
                let closure_name = format!(
                    "__closure_{}",
                    CLOSURE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
                );

                scopes.push_scope();
                let param_ty = t_arg1.ty();
                let mut typed_params = Vec::new();
                for p in params {
                    scopes.declare(p.clone(), false, param_ty);
                    typed_params.push((p.clone(), param_ty));
                }

                let t_body = type_check_expr(scopes, errors, type_ctx, body)
                    .unwrap_or(TypedExpr::Int(0, c_span.clone()));
                scopes.pop_scope();

                let t_closure = TypedExpr::Closure(
                    closure_name,
                    typed_params,
                    Box::new(t_body),
                    Type::Int,
                    c_span.clone(),
                );
                return Some(TypedExpr::MacroCall(
                    name.to_string(),
                    vec![t_closure, t_arg1],
                    Type::Int,
                    span.clone(),
                ));
            }
        }
    }

    let mut typed_args = Vec::new();
    for arg in args {
        if let Some(t_arg) = type_check_expr(scopes, errors, type_ctx, arg) {
            typed_args.push(t_arg);
        }
    }
    let macro_ret_ty = match name.trim_end_matches('!') {
        "format" | "arg_at" | "args_at" | "args" => Type::Str,
        "arg_count" | "args_count" | "thread" | "spawn" | "len" => Type::Int,
        _ => Type::Unit,
    };
    Some(TypedExpr::MacroCall(
        name.to_string(),
        typed_args,
        macro_ret_ty,
        span.clone(),
    ))
}

pub fn type_check_call<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    raw_name: &str,
    args: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
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
                    static CLOSURE_COUNTER: std::sync::atomic::AtomicUsize =
                        std::sync::atomic::AtomicUsize::new(0);
                    let closure_name = format!(
                        "__closure_{}",
                        CLOSURE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
                    );

                    scopes.push_scope();
                    let mut typed_params = Vec::new();
                    for p in params {
                        scopes.declare(p.clone(), false, closure_elem_ty.clone());
                        typed_params.push((p.clone(), closure_elem_ty.clone()));
                    }

                    let t_body = type_check_expr(scopes, errors, type_ctx, body)
                        .unwrap_or(TypedExpr::Int(0, c_span.clone()));
                    scopes.pop_scope();

                    let ret_ty = t_body.ty();
                    typed_args.push(TypedExpr::Closure(
                        closure_name,
                        typed_params,
                        Box::new(t_body),
                        ret_ty,
                        c_span.clone(),
                    ));
                } else if let Some(t_arg) = type_check_expr(scopes, errors, type_ctx, arg) {
                    typed_args.push(t_arg);
                }
            }
        }
    }

    let normalized_name = match raw_name {
        "Some" => "std_core_Option_Some".to_string(),
        "None" => "std_core_Option_None".to_string(),
        "Ok" => "std_core_Result_Ok".to_string(),
        "Err" => "std_core_Result_Err".to_string(),
        _ => raw_name.replace("::", "_"),
    };
    if let Some((enum_name, variant_name)) = normalized_name.rsplit_once('_') {
        let found_enum = type_ctx
            .enum_map
            .iter()
            .find(|(k, _)| *k == enum_name || k.ends_with(&format!("_{enum_name}")));
        if let Some((_, (static_enum_name, variants))) = found_enum {
            if let Some((disc, _)) = variants.get(variant_name) {
                return Some(TypedExpr::EnumConstruct(
                    static_enum_name.to_string(),
                    variant_name.to_string(),
                    *disc as usize,
                    typed_args,
                    Type::Enum(static_enum_name),
                    span.clone(),
                ));
            }
        }
    }

    let mut name = raw_name.replace("::", "_");
    let is_intrinsic_macro = matches!(
        name.as_str(),
        "log"
            | "log!"
            | "println"
            | "println!"
            | "print"
            | "print!"
            | "assert"
            | "assert!"
            | "assert_eq"
            | "assert_eq!"
            | "panic"
            | "panic!"
            | "format"
            | "format!"
            | "vec"
            | "vec!"
            | "push"
            | "push_str"
            | "pop"
            | "len"
            | "arg_count"
            | "arg_at"
            | "args_count"
            | "args_at"
            | "args"
            | "thread"
            | "thread!"
            | "spawn!"
    );
    if is_intrinsic_macro {
        if name == "push" || name == "push_str" || name == "pop" {
            if let Some(first_arg) = typed_args.first() {
                if let TypedExpr::Ident(var_name, _, _) = first_arg {
                    if let Some(var_info) = scopes.lookup_mut(var_name) {
                        if !var_info.is_mutable {
                            errors.push(SemanticError {
                                code: "E0382",
                                message: format!(
                                    "Cannot call mutating macro '{name}' on immutable variable '{var_name}'"
                                ),
                                label: format!("'{var_name}' is immutable"),
                                secondary_label: None,
                                help: Some(format!("Declare as mutable: 'let mut {var_name}'")),
                                span: span.clone(),
                            });
                        }
                        if name == "push" && typed_args.len() > 1 {
                            let elem_ty = typed_args[1].ty();
                            var_info.ty = Type::Vec(crate::ast::intern_type(elem_ty));
                        }
                    }
                }
            }
        }
        let macro_ret_ty = match name.trim_end_matches('!') {
            "format" | "arg_at" | "args_at" | "args" => Type::Str,
            "arg_count" | "args_count" | "thread" | "spawn" | "len" => Type::Int,
            "vec" => {
                let elem_ty = if !typed_args.is_empty() {
                    typed_args[0].ty()
                } else {
                    Type::Int
                };
                Type::Vec(crate::ast::intern_type(elem_ty))
            }
            _ => Type::Unit,
        };
        return Some(TypedExpr::MacroCall(
            name,
            typed_args,
            macro_ret_ty,
            span.clone(),
        ));
    }

    let mut resolved_name = name.clone();
    let split_sep = if name.contains("::") {
        Some("::")
    } else if name.contains('.') {
        Some(".")
    } else {
        None
    };
    if let Some(sep) = split_sep {
        let split_res = if sep == "." {
            name.rsplit_once('.')
        } else {
            name.split_once(sep)
        };
        if let Some((target_or_var, method_name)) = split_res {
            if method_name == "len"
                || method_name == "push"
                || method_name == "pop"
                || method_name == "push_str"
            {
                if let Some(target_info) = scopes.lookup_mut(target_or_var) {
                    if (method_name == "push" || method_name == "push_str" || method_name == "pop")
                        && !target_info.is_mutable
                    {
                        errors.push(SemanticError {
                            code: "E0382",
                            message: format!(
                                "Cannot call mutating method '{method_name}' on immutable variable '{target_or_var}'"
                            ),
                            label: format!("'{target_or_var}' is immutable"),
                            secondary_label: None,
                            help: Some(format!("Declare as mutable: 'let mut {target_or_var}'")),
                            span: span.clone(),
                        });
                    }

                    if method_name == "push" && !typed_args.is_empty() {
                        let arg_ty = typed_args[0].ty();
                        target_info.ty = Type::Vec(crate::ast::intern_type(arg_ty));
                    }
                }
                let target_ast = if target_or_var.contains('.') {
                    Expr::Call(target_or_var.to_string(), vec![], span.clone())
                } else {
                    Expr::Ident(target_or_var.to_string(), span.clone())
                };
                if let Some(target_expr) =
                    type_check_expr(scopes, errors, type_ctx, &target_ast)
                {
                    typed_args.insert(0, target_expr);
                    let macro_ret_ty = match method_name {
                        "len" => Type::Int,
                        _ => Type::Unit,
                    };
                    return Some(TypedExpr::MacroCall(
                        method_name.to_string(),
                        typed_args,
                        macro_ret_ty,
                        span.clone(),
                    ));
                }
            }
            let short_target = target_or_var.split("::").last().unwrap_or(target_or_var);
            let mangled = format!("{}_{}", target_or_var.replace("::", "_"), method_name);
            let short_mangled = format!("{}_{}", short_target, method_name);
            let found_fn = type_ctx.fn_map.iter().find(|(k, _)| {
                **k == mangled
                    || **k == short_mangled
                    || k.ends_with(&format!("_{mangled}"))
                    || k.ends_with(&format!("_{short_mangled}"))
            });
            if let Some((mangled_fn_name, target_func)) = found_fn {
                resolved_name = mangled_fn_name.clone();
                let expects_self = target_func
                    .params
                    .first()
                    .map(|p| p.name == "self")
                    .unwrap_or(false);
                if expects_self {
                    let target_ast = if target_or_var.contains('.') {
                        Expr::Call(target_or_var.to_string(), vec![], span.clone())
                    } else {
                        Expr::Ident(target_or_var.to_string(), span.clone())
                    };
                    if let Some(target_expr) =
                        type_check_expr(scopes, errors, type_ctx, &target_ast)
                    {
                        typed_args.insert(0, target_expr);
                    }
                }
            } else {
                let target_ast = if target_or_var.contains('.') {
                    Expr::Call(target_or_var.to_string(), vec![], span.clone())
                } else {
                    Expr::Ident(target_or_var.to_string(), span.clone())
                };
                if let Some(target_expr) =
                    type_check_expr(scopes, errors, type_ctx, &target_ast)
                {
                    if typed_args.is_empty() || typed_args[0].span() != target_expr.span() {
                        typed_args.insert(0, target_expr);
                    }
                }
                name = method_name.to_string();
            }
        }
    } else if !type_ctx.fn_map.contains_key(&name) && !typed_args.is_empty() {
        let target_ty = typed_args[0].ty();
        match target_ty {
            Type::Obj(tn) | Type::Enum(tn) => {
                let method_mangled = format!("{tn}_{name}");
                if type_ctx.fn_map.contains_key(&method_mangled) {
                    resolved_name = method_mangled;
                }
            }
            _ => {}
        }
        if let Type::DynTrait(_trait_name) = typed_args[0].ty() {
            let receiver = typed_args.remove(0);
            return Some(TypedExpr::DynCall(
                Box::new(receiver),
                name,
                typed_args,
                Type::Bool,
                span.clone(),
            ));
        }
        if let TypedExpr::Ident(target_name, _, _) = &typed_args[0] {
            if target_name == "rc" && name == "new" {
                typed_args.remove(0);
                if typed_args.len() != 1 {
                    errors.push(SemanticError {
                        code: "E0061",
                        message: "rc.new expects exactly 1 argument".to_string(),
                        label: "Invalid argument count".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                    return Some(TypedExpr::Int(0, span.clone()));
                }
                let inner_ty = typed_args[0].ty();
                let rc_ty = Type::Rc(crate::ast::intern_type(inner_ty));
                return Some(TypedExpr::Call(
                    "rc_new".to_string(),
                    typed_args,
                    rc_ty,
                    span.clone(),
                ));
            }

            if target_name == "arc" && name == "new" {
                typed_args.remove(0);
                if typed_args.len() != 1 {
                    errors.push(SemanticError {
                        code: "E0061",
                        message: "arc.new expects exactly 1 argument".to_string(),
                        label: "Invalid argument count".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                    return Some(TypedExpr::Int(0, span.clone()));
                }
                let inner_ty = typed_args[0].ty();
                let arc_ty = Type::Arc(crate::ast::intern_type(inner_ty));
                return Some(TypedExpr::Call(
                    "arc_new".to_string(),
                    typed_args,
                    arc_ty,
                    span.clone(),
                ));
            }

            let normalized_target = match typed_args[0].ty() {
                Type::Obj(s_name) | Type::Enum(s_name) => s_name.to_string(),
                _ => {
                    if let TypedExpr::Ident(target_name, _, _) = &typed_args[0] {
                        target_name.replace("::", "_")
                    } else {
                        "".to_string()
                    }
                }
            };
            let mangled = format!("{}_{}", normalized_target, name);
            let found_mangled = if type_ctx.fn_map.contains_key(&mangled) {
                Some(mangled.clone())
            } else if let Some((k, _)) = type_ctx.fn_map.iter().find(|(k, _)| {
                let short_target = normalized_target.split('_').last().unwrap_or("");
                let short_mangled = format!("{short_target}_{name}");
                **k == short_mangled || k.ends_with(&format!("_{short_mangled}"))
            }) {
                Some(k.clone())
            } else {
                None
            };

            if let Some(mangled_fn) = found_mangled {
                resolved_name = mangled_fn;
                let short_target =
                    normalized_target.split('_').last().unwrap_or(&normalized_target);
                if type_ctx.struct_map.contains_key(&normalized_target)
                    || type_ctx.enum_map.contains_key(&normalized_target)
                    || type_ctx.struct_map.contains_key(short_target)
                    || type_ctx.enum_map.contains_key(short_target)
                {
                    if let TypedExpr::Ident(id, _, _) = &typed_args[0] {
                        let short_id = id.split("::").last().unwrap_or(id);
                        if id == &normalized_target || short_id == short_target {
                            typed_args.remove(0);
                        }
                    }
                }
            }
        }

        if name == "clone" && !typed_args.is_empty() {
            match typed_args[0].ty() {
                Type::Rc(inner_ty) => {
                    return Some(TypedExpr::Call(
                        "rc_clone".to_string(),
                        typed_args,
                        Type::Rc(inner_ty),
                        span.clone(),
                    ));
                }
                Type::Arc(inner_ty) => {
                    return Some(TypedExpr::Call(
                        "arc_clone".to_string(),
                        typed_args,
                        Type::Arc(inner_ty),
                        span.clone(),
                    ));
                }
                _ => {}
            }
        }

        if name == "push" && !typed_args.is_empty() {
            let elem_ty = typed_args.last().unwrap().ty();
            if let TypedExpr::Ident(var_name, _, _) = &typed_args[0] {
                if let Some(target_info) = scopes.lookup_mut(var_name) {
                    if !target_info.is_mutable {
                        errors.push(SemanticError {
                            code: "E0382",
                            message: format!(
                                "Cannot call mutating method 'push' on immutable variable '{var_name}'"
                            ),
                            label: format!("'{var_name}' is immutable"),
                            secondary_label: None,
                            help: Some(format!("Declare as mutable: 'let mut {var_name}'")),
                            span: span.clone(),
                        });
                    }
                    target_info.ty = Type::Vec(crate::ast::intern_type(elem_ty));
                }
            }
            return Some(TypedExpr::MacroCall(
                "push".to_string(),
                typed_args,
                Type::Unit,
                span.clone(),
            ));
        }

        if name == "iter" && !typed_args.is_empty() {
            let target_ty = typed_args[0].ty();
            match target_ty {
                Type::Obj(s_name) if s_name == "Range" => {
                    return Some(typed_args.remove(0));
                }
                Type::Vec(_) | Type::Ref(_) | Type::MutRef(_) => {
                    return Some(typed_args.remove(0));
                }
                _ => {}
            }
        }

        if name == "map" && !typed_args.is_empty() {
            return Some(TypedExpr::Call(
                "intrinsic_iter_map".to_string(),
                typed_args,
                Type::Obj(crate::ast::intern_str("MapIter")),
                span.clone(),
            ));
        }

        if name == "for_each" && !typed_args.is_empty() {
            let target_ty = typed_args[0].ty();
            let deref_ty = match &target_ty {
                Type::Ref(inner) | Type::MutRef(inner) => (**inner).clone(),
                other => other.clone(),
            };
            if deref_ty == Type::Obj(crate::ast::intern_str("MapIter")) {
                return Some(TypedExpr::Call(
                    "intrinsic_map_for_each".to_string(),
                    typed_args,
                    Type::Unit,
                    span.clone(),
                ));
            } else if matches!(deref_ty, Type::Vec(_)) {
                return Some(TypedExpr::Call(
                    "intrinsic_vec_for_each".to_string(),
                    typed_args,
                    Type::Unit,
                    span.clone(),
                ));
            } else {
                return Some(TypedExpr::Call(
                    "intrinsic_iter_for_each".to_string(),
                    typed_args,
                    Type::Unit,
                    span.clone(),
                ));
            }
        }

        if !type_ctx.extern_fn_names.contains(&resolved_name)
            && !type_ctx.fn_map.contains_key(&resolved_name)
        {
            let norm = resolved_name.replace("::", "_");
            if let Some((found_fn_name, _)) = type_ctx
                .fn_map
                .iter()
                .find(|(k, _)| **k == norm || k.ends_with(&format!("_{norm}")))
            {
                resolved_name = found_fn_name.clone();
            }
            if !typed_args.is_empty() {
                let first_arg_ty = typed_args[0].ty();
                let type_name = match first_arg_ty {
                    Type::Obj(n) => Some(n),
                    Type::Enum(n) => Some(n),
                    _ => None,
                };
                if let Some(tn) = type_name {
                    let mangled = format!("{}_{}", tn, name);
                    let mono_mangled = format!("{}_{}", name, tn);
                    if type_ctx.fn_map.contains_key(&mangled) {
                        resolved_name = mangled;
                    } else if type_ctx.fn_map.contains_key(&mono_mangled) {
                        resolved_name = mono_mangled;
                    }
                }
            }
        }
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

    let ret_ty = if scopes.lookup(&resolved_name).is_some() {
        Type::Int
    } else if let Some(target_func) = type_ctx.fn_map.get(&resolved_name) {
        if target_func.params.len() != typed_args.len() && !typed_args.is_empty() {
            if (target_func.params.is_empty() || target_func.params[0].name != "self")
                && target_func.params.len() == typed_args.len() - 1
            {
                typed_args.remove(0);
            }
        }
        if target_func.params.len() != typed_args.len() {
            errors.push(SemanticError {
                code: "E0061",
                message: format!(
                    "Function '{resolved_name}' expects {} arguments, found {}",
                    target_func.params.len(),
                    typed_args.len()
                ),
                label: format!("Expected {} args", target_func.params.len()),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        if target_func.params.len() == typed_args.len() {
            for (param, arg) in target_func.params.iter().zip(typed_args.iter_mut()) {
                match (param.ty, arg.ty()) {
                    (Type::MutRef(expected), actual) if actual == *expected => {
                        let arg_span = arg.span();
                        *arg = TypedExpr::Ref(
                            Box::new(arg.clone()),
                            true,
                            Type::MutRef(expected),
                            arg_span,
                        );
                    }
                    (Type::Ref(expected), actual) if actual == *expected => {
                        let arg_span = arg.span();
                        *arg = TypedExpr::Ref(
                            Box::new(arg.clone()),
                            false,
                            Type::Ref(expected),
                            arg_span,
                        );
                    }
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
                if let Type::DynTrait(t_name) = param.ty {
                    *arg = TypedExpr::CoerceToDyn(Box::new(arg.clone()), t_name, span.clone());
                }
            }
        }
        if matches!(target_func.return_type, Type::Generic(_)) {
            Type::Int
        } else {
            target_func.return_type
        }
    } else if let Some((param_decl_types, ext_ret_ty)) =
        type_ctx.extern_signatures.get(&resolved_name)
    {
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
        }
        *ext_ret_ty
    } else {
        errors.push(SemanticError {
            code: "E0425",
            message: format!("Undefined function '{resolved_name}' (raw: '{raw_name}')"),
            label: "Function does not exist".to_string(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
        Type::Unit
    };

    Some(TypedExpr::Call(
        resolved_name,
        typed_args,
        ret_ty,
        span.clone(),
    ))
}

pub fn type_check_closure<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    params: &[String],
    body: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    static CLOSURE_COUNTER: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);
    let closure_name = format!(
        "__closure_{}",
        CLOSURE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    );

    scopes.push_scope();
    let mut typed_params = Vec::new();
    for p in params {
        scopes.declare(p.clone(), false, Type::Int);
        typed_params.push((p.clone(), Type::Int));
    }

    let t_body = type_check_expr(scopes, errors, type_ctx, body)
        .unwrap_or(TypedExpr::Int(0, span.clone()));
    scopes.pop_scope();

    Some(TypedExpr::Closure(
        closure_name,
        typed_params,
        Box::new(t_body),
        Type::Int,
        span.clone(),
    ))
}
