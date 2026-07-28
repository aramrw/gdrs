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
            if let Expr::Ident(arg_name, _) = arg {
                if let Some(info) = scopes.lookup(arg_name) {
                    if !info.ty.is_copy() {
                        scopes.mark_moved(arg_name);
                    }
                }
            }
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
    if !args.is_empty() {
        if let Expr::Ident(ref struct_name, _) = args[0] {
            if scopes.lookup(struct_name).is_none()
                && (type_ctx.contains_struct(struct_name) || type_ctx.contains_enum(struct_name))
            {
                let static_name = format!("{struct_name}::{raw_name}");
                let mangled = format!("{struct_name}_{raw_name}");
                if type_ctx.contains_fn(&mangled) || type_ctx.contains_fn(&static_name) {
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

            if raw_name.ends_with("push") && typed_args.len() >= 2 {
                if let Expr::Ident(vec_var_name, _) = &args[0] {
                    let pushed_ty = typed_args[1].ty();
                    if pushed_ty != Type::Int && pushed_ty != Type::Unit {
                        let new_vec_ty = Type::Vec(crate::ast::intern_type(pushed_ty));
                        if let Some(info) = scopes.lookup_mut(vec_var_name) {
                            info.ty = new_vec_ty;
                        }
                        if let TypedExpr::Ident(_, t_ty, _) = &mut typed_args[0] {
                            *t_ty = new_vec_ty;
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
        || raw_name.starts_with("std_core_");

    if is_enum_candidate {
        let normalized_name = match raw_name {
            "Some" | "Option::Some" | "Option_Some" => "std_core_Option_Some".to_string(),
            "None" | "Option::None" | "Option_None" => "std_core_Option_None".to_string(),
            "Ok" | "Result::Ok" | "Result_Ok" => "std_core_Result_Ok".to_string(),
            "Err" | "Result::Err" | "Result_Err" => "std_core_Result_Err".to_string(),
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
    let is_obj_method = if !typed_args.is_empty() {
        let type_name = match typed_args[0].ty() {
            Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
            Type::Ref(inner) | Type::MutRef(inner) => match inner {
                Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
                _ => None,
            },
            _ => None,
        };
        if let Some(tn) = type_name {
            let mangled = format!("{tn}_{name}");
            type_ctx.contains_fn(&mangled)
        } else {
            false
        }
    } else {
        false
    };

    let is_intrinsic_macro = !is_obj_method && matches!(
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
            | "push_str"
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
        let clean_macro = name.trim_end_matches('!');
        if (clean_macro == "push" || clean_macro == "push_str") && typed_args.len() >= 2 {
            if let TypedExpr::Ident(vec_var_name, _, _) = &typed_args[0] {
                let elem_ty = typed_args[1].ty();
                if elem_ty != Type::Int && elem_ty != Type::Unit {
                    if let Some(info) = scopes.lookup_mut(vec_var_name) {
                        info.ty = Type::Vec(crate::ast::intern_type(elem_ty));
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

    // 1. Check if first argument is a receiver target for method lookup `target.method(...)`
    if !typed_args.is_empty() {
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
        .map(|f| f.params.iter().any(|p| matches!(p.ty, Type::Generic(_))))
        .unwrap_or(false);

    // 2. Auto-monomorphize static method calls like `Vec2_new(1.0, 2.0)` or `Vec3_new(1.0, 2.0, 3.0)`
    if resolved_name == name || !type_ctx.contains_fn(&resolved_name) || is_generic_fn {
        let target_type = if !typed_args.is_empty() {
            match typed_args[0].ty() {
                Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
                Type::Vec(_) => Some("Vec".to_string()),
                Type::String => Some("String".to_string()),
                _ => None,
            }
        } else {
            None
        };

        let (base_struct, method_name) = if let Some((bs, mn)) = name.rsplit_once('_') {
            (bs.to_string(), mn.to_string())
        } else if let Some(ref tt) = target_type {
            (tt.clone(), name.clone())
        } else {
            (String::new(), String::new())
        };

        if !base_struct.is_empty() {
            let mut type_args = Vec::new();
            if !typed_args.is_empty() {
                if let Type::Vec(inner) = typed_args[0].ty() {
                    type_args.push(*inner);
                }
            }
            if type_args.is_empty() && !typed_args.is_empty() {
                if let Type::Obj(obj_name) = typed_args[0].ty() {
                    let name_str = obj_name.to_string();
                    if let Some((_, suffix)) = name_str.rsplit_once('_') {
                        if type_ctx.contains_struct(suffix) || type_ctx.contains_enum(suffix) {
                            type_args.push(Type::Obj(crate::ast::intern_str(suffix)));
                        }
                    }
                }
            }
            if type_args.is_empty() {
                let actual_args = if !typed_args.is_empty() && matches!(typed_args[0].ty(), Type::Obj(_) | Type::Enum(_)) {
                    &typed_args[1..]
                } else {
                    &typed_args[..]
                };
                for a in actual_args {
                    let t = a.ty();
                    if !matches!(t, Type::Unit) && !type_args.contains(&t) {
                        type_args.push(t);
                    }
                }
            }
            if !type_args.is_empty() {
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
                    if let Some(target_func) = type_ctx.get_fn(&mangled_fn) {
                        resolved_name = target_func.name;
                    }
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

    let ret_ty = if let Some(target_func) = type_ctx.get_fn(&resolved_name) {
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
                if param.name != "self" && !param.ty.is_copy() && !matches!(param.ty, Type::Ref(_) | Type::MutRef(_)) {
                    if let TypedExpr::Ident(arg_name, _, _) = arg {
                        scopes.mark_moved(arg_name);
                    }
                }
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
    } else if scopes.lookup(&resolved_name).is_some() {
        Type::Int
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
