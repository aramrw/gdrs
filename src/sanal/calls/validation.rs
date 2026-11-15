//! sanal/calls/validation.rs
//! Argument type validation, borrow checking, and automatic borrowing for function and method calls.

use crate::{
    ast::{FuncDecl, Span, Type, TypedExpr},
    sanal::{types::TypeCtx, ScopeStack, SemanticError},
};

/// Returns true when a method's `self` parameter acts as an implicit borrow rather than moving ownership.
pub fn is_non_consuming_self_method(
    fn_name: &str,
    params: &[crate::ast::Param],
    return_type: Type,
    trait_methods: &std::collections::HashMap<String, Vec<(String, Vec<Type>, Type)>>,
    trait_impls: &std::collections::HashSet<(String, String)>,
) -> bool {
    let is_non_drop_trait_copy_method = !params.is_empty()
        && params[0].name == "self"
        && return_type != Type::Unit
        && return_type.is_copy()
        && fn_name.rsplit_once('_').is_some_and(|(ty_prefix, m_name)| {
            trait_impls.iter().any(|(imp_ty, tr_name)| {
                !tr_name.ends_with("Drop")
                    && *tr_name != "Drop"
                    && (imp_ty == ty_prefix
                        || ty_prefix.ends_with(&format!("_{imp_ty}"))
                        || imp_ty.ends_with(&format!("_{ty_prefix}")))
                    && trait_methods
                        .get(tr_name)
                        .or_else(|| {
                            trait_methods
                                .iter()
                                .find(|(k, _)| k.ends_with(&format!("_{tr_name}")))
                                .map(|(_, v)| v)
                        })
                        .is_some_and(|ms| ms.iter().any(|(mn, _, _)| mn == m_name))
            })
        });
    fn_name.ends_with("_drop")
        || fn_name.ends_with("_fmt")
        || (fn_name.ends_with("_to_string") && !fn_name.ends_with("read_to_string"))
        || is_non_drop_trait_copy_method
}

pub fn validate_call_arguments<'a>(
    target_func: &FuncDecl,
    typed_args: &mut Vec<TypedExpr>,
    is_method_syntax: bool,
    resolved_name: &str,
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) {
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
        let is_non_consuming_self_fn = is_non_consuming_self_method(
            resolved_name,
            &target_func.params,
            target_func.return_type,
            type_ctx.trait_methods,
            type_ctx.trait_impls,
        );
        let mut call_borrows: Vec<(String, bool)> = Vec::new();
        let mut call_moved: Vec<String> = Vec::new();
        let mut call_val_reads: Vec<String> = Vec::new();

        for (arg_idx, (param, arg)) in
            target_func.params.iter().zip(typed_args.iter_mut()).enumerate()
        {
            let is_receiver = is_method_syntax && arg_idx == 0;
            let param_moves_arg = if param.name == "self" {
                !is_non_consuming_self_fn
                    && !matches!(param.ty, Type::Ref(_) | Type::MutRef(_))
                    && type_ctx.has_drop_ownership(&param.ty)
            } else {
                !param.ty.is_copy() && !matches!(param.ty, Type::Ref(_) | Type::MutRef(_))
            };

            // Auto-deref smart pointer receiver (`Box<T>`, `Rc<T>`, `Arc<T>`) when method expects `T`, `&T`, or `&mut T`,
            // or Deref coercion on `&Box<T>` / `&Rc<T>` / `&Arc<T>` -> `&T` (and `&mut Box<T>` -> `&mut T`) for any argument.
            {
                let resolved_arg_ty = type_ctx.infer.borrow_mut().resolve(arg.ty());
                let resolved_param_ty = type_ctx.infer.borrow_mut().resolve(param.ty);
                let param_unwrapped = match resolved_param_ty {
                    Type::Ref(inner) | Type::MutRef(inner) => *inner,
                    other => other,
                };
                if !matches!(param_unwrapped, Type::Box(_) | Type::Rc(_) | Type::Arc(_)) {
                    if is_receiver {
                        let smart_inner = match resolved_arg_ty {
                            Type::Box(inner) | Type::Rc(inner) | Type::Arc(inner) => {
                                Some((resolved_arg_ty, *inner, false))
                            }
                            Type::Ref(outer) | Type::MutRef(outer) => match *outer {
                                Type::Box(inner) | Type::Rc(inner) | Type::Arc(inner) => {
                                    Some((*outer, *inner, true))
                                }
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some((smart_ty, inner_ty, was_ref)) = smart_inner {
                            if matches!(smart_ty, Type::Rc(_) | Type::Arc(_))
                                && matches!(resolved_param_ty, Type::MutRef(_))
                            {
                                errors.push(SemanticError {
                                    code: "E0596",
                                    message: format!(
                                        "Cannot borrow content of `{}` as mutable",
                                        crate::sanal::compat::format_type(&smart_ty)
                                    ),
                                    label: "Shared smart pointer cannot be mutably borrowed".to_string(),
                                    secondary_label: None,
                                    help: Some("Use `Box<T>` or an owned `mut` binding for mutation".to_string()),
                                    span: arg.span(),
                                });
                            }
                            if matches!(smart_ty, Type::Rc(_) | Type::Arc(_)) && param_moves_arg {
                                errors.push(SemanticError {
                                    code: "E0507",
                                    message: format!(
                                        "Cannot move out of `{}` in consuming method `{resolved_name}`",
                                        crate::sanal::compat::format_type(&smart_ty)
                                    ),
                                    label: "Cannot move out of shared pointer".to_string(),
                                    secondary_label: None,
                                    help: None,
                                    span: arg.span(),
                                });
                            }
                            let arg_span = arg.span();
                            let base_smart = if was_ref {
                                TypedExpr::Deref(Box::new(arg.clone()), smart_ty, arg_span.clone())
                            } else {
                                arg.clone()
                            };
                            *arg = TypedExpr::Deref(Box::new(base_smart), inner_ty, arg_span);
                        }
                    } else if matches!(resolved_param_ty, Type::Ref(_) | Type::MutRef(_)) {
                        if let Type::Ref(outer) | Type::MutRef(outer) = resolved_arg_ty {
                            if let Type::Box(inner) | Type::Rc(inner) | Type::Arc(inner) = *outer {
                                let is_mut_param = matches!(resolved_param_ty, Type::MutRef(_));
                                if is_mut_param && matches!(*outer, Type::Rc(_) | Type::Arc(_)) {
                                    errors.push(SemanticError {
                                        code: "E0596",
                                        message: format!(
                                            "Cannot borrow content of `{}` as mutable",
                                            crate::sanal::compat::format_type(outer)
                                        ),
                                        label: "Shared smart pointer cannot be mutably borrowed"
                                            .to_string(),
                                        secondary_label: None,
                                        help: None,
                                        span: arg.span(),
                                    });
                                }
                                let arg_span = arg.span();
                                let smart_expr = match arg.clone() {
                                    TypedExpr::Ref(inner_e, _, _, _) => *inner_e,
                                    other => {
                                        TypedExpr::Deref(Box::new(other), *outer, arg_span.clone())
                                    }
                                };
                                let derefed_inner =
                                    TypedExpr::Deref(Box::new(smart_expr), *inner, arg_span.clone());
                                let coerced_ref_ty = if is_mut_param {
                                    Type::MutRef(inner)
                                } else {
                                    Type::Ref(inner)
                                };
                                *arg = TypedExpr::Ref(
                                    Box::new(derefed_inner),
                                    is_mut_param,
                                    coerced_ref_ty,
                                    arg_span,
                                );
                            }
                        }
                    }
                }
            }

            // Check cross-argument aliasing and move conflicts within this call
            match param.ty {
                Type::MutRef(_) | Type::Ref(_) => {
                    let is_mut_borrow = matches!(param.ty, Type::MutRef(_));
                    let borrowed_var = match &*arg {
                        TypedExpr::Ref(inner, _, _, _) => {
                            crate::sanal::compat::extract_root_var(inner).map(|s| s.to_string())
                        }
                        TypedExpr::Ident(v, ty, _)
                            if matches!(ty, Type::Ref(_) | Type::MutRef(_)) =>
                        {
                            scopes.borrow_target(v)
                        }
                        other => {
                            crate::sanal::compat::extract_root_var(other).map(|s| s.to_string())
                        }
                    };
                    if let Some(root_var) = borrowed_var {
                        if call_moved.iter().any(|m| m == &root_var) {
                            errors.push(SemanticError {
                                code: "E0382",
                                message: format!(
                                    "Borrow of moved value `{root_var}` across arguments of call"
                                ),
                                label: "Value already moved by an earlier argument".to_string(),
                                secondary_label: None,
                                help: None,
                                span: arg.span(),
                            });
                        } else if is_mut_borrow {
                            if let Some((_, was_mut)) =
                                call_borrows.iter().find(|(v, _)| v == &root_var)
                            {
                                errors.push(SemanticError {
                                    code: if *was_mut { "E0499" } else { "E0502" },
                                    message: if *was_mut {
                                        format!("Cannot borrow `{root_var}` as mutable more than once at a time in this call")
                                    } else {
                                        format!("Cannot borrow `{root_var}` as mutable because it is also borrowed as immutable in this call")
                                    },
                                    label: "Conflicting mutable borrow in call".to_string(),
                                    secondary_label: None,
                                    help: None,
                                    span: arg.span(),
                                });
                            } else if call_val_reads.iter().any(|r| r == &root_var) {
                                errors.push(SemanticError {
                                    code: "E0502",
                                    message: format!(
                                        "Cannot borrow `{root_var}` as mutable because it is also used by value in this call"
                                    ),
                                    label: "Conflicting mutable borrow in call".to_string(),
                                    secondary_label: None,
                                    help: None,
                                    span: arg.span(),
                                });
                            }
                        } else if call_borrows
                            .iter()
                            .any(|(v, was_mut)| v == &root_var && *was_mut)
                        {
                            errors.push(SemanticError {
                                code: "E0502",
                                message: format!(
                                    "Cannot borrow `{root_var}` as immutable because it is also borrowed as mutable in this call"
                                ),
                                label: "Conflicting borrow in call".to_string(),
                                secondary_label: None,
                                help: None,
                                span: arg.span(),
                            });
                        }
                        call_borrows.push((root_var, is_mut_borrow));
                    }
                }
                _ => {
                    if param_moves_arg {
                        if let TypedExpr::Ident(arg_name, _, arg_span) = arg {
                            if call_moved.iter().any(|m| m == arg_name) {
                                errors.push(SemanticError {
                                    code: "E0382",
                                    message: format!("Use of moved value '{arg_name}'"),
                                    label: "Value already moved by an earlier argument in this call".to_string(),
                                    secondary_label: None,
                                    help: None,
                                    span: arg_span.clone(),
                                });
                            }
                            if call_borrows.iter().any(|(v, _)| v == arg_name) {
                                errors.push(SemanticError {
                                    code: "E0505",
                                    message: format!(
                                        "Cannot move out of `{arg_name}` because it is borrowed in this call"
                                    ),
                                    label: "Move while borrowed in call".to_string(),
                                    secondary_label: None,
                                    help: None,
                                    span: arg_span.clone(),
                                });
                            }
                            call_moved.push(arg_name.clone());
                        }
                    } else if let Some(root_var) = crate::sanal::compat::extract_root_var(arg) {
                        let root_owned = root_var.to_string();
                        if call_borrows
                            .iter()
                            .any(|(v, was_mut)| v == &root_owned && *was_mut)
                        {
                            errors.push(SemanticError {
                                code: "E0502",
                                message: format!(
                                    "Cannot use `{root_owned}` because it is also mutably borrowed in this call"
                                ),
                                label: "Conflicting use while mutably borrowed".to_string(),
                                secondary_label: None,
                                help: None,
                                span: arg.span(),
                            });
                        }
                        call_val_reads.push(root_owned);
                    }
                }
            }

            if param_moves_arg {
                type_ctx.check_not_moved_from_projection(arg, errors);
                crate::sanal::compat::mark_expr_moved_if_ident(scopes, errors, arg);
            }
            let mut reported_borrow_err = false;
            match (param.ty, arg.ty()) {
                (Type::MutRef(_), Type::MutRef(_)) => {}
                (Type::MutRef(_), Type::Ref(_)) => {
                    errors.push(SemanticError {
                        code: "E0596",
                        message: "Cannot borrow immutable `&T` reference as `&mut T`"
                            .to_string(),
                        label: "Cannot borrow as mutable".to_string(),
                        secondary_label: None,
                        help: Some("Pass an `&mut` reference or a `mut` variable".to_string()),
                        span: arg.span(),
                    });
                }
                (Type::MutRef(expected), actual)
                    if is_receiver && crate::sanal::compat::is_type_compatible(expected, &actual) =>
                {
                    if let Some(var_name) = crate::sanal::compat::extract_root_var(arg) {
                        let var_owned = var_name.to_string();
                        if let Some(info) = scopes.lookup(&var_owned) {
                            if !info.is_mutable && !matches!(info.ty, Type::MutRef(_) | Type::Ptr(_)) {
                                errors.push(SemanticError {
                                    code: "E0596",
                                    message: format!(
                                        "Cannot borrow immutable variable `{var_owned}` as mutable"
                                    ),
                                    label: "Cannot borrow as mutable".to_string(),
                                    secondary_label: None,
                                    help: Some(format!("Declare as mutable: `let mut {var_owned}`")),
                                    span: arg.span(),
                                });
                            }
                        }
                        if let Some((was_mut, holder)) = scopes.active_borrow(&var_owned) {
                            errors.push(SemanticError {
                                code: if was_mut { "E0499" } else { "E0502" },
                                message: format!(
                                    "Cannot borrow `{var_owned}` as mutable because it is already borrowed by `{holder}`"
                                ),
                                label: "Conflicting mutable borrow".to_string(),
                                secondary_label: None,
                                help: None,
                                span: arg.span(),
                            });
                        }
                    } else {
                        type_ctx.check_static_lvalue_mutable(arg, "E0596", errors, &arg.span());
                    }
                    let arg_span = arg.span();
                    crate::sanal::refs::check_unaligned_packed_borrow(arg, type_ctx, errors, &arg_span);
                    *arg = TypedExpr::Ref(
                        Box::new(arg.clone()),
                        true,
                        Type::MutRef(expected),
                        arg_span,
                    );
                }
                (Type::Ref(_), Type::Ref(_) | Type::MutRef(_)) => {}
                (Type::Ref(expected), actual)
                    if is_receiver && crate::sanal::compat::is_type_compatible(expected, &actual) =>
                {
                    if let Some(var_name) = crate::sanal::compat::extract_root_var(arg) {
                        let var_owned = var_name.to_string();
                        if let Some((true, holder)) = scopes.active_borrow(&var_owned) {
                            errors.push(SemanticError {
                                code: "E0502",
                                message: format!(
                                    "Cannot borrow `{var_owned}` as immutable because it is also borrowed as mutable by `{holder}`"
                                ),
                                label: "Immutable borrow occurs here".to_string(),
                                secondary_label: None,
                                help: None,
                                span: arg.span(),
                            });
                        }
                    } else {
                        type_ctx.check_static_lvalue_mutable(arg, "E0596", errors, &arg.span());
                    }
                    let arg_span = arg.span();
                    crate::sanal::refs::check_unaligned_packed_borrow(arg, type_ctx, errors, &arg_span);
                    *arg = TypedExpr::Ref(
                        Box::new(arg.clone()),
                        false,
                        Type::Ref(expected),
                        arg_span,
                    );
                }
                (Type::MutRef(expected), actual) | (Type::Ref(expected), actual)
                    if crate::sanal::compat::is_type_compatible(expected, &actual) =>
                {
                    let is_mut = matches!(param.ty, Type::MutRef(_));
                    let prefix = if is_mut { "&mut " } else { "&" };
                    let resolved_param = type_ctx.infer.borrow_mut().resolve(param.ty);
                    let resolved_arg = type_ctx.infer.borrow_mut().resolve(actual);
                    let help_expr = match &*arg {
                        TypedExpr::Ident(name, _, _) => format!("{prefix}{name}"),
                        _ => format!("{prefix}<expr>"),
                    };
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Mismatched types: expected `{}`, found `{}`",
                            crate::sanal::compat::format_type(&resolved_param),
                            crate::sanal::compat::format_type(&resolved_arg),
                        ),
                        label: "Expected a reference".to_string(),
                        secondary_label: None,
                        help: Some(format!("Consider borrowing here: `{help_expr}`")),
                        span: arg.span(),
                    });
                    reported_borrow_err = true;
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
                type_ctx.validate_dyn_coercion(&arg.ty(), t_name, &arg.span(), errors);
                *arg = TypedExpr::CoerceToDyn(Box::new(arg.clone()), t_name, span.clone());
            }
                let is_slice_iter_call = is_receiver
                    && (resolved_name.ends_with("_into_iter") || resolved_name.ends_with("_iter"))
                    && matches!(
                        arg.ty(),
                        Type::Slice(_)
                            | Type::Array(_, _)
                            | Type::Ref(Type::Slice(_))
                            | Type::MutRef(Type::Slice(_))
                            | Type::Ref(Type::Array(_, _))
                            | Type::MutRef(Type::Array(_, _))
                    );
                if !reported_borrow_err && !is_slice_iter_call {
                    let unify_res = type_ctx.infer.borrow_mut().unify(param.ty, arg.ty());
                    let resolved_param = type_ctx.infer.borrow_mut().resolve(param.ty);
                    let resolved_arg = type_ctx.infer.borrow_mut().resolve(arg.ty());
                let is_string_borrow_as_str = resolved_param == Type::Str
                    && matches!(
                        resolved_arg,
                        Type::String | Type::Obj("String") | Type::Obj("std_string_String")
                    );
                if !is_string_borrow_as_str
                    && unify_res.is_err()
                    && !crate::sanal::compat::is_type_compatible(&resolved_param, &resolved_arg)
                {
                    if matches!(resolved_param, Type::FnPtr(..))
                        && matches!(resolved_arg, Type::Obj(cname) if cname.starts_with("__Closure_"))
                    {
                        errors.push(SemanticError {
                            code: "E0434",
                            message: format!(
                                "Cannot coerce capturing closure `{resolved_arg:?}` to function pointer `{resolved_param:?}` in call to `{resolved_name}`"
                            ),
                            label: "Closures can only be coerced to `fn` pointers if they capture no variables".to_string(),
                            secondary_label: None,
                            help: Some("Use a non-capturing closure or parameterize over `where F: Fn(...) -> ...`".to_string()),
                            span: arg.span(),
                        });
                    } else {
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "Mismatched type for parameter `{}` in call to `{resolved_name}`: expected `{:?}`, found `{:?}`",
                                param.name,
                                resolved_param,
                                resolved_arg
                            ),
                            label: format!("Expected `{:?}`", resolved_param),
                            secondary_label: None,
                            help: None,
                            span: arg.span(),
                        });
                    }
                }
            }
        }

        // Detect conflicting simultaneous borrows of the same variable in a single call
        let mut arg_borrows: Vec<(&str, bool, Span)> = Vec::new();
        for arg in typed_args.iter() {
            if let TypedExpr::Ref(inner, is_mut, _, a_span) = arg {
                if let Some(root) = crate::sanal::compat::extract_root_var(inner) {
                    if let Some((_, prev_mut, _)) =
                        arg_borrows.iter().find(|(r, pm, _)| *r == root && (*is_mut || *pm))
                    {
                        let both_mut = *is_mut && *prev_mut;
                        errors.push(SemanticError {
                            code: if both_mut { "E0499" } else { "E0502" },
                            message: if both_mut {
                                format!("Cannot borrow `{root}` as mutable more than once in the same call")
                            } else {
                                format!("Cannot borrow `{root}` as both mutable and immutable in the same call")
                            },
                            label: "Conflicting borrow in call".to_string(),
                            secondary_label: None,
                            help: None,
                            span: a_span.clone(),
                        });
                    } else {
                        arg_borrows.push((root, *is_mut, a_span.clone()));
                    }
                }
            }
        }
    }
}
