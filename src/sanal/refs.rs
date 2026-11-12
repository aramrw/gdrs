//! sanal/refs.rs
//! Type checking for references (&, &mut) and dereferencing (*, *ptr = val).

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_ref<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    inner: &Expr,
    is_mut: bool,
    span: &Span,
) -> Option<TypedExpr> {
    let mut curr = inner;
    loop {
        match curr {
            Expr::FieldAccess(base, _, _)
            | Expr::IndexAccess(base, _, _)
            | Expr::Deref(base, _) => {
                curr = base.as_ref();
            }
            _ => break,
        }
    }
    let mut suppress_ident_borrow_err = false;
    if let Expr::Ident(var_name, _) = curr {
        if is_mut {
            if let Some(info) = scopes.lookup(var_name) {
                if !info.is_mutable && !matches!(info.ty, Type::MutRef(_) | Type::Ptr(_)) {
                    errors.push(SemanticError {
                        code: "E0596",
                        message: format!("Cannot borrow immutable variable `{var_name}` as mutable"),
                        label: "Cannot borrow as mutable".to_string(),
                        secondary_label: None,
                        help: Some(format!("Consider declaring `let mut {var_name}`")),
                        span: span.clone(),
                    });
                }
            }
            if let Some((was_mut, holder)) = scopes.active_borrow(var_name) {
                suppress_ident_borrow_err = true;
                errors.push(SemanticError {
                    code: if was_mut { "E0499" } else { "E0502" },
                    message: if was_mut {
                        format!("Cannot borrow `{var_name}` as mutable more than once at a time (already borrowed by `{holder}`)")
                    } else {
                        format!("Cannot borrow `{var_name}` as mutable because it is also borrowed as immutable by `{holder}`")
                    },
                    label: "Conflicting mutable borrow".to_string(),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
        }
    }
    let errs_before = errors.len();
    let t_inner = type_check_expr(scopes, errors, type_ctx, inner)?;
    if suppress_ident_borrow_err && errors.len() > errs_before {
        // Avoid duplicate E0502 emitted by type_check_ident for the same expression
        if errors.last().is_some_and(|e| e.code == "E0502") {
            errors.pop();
        }
    }
    let inner_ty = t_inner.ty();
    let ref_ty = if is_mut {
        Type::MutRef(crate::ast::intern_type(inner_ty))
    } else {
        Type::Ref(crate::ast::intern_type(inner_ty))
    };
    Some(TypedExpr::Ref(
        Box::new(t_inner),
        is_mut,
        ref_ty,
        span.clone(),
    ))
}

pub fn type_check_deref<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    inner: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_inner = type_check_expr(scopes, errors, type_ctx, inner)?;
    match t_inner.ty() {
        Type::Ptr(inner_ty) => {
            if !type_ctx.is_unsafe {
                errors.push(SemanticError {
                    code: "E0133",
                    message: "Dereference of raw pointer requires an 'unsafe:' block".to_string(),
                    label: "Raw pointer dereference requires 'unsafe:' block".to_string(),
                    secondary_label: None,
                    help: Some("Wrap this dereference inside an 'unsafe:' block".to_string()),
                    span: span.clone(),
                });
            }
            if *inner_ty == Type::Void {
                errors.push(SemanticError {
                    code: "E0614",
                    message: "Cannot dereference `*void`".to_string(),
                    label: "Cannot dereference untyped `*void` pointer".to_string(),
                    secondary_label: None,
                    help: Some("Cast to a typed pointer first (e.g. `ptr as *u8` or `ptr as *i64`)".to_string()),
                    span: span.clone(),
                });
                Some(TypedExpr::Deref(Box::new(t_inner), Type::Unit, span.clone()))
            } else {
                Some(TypedExpr::Deref(Box::new(t_inner), *inner_ty, span.clone()))
            }
        }
        Type::Rc(inner_ty) | Type::Arc(inner_ty) | Type::Ref(inner_ty) | Type::MutRef(inner_ty) => {
            if !inner_ty.is_copy() {
                errors.push(SemanticError {
                    code: "E0507",
                    message: format!(
                        "Cannot move out of dereferenced `{:?}` which is not `Copy`",
                        t_inner.ty()
                    ),
                    label: "Cannot move out of borrowed/shared content".to_string(),
                    secondary_label: None,
                    help: Some("Operate through the reference directly instead of moving the inner value out".to_string()),
                    span: span.clone(),
                });
            }
            Some(TypedExpr::Deref(Box::new(t_inner), *inner_ty, span.clone()))
        }
        other => {
            errors.push(SemanticError {
                code: "E0614",
                message: format!("Cannot dereference type `{:?}`", other),
                label: "Type cannot be dereferenced".to_string(),
                secondary_label: None,
                help: Some("Use raw pointer `*T`, `rc<T>`, `arc<T>`, or reference `&T`".to_string()),
                span: span.clone(),
            });
            Some(TypedExpr::Deref(
                Box::new(t_inner),
                Type::Unit,
                span.clone(),
            ))
        }
    }
}

pub fn type_check_deref_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    ptr: &Expr,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_ptr = type_check_expr(scopes, errors, type_ctx, ptr)?;
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;
    type_ctx.check_not_moved_from_projection(&t_val, errors);
    crate::sanal::compat::mark_expr_moved_if_ident(scopes, errors, &t_val);
    match t_ptr.ty() {
        Type::Ptr(inner_ty) => {
            if !type_ctx.is_unsafe {
                errors.push(SemanticError {
                    code: "E0133",
                    message: "Dereference assignment to raw pointer requires an 'unsafe:' block".to_string(),
                    label: "Raw pointer write requires 'unsafe:' block".to_string(),
                    secondary_label: None,
                    help: Some("Wrap this assignment inside an 'unsafe:' block".to_string()),
                    span: span.clone(),
                });
            }
            if *inner_ty == Type::Void {
                errors.push(SemanticError {
                    code: "E0614",
                    message: "Cannot dereference assign to `*void`".to_string(),
                    label: "Cannot dereference assign to untyped `*void` pointer".to_string(),
                    secondary_label: None,
                    help: Some("Cast to a typed pointer first (e.g. `ptr as *u8` or `ptr as *i64`)".to_string()),
                    span: span.clone(),
                });
            } else if !crate::sanal::compat::is_type_compatible(inner_ty, &t_val.ty()) {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched type in raw pointer write. Pointer holds `{:?}`, found `{:?}`",
                        *inner_ty,
                        t_val.ty()
                    ),
                    label: format!("Expected `{:?}`", *inner_ty),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
            Some(TypedExpr::DerefAssign(
                Box::new(t_ptr),
                Box::new(t_val),
                span.clone(),
            ))
        }
        Type::Ref(_) => {
            errors.push(SemanticError {
                code: "E0594",
                message: "Cannot assign through immutable reference `&T`".to_string(),
                label: "Immutable reference cannot be mutated".to_string(),
                secondary_label: None,
                help: Some("Use `&mut T` or `rc<T>` / `arc<T>` if mutation is needed".to_string()),
                span: span.clone(),
            });
            Some(TypedExpr::DerefAssign(
                Box::new(t_ptr),
                Box::new(t_val),
                span.clone(),
            ))
        }
        Type::Rc(inner_ty) | Type::Arc(inner_ty) | Type::MutRef(inner_ty) => {
            if !crate::sanal::compat::is_type_compatible(inner_ty, &t_val.ty()) {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched type in dereference assignment. Pointer holds `{:?}`, found `{:?}`",
                        *inner_ty,
                        t_val.ty()
                    ),
                    label: format!("Expected `{:?}`", *inner_ty),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
            Some(TypedExpr::DerefAssign(
                Box::new(t_ptr),
                Box::new(t_val),
                span.clone(),
            ))
        }
        other => {
            errors.push(SemanticError {
                code: "E0614",
                message: format!("Cannot dereference assign type `{:?}`", other),
                label: "Type cannot be dereferenced".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
            Some(TypedExpr::DerefAssign(
                Box::new(t_ptr),
                Box::new(t_val),
                span.clone(),
            ))
        }
    }
}
