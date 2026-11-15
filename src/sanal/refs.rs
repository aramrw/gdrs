//! sanal/refs.rs
//! Type checking for references (&, &mut) and dereferencing (*, *ptr = val).

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

fn validate_mut_deref_target<'a>(
    scopes: &ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    t_inner: &TypedExpr,
    span: &Span,
) {
    if let Some(var_name) = crate::sanal::compat::extract_root_var(t_inner) {
        if let Some((_, holder)) = scopes.active_borrow(var_name) {
            errors.push(SemanticError {
                code: "E0506",
                message: format!(
                    "Cannot mutably dereference `{var_name}` because it is borrowed by `{holder}`"
                ),
                label: "Mutable deref while borrowed".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        if let Some(info) = scopes.lookup(var_name) {
            if !info.is_mutable && !matches!(info.ty, Type::MutRef(_) | Type::Ptr(_)) {
                errors.push(SemanticError {
                    code: "E0596",
                    message: format!(
                        "Cannot mutably dereference immutable variable `{var_name}`"
                    ),
                    label: "Variable is immutable".to_string(),
                    secondary_label: None,
                    help: Some(format!("Declare as mutable: `let mut {var_name}`")),
                    span: span.clone(),
                });
            }
        }
    }
}

/// Lowers `Deref::deref(&self)` or `DerefMut::deref_mut(&mut self)` on a smart-pointer `Obj`.
/// Returns `(TypedExpr::Deref(Call(...), inner_ty), inner_ty)` on success.
pub(crate) fn try_lower_deref_target<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    t_inner: &TypedExpr,
    is_mut: bool,
    span: &Span,
) -> Option<(TypedExpr, Type)> {
    let resolved_ty = type_ctx.infer.borrow_mut().resolve(t_inner.ty());
    let struct_name = match resolved_ty {
        Type::Obj(s) => s,
        Type::Ref(inner) => match *inner {
            Type::Obj(s) if !is_mut => s,
            Type::Obj(_) => return None,
            _ => return None,
        },
        Type::MutRef(inner) => match *inner {
            Type::Obj(s) => s,
            _ => return None,
        },
        _ => return None,
    };
    let method = if is_mut { "deref_mut" } else { "deref" };
    let fn_info = crate::sanal::binops::lookup_struct_method_fn(type_ctx, struct_name, method)?;

    if is_mut {
        validate_mut_deref_target(scopes, errors, type_ctx, t_inner, span);
    }

    let mut self_arg = t_inner.clone();
    if let Some(first_param) = fn_info.params.first() {
        let arg_span = self_arg.span();
        match (first_param.ty, resolved_ty) {
            (Type::MutRef(_), Type::Obj(_)) => {
                self_arg = TypedExpr::Ref(
                    Box::new(self_arg),
                    true,
                    Type::MutRef(crate::ast::intern_type(resolved_ty)),
                    arg_span,
                );
            }
            (Type::Ref(_), Type::Obj(_)) => {
                self_arg = TypedExpr::Ref(
                    Box::new(self_arg),
                    false,
                    Type::Ref(crate::ast::intern_type(resolved_ty)),
                    arg_span,
                );
            }
            (Type::Ref(_), Type::MutRef(inner)) => {
                let derefed = TypedExpr::Deref(Box::new(self_arg), *inner, arg_span.clone());
                self_arg = TypedExpr::Ref(Box::new(derefed), false, Type::Ref(inner), arg_span);
            }
            _ => {}
        }
    }

    let mut call_args = vec![self_arg];
    crate::sanal::calls::validation::validate_call_arguments(
        &fn_info,
        &mut call_args,
        true,
        &fn_info.name,
        scopes,
        errors,
        type_ctx,
        span,
    );
    let ret_ty = type_ctx.infer.borrow_mut().resolve(fn_info.return_type);
    let elem_ty = match ret_ty {
        Type::MutRef(inner) if is_mut => *inner,
        Type::Ref(inner) | Type::MutRef(inner) if !is_mut => *inner,
        _ => return None,
    };
    let call_expr = TypedExpr::Call(fn_info.name.clone(), call_args, ret_ty, span.clone());
    let deref_expr = TypedExpr::Deref(Box::new(call_expr), elem_ty, span.clone());
    Some((deref_expr, elem_ty))
}

fn strip_ref_ty(mut ty: Type) -> Type {
    while let Type::Ref(inner) | Type::MutRef(inner) = ty {
        ty = *inner;
    }
    ty
}

/// Emits `E0793` if borrowing `expr` would create an unaligned reference into a `#[repr(packed)]` struct.
pub fn check_unaligned_packed_borrow(
    expr: &TypedExpr,
    type_ctx: &TypeCtx<'_>,
    errors: &mut Vec<SemanticError>,
    span: &Span,
) {
    let mut min_packed: Option<(u32, String, String)> = None;
    let mut curr = expr;
    loop {
        match curr {
            TypedExpr::FieldAccess(base, field_name, _, _) => {
                let base_ty = strip_ref_ty(type_ctx.infer.borrow_mut().probe(base.ty()));
                if let Type::Obj(struct_name) = base_ty {
                    if let Some(layout) = type_ctx.get_struct(struct_name) {
                        if let Some(pack) = layout.repr_packed {
                            let pack = pack.max(1);
                            if min_packed.as_ref().is_none_or(|(p, _, _)| pack < *p) {
                                min_packed = Some((pack, layout.name.clone(), field_name.clone()));
                            }
                        }
                    }
                }
                curr = base.as_ref();
            }
            TypedExpr::IndexAccess(base, _, _, _) => {
                let base_ty = strip_ref_ty(type_ctx.infer.borrow_mut().probe(base.ty()));
                if matches!(base_ty, Type::Array(_, _)) {
                    curr = base.as_ref();
                } else {
                    break;
                }
            }
            _ => break,
        }
    }

    let Some((pack_align, struct_name, field_name)) = min_packed else {
        return;
    };

    let target_ty = type_ctx.infer.borrow_mut().probe(expr.ty());
    if let Type::Obj(ts) = target_ty {
        let _ = type_ctx.get_struct(ts);
    }
    let enum_layout_map: crate::codegen::drops::EnumLayoutMap = type_ctx
        .enum_map
        .borrow()
        .iter()
        .map(|(k, (_, variants))| {
            let mut list: Vec<(String, i64, Vec<Type>)> = variants
                .iter()
                .map(|(vn, (tag, tys))| (vn.clone(), *tag, tys.clone()))
                .collect();
            list.sort_by_key(|(_, tag, _)| *tag);
            (k.clone(), list)
        })
        .collect();
    let struct_map = type_ctx.struct_map.borrow();
    let (_, target_align) =
        crate::codegen::layout::size_and_align(&target_ty, &struct_map, &enum_layout_map);
    if target_align > pack_align {
        errors.push(SemanticError {
            code: "E0793",
            message: format!(
                "Reference to packed field `{struct_name}.{field_name}` is unaligned (requires {target_align}-byte alignment, but `{struct_name}` is packed to {pack_align}-byte alignment)"
            ),
            label: "Unaligned reference to packed field".to_string(),
            secondary_label: None,
            help: Some(format!(
                "Copy the field into a local variable first (e.g. `let val = ...{field_name};`) before taking a reference"
            )),
            span: span.clone(),
        });
    }
}

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
        let borrow_path = crate::sanal::objects::fields::expr_projection_path(inner)
            .unwrap_or_else(|| var_name.clone());
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
            if let Some((was_mut, holder)) = scopes.active_borrow_including_projections(&borrow_path) {
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
    let t_inner = if let Expr::Deref(ptr_expr, d_span) = inner {
        let t_ptr = type_check_expr(scopes, errors, type_ctx, ptr_expr)?;
        let ptr_ty = type_ctx.infer.borrow_mut().probe(t_ptr.ty());
        let inner_ty_opt = match ptr_ty {
            Type::Ptr(i) | Type::Box(i) | Type::MutRef(i) => Some(*i),
            Type::Ref(i) | Type::Rc(i) | Type::Arc(i) => {
                if is_mut {
                    errors.push(SemanticError {
                        code: "E0596",
                        message: format!("Cannot mutably reborrow through immutable/shared `{ptr_ty:?}`"),
                        label: "Immutable reference".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                }
                Some(*i)
            }
            _ => None,
        };
        if let Some(deref_ty) = inner_ty_opt {
            TypedExpr::Deref(Box::new(t_ptr), deref_ty, d_span.clone())
        } else if let Some((deref_expr, _)) =
            try_lower_deref_target(scopes, errors, type_ctx, &t_ptr, is_mut, d_span)
        {
            deref_expr
        } else {
            type_check_expr(scopes, errors, type_ctx, inner)?
        }
    } else {
        type_check_expr(scopes, errors, type_ctx, inner)?
    };
    if suppress_ident_borrow_err && errors.len() > errs_before {
        // Avoid duplicate E0502 emitted by type_check_ident for the same expression
        if errors.last().is_some_and(|e| e.code == "E0502") {
            errors.pop();
        }
    }
    if is_mut {
        type_ctx.check_static_lvalue_mutable(&t_inner, "E0596", errors, span);
    }
    let inner_ty = t_inner.ty();
    check_unaligned_packed_borrow(&t_inner, type_ctx, errors, span);
    let is_range_slice = matches!(
        &t_inner,
        TypedExpr::IndexAccess(_, idx, _, _)
            if matches!(idx.as_ref(), TypedExpr::Range(..))
                || matches!(idx.ty(), Type::Obj("Range"))
    );
    let ref_ty = if is_range_slice {
        match inner_ty {
            Type::Slice(elem_ty) => {
                if is_mut {
                    Type::MutRef(crate::ast::intern_type(Type::Slice(elem_ty)))
                } else {
                    Type::Slice(elem_ty)
                }
            }
            Type::Str => {
                if is_mut {
                    errors.push(SemanticError {
                        code: "E0596",
                        message: "Cannot take a mutable slice of `str` or `String`".to_string(),
                        label: "Mutable string slicing is not supported".to_string(),
                        secondary_label: None,
                        help: Some("Use an immutable slice `&s[start..end]` instead".to_string()),
                        span: span.clone(),
                    });
                }
                Type::Str
            }
            other => {
                if is_mut {
                    Type::MutRef(crate::ast::intern_type(other))
                } else {
                    Type::Ref(crate::ast::intern_type(other))
                }
            }
        }
    } else if is_mut {
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
    let resolved_inner_ty = type_ctx.infer.borrow_mut().resolve(t_inner.ty());
    match resolved_inner_ty {
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
        Type::Box(inner_ty) => {
            Some(TypedExpr::Deref(Box::new(t_inner), *inner_ty, span.clone()))
        }
        Type::Rc(inner_ty) | Type::Arc(inner_ty) | Type::Ref(inner_ty) | Type::MutRef(inner_ty) => {
            if !inner_ty.is_copy() {
                errors.push(SemanticError {
                    code: "E0507",
                    message: format!(
                        "Cannot move out of dereferenced `{:?}` which is not `Copy`",
                        resolved_inner_ty
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
            if let Some((deref_expr, elem_ty)) =
                try_lower_deref_target(scopes, errors, type_ctx, &t_inner, false, span)
            {
                if !elem_ty.is_copy() {
                    errors.push(SemanticError {
                        code: "E0507",
                        message: format!(
                            "Cannot move out of dereferenced `{:?}` which is not `Copy`",
                            resolved_inner_ty
                        ),
                        label: "Cannot move out of borrowed/shared content".to_string(),
                        secondary_label: None,
                        help: Some("Operate through `&*...` instead of moving the inner value out".to_string()),
                        span: span.clone(),
                    });
                }
                return Some(deref_expr);
            }
            errors.push(SemanticError {
                code: "E0614",
                message: format!("Cannot dereference type `{:?}`", other),
                label: "Type cannot be dereferenced".to_string(),
                secondary_label: None,
                help: Some("Use raw pointer `*T`, `Box<T>`, `Rc<T>`, `Arc<T>`, or reference `&T`".to_string()),
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
    let resolved_ptr_ty = type_ctx.infer.borrow_mut().resolve(t_ptr.ty());
    match resolved_ptr_ty {
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
                help: Some("Use `&mut T` or `Box<T>` if mutation is needed".to_string()),
                span: span.clone(),
            });
            Some(TypedExpr::DerefAssign(
                Box::new(t_ptr),
                Box::new(t_val),
                span.clone(),
            ))
        }
        Type::Box(inner_ty) => {
            if let Some(var_name) = crate::sanal::compat::extract_root_var(&t_ptr) {
                if let Some((_, holder)) = scopes.active_borrow(var_name) {
                    errors.push(SemanticError {
                        code: "E0506",
                        message: format!(
                            "Cannot assign to `*{var_name}` because `{var_name}` is borrowed by `{holder}`"
                        ),
                        label: "Assignment while borrowed".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                }
                if let Some(info) = scopes.lookup(var_name) {
                    if !info.is_mutable && !matches!(info.ty, Type::MutRef(_) | Type::Ptr(_)) {
                        errors.push(SemanticError {
                            code: "E0596",
                            message: format!(
                                "Cannot assign through immutable `Box` variable `{var_name}`"
                            ),
                            label: "Variable is immutable".to_string(),
                            secondary_label: None,
                            help: Some(format!("Declare as mutable: `let mut {var_name}`")),
                            span: span.clone(),
                        });
                    }
                }
            }
            let unify_res = type_ctx.infer.borrow_mut().unify(*inner_ty, t_val.ty());
            let resolved_expected = type_ctx.infer.borrow_mut().resolve(*inner_ty);
            let resolved_found = type_ctx.infer.borrow_mut().resolve(t_val.ty());
            if unify_res.is_err()
                && !crate::sanal::compat::is_type_compatible(&resolved_expected, &resolved_found)
            {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched type in dereference assignment. `Box` holds `{:?}`, found `{:?}`",
                        resolved_expected,
                        resolved_found
                    ),
                    label: format!("Expected `{:?}`", resolved_expected),
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
        Type::Rc(inner_ty) | Type::Arc(inner_ty) | Type::MutRef(inner_ty) => {
            let unify_res = type_ctx.infer.borrow_mut().unify(*inner_ty, t_val.ty());
            let resolved_expected = type_ctx.infer.borrow_mut().resolve(*inner_ty);
            let resolved_found = type_ctx.infer.borrow_mut().resolve(t_val.ty());
            if unify_res.is_err()
                && !crate::sanal::compat::is_type_compatible(&resolved_expected, &resolved_found)
            {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched type in dereference assignment. Pointer holds `{:?}`, found `{:?}`",
                        resolved_expected,
                        resolved_found
                    ),
                    label: format!("Expected `{:?}`", resolved_expected),
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
            if let Some((TypedExpr::Deref(call_expr, elem_ty, _), _)) =
                try_lower_deref_target(scopes, errors, type_ctx, &t_ptr, true, span)
            {
                let unify_res = type_ctx.infer.borrow_mut().unify(elem_ty, t_val.ty());
                let resolved_expected = type_ctx.infer.borrow_mut().resolve(elem_ty);
                let resolved_found = type_ctx.infer.borrow_mut().resolve(t_val.ty());
                if unify_res.is_err()
                    && !crate::sanal::compat::is_type_compatible(&resolved_expected, &resolved_found)
                {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Mismatched type in dereference assignment. `DerefMut` target holds `{:?}`, found `{:?}`",
                            resolved_expected, resolved_found
                        ),
                        label: format!("Expected `{:?}`", resolved_expected),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                }
                return Some(TypedExpr::DerefAssign(call_expr, Box::new(t_val), span.clone()));
            }
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
