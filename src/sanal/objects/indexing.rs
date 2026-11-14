//! sanal/objects/indexing.rs
//! Type checking for array/tuple initialization and indexing operations.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        compat::{is_type_compatible, mark_expr_moved_if_ident},
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_array_init<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    elems: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    let mut typed_elems = Vec::new();
    for e in elems {
        if let Some(te) = type_check_expr(scopes, errors, type_ctx, e) {
            type_ctx.check_not_moved_from_projection(&te, errors);
            mark_expr_moved_if_ident(scopes, errors, &te);
            typed_elems.push(te);
        }
    }

    let elem_ty = if !typed_elems.is_empty() {
        typed_elems[0].ty()
    } else {
        type_ctx
            .infer
            .borrow_mut()
            .fresh(span.clone(), "element type of array")
    };

    for (i, elem) in typed_elems.iter().enumerate().skip(1) {
        let unify_res = type_ctx.infer.borrow_mut().unify(elem_ty, elem.ty());
        if unify_res.is_err() && !is_type_compatible(&elem_ty, &elem.ty()) {
            let resolved_expected = type_ctx.infer.borrow_mut().resolve(elem_ty);
            let resolved_found = type_ctx.infer.borrow_mut().resolve(elem.ty());
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Array elements must all have the same type. Expected `{:?}`, element {} has type `{:?}`",
                    resolved_expected,
                    i + 1,
                    resolved_found
                ),
                label: format!("Expected `{:?}`", resolved_expected),
                secondary_label: None,
                help: Some("Arrays are homogeneous and cannot hold mixed types".into()),
                span: elem.span().clone(),
            });
        }
    }

    let resolved_elem = type_ctx.infer.borrow_mut().resolve(elem_ty);
    let arr_ty = Type::Array(crate::ast::intern_type(resolved_elem), typed_elems.len());
    Some(TypedExpr::ArrayInit(typed_elems, arr_ty, span.clone()))
}

pub fn type_check_tuple_init<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    elems: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
    if elems.is_empty() {
        return Some(TypedExpr::TupleInit(Vec::new(), Type::Unit, span.clone()));
    }

    let expected_elems = type_ctx.current_expected_type.and_then(|exp| {
        let resolved = type_ctx.infer.borrow_mut().probe(exp);
        if let Type::Tuple(tys) = resolved {
            Some(tys.to_vec())
        } else {
            None
        }
    });

    let mut typed_elems = Vec::with_capacity(elems.len());
    let mut elem_tys = Vec::with_capacity(elems.len());
    for (i, e) in elems.iter().enumerate() {
        let mut elem_ctx = type_ctx.clone();
        elem_ctx.current_expected_type = expected_elems.as_ref().and_then(|v| v.get(i).copied());
        if let Some(te) = type_check_expr(scopes, errors, &elem_ctx, e) {
            type_ctx.check_not_moved_from_projection(&te, errors);
            mark_expr_moved_if_ident(scopes, errors, &te);
            let mut resolved_ty = type_ctx.infer.borrow_mut().resolve(te.ty());
            if let Some(exp_ty) = elem_ctx.current_expected_type {
                if matches!(
                    (exp_ty, resolved_ty),
                    (Type::I32, Type::Int) | (Type::F32, Type::Float)
                ) {
                    resolved_ty = exp_ty;
                }
            }
            elem_tys.push(resolved_ty);
            typed_elems.push(te);
        }
    }
    let tuple_ty = Type::Tuple(crate::ast::intern_tuple(&elem_tys));
    Some(TypedExpr::TupleInit(typed_elems, tuple_ty, span.clone()))
}

pub fn type_check_index_access<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    idx: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;

    let resolved_idx_ty = type_ctx.infer.borrow_mut().probe(t_idx.ty());
    let is_range = matches!(resolved_idx_ty, Type::Obj("Range"))
        || matches!(t_idx, TypedExpr::Range(..));

    let mut resolved_target = type_ctx.infer.borrow_mut().resolve(t_target.ty());
    while let Type::Ref(inner)
    | Type::MutRef(inner)
    | Type::Box(inner)
    | Type::Rc(inner)
    | Type::Arc(inner) = resolved_target
    {
        resolved_target = *inner;
    }
    let target_ty = resolved_target;

    if is_range {
        if let TypedExpr::Range(ref s_expr, ref e_expr, _, _, _) = t_idx {
            for bound_expr in [s_expr.as_ref(), e_expr.as_ref()] {
                let b_ty = type_ctx.infer.borrow_mut().probe(bound_expr.ty());
                if matches!(b_ty, Type::Infer(_)) {
                    let _ = type_ctx.infer.borrow_mut().unify(Type::Int, b_ty);
                } else if !b_ty.is_integer() {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Slice range bound must be an integer, found `{:?}`",
                            b_ty
                        ),
                        label: "Invalid slice range bound type".into(),
                        secondary_label: None,
                        help: None,
                        span: bound_expr.span(),
                    });
                }
            }
        }
        let slice_ty = match target_ty {
            Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => Type::Slice(e_ty),
            Type::Str
            | Type::String
            | Type::Obj("String")
            | Type::Obj("std_string_String") => Type::Str,
            Type::Obj(s) if s.contains("Vec") => {
                let e_ty = crate::sanal::mono::lookup_mangled(s)
                    .and_then(|(_, t_args)| t_args.first().copied())
                    .unwrap_or(Type::Int);
                Type::Slice(crate::ast::intern_type(e_ty))
            }
            other_ty => {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!("Cannot range-slice non-sliceable type `{:?}`", other_ty),
                    label: "Cannot slice this type".into(),
                    secondary_label: None,
                    help: None,
                    span: t_target.span().clone(),
                });
                Type::Slice(crate::ast::intern_type(Type::Int))
            }
        };
        return Some(TypedExpr::IndexAccess(
            Box::new(t_target),
            Box::new(t_idx),
            slice_ty,
            span.clone(),
        ));
    }

    if let Type::Obj(s) = target_ty {
        if let Some(fn_info) = crate::sanal::binops::lookup_struct_method_fn(type_ctx, s, "index")
        {
            let mut self_arg = t_target.clone();
            if let Some(first_param) = fn_info.params.first() {
                let expected_self = type_ctx.infer.borrow_mut().probe(first_param.ty);
                let actual_self = type_ctx.infer.borrow_mut().probe(self_arg.ty());
                if matches!(expected_self, Type::Ref(_)) {
                    if let Some(root_var) = crate::sanal::compat::extract_root_var(&self_arg) {
                        if let Some((true, holder)) = scopes.active_borrow(root_var) {
                            errors.push(SemanticError {
                                code: "E0502",
                                message: format!(
                                    "Cannot borrow `{root_var}` as immutable because it is also borrowed as mutable by `{holder}`"
                                ),
                                label: "Immutable borrow occurs here".to_string(),
                                secondary_label: None,
                                help: None,
                                span: self_arg.span(),
                            });
                        }
                    }
                    let arg_span = self_arg.span();
                    if matches!(actual_self, Type::MutRef(_)) {
                        if let Type::MutRef(inner) = actual_self {
                            let derefed = TypedExpr::Deref(Box::new(self_arg), *inner, arg_span.clone());
                            self_arg = TypedExpr::Ref(
                                Box::new(derefed),
                                false,
                                Type::Ref(inner),
                                arg_span,
                            );
                        }
                    } else if !matches!(actual_self, Type::Ref(_)) {
                        self_arg = TypedExpr::Ref(
                            Box::new(self_arg),
                            false,
                            Type::Ref(crate::ast::intern_type(target_ty)),
                            arg_span,
                        );
                    }
                }
            }
            let mut idx_arg = t_idx.clone();
            if fn_info.params.len() >= 2 {
                crate::sanal::binops::auto_borrow_op_arg_if_ref(
                    fn_info.params[1].ty,
                    &mut idx_arg,
                    scopes,
                    errors,
                    type_ctx,
                );
            }
            let mut call_args = vec![self_arg, idx_arg];
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
            let call_expr = TypedExpr::Call(fn_info.name.clone(), call_args, ret_ty, span.clone());
            return match ret_ty {
                Type::Ref(inner) | Type::MutRef(inner) => {
                    Some(TypedExpr::Deref(Box::new(call_expr), *inner, span.clone()))
                }
                _ => Some(call_expr),
            };
        }
    }

    if matches!(resolved_idx_ty, Type::Infer(_)) {
        let _ = type_ctx.infer.borrow_mut().unify(Type::Int, resolved_idx_ty);
    } else if !resolved_idx_ty.is_integer() {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Array index must be an integer, found `{:?}`", resolved_idx_ty),
            label: "Invalid index type".into(),
            secondary_label: None,
            help: None,
            span: t_idx.span().clone(),
        });
    }

    let elem_ty = match target_ty {
        Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => *e_ty,
        Type::Obj(s) => {
            if let Some((_, t_args)) = crate::sanal::mono::lookup_mangled(s) {
                t_args.first().copied().unwrap_or(Type::Int)
            } else {
                Type::Int
            }
        }
        other_ty => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Cannot index into non-array type `{:?}`", other_ty),
                label: "Not an array".into(),
                secondary_label: None,
                help: None,
                span: t_target.span().clone(),
            });
            Type::Int
        }
    };

    Some(TypedExpr::IndexAccess(
        Box::new(t_target),
        Box::new(t_idx),
        elem_ty,
        span.clone(),
    ))
}

pub fn type_check_index_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    idx: &Expr,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;
    type_ctx.check_not_moved_from_projection(&t_val, errors);
    mark_expr_moved_if_ident(scopes, errors, &t_val);

    let mut curr = target;
    while let Expr::FieldAccess(inner, _, _) | Expr::IndexAccess(inner, _, _) | Expr::Deref(inner, _) = curr {
        curr = inner.as_ref();
    }
    if let Expr::Ident(var_name, _) = curr {
        if let Some((_, holder)) = scopes.active_borrow(var_name) {
            errors.push(SemanticError {
                code: "E0506",
                message: format!(
                    "Cannot assign to element of `{var_name}` because `{var_name}` is borrowed by `{holder}`"
                ),
                label: "Indexed assignment while borrowed".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        if let Some(info) = scopes.lookup(var_name) {
            if matches!(info.ty, Type::Ref(_) | Type::Rc(_) | Type::Arc(_))
                || (matches!(info.ty, Type::Slice(_)) && scopes.borrow_target(var_name).is_some())
            {
                errors.push(SemanticError {
                    code: "E0594",
                    message: format!("Cannot mutate element through immutable reference '{var_name}'"),
                    label: "Reference is immutable".to_string(),
                    secondary_label: None,
                    help: Some("Use `&mut` or an owned mutable binding `let mut`".to_string()),
                    span: span.clone(),
                });
            } else if !info.is_mutable && !matches!(info.ty, Type::MutRef(_) | Type::Ptr(_)) {
                errors.push(SemanticError {
                    code: "E0596",
                    message: format!("Cannot assign to element of immutable variable '{var_name}'"),
                    label: "Variable is immutable".to_string(),
                    secondary_label: None,
                    help: Some(format!("Declare as mutable: `let mut {var_name}`")),
                    span: span.clone(),
                });
            }
        }
    }

    let mut clean_target_ty = type_ctx.infer.borrow_mut().resolve(t_target.ty());
    while let Type::Ref(inner) | Type::MutRef(inner) | Type::Box(inner) = clean_target_ty {
        clean_target_ty = *inner;
    }

    if let Type::Obj(s) = clean_target_ty {
        if let Some(fn_info) =
            crate::sanal::binops::lookup_struct_method_fn(type_ctx, s, "index_mut")
        {
            let mut self_arg = t_target;
            if let Some(first_param) = fn_info.params.first() {
                let expected_self = type_ctx.infer.borrow_mut().probe(first_param.ty);
                let actual_self = type_ctx.infer.borrow_mut().probe(self_arg.ty());
                if matches!(expected_self, Type::MutRef(_))
                    && !matches!(actual_self, Type::Ref(_) | Type::MutRef(_))
                {
                    let arg_span = self_arg.span();
                    self_arg = TypedExpr::Ref(
                        Box::new(self_arg),
                        true,
                        Type::MutRef(crate::ast::intern_type(actual_self)),
                        arg_span,
                    );
                }
            }
            let mut idx_arg = t_idx;
            if fn_info.params.len() >= 2 {
                crate::sanal::binops::auto_borrow_op_arg_if_ref(
                    fn_info.params[1].ty,
                    &mut idx_arg,
                    scopes,
                    errors,
                    type_ctx,
                );
            }
            let mut call_args = vec![self_arg, idx_arg];
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
            let out_ty = match ret_ty {
                Type::MutRef(inner) => Some(*inner),
                other => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "`IndexMut::index_mut` must return `&mut Output`, found `{other:?}`"
                        ),
                        label: "Invalid `index_mut` return type".into(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                    None
                }
            };
            if let Some(elem_ty) = out_ty {
                let unify_res = type_ctx.infer.borrow_mut().unify(elem_ty, t_val.ty());
                let resolved_elem = type_ctx.infer.borrow_mut().resolve(elem_ty);
                let resolved_val = type_ctx.infer.borrow_mut().resolve(t_val.ty());
                if unify_res.is_err() && !is_type_compatible(&resolved_elem, &resolved_val) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Cannot assign type `{:?}` to indexed target holding `{:?}`",
                            resolved_val, resolved_elem
                        ),
                        label: "Type mismatch".into(),
                        secondary_label: None,
                        help: None,
                        span: t_val.span().clone(),
                    });
                }
            }
            let call_expr = TypedExpr::Call(fn_info.name.clone(), call_args, ret_ty, span.clone());
            return Some(TypedExpr::DerefAssign(
                Box::new(call_expr),
                Box::new(t_val),
                span.clone(),
            ));
        }
    }

    let resolved_idx_ty = type_ctx.infer.borrow_mut().probe(t_idx.ty());
    if matches!(resolved_idx_ty, Type::Infer(_)) {
        let _ = type_ctx.infer.borrow_mut().unify(Type::Int, resolved_idx_ty);
    } else if !resolved_idx_ty.is_integer() {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Array index must be an integer, found `{:?}`", resolved_idx_ty),
            label: "Invalid index type".into(),
            secondary_label: None,
            help: None,
            span: t_idx.span().clone(),
        });
    }
    let opt_elem_ty = match clean_target_ty {
        Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => Some(*e_ty),
        Type::Obj(s) => crate::sanal::mono::lookup_mangled(s)
            .and_then(|(_, t_args)| t_args.first().copied()),
        _ => None,
    };
    if let Some(elem_ty) = opt_elem_ty {
        let unify_res = type_ctx.infer.borrow_mut().unify(elem_ty, t_val.ty());
        let resolved_elem = type_ctx.infer.borrow_mut().resolve(elem_ty);
        let resolved_val = type_ctx.infer.borrow_mut().resolve(t_val.ty());
        if unify_res.is_err() && !is_type_compatible(&resolved_elem, &resolved_val) {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot assign type `{:?}` to array holding `{:?}`",
                    resolved_val,
                    resolved_elem
                ),
                label: "Type mismatch".into(),
                secondary_label: None,
                help: None,
                span: t_val.span().clone(),
            });
        }
    }

    Some(TypedExpr::IndexAssign(
        Box::new(t_target),
        Box::new(t_idx),
        Box::new(t_val),
        span.clone(),
    ))
}

