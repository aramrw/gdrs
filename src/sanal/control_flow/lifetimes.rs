//! sanal/control_flow/lifetimes.rs
//! Reference escape and lifetime checks for returns and blocks.

use crate::{
    ast::{Span, Type, TypedExpr},
    sanal::{
        compat::{extract_root_ident_with_ty, extract_root_var, is_diverging_expr, is_static_place},
        ScopeStack, SemanticError,
    },
};

pub(crate) fn is_borrowed_view_call(fn_name: &str) -> bool {
    let bare = fn_name.trim_start_matches('.');
    bare == "as_str"
        || bare == "std_string_String_as_str"
        || bare.ends_with("_String_as_str")
        || bare == "std_vec_Vec_iter"
        || bare == "std_vec_Vec_iter_ref"
        || bare == "std_vec_Vec_into_iter"
        || (bare.starts_with("std_vec_Vec")
            && (bare.ends_with("_iter")
                || bare.ends_with("_iter_ref")
                || bare.ends_with("_into_iter")
                || bare.ends_with("_get")
                || bare.ends_with("_get_mut")))
        || (bare.starts_with("std_collections_")
            && (bare.ends_with("_get")
                || bare.ends_with("_get_mut")
                || bare.ends_with("_front")
                || bare.ends_with("_back")
                || bare.ends_with("_slot_key")
                || bare.ends_with("_slot_val")))
}

pub(crate) fn borrowed_view_root<'a>(
    fn_name: &str,
    args: &'a [TypedExpr],
) -> Option<&'a str> {
    if !is_borrowed_view_call(fn_name) {
        return None;
    }
    let mut recv = args.first()?;
    while let TypedExpr::Ref(inner, _, _, _) = recv {
        recv = inner.as_ref();
    }
    extract_root_var(recv)
}

pub fn type_may_borrow(ty: &Type) -> bool {
    match ty {
        Type::Ref(_) | Type::MutRef(_) | Type::Str | Type::Slice(_) => true,
        Type::Obj(name) | Type::Enum(name) => {
            name.contains("VecIter")
                || name.contains("VecRefIter")
                || crate::sanal::mono::lookup_mangled(name)
                    .is_some_and(|(_, args)| args.iter().any(type_may_borrow))
        }
        Type::Array(t, _)
        | Type::Vec(t)
        | Type::Box(t)
        | Type::Rc(t)
        | Type::Arc(t) => type_may_borrow(t),
        Type::Tuple(elems) => elems.iter().any(type_may_borrow),
        _ => false,
    }
}

pub fn check_return_ref_lifetime(
    scopes: &ScopeStack,
    expr: &TypedExpr,
    errors: &mut Vec<SemanticError>,
) {
    check_return_ref_lifetime_inner(scopes, expr, &[], errors);
}

fn check_return_ref_lifetime_inner(
    scopes: &ScopeStack,
    expr: &TypedExpr,
    caller_bindings: &[String],
    errors: &mut Vec<SemanticError>,
) {
    match expr {
        TypedExpr::Ref(inner, _, _, span)
        | TypedExpr::IndexAccess(inner, _, Type::Slice(_) | Type::Str, span) => {
            if is_static_place(inner) {
                return;
            }
            match extract_root_ident_with_ty(inner) {
                None => errors.push(SemanticError {
                    code: "E0515",
                    message: "Cannot return reference to temporary value".to_string(),
                    label: "Returns a reference to data owned by the current function".to_string(),
                    secondary_label: None,
                    help: Some("Return an owned value instead of a reference".to_string()),
                    span: span.clone(),
                }),
                Some((root, root_ty)) => {
                    let valid_caller_origin =
                        matches!(root_ty, Type::Ref(_) | Type::MutRef(_) | Type::Slice(_))
                            && (scopes.lookup(root).is_some_and(|info| info.from_caller)
                                || caller_bindings.iter().any(|b| b == root));
                    if !valid_caller_origin {
                        errors.push(SemanticError {
                            code: "E0515",
                            message: format!("Cannot return reference to local variable `{root}`"),
                            label: "Returns a reference to data owned by the current function"
                                .to_string(),
                            secondary_label: None,
                            help: Some("Return an owned value instead of a reference".to_string()),
                            span: span.clone(),
                        });
                    }
                }
            }
        }
        TypedExpr::Ident(name, ty, span) => {
            let borrowed_str_or_iter = matches!(ty, Type::Str | Type::Slice(_))
                || matches!(ty, Type::Obj(s) if s.contains("VecIter") || s.contains("VecRefIter"));
            let valid_caller_borrow = scopes
                .borrow_target(name)
                .is_some_and(|root| scopes.lookup(&root).is_some_and(|info| info.from_caller));
            let is_caller_origin = scopes.lookup(name).is_some_and(|info| info.from_caller)
                || caller_bindings.iter().any(|b| b == name);
            if (matches!(ty, Type::Ref(_) | Type::MutRef(_))
                || (borrowed_str_or_iter && scopes.borrow_target(name).is_some() && !valid_caller_borrow))
                && !is_caller_origin
            {
                errors.push(SemanticError {
                    code: "E0515",
                    message: format!(
                        "Cannot return reference `{name}` that borrows from a local variable"
                    ),
                    label: "Returns a reference to data owned by the current function"
                        .to_string(),
                    secondary_label: None,
                    help: Some("Return an owned value instead of a reference".to_string()),
                    span: span.clone(),
                });
            }
        }
        TypedExpr::TupleInit(elems, _, _) | TypedExpr::ArrayInit(elems, _, _) => {
            for elem in elems {
                check_return_ref_lifetime_inner(scopes, elem, caller_bindings, errors);
            }
        }
        TypedExpr::ObjInit(_, fields, _, _) => {
            for (_, val) in fields {
                check_return_ref_lifetime_inner(scopes, val, caller_bindings, errors);
            }
        }
        TypedExpr::EnumConstruct(_, _, _, args, _, _) => {
            for arg in args {
                check_return_ref_lifetime_inner(scopes, arg, caller_bindings, errors);
            }
        }
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            if let Some(last) = stmts.last() {
                check_return_ref_lifetime_inner(scopes, last, caller_bindings, errors);
            }
        }
        TypedExpr::IfElse(_, then_b, else_b, _, _) => {
            if !is_diverging_expr(then_b) {
                check_return_ref_lifetime_inner(scopes, then_b, caller_bindings, errors);
            }
            if !is_diverging_expr(else_b) {
                check_return_ref_lifetime_inner(scopes, else_b, caller_bindings, errors);
            }
        }
        TypedExpr::Match(target, arms, _, _) => {
            let target_from_caller = extract_root_var(target).is_some_and(|root| {
                scopes.lookup(root).is_some_and(|i| i.from_caller)
                    || caller_bindings.iter().any(|b| b == root)
                    || scopes
                        .borrow_target(root)
                        .is_some_and(|bt| scopes.lookup(&bt).is_some_and(|i| i.from_caller))
            });
            for arm in arms {
                if !crate::sanal::compat::definitely_returns(&arm.body) {
                    if let Some(last) = arm.body.last() {
                        if target_from_caller && !arm.bindings.is_empty() {
                            let mut next_bindings = caller_bindings.to_vec();
                            for (b_name, _) in &arm.bindings {
                                if b_name != "_" {
                                    next_bindings.push(b_name.clone());
                                }
                            }
                            check_return_ref_lifetime_inner(scopes, last, &next_bindings, errors);
                        } else {
                            check_return_ref_lifetime_inner(scopes, last, caller_bindings, errors);
                        }
                    }
                }
            }
        }
        TypedExpr::Call(fn_name, args, _, span) => {
            if is_borrowed_view_call(fn_name) {
                match borrowed_view_root(fn_name, args) {
                    None => errors.push(SemanticError {
                        code: "E0515",
                        message: "Cannot return borrowed view of a temporary value".to_string(),
                        label: "Returns a view into data owned by the current function".to_string(),
                        secondary_label: None,
                        help: Some("Return an owned value instead".to_string()),
                        span: span.clone(),
                    }),
                    Some(root) => {
                        let valid_caller_origin = scopes
                            .lookup(root)
                            .is_some_and(|info| {
                                matches!(info.ty, Type::Ref(_) | Type::MutRef(_)) && info.from_caller
                            })
                            || caller_bindings.iter().any(|b| b == root);
                        if !valid_caller_origin {
                            errors.push(SemanticError {
                                code: "E0515",
                                message: format!(
                                    "Cannot return borrowed view of local variable `{root}`"
                                ),
                                label: "Returns a view into data owned by the current function"
                                    .to_string(),
                                secondary_label: None,
                                help: Some("Return an owned value instead".to_string()),
                                span: span.clone(),
                            });
                        }
                    }
                }
            } else {
                for arg in args {
                    if matches!(arg.ty(), Type::Ref(_) | Type::MutRef(_)) {
                        check_return_ref_lifetime_inner(scopes, arg, caller_bindings, errors);
                    }
                }
            }
        }
        _ => {}
    }
}

fn push_block_escape_error(target: &str, span: &Span, errors: &mut Vec<SemanticError>) {
    errors.push(SemanticError {
        code: "E0597",
        message: format!(
            "`{target}` does not live long enough; dropped at end of block while borrowed"
        ),
        label: "Borrowed value does not live long enough".to_string(),
        secondary_label: None,
        help: Some("Bind the value outside this block before borrowing it".to_string()),
        span: span.clone(),
    });
}

pub fn check_block_escape_lifetime(
    scopes: &ScopeStack,
    expr: &TypedExpr,
    errors: &mut Vec<SemanticError>,
) {
    match expr {
        TypedExpr::Ref(inner, _, _, span) => {
            if is_static_place(inner) {
                return;
            }
            if let Some(root) = extract_root_var(inner) {
                if scopes.current_scope_contains(root) {
                    push_block_escape_error(root, span, errors);
                } else if let Some(target) = scopes.borrow_target(root) {
                    if scopes.current_scope_contains(&target) {
                        push_block_escape_error(&target, span, errors);
                    }
                }
            } else {
                errors.push(SemanticError {
                    code: "E0716",
                    message: "Temporary value dropped while borrowed at end of block".to_string(),
                    label: "Creates a dangling reference to a temporary".to_string(),
                    secondary_label: None,
                    help: Some("Bind the value outside this block before borrowing it".to_string()),
                    span: span.clone(),
                });
            }
        }
        TypedExpr::Ident(name, ty, span) => {
            let may_hold_borrow =
                matches!(ty, Type::Ref(_) | Type::MutRef(_) | Type::Str | Type::Slice(_))
                    || matches!(ty, Type::Obj(s) if s.contains("VecIter") || s.contains("VecRefIter"));
            if may_hold_borrow {
                if let Some(target) = scopes.borrow_target(name) {
                    if scopes.current_scope_contains(&target) {
                        push_block_escape_error(&target, span, errors);
                    }
                }
            }
        }
        TypedExpr::Call(fn_name, args, _, span) if is_borrowed_view_call(fn_name) => {
            match borrowed_view_root(fn_name, args) {
                Some(root) if scopes.current_scope_contains(root) => {
                    push_block_escape_error(root, span, errors);
                }
                Some(root) => {
                    if let Some(target) = scopes.borrow_target(root) {
                        if scopes.current_scope_contains(&target) {
                            push_block_escape_error(&target, span, errors);
                        }
                    }
                }
                None => errors.push(SemanticError {
                    code: "E0716",
                    message: "Temporary value dropped while borrowed at end of block".to_string(),
                    label: "Creates a dangling view into a temporary".to_string(),
                    secondary_label: None,
                    help: Some("Bind the value outside this block before taking a view".to_string()),
                    span: span.clone(),
                }),
            }
        }
        TypedExpr::TupleInit(elems, _, _) | TypedExpr::ArrayInit(elems, _, _) => {
            for elem in elems {
                check_block_escape_lifetime(scopes, elem, errors);
            }
        }
        TypedExpr::ObjInit(_, fields, _, _) => {
            for (_, val) in fields {
                check_block_escape_lifetime(scopes, val, errors);
            }
        }
        TypedExpr::EnumConstruct(_, _, _, args, _, _) => {
            for arg in args {
                check_block_escape_lifetime(scopes, arg, errors);
            }
        }
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            if let Some(last) = stmts.last() {
                check_block_escape_lifetime(scopes, last, errors);
            }
        }
        TypedExpr::IfElse(_, then_b, else_b, _, _) => {
            if !is_diverging_expr(then_b) {
                check_block_escape_lifetime(scopes, then_b, errors);
            }
            if !is_diverging_expr(else_b) {
                check_block_escape_lifetime(scopes, else_b, errors);
            }
        }
        TypedExpr::Match(_, arms, _, _) => {
            for arm in arms {
                if !crate::sanal::compat::definitely_returns(&arm.body) {
                    if let Some(last) = arm.body.last() {
                        check_block_escape_lifetime(scopes, last, errors);
                    }
                }
            }
        }
        _ => {}
    }
}

