//! sanal/control_flow/lifetimes.rs
//! Reference escape and lifetime checks for returns and blocks.

use crate::{
    ast::{Span, Type, TypedExpr},
    sanal::{
        compat::{extract_root_ident_with_ty, extract_root_var, is_diverging_expr},
        ScopeStack, SemanticError,
    },
};

pub(crate) fn is_borrowed_view_call(fn_name: &str) -> bool {
    let bare = fn_name.trim_start_matches('.');
    bare == "as_str"
        || bare == "std_string_String_as_str"
        || bare.ends_with("_String_as_str")
        || bare == "std_vec_Vec_iter"
        || bare == "std_vec_Vec_into_iter"
        || (bare.starts_with("std_vec_Vec") && (bare.ends_with("_iter") || bare.ends_with("_into_iter")))
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

pub fn check_return_ref_lifetime(
    scopes: &ScopeStack,
    expr: &TypedExpr,
    errors: &mut Vec<SemanticError>,
) {
    match expr {
        TypedExpr::Ref(inner, _, _, span) => match extract_root_ident_with_ty(inner) {
            None => errors.push(SemanticError {
                code: "E0515",
                message: "Cannot return reference to temporary value".to_string(),
                label: "Returns a reference to data owned by the current function".to_string(),
                secondary_label: None,
                help: Some("Return an owned value instead of a reference".to_string()),
                span: span.clone(),
            }),
            Some((root, root_ty)) => {
                let valid_caller_origin = matches!(root_ty, Type::Ref(_) | Type::MutRef(_))
                    && scopes.lookup(root).is_some_and(|info| info.from_caller);
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
        },
        TypedExpr::Ident(name, ty, span) => {
            let borrowed_str_or_iter = matches!(ty, Type::Str)
                || matches!(ty, Type::Obj(s) if s.contains("VecIter"));
            if (matches!(ty, Type::Ref(_) | Type::MutRef(_))
                || (borrowed_str_or_iter && scopes.borrow_target(name).is_some()))
                && !scopes.lookup(name).is_some_and(|info| info.from_caller)
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
                check_return_ref_lifetime(scopes, elem, errors);
            }
        }
        TypedExpr::ObjInit(_, fields, _, _) => {
            for (_, val) in fields {
                check_return_ref_lifetime(scopes, val, errors);
            }
        }
        TypedExpr::EnumConstruct(_, _, _, args, _, _) => {
            for arg in args {
                check_return_ref_lifetime(scopes, arg, errors);
            }
        }
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            if let Some(last) = stmts.last() {
                check_return_ref_lifetime(scopes, last, errors);
            }
        }
        TypedExpr::IfElse(_, then_b, else_b, _, _) => {
            if !is_diverging_expr(then_b) {
                check_return_ref_lifetime(scopes, then_b, errors);
            }
            if !is_diverging_expr(else_b) {
                check_return_ref_lifetime(scopes, else_b, errors);
            }
        }
        TypedExpr::Match(_, arms, _, _) => {
            for arm in arms {
                if !crate::sanal::compat::definitely_returns(&arm.body) {
                    if let Some(last) = arm.body.last() {
                        check_return_ref_lifetime(scopes, last, errors);
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
                            });
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
                        check_return_ref_lifetime(scopes, arg, errors);
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
            let may_hold_borrow = matches!(ty, Type::Ref(_) | Type::MutRef(_) | Type::Str)
                || matches!(ty, Type::Obj(s) if s.contains("VecIter"));
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

