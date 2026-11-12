//! sanal/control_flow/lifetimes.rs
//! Reference escape and lifetime checks for returns and blocks.

use crate::{
    ast::{Span, Type, TypedExpr},
    sanal::{
        compat::{extract_root_ident_with_ty, extract_root_var, is_diverging_expr},
        ScopeStack, SemanticError,
    },
};

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
            if matches!(ty, Type::Ref(_) | Type::MutRef(_))
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
        TypedExpr::Call(_, args, _, _) => {
            for arg in args {
                if matches!(arg.ty(), Type::Ref(_) | Type::MutRef(_)) {
                    check_return_ref_lifetime(scopes, arg, errors);
                }
            }
        }
        _ => {}
    }
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
                    errors.push(SemanticError {
                        code: "E0597",
                        message: format!(
                            "`{root}` does not live long enough; dropped at end of block while borrowed"
                        ),
                        label: "Borrowed value does not live long enough".to_string(),
                        secondary_label: None,
                        help: Some("Bind the value outside this block before borrowing it".to_string()),
                        span: span.clone(),
                    });
                }
            }
        }
        TypedExpr::Ident(name, ty, span) if matches!(ty, Type::Ref(_) | Type::MutRef(_)) => {
            if let Some(target) = scopes.borrow_target(name) {
                if scopes.current_scope_contains(&target) {
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
            }
        }
        _ => {}
    }
}

