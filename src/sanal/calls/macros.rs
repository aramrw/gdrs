//! sanal/calls/macros.rs
//! Macro call type-checking and thread safety validation.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        calls::closures::build_non_capturing_closure,
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

fn check_send_type(ty: &Type, is_unsafe: bool) -> Option<(&'static str, String)> {
    match ty {
        Type::Rc(_) => Some((
            "Non-atomic `rc<T>` is not `Send` and cannot cross thread boundaries",
            "Use `arc.new(...)` (`arc<T>`) for thread-safe shared ownership".to_string(),
        )),
        Type::Ref(_) | Type::MutRef(_) => Some((
            "Borrowed references (`&T` / `&mut T`) cannot cross thread boundaries",
            "Pass an owned value or wrap shared state in `arc.new(...)`".to_string(),
        )),
        Type::Ptr(_) if !is_unsafe => Some((
            "Raw pointers (`*T`) are not `Send` outside an `unsafe:` block",
            "Wrap in `arc.new(...)` or move the spawn into an `unsafe:` block".to_string(),
        )),
        Type::Arc(inner) | Type::Vec(inner) | Type::Slice(inner) | Type::Array(inner, _) => {
            check_send_type(inner, is_unsafe)
        }
        Type::Tuple(elems) => elems.iter().find_map(|e| check_send_type(e, is_unsafe)),
        _ => None,
    }
}

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
                let arg_ty = t_arg1.ty();
                if let Some((reason, help)) = check_send_type(&arg_ty, type_ctx.is_unsafe) {
                    errors.push(SemanticError {
                        code: "E0277",
                        message: format!("Type `{arg_ty:?}` cannot be sent between threads safely: {reason}"),
                        label: "Not `Send`".to_string(),
                        secondary_label: None,
                        help: Some(help),
                        span: t_arg1.span().clone(),
                    });
                }
                if !arg_ty.is_copy() {
                    if let TypedExpr::Ident(arg_name, _, arg_span) = &t_arg1 {
                        crate::sanal::compat::check_not_borrowed_on_move(
                            scopes, errors, arg_name, arg_span,
                        );
                        scopes.mark_moved(arg_name);
                    }
                }
                let param_ty = t_arg1.ty();
                let t_closure = build_non_capturing_closure(
                    scopes,
                    errors,
                    type_ctx,
                    params,
                    param_ty,
                    body,
                    c_span,
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

    if name.trim_end_matches('!') == "stringify" {
        let typed_args = if args.len() == 1 {
            vec![TypedExpr::String(String::new(), args[0].span())]
        } else {
            Vec::new()
        };
        return Some(crate::sanal::macros::validate_and_finalize_macro(
            scopes,
            errors,
            type_ctx,
            name,
            typed_args,
            span,
        ));
    }

    let mut arg_ctx = type_ctx.clone();
    if name.trim_end_matches('!') == "vec" {
        arg_ctx.current_expected_type = type_ctx.current_expected_type.and_then(|exp| {
            let resolved = type_ctx.infer.borrow_mut().probe(exp);
            match resolved {
                Type::Vec(elem) | Type::Slice(elem) | Type::Array(elem, _) => Some(*elem),
                _ => None,
            }
        });
    } else {
        arg_ctx.current_expected_type = None;
    }

    let mut typed_args = Vec::new();
    for arg in args {
        if let Some(t_arg) = type_check_expr(scopes, errors, &arg_ctx, arg) {
            typed_args.push(t_arg);
        }
    }
    Some(crate::sanal::macros::validate_and_finalize_macro(
        scopes,
        errors,
        type_ctx,
        name,
        typed_args,
        span,
    ))
}
