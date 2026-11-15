//! sanal/compat.rs
//! Shared type-compatibility rules, control-flow divergence/return analysis,
//! and ownership move-tracking helpers used across `sanal`.

use crate::{
    ast::{Span, Type, TypedExpr},
    sanal::{ScopeStack, SemanticError},
};

fn type_matches_predicate(ty: &Type, pred: fn(&Type) -> bool) -> bool {
    if pred(ty) {
        return true;
    }
    match ty {
        Type::Ptr(t)
        | Type::Ref(t)
        | Type::MutRef(t)
        | Type::Slice(t)
        | Type::Vec(t)
        | Type::Box(t)
        | Type::Rc(t)
        | Type::Arc(t)
        | Type::Array(t, _) => type_matches_predicate(t, pred),
        Type::FnPtr(params, ret) => {
            params.iter().any(|t| type_matches_predicate(t, pred))
                || type_matches_predicate(ret, pred)
        }
        Type::Tuple(tys) => tys.iter().any(|t| type_matches_predicate(t, pred)),
        Type::Enum(name) | Type::Obj(name) => crate::sanal::mono::lookup_mangled(name)
            .is_some_and(|(_, t_args)| t_args.iter().any(|t| type_matches_predicate(t, pred))),
        _ => false,
    }
}

/// Returns `true` if `ty` contains any unresolved `Type::Generic` parameter (including inside nested containers/refs).
pub fn type_contains_generic(ty: &Type) -> bool {
    type_matches_predicate(ty, |t| matches!(t, Type::Generic(_)))
}

/// Returns `true` if `ty` contains any unresolved `Type::Infer` variable (including inside nested containers/refs).
pub fn type_contains_infer(ty: &Type) -> bool {
    type_matches_predicate(ty, |t| matches!(t, Type::Infer(_)))
}

/// Formats a [`Type`] in human-readable gdrs surface syntax for diagnostics.
pub fn format_type(ty: &Type) -> String {
    match ty {
        Type::Int => "i64".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I8 => "i8".to_string(),
        Type::U64 => "u64".to_string(),
        Type::U32 => "u32".to_string(),
        Type::U16 => "u16".to_string(),
        Type::U8 => "u8".to_string(),
        Type::Float => "f64".to_string(),
        Type::F32 => "f32".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str => "str".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "()".to_string(),
        Type::Void => "void".to_string(),
        Type::Obj(name) | Type::Enum(name) | Type::Generic(name) => name.to_string(),
        Type::DynTrait(name) => format!("dyn {name}"),
        Type::Array(inner, len) => format!("[{}; {len}]", format_type(inner)),
        Type::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(format_type).collect();
            if parts.len() == 1 {
                format!("({},)", parts[0])
            } else {
                format!("({})", parts.join(", "))
            }
        }
        Type::Slice(inner) => format!("[{}]", format_type(inner)),
        Type::Vec(inner) => format!("Vec<{}>", format_type(inner)),
        Type::Box(inner) => format!("Box<{}>", format_type(inner)),
        Type::Rc(inner) => format!("Rc<{}>", format_type(inner)),
        Type::Arc(inner) => format!("Arc<{}>", format_type(inner)),
        Type::FnPtr(params, ret) => {
            let ps: Vec<String> = params.iter().map(format_type).collect();
            if **ret == Type::Unit {
                format!("fn({})", ps.join(", "))
            } else {
                format!("fn({}) -> {}", ps.join(", "), format_type(ret))
            }
        }
        Type::Ref(inner) => format!("&{}", format_type(inner)),
        Type::MutRef(inner) => format!("&mut {}", format_type(inner)),
        Type::Ptr(inner) => format!("*{}", format_type(inner)),
        Type::Infer(id) => format!("?{id}"),
        Type::Error => "{error}".to_string(),
    }
}

/// Returns `true` if a value of type `found` can be used where `expected` is required.
pub fn is_type_compatible(expected: &Type, found: &Type) -> bool {
    if expected == found {
        return true;
    }
    match (expected, found) {
        (Type::Error, _) | (_, Type::Error) => true,
        (_, Type::Void) => true,
        (Type::Generic(_), _) | (_, Type::Generic(_)) => true,
        (Type::Infer(_), _) | (_, Type::Infer(_)) => true,
        (Type::DynTrait(_), _) => true,
        (e, f) if e.is_integer() && f.is_integer() => true,
        (e, f) if e.is_float() && f.is_numeric() => true,
        (
            Type::String | Type::Obj("String") | Type::Obj("std_string_String"),
            Type::String | Type::Obj("String") | Type::Obj("std_string_String"),
        ) => true,
        (Type::Str | Type::Obj("String"), Type::Str | Type::Obj("String")) => true,
        (Type::Vec(e1), Type::Vec(e2))
        | (Type::Slice(e1), Type::Slice(e2))
        | (Type::Vec(e1), Type::Slice(e2))
        | (Type::Slice(e1), Type::Vec(e2))
        | (Type::Vec(e1), Type::Array(e2, _))
        | (Type::Slice(e1), Type::Array(e2, _)) => is_type_compatible(e1, e2),
        (Type::Slice(e1), Type::Ref(inner)) | (Type::Slice(e1), Type::MutRef(inner)) => {
            match *inner {
                Type::Array(e2, _) | Type::Vec(e2) | Type::Slice(e2) => is_type_compatible(e1, e2),
                _ => false,
            }
        }
        (Type::MutRef(s_inner), Type::MutRef(other_inner))
            if matches!(*s_inner, Type::Slice(_)) =>
        {
            if let Type::Slice(e1) = *s_inner {
                match *other_inner {
                    Type::Array(e2, _) | Type::Vec(e2) | Type::Slice(e2) => {
                        is_type_compatible(e1, e2)
                    }
                    _ => false,
                }
            } else {
                false
            }
        }
        (Type::MutRef(s_inner), Type::Slice(e2)) if matches!(*s_inner, Type::Slice(_)) => {
            if let Type::Slice(e1) = *s_inner {
                is_type_compatible(e1, e2)
            } else {
                false
            }
        }
        (Type::Vec(_), Type::Obj(s)) | (Type::Obj(s), Type::Vec(_)) => s.contains("Vec"),
        (Type::Array(e1, n1), Type::Array(e2, n2)) => n1 == n2 && is_type_compatible(e1, e2),
        (Type::Tuple(t1), Type::Tuple(t2)) => {
            t1.len() == t2.len()
                && t1
                    .iter()
                    .zip(t2.iter())
                    .all(|(a, b)| is_type_compatible(a, b))
        }
        (Type::Ref(a), Type::Ref(b))
        | (Type::MutRef(a), Type::MutRef(b))
        | (Type::Ref(a), Type::MutRef(b)) => is_type_compatible(a, b),
        (Type::Box(a), Type::Box(b))
        | (Type::Rc(a), Type::Rc(b))
        | (Type::Arc(a), Type::Arc(b)) => is_type_compatible(a, b),
        (Type::FnPtr(p1, r1), Type::FnPtr(p2, r2)) => {
            p1.len() == p2.len()
                && p1
                    .iter()
                    .zip(p2.iter())
                    .all(|(a, b)| is_type_compatible(a, b))
                && is_type_compatible(r1, r2)
        }
        (Type::Ptr(a), Type::Ptr(b)) => {
            **a == Type::Void || **b == Type::Void || is_type_compatible(a, b)
        }
        (Type::Obj(e1), Type::Obj(e2))
        | (Type::Enum(e1), Type::Enum(e2))
        | (Type::Obj(e1), Type::Enum(e2))
        | (Type::Enum(e1), Type::Obj(e2)) => {
            e1 == e2
                || e2.starts_with(&format!("{e1}_"))
                || e1.starts_with(&format!("{e2}_"))
                || e2.ends_with(&format!("_{e1}"))
                || e1.ends_with(&format!("_{e2}"))
        }
        _ => false,
    }
}

/// Returns `true` if `expr` unconditionally diverges (`return`, `break`, `continue`, `panic!`, etc.).
pub fn is_diverging_expr(expr: &TypedExpr) -> bool {
    match expr {
        TypedExpr::Return(..) | TypedExpr::Break(..) | TypedExpr::Continue(..) => true,
        TypedExpr::Loop(_, ty, _) => *ty == Type::Void,
        TypedExpr::MacroCall(name, ..) => name.trim_end_matches('!') == "panic",
        TypedExpr::Block(stmts, ..) | TypedExpr::Unsafe(stmts, ..) => definitely_returns(stmts),
        TypedExpr::IfElse(_, then_b, else_b, _, _) => {
            is_diverging_expr(then_b) && is_diverging_expr(else_b)
        }
        TypedExpr::Match(_, arms, _, _) => {
            !arms.is_empty() && arms.iter().all(|arm| definitely_returns(&arm.body))
        }
        _ => false,
    }
}

/// Returns `true` if every execution path through `stmts` diverges or executes `return`.
pub fn definitely_returns(stmts: &[TypedExpr]) -> bool {
    stmts.iter().any(is_diverging_expr)
}

fn unwrap_lvalue_step(expr: &TypedExpr) -> Option<&TypedExpr> {
    match expr {
        TypedExpr::FieldAccess(inner, _, _, _)
        | TypedExpr::IndexAccess(inner, _, _, _)
        | TypedExpr::Deref(inner, _, _) => Some(inner.as_ref()),
        TypedExpr::Call(fn_name, args, _, _)
            if (fn_name.ends_with("_deref")
                || fn_name.ends_with("_deref_mut")
                || fn_name.ends_with("_index")
                || fn_name.ends_with("_index_mut"))
                && !args.is_empty() =>
        {
            match &args[0] {
                TypedExpr::Ref(inner, _, _, _) => Some(inner.as_ref()),
                other => Some(other),
            }
        }
        _ => None,
    }
}

/// Extracts the underlying variable name from an lvalue expression (`x`, `x.field`, `*x`, etc.).
pub fn extract_root_var(mut expr: &TypedExpr) -> Option<&str> {
    loop {
        if let TypedExpr::Ident(name, _, _) = expr {
            return Some(name.as_str());
        }
        expr = unwrap_lvalue_step(expr)?;
    }
}

/// Extracts both the underlying root variable name and its recorded AST type from an lvalue expression.
pub fn extract_root_ident_with_ty(mut expr: &TypedExpr) -> Option<(&str, Type)> {
    loop {
        if let TypedExpr::Ident(name, ty, _) = expr {
            return Some((name.as_str(), *ty));
        }
        expr = unwrap_lvalue_step(expr)?;
    }
}

/// Returns true if an lvalue expression is rooted in a `'static` global (`static` / `static mut`).
pub fn is_static_place(mut expr: &TypedExpr) -> bool {
    loop {
        if matches!(expr, TypedExpr::StaticRef(..)) {
            return true;
        }
        let Some(next) = unwrap_lvalue_step(expr) else {
            return false;
        };
        expr = next;
    }
}

/// Checks and applies tail consumption (projection move check + move/borrow check on `Ident`)
/// when a non-`Unit`, non-diverging expression is yielded out of a block, branch, or function.
pub fn consume_tail_expr<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &crate::sanal::types::TypeCtx<'a>,
    expr: &TypedExpr,
) {
    if expr.ty() != Type::Unit
        && !matches!(expr, TypedExpr::Let(..) | TypedExpr::LetTuple(..) | TypedExpr::LetStruct(..))
        && !is_diverging_expr(expr)
    {
        type_ctx.check_not_moved_from_projection(expr, errors);
        mark_expr_moved_if_ident(scopes, errors, expr);
    }
}

/// Emits `E0505` if `name` is currently borrowed, or `E0507` if attempting to move a non-consuming `self`.
pub fn check_not_borrowed_on_move(
    scopes: &ScopeStack,
    errors: &mut Vec<SemanticError>,
    name: &str,
    span: &Span,
) {
    if scopes.lookup(name).is_some_and(|i| i.is_borrowed_self) {
        errors.push(SemanticError {
            code: "E0507",
            message: format!("Cannot move out of borrowed `{name}` inside a non-consuming method"),
            label: format!("Move of `{name}` occurs here"),
            secondary_label: None,
            help: Some("Operate on `&self` or fields, or change the method to return a non-Copy owned value".to_string()),
            span: span.clone(),
        });
    }
    if let Some((_, holder)) = scopes.active_borrow_including_projections(name) {
        errors.push(SemanticError {
            code: "E0505",
            message: format!("Cannot move out of `{name}` because it is borrowed by `{holder}`"),
            label: format!("Move out of `{name}` occurs here while borrowed"),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
    }
}

/// Marks a local variable binding as moved if `expr` is an identifier of a non-`Copy` type
/// or a dereference `*b` of an owned `Box<T>` where `T` is non-`Copy`.
#[inline]
pub fn mark_expr_moved_if_ident(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    expr: &TypedExpr,
) {
    match expr {
        TypedExpr::Ident(name, ty, span) => {
            if !ty.is_copy() {
                check_not_borrowed_on_move(scopes, errors, name, span);
                scopes.mark_moved(name);
            }
        }
        TypedExpr::StaticRef(name, ty, span) => {
            if !ty.is_copy() {
                errors.push(SemanticError {
                    code: "E0507",
                    message: format!(
                        "Cannot move out of static item `{}`",
                        name.rsplit('_').next().unwrap_or(name)
                    ),
                    label: "Cannot move out of static item".to_string(),
                    secondary_label: None,
                    help: Some(
                        "Borrow the static item (`&...` / `&mut ...`) or use a `Copy` type"
                            .to_string(),
                    ),
                    span: span.clone(),
                });
            }
        }
        TypedExpr::Deref(inner, ty, span) if matches!(inner.ty(), Type::Box(_)) => {
            if !ty.is_copy() {
                if let TypedExpr::Ident(name, _, _) = inner.as_ref() {
                    check_not_borrowed_on_move(scopes, errors, name, span);
                    scopes.mark_moved(name);
                } else {
                    errors.push(SemanticError {
                        code: "E0507",
                        message: format!(
                            "Cannot move out of `{:?}` which is behind a reference or projection",
                            inner.ty()
                        ),
                        label: "Cannot move out of non-local `Box`".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                }
            }
        }
        _ => {}
    }
}
