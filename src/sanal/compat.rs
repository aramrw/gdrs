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
        | Type::Rc(t)
        | Type::Arc(t)
        | Type::Array(t, _) => type_matches_predicate(t, pred),
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
        Type::Rc(inner) => format!("rc<{}>", format_type(inner)),
        Type::Arc(inner) => format!("arc<{}>", format_type(inner)),
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
        (Type::Rc(a), Type::Rc(b)) | (Type::Arc(a), Type::Arc(b)) => is_type_compatible(a, b),
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

/// Extracts the underlying variable name from an lvalue expression (`x`, `x.field`, `*x`, etc.).
pub fn extract_root_var(mut expr: &TypedExpr) -> Option<&str> {
    loop {
        match expr {
            TypedExpr::Ident(name, _, _) => return Some(name.as_str()),
            TypedExpr::FieldAccess(inner, _, _, _)
            | TypedExpr::IndexAccess(inner, _, _, _)
            | TypedExpr::Deref(inner, _, _) => {
                expr = inner.as_ref();
            }
            _ => return None,
        }
    }
}

/// Extracts both the underlying root variable name and its recorded AST type from an lvalue expression.
pub fn extract_root_ident_with_ty(mut expr: &TypedExpr) -> Option<(&str, Type)> {
    loop {
        match expr {
            TypedExpr::Ident(name, ty, _) => return Some((name.as_str(), *ty)),
            TypedExpr::FieldAccess(inner, _, _, _)
            | TypedExpr::IndexAccess(inner, _, _, _)
            | TypedExpr::Deref(inner, _, _) => {
                expr = inner.as_ref();
            }
            _ => return None,
        }
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
        && !matches!(expr, TypedExpr::Let(..) | TypedExpr::LetTuple(..))
        && !is_diverging_expr(expr)
    {
        type_ctx.check_not_moved_from_projection(expr, errors);
        mark_expr_moved_if_ident(scopes, errors, expr);
    }
}

/// Emits `E0505` if `name` is currently borrowed when attempting to move out of it.
pub fn check_not_borrowed_on_move(
    scopes: &ScopeStack,
    errors: &mut Vec<SemanticError>,
    name: &str,
    span: &Span,
) {
    if let Some((_, holder)) = scopes.active_borrow(name) {
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

/// Marks a local variable binding as moved if `expr` is an identifier of a non-`Copy` type.
#[inline]
pub fn mark_expr_moved_if_ident(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    expr: &TypedExpr,
) {
    if let TypedExpr::Ident(name, ty, span) = expr {
        if !ty.is_copy() {
            check_not_borrowed_on_move(scopes, errors, name, span);
            scopes.mark_moved(name);
        }
    }
}
