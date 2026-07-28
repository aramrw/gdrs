//! sanal/binops.rs
//! Type checking for arithmetic, bitwise, relational, and logical binary/unary operators.

use crate::{
    ast::{Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

#[inline]
pub fn is_int(ty: Type) -> bool {
    matches!(ty, Type::I32 | Type::Int)
}

#[inline]
pub fn is_float(ty: Type) -> bool {
    matches!(ty, Type::F32 | Type::Float)
}

pub fn check_binary_op(
    op_name: &str,
    t_lhs: &TypedExpr,
    t_rhs: &TypedExpr,
    allow_float: bool,
    span: &Span,
    errors: &mut Vec<SemanticError>,
) -> Type {
    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();

    match (l_ty, r_ty) {
        (Type::I32, Type::I32) => Type::I32,
        (Type::Int, Type::Int) => Type::Int,
        (Type::I32, Type::Int) | (Type::Int, Type::I32) => Type::Int,
        (Type::F32, Type::F32) if allow_float => Type::F32,
        (Type::Float, Type::Float) if allow_float => Type::Float,
        (Type::F32, Type::Float) | (Type::Float, Type::F32) if allow_float => Type::Float,
        _ if allow_float && is_int(l_ty) && is_float(r_ty) => r_ty,
        _ if allow_float && is_float(l_ty) && is_int(r_ty) => l_ty,
        (Type::Generic(g), _) | (_, Type::Generic(g)) => Type::Generic(g),
        _ => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Cannot perform '{op_name}' on types `{l_ty:?}` and `{r_ty:?}`"),
                label: format!("Type mismatch: `{l_ty:?}` vs `{r_ty:?}`"),
                secondary_label: None,
                help: if !allow_float && (is_float(l_ty) || is_float(r_ty)) {
                    Some("Bitwise operations can only be used on integers.".into())
                } else {
                    Some("Both operands must be numeric types (i32, i64, f32, f64).".into())
                },
                span: span.clone(),
            });
            Type::I32
        }
    }
}

fn lookup_struct_method_fn<'a>(type_ctx: &TypeCtx<'a>, struct_name: &str, method: &str) -> Option<crate::ast::FuncDecl> {
    let mangled = format!("{}_{}", struct_name, method);
    if let Some(fn_info) = type_ctx.get_fn(&mangled) {
        return Some(fn_info);
    }
    let parts: Vec<&str> = struct_name.split('_').collect();
    if parts.len() > 1 {
        let base_struct = parts[..parts.len() - 1].join("_");
        let base_mangled = format!("{}_{}", base_struct, method);
        if let Some(fn_info) = type_ctx.get_fn(&base_mangled) {
            return Some(fn_info);
        }
    }
    None
}

pub fn type_check_add<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if let Type::Ptr(_) = t_lhs.ty() {
        let ty = t_lhs.ty();
        return Some(TypedExpr::Add(Box::new(t_lhs), Box::new(t_rhs), ty, span.clone()));
    }
    if let Type::Ptr(_) = t_rhs.ty() {
        let ty = t_rhs.ty();
        return Some(TypedExpr::Add(Box::new(t_lhs), Box::new(t_rhs), ty, span.clone()));
    }
    if let Type::Obj(struct_name) = t_lhs.ty() {
        if let Some(fn_info) = lookup_struct_method_fn(type_ctx, struct_name, "add") {
            return Some(TypedExpr::Call(
                fn_info.name.clone(),
                vec![t_lhs, t_rhs],
                fn_info.return_type,
                span.clone(),
            ));
        }
    }
    let ty = check_binary_op("+", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Add(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_sub<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if let Type::Ptr(_) = t_lhs.ty() {
        let ty = t_lhs.ty();
        return Some(TypedExpr::Sub(Box::new(t_lhs), Box::new(t_rhs), ty, span.clone()));
    }
    if let Type::Obj(struct_name) = t_lhs.ty() {
        if let Some(fn_info) = lookup_struct_method_fn(type_ctx, struct_name, "sub") {
            return Some(TypedExpr::Call(
                fn_info.name.clone(),
                vec![t_lhs, t_rhs],
                fn_info.return_type,
                span.clone(),
            ));
        }
    }
    let ty = check_binary_op("-", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Sub(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_mul<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if let Type::Obj(struct_name) = t_lhs.ty() {
        if let Some(fn_info) = lookup_struct_method_fn(type_ctx, struct_name, "mul") {
            return Some(TypedExpr::Call(
                fn_info.name.clone(),
                vec![t_lhs, t_rhs],
                fn_info.return_type,
                span.clone(),
            ));
        }
    }
    let ty = check_binary_op("*", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Mul(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_div<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if let Type::Obj(struct_name) = t_lhs.ty() {
        if let Some(fn_info) = lookup_struct_method_fn(type_ctx, struct_name, "div") {
            return Some(TypedExpr::Call(
                fn_info.name.clone(),
                vec![t_lhs, t_rhs],
                fn_info.return_type,
                span.clone(),
            ));
        }
    }
    let ty = check_binary_op("/", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Div(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_pipe<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    let ty = check_binary_op("|", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Pipe(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_ampersand<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    let ty = check_binary_op("&", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Ampersand(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_caret<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    let ty = check_binary_op("^", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Caret(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_shl<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    let ty = check_binary_op("<<", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Shl(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_shr<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    let ty = check_binary_op(">>", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Shr(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_mod<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    let ty = check_binary_op("%", &t_lhs, &t_rhs, true, span, errors);
    Some(TypedExpr::Mod(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

pub fn type_check_neg<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;
    let ty = t_val.ty();

    if !matches!(ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_)) {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot negate non-numeric type `{:?}`", ty),
            label: "Invalid negation".into(),
            secondary_label: None,
            help: Some("The '-' operator can only be used on integers and floats".into()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::Neg(Box::new(t_val), ty, span.clone()))
}

pub fn type_check_not<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;

    if t_val.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot apply logical NOT to non-boolean type `{:?}`", t_val.ty()),
            label: "Expected boolean expression".into(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
    }

    Some(TypedExpr::Not(Box::new(t_val), span.clone()))
}

pub fn type_check_greater_than<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();

    if !matches!(l_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
        || !matches!(r_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
    {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare types `{l_ty:?}` and `{r_ty:?}` with '>'"),
            label: "Invalid comparison operator".into(),
            secondary_label: None,
            help: Some("Ordering comparisons can only be used on numbers (`Int` or `Float`)".into()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::GreaterThan(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

pub fn type_check_less_than<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();

    if !matches!(l_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
        || !matches!(r_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
    {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare types `{l_ty:?}` and `{r_ty:?}` with '<'"),
            label: "Invalid comparison operator".into(),
            secondary_label: None,
            help: Some("Ordering comparisons can only be used on numbers (`Int` or `Float`)".into()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::LessThan(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

pub fn type_check_greater_equal<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();

    if !matches!(l_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
        || !matches!(r_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
    {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare types `{l_ty:?}` and `{r_ty:?}` with '>='"),
            label: "Invalid comparison operator".into(),
            secondary_label: None,
            help: Some("Ordering comparisons can only be used on numbers (`Int` or `Float`)".into()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::GreaterEqual(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

pub fn type_check_less_equal<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();

    if !matches!(l_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
        || !matches!(r_ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_))
    {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare types `{l_ty:?}` and `{r_ty:?}` with '<='"),
            label: "Invalid comparison operator".into(),
            secondary_label: None,
            help: Some("Ordering comparisons can only be used on numbers (`Int` or `Float`)".into()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::LessEqual(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

pub fn type_check_equal<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();

    let numeric_compatible = matches!(
        (l_ty, r_ty),
        (Type::I32 | Type::Int, Type::I32 | Type::Int)
            | (Type::F32 | Type::Float, Type::F32 | Type::Float)
    );
    if l_ty != r_ty && !numeric_compatible {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare distinct types `{l_ty:?}` and `{r_ty:?}` for equality"),
            label: format!("Type mismatch: `{l_ty:?}` vs `{r_ty:?}`"),
            secondary_label: None,
            help: Some("Both operands must be the same type to check for equality".into()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::Equal(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

pub fn type_check_not_equal<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();

    let numeric_compatible = matches!(
        (l_ty, r_ty),
        (Type::I32 | Type::Int, Type::I32 | Type::Int)
            | (Type::F32 | Type::Float, Type::F32 | Type::Float)
    );
    if l_ty != r_ty && !numeric_compatible {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare distinct types `{l_ty:?}` and `{r_ty:?}` for equality"),
            label: format!("Type mismatch: `{l_ty:?}` vs `{r_ty:?}`"),
            secondary_label: None,
            help: Some("Both operands must be the same type to check for equality".into()),
            span: span.clone(),
        });
    }

    Some(TypedExpr::NotEqual(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

pub fn type_check_and<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    if t_lhs.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Left side of '&&' must be a `Bool`, found `{:?}`", t_lhs.ty()),
            label: "Expected boolean".into(),
            secondary_label: None,
            help: None,
            span: t_lhs.span().clone(),
        });
    }

    if t_rhs.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Right side of '&&' must be a `Bool`, found `{:?}`", t_rhs.ty()),
            label: "Expected boolean".into(),
            secondary_label: None,
            help: None,
            span: t_rhs.span().clone(),
        });
    }

    Some(TypedExpr::And(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

pub fn type_check_or<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

    if t_lhs.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Left side of '||' must be a `Bool`, found `{:?}`", t_lhs.ty()),
            label: "Expected boolean".into(),
            secondary_label: None,
            help: None,
            span: t_lhs.span().clone(),
        });
    }

    if t_rhs.ty() != Type::Bool {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Right side of '||' must be a `Bool`, found `{:?}`", t_rhs.ty()),
            label: "Expected boolean".into(),
            secondary_label: None,
            help: None,
            span: t_rhs.span().clone(),
        });
    }

    Some(TypedExpr::Or(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}
