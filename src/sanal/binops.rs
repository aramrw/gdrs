//! sanal/binops.rs
//! Type checking for arithmetic, bitwise, relational, and logical binary/unary operators.

use crate::{
    ast::{AssignOp, Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

#[inline]
pub fn is_int(ty: Type) -> bool {
    ty.is_integer()
}

#[inline]
pub fn is_float(ty: Type) -> bool {
    ty.is_float()
}

pub fn check_binary_op(
    op_name: &str,
    t_lhs: &TypedExpr,
    t_rhs: &TypedExpr,
    allow_float: bool,
    type_ctx: &TypeCtx<'_>,
    span: &Span,
    errors: &mut Vec<SemanticError>,
) -> Type {
    let mut infer = type_ctx.infer.borrow_mut();
    let mut l_ty = infer.probe(t_lhs.ty());
    let mut r_ty = infer.probe(t_rhs.ty());
    if matches!(l_ty, Type::Infer(_)) && !matches!(r_ty, Type::Infer(_)) {
        if allow_float || is_int(r_ty) {
            let _ = infer.unify(l_ty, r_ty);
            l_ty = infer.probe(l_ty);
        }
    } else if matches!(r_ty, Type::Infer(_)) && !matches!(l_ty, Type::Infer(_)) {
        if allow_float || is_int(l_ty) {
            let _ = infer.unify(r_ty, l_ty);
            r_ty = infer.probe(r_ty);
        }
    } else if matches!(l_ty, Type::Infer(_)) && matches!(r_ty, Type::Infer(_)) {
        let _ = infer.unify(l_ty, r_ty);
        l_ty = infer.probe(l_ty);
        r_ty = infer.probe(r_ty);
    }
    drop(infer);

    if l_ty == r_ty && (is_int(l_ty) || (allow_float && is_float(l_ty))) {
        return l_ty;
    }
    if (op_name == ">>" || op_name == "<<") && is_int(l_ty) && is_int(r_ty) {
        return l_ty;
    }
    if is_int(l_ty) && is_int(r_ty) {
        if l_ty.is_unsigned_integer() && r_ty == Type::Int {
            return l_ty;
        }
        if r_ty.is_unsigned_integer() && l_ty == Type::Int {
            return r_ty;
        }
        if l_ty.is_unsigned_integer() && r_ty.is_unsigned_integer() {
            return if l_ty == Type::U64 || r_ty == Type::U64 {
                Type::U64
            } else if l_ty == Type::U32 || r_ty == Type::U32 {
                Type::U32
            } else if l_ty == Type::U16 || r_ty == Type::U16 {
                Type::U16
            } else {
                Type::U8
            };
        }
        return if l_ty == Type::Int || r_ty == Type::Int {
            Type::Int
        } else if l_ty == Type::I32 || r_ty == Type::I32 {
            Type::I32
        } else if l_ty == Type::I16 || r_ty == Type::I16 {
            Type::I16
        } else {
            Type::I8
        };
    }
    if allow_float && is_float(l_ty) && is_float(r_ty) {
        return if l_ty == Type::Float || r_ty == Type::Float {
            Type::Float
        } else {
            Type::F32
        };
    }
    if allow_float && is_int(l_ty) && is_float(r_ty) {
        return r_ty;
    }
    if allow_float && is_float(l_ty) && is_int(r_ty) {
        return l_ty;
    }

    match (l_ty, r_ty) {
        (Type::Generic(g), _) | (_, Type::Generic(g)) => Type::Generic(g),
        (Type::Infer(id), Type::Infer(_)) => Type::Infer(id),
        (Type::Infer(_), other) if allow_float && (is_int(other) || is_float(other)) => other,
        (other, Type::Infer(_)) if allow_float && (is_int(other) || is_float(other)) => other,
        (Type::Infer(_), other) if !allow_float && is_int(other) => other,
        (other, Type::Infer(_)) if !allow_float && is_int(other) => other,
        _ => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Cannot perform '{op_name}' on types `{l_ty:?}` and `{r_ty:?}`"),
                label: format!("Type mismatch: `{l_ty:?}` vs `{r_ty:?}`"),
                secondary_label: None,
                help: if !allow_float && (is_float(l_ty) || is_float(r_ty)) {
                    Some("Bitwise operations can only be used on integers.".into())
                } else {
                    Some("Both operands must be numeric types.".into())
                },
                span: span.clone(),
            });
            Type::I32
        }
    }
}

fn check_ord_comparison(
    op_name: &str,
    l_ty: Type,
    r_ty: Type,
    type_ctx: &TypeCtx<'_>,
    span: &Span,
    errors: &mut Vec<SemanticError>,
) {
    let mut infer = type_ctx.infer.borrow_mut();
    let mut l = infer.probe(l_ty);
    let mut r = infer.probe(r_ty);
    if matches!(l, Type::Infer(_)) || matches!(r, Type::Infer(_)) {
        let _ = infer.unify(l, r);
        l = infer.probe(l);
        r = infer.probe(r);
    }
    drop(infer);

    let is_l_num = l.is_numeric() || matches!(l, Type::Generic(_) | Type::Infer(_));
    let is_r_num = r.is_numeric() || matches!(r, Type::Generic(_) | Type::Infer(_));
    if !is_l_num || !is_r_num {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare types `{l:?}` and `{r:?}` with '{op_name}'"),
            label: "Invalid comparison operator".into(),
            secondary_label: None,
            help: Some("Ordering comparisons can only be used on numbers (`Int` or `Float`)".into()),
            span: span.clone(),
        });
    }
}

fn check_equality_operands(
    l_ty: Type,
    r_ty: Type,
    type_ctx: &TypeCtx<'_>,
    span: &Span,
    errors: &mut Vec<SemanticError>,
) {
    let mut infer = type_ctx.infer.borrow_mut();
    let mut l = infer.resolve(l_ty);
    let mut r = infer.resolve(r_ty);
    if crate::sanal::compat::type_contains_infer(&l) || crate::sanal::compat::type_contains_infer(&r) {
        let _ = infer.unify_branches(l, r);
        l = infer.resolve(l);
        r = infer.resolve(r);
    }
    drop(infer);

    let is_str_eq = matches!(
        l,
        Type::Str | Type::String | Type::Obj("String") | Type::Obj("std_string_String")
    ) && matches!(
        r,
        Type::Str | Type::String | Type::Obj("String") | Type::Obj("std_string_String")
    );
    let numeric_compatible = (l.is_integer() && r.is_integer()) || (l.is_float() && r.is_float());
    if l != r
        && !numeric_compatible
        && !is_str_eq
        && !crate::sanal::compat::is_type_compatible(&l, &r)
        && !matches!(l, Type::Infer(_))
        && !matches!(r, Type::Infer(_))
    {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Cannot compare distinct types `{l:?}` and `{r:?}` for equality"),
            label: format!("Type mismatch: `{l:?}` vs `{r:?}`"),
            secondary_label: None,
            help: Some("Both operands must be the same type to check for equality".into()),
            span: span.clone(),
        });
    }
}

pub(crate) fn lookup_struct_method_fn<'a>(type_ctx: &TypeCtx<'a>, struct_name: &str, method: &str) -> Option<crate::ast::FuncDecl> {
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

fn extract_struct_name_from_ty(type_ctx: &TypeCtx<'_>, ty: Type) -> Option<&'static str> {
    let resolved = type_ctx.infer.borrow_mut().probe(ty);
    match resolved {
        Type::Obj(s) => Some(s),
        Type::Ref(inner) | Type::MutRef(inner) => match *inner {
            Type::Obj(s) => Some(s),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn auto_borrow_op_arg_if_ref(
    param_ty: Type,
    arg: &mut TypedExpr,
    scopes: &ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'_>,
) {
    let resolved_param = type_ctx.infer.borrow_mut().probe(param_ty);
    let resolved_arg = type_ctx.infer.borrow_mut().probe(arg.ty());
    if let Type::Ref(expected) = resolved_param {
        if !matches!(resolved_arg, Type::Ref(_) | Type::MutRef(_))
            && crate::sanal::compat::is_type_compatible(&expected, &resolved_arg)
        {
            if let Some(root_var) = crate::sanal::compat::extract_root_var(arg) {
                if let Some((true, holder)) = scopes.active_borrow(root_var) {
                    errors.push(SemanticError {
                        code: "E0502",
                        message: format!(
                            "Cannot borrow `{root_var}` as immutable because it is also borrowed as mutable by `{holder}`"
                        ),
                        label: "Immutable borrow occurs here".to_string(),
                        secondary_label: None,
                        help: None,
                        span: arg.span(),
                    });
                }
            }
            let arg_span = arg.span();
            *arg = TypedExpr::Ref(
                Box::new(arg.clone()),
                false,
                Type::Ref(expected),
                arg_span,
            );
        }
    }
}

fn finish_overloaded_op_call<'a>(
    fn_info: crate::ast::FuncDecl,
    mut args: Vec<TypedExpr>,
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) -> TypedExpr {
    if !args.is_empty() && !fn_info.params.is_empty() {
        auto_borrow_op_arg_if_ref(fn_info.params[0].ty, &mut args[0], scopes, errors, type_ctx);
    }
    if args.len() == 2 && fn_info.params.len() == 2 {
        auto_borrow_op_arg_if_ref(fn_info.params[1].ty, &mut args[1], scopes, errors, type_ctx);
    }
    crate::sanal::calls::validation::validate_call_arguments(
        &fn_info,
        &mut args,
        true,
        &fn_info.name,
        scopes,
        errors,
        type_ctx,
        span,
    );
    let ret_ty = type_ctx.infer.borrow_mut().resolve(fn_info.return_type);
    TypedExpr::Call(fn_info.name.clone(), args, ret_ty, span.clone())
}

fn lookup_op_method_for_ty<'a>(
    type_ctx: &TypeCtx<'a>,
    ty: Type,
    method: &str,
) -> Option<crate::ast::FuncDecl> {
    let resolved = type_ctx.infer.borrow_mut().probe(ty);
    match resolved {
        Type::Ref(inner) => {
            if let Type::Obj(s) = *inner {
                let ref_prefix = format!("__ref_{s}");
                if let Some(f) = lookup_struct_method_fn(type_ctx, &ref_prefix, method) {
                    return Some(f);
                }
                return lookup_struct_method_fn(type_ctx, s, method);
            }
            None
        }
        Type::MutRef(inner) => {
            if let Type::Obj(s) = *inner {
                let mutref_prefix = format!("__mutref_{s}");
                if let Some(f) = lookup_struct_method_fn(type_ctx, &mutref_prefix, method) {
                    return Some(f);
                }
                let ref_prefix = format!("__ref_{s}");
                if let Some(f) = lookup_struct_method_fn(type_ctx, &ref_prefix, method) {
                    return Some(f);
                }
                return lookup_struct_method_fn(type_ctx, s, method);
            }
            None
        }
        Type::Obj(s) => lookup_struct_method_fn(type_ctx, s, method),
        _ => None,
    }
}

fn try_type_check_overloaded_binop<'a>(
    t_lhs: &TypedExpr,
    t_rhs: &TypedExpr,
    method: &str,
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) -> Option<TypedExpr> {
    let fn_info = lookup_op_method_for_ty(type_ctx, t_lhs.ty(), method)?;
    Some(finish_overloaded_op_call(
        fn_info,
        vec![t_lhs.clone(), t_rhs.clone()],
        scopes,
        errors,
        type_ctx,
        span,
    ))
}

fn try_type_check_overloaded_unop<'a>(
    t_val: &TypedExpr,
    method: &str,
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) -> Option<TypedExpr> {
    let fn_info = lookup_op_method_for_ty(type_ctx, t_val.ty(), method)?;
    Some(finish_overloaded_op_call(
        fn_info,
        vec![t_val.clone()],
        scopes,
        errors,
        type_ctx,
        span,
    ))
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }
    if let Type::Ptr(_) = t_lhs.ty() {
        let ty = t_lhs.ty();
        return Some(TypedExpr::Add(Box::new(t_lhs), Box::new(t_rhs), ty, span.clone()));
    }
    if let Type::Ptr(_) = t_rhs.ty() {
        let ty = t_rhs.ty();
        return Some(TypedExpr::Add(Box::new(t_lhs), Box::new(t_rhs), ty, span.clone()));
    }
    if let Some(call) =
        try_type_check_overloaded_binop(&t_lhs, &t_rhs, "add", scopes, errors, type_ctx, span)
    {
        return Some(call);
    }
    let ty = check_binary_op("+", &t_lhs, &t_rhs, true, type_ctx, span, errors);
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }
    if let Type::Ptr(_) = t_lhs.ty() {
        let ty = t_lhs.ty();
        return Some(TypedExpr::Sub(Box::new(t_lhs), Box::new(t_rhs), ty, span.clone()));
    }
    if let Some(call) =
        try_type_check_overloaded_binop(&t_lhs, &t_rhs, "sub", scopes, errors, type_ctx, span)
    {
        return Some(call);
    }
    let ty = check_binary_op("-", &t_lhs, &t_rhs, true, type_ctx, span, errors);
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }
    if let Some(call) =
        try_type_check_overloaded_binop(&t_lhs, &t_rhs, "mul", scopes, errors, type_ctx, span)
    {
        return Some(call);
    }
    let ty = check_binary_op("*", &t_lhs, &t_rhs, true, type_ctx, span, errors);
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }
    if let Some(call) =
        try_type_check_overloaded_binop(&t_lhs, &t_rhs, "div", scopes, errors, type_ctx, span)
    {
        return Some(call);
    }
    let ty = check_binary_op("/", &t_lhs, &t_rhs, true, type_ctx, span, errors);
    Some(TypedExpr::Div(
        Box::new(t_lhs),
        Box::new(t_rhs),
        ty,
        span.clone(),
    ))
}

fn type_check_bitwise_binop<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    op_str: &str,
    method: &str,
    ctor: fn(Box<TypedExpr>, Box<TypedExpr>, Type, Span) -> TypedExpr,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }
    if let Some(call) =
        try_type_check_overloaded_binop(&t_lhs, &t_rhs, method, scopes, errors, type_ctx, span)
    {
        return Some(call);
    }
    let ty = check_binary_op(op_str, &t_lhs, &t_rhs, false, type_ctx, span, errors);
    Some(ctor(
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
    type_check_bitwise_binop(
        scopes,
        errors,
        type_ctx,
        "|",
        "bitor",
        TypedExpr::Pipe,
        lhs,
        rhs,
        span,
    )
}

pub fn type_check_ampersand<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    type_check_bitwise_binop(
        scopes,
        errors,
        type_ctx,
        "&",
        "bitand",
        TypedExpr::Ampersand,
        lhs,
        rhs,
        span,
    )
}

pub fn type_check_caret<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    type_check_bitwise_binop(
        scopes,
        errors,
        type_ctx,
        "^",
        "bitxor",
        TypedExpr::Caret,
        lhs,
        rhs,
        span,
    )
}

pub fn type_check_shl<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    type_check_bitwise_binop(
        scopes,
        errors,
        type_ctx,
        "<<",
        "shl",
        TypedExpr::Shl,
        lhs,
        rhs,
        span,
    )
}

pub fn type_check_shr<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    type_check_bitwise_binop(
        scopes,
        errors,
        type_ctx,
        ">>",
        "shr",
        TypedExpr::Shr,
        lhs,
        rhs,
        span,
    )
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }
    if let Some(call) =
        try_type_check_overloaded_binop(&t_lhs, &t_rhs, "rem", scopes, errors, type_ctx, span)
    {
        return Some(call);
    }
    let ty = check_binary_op("%", &t_lhs, &t_rhs, true, type_ctx, span, errors);
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
    if let Some(call) =
        try_type_check_overloaded_unop(&t_val, "neg", scopes, errors, type_ctx, span)
    {
        return Some(call);
    }
    let ty = type_ctx.infer.borrow_mut().probe(t_val.ty());

    if !matches!(ty, Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Generic(_) | Type::Infer(_)) {
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
    if let Some(call) =
        try_type_check_overloaded_unop(&t_val, "not", scopes, errors, type_ctx, span)
    {
        return Some(call);
    }

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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();
    check_ord_comparison(">", l_ty, r_ty, type_ctx, span, errors);

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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();
    check_ord_comparison("<", l_ty, r_ty, type_ctx, span, errors);

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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();
    check_ord_comparison(">=", l_ty, r_ty, type_ctx, span, errors);

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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

    let l_ty = t_lhs.ty();
    let r_ty = t_rhs.ty();
    check_ord_comparison("<=", l_ty, r_ty, type_ctx, span, errors);

    Some(TypedExpr::LessEqual(
        Box::new(t_lhs),
        Box::new(t_rhs),
        span.clone(),
    ))
}

fn try_lower_equality_trait_call<'a>(
    t_lhs: TypedExpr,
    t_rhs: TypedExpr,
    negate: bool,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
    errors: &mut Vec<SemanticError>,
) -> Result<TypedExpr, (TypedExpr, TypedExpr)> {
    let l_ty = type_ctx.infer.borrow_mut().resolve(t_lhs.ty());
    let r_ty = type_ctx.infer.borrow_mut().resolve(t_rhs.ty());

    let is_builtin_str = matches!(
        l_ty,
        Type::Obj("String") | Type::Obj("std_string_String")
    );
    if is_builtin_str || l_ty != r_ty {
        return Err((t_lhs, t_rhs));
    }

    let type_name = match l_ty {
        Type::Obj(name) | Type::Enum(name) => name,
        _ => return Err((t_lhs, t_rhs)),
    };

    if let Some(eq_fn) = lookup_struct_method_fn(type_ctx, type_name, "eq") {
        let ref_ty = Type::Ref(crate::ast::intern_type(l_ty));
        let lhs_ref = TypedExpr::Ref(Box::new(t_lhs), false, ref_ty, span.clone());
        let rhs_ref = TypedExpr::Ref(Box::new(t_rhs), false, ref_ty, span.clone());
        let eq_call = TypedExpr::Call(
            eq_fn.name.clone(),
            vec![lhs_ref, rhs_ref],
            Type::Bool,
            span.clone(),
        );
        if negate {
            return Ok(TypedExpr::Not(Box::new(eq_call), span.clone()));
        }
        return Ok(eq_call);
    }

    if matches!(l_ty, Type::Obj(_)) {
        errors.push(SemanticError {
            code: "E0369",
            message: format!("Binary operation `{}` cannot be applied to type `{type_name}`", if negate { "!=" } else { "==" }),
            label: format!("`{type_name}` does not implement `PartialEq`"),
            secondary_label: None,
            help: Some(format!("Implement `PartialEq` for `{type_name}` or add `#[derive(PartialEq)]`")),
            span: span.clone(),
        });
    }

    Err((t_lhs, t_rhs))
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

    check_equality_operands(t_lhs.ty(), t_rhs.ty(), type_ctx, span, errors);

    match try_lower_equality_trait_call(t_lhs, t_rhs, false, type_ctx, span, errors) {
        Ok(call_expr) => Some(call_expr),
        Err((t_lhs, t_rhs)) => Some(TypedExpr::Equal(
            Box::new(t_lhs),
            Box::new(t_rhs),
            span.clone(),
        )),
    }
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

    check_equality_operands(t_lhs.ty(), t_rhs.ty(), type_ctx, span, errors);

    match try_lower_equality_trait_call(t_lhs, t_rhs, true, type_ctx, span, errors) {
        Ok(call_expr) => Some(call_expr),
        Err((t_lhs, t_rhs)) => Some(TypedExpr::NotEqual(
            Box::new(t_lhs),
            Box::new(t_rhs),
            span.clone(),
        )),
    }
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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

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
    let pre_rhs_moves = scopes.snapshot_moves();
    let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
    if crate::sanal::compat::is_diverging_expr(&t_rhs) {
        scopes.restore_moves(&pre_rhs_moves);
    }

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

fn check_compound_assign_lhs_mutability<'a>(
    lhs: &Expr,
    t_lhs: &TypedExpr,
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) {
    let lhs_ty = type_ctx.infer.borrow_mut().probe(t_lhs.ty());
    if matches!(lhs_ty, Type::Ref(_)) {
        errors.push(SemanticError {
            code: "E0596",
            message: "Cannot use compound assignment through an immutable reference".to_string(),
            label: "Immutable reference".to_string(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
        return;
    }

    if let Some(root_var) = crate::sanal::compat::extract_root_var(t_lhs) {
        let borrow_path = crate::sanal::objects::fields::expr_projection_path(lhs)
            .unwrap_or_else(|| root_var.to_string());
        if let Some((_, holder)) = scopes.active_borrow_including_projections(&borrow_path) {
            errors.push(SemanticError {
                code: "E0506",
                message: format!(
                    "Cannot mutate `{borrow_path}` because it is borrowed by `{holder}`"
                ),
                label: "Mutation occurs while borrowed".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
        let is_mut_through_ref = matches!(lhs_ty, Type::MutRef(_))
            || matches!(t_lhs, TypedExpr::Deref(inner, _, _) if matches!(type_ctx.infer.borrow_mut().probe(inner.ty()), Type::MutRef(_)));
        if !is_mut_through_ref {
            if let Some(info) = scopes.lookup(root_var) {
                let is_root_mut_ref = matches!(
                    type_ctx.infer.borrow_mut().probe(info.ty),
                    Type::MutRef(_)
                );
                if !info.is_mutable && !is_root_mut_ref {
                    errors.push(SemanticError {
                        code: "E0382",
                        message: format!(
                            "Cannot mutate immutable variable `{root_var}` via compound assignment"
                        ),
                        label: format!("Variable `{root_var}` is immutable"),
                        secondary_label: None,
                        help: Some(format!("Consider declaring `{root_var}` as `let mut {root_var}`")),
                        span: span.clone(),
                    });
                }
            }
        }
        scopes.mark_active(root_var);
    } else {
        type_ctx.check_static_lvalue_mutable(t_lhs, "E0596", errors, span);
    }
}

/// Type checks compound assignment (`+=`, `-=`, `*=`, `/=`), preferring an
/// overloaded `{Add,Sub,Mul,Div}Assign` method on structs before falling back
/// to desugared primitive assignment.
pub fn type_check_compound_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    op: AssignOp,
    lhs: &Expr,
    rhs: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let (method, bin_ctor): (&str, fn(Box<Expr>, Box<Expr>, Span) -> Expr) = match op {
        AssignOp::Add => ("add_assign", Expr::Add),
        AssignOp::Sub => ("sub_assign", Expr::Sub),
        AssignOp::Mul => ("mul_assign", Expr::Mul),
        AssignOp::Div => ("div_assign", Expr::Div),
        AssignOp::Rem => ("rem_assign", Expr::Mod),
        AssignOp::BitAnd => ("bitand_assign", Expr::Ampersand),
        AssignOp::BitOr => ("bitor_assign", Expr::Pipe),
        AssignOp::BitXor => ("bitxor_assign", Expr::Caret),
        AssignOp::Shl => ("shl_assign", Expr::Shl),
        AssignOp::Shr => ("shr_assign", Expr::Shr),
    };

    let saved_moves = scopes.snapshot_moves();
    let mut probe_errors = Vec::new();
    let probe_lhs = type_check_expr(scopes, &mut probe_errors, type_ctx, lhs);
    let overloaded_fn = probe_lhs
        .as_ref()
        .and_then(|tl| extract_struct_name_from_ty(type_ctx, tl.ty()))
        .and_then(|sname| lookup_struct_method_fn(type_ctx, sname, method));

    if let (Some(mut t_lhs), Some(fn_info)) = (probe_lhs, overloaded_fn) {
        errors.extend(probe_errors);
        let pre_rhs_moves = scopes.snapshot_moves();
        let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
        if crate::sanal::compat::is_diverging_expr(&t_rhs) {
            scopes.restore_moves(&pre_rhs_moves);
        }

        if let Some(first_param) = fn_info.params.first() {
            let expected_self = type_ctx.infer.borrow_mut().probe(first_param.ty);
            let actual_lhs = type_ctx.infer.borrow_mut().probe(t_lhs.ty());
            if matches!(expected_self, Type::MutRef(_)) {
                check_compound_assign_lhs_mutability(lhs, &t_lhs, scopes, errors, type_ctx, span);
                if !matches!(actual_lhs, Type::MutRef(_) | Type::Ref(_)) {
                    let lhs_span = t_lhs.span();
                    t_lhs = TypedExpr::Ref(
                        Box::new(t_lhs),
                        true,
                        Type::MutRef(crate::ast::intern_type(actual_lhs)),
                        lhs_span,
                    );
                }
            } else if matches!(expected_self, Type::Ref(_))
                && !matches!(actual_lhs, Type::MutRef(_) | Type::Ref(_))
            {
                let lhs_span = t_lhs.span();
                t_lhs = TypedExpr::Ref(
                    Box::new(t_lhs),
                    false,
                    Type::Ref(crate::ast::intern_type(actual_lhs)),
                    lhs_span,
                );
            }
        }

        return Some(finish_overloaded_op_call(
            fn_info,
            vec![t_lhs, t_rhs],
            scopes,
            errors,
            type_ctx,
            span,
        ));
    }

    scopes.restore_moves(&saved_moves);
    let desugared_rhs = bin_ctor(Box::new(lhs.clone()), Box::new(rhs.clone()), span.clone());
    match lhs {
        Expr::Ident(name, _) => {
            crate::sanal::vars::type_check_assign(scopes, errors, type_ctx, name, &desugared_rhs, span)
        }
        Expr::FieldAccess(obj, field, _) => crate::sanal::objects::type_check_field_assign(
            scopes,
            errors,
            type_ctx,
            obj,
            field,
            &desugared_rhs,
            span,
        ),
        Expr::IndexAccess(target, idx, _) => crate::sanal::objects::indexing::type_check_index_assign(
            scopes,
            errors,
            type_ctx,
            target,
            idx,
            &desugared_rhs,
            span,
        ),
        Expr::Deref(inner, _) => crate::sanal::refs::type_check_deref_assign(
            scopes,
            errors,
            type_ctx,
            inner,
            &desugared_rhs,
            span,
        ),
        _ => {
            errors.push(SemanticError {
                code: "E0070",
                message: "Invalid left-hand side of compound assignment".to_string(),
                label: "Expected assignable place".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
            None
        }
    }
}
