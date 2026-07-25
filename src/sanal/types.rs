use crate::{
    ast::{Expr, FuncDecl, Span, Type, TypedExpr, intern_str},
    sanal::{ScopeStack, SemanticError, StructLayout},
};
use std::collections::HashMap;

#[derive(Clone)]
pub struct TypeCtx<'a> {
    pub fn_map: &'a HashMap<String, &'a FuncDecl>,
    pub struct_map: &'a HashMap<String, StructLayout>,
    pub enum_map: &'a HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>,
    pub extern_fn_names: &'a std::collections::HashSet<String>,
    pub is_unsafe: bool,
}

/// Type checks an untyped Expr and produces a TypedExpr
pub fn type_check_expr<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    expr: &Expr,
) -> Option<TypedExpr> {
    match expr {
        Expr::Int(n, span) => Some(TypedExpr::Int(*n, span.clone())),
        Expr::Float(f, span) => Some(TypedExpr::Float(*f, span.clone())),
        Expr::Bool(b, span) => Some(TypedExpr::Bool(*b, span.clone())),
        Expr::String(s, span) => Some(TypedExpr::String(s.clone(), span.clone())),

        Expr::Ident(name, span) => {
            if let Some(info) = scopes.lookup(name) {
                Some(TypedExpr::Ident(name.clone(), info.ty, span.clone()))
            } else {
                let normalized = name.replace("::", "_");
                if type_ctx.struct_map.contains_key(&normalized) {
                    Some(TypedExpr::Ident(name.clone(), Type::Obj(intern_str(&normalized)), span.clone()))
                } else if type_ctx.enum_map.contains_key(&normalized) {
                    Some(TypedExpr::Ident(name.clone(), Type::Enum(intern_str(&normalized)), span.clone()))
                } else {
                    errors.push(SemanticError {
                        message: format!("Undefined variable '{name}'"),
                        label: "Variable does not exist in this scope".to_string(),
                        help: None,
                        span: span.clone(),
                    });
                    None
                }
            }
        }

        Expr::Let(name, is_mutable, value, span) => {
            let typed_val = type_check_expr(scopes, errors, type_ctx, value)?;
            let mut ty = typed_val.ty();

            if *is_mutable {
                if ty == Type::Str {
                    ty = Type::String;
                } else if let Type::Array(elem_ty, _) = ty {
                    ty = Type::Vec(elem_ty);
                } else if let Type::Slice(elem_ty) = ty {
                    ty = Type::Vec(elem_ty);
                }
            } else {
                if ty == Type::String {
                    ty = Type::Str;
                } else if let Type::Array(elem_ty, _) = ty {
                    ty = Type::Slice(elem_ty);
                } else if let Type::Vec(elem_ty) = ty {
                    ty = Type::Slice(elem_ty);
                }
            }

            scopes.declare(name.clone(), *is_mutable, ty);
            Some(TypedExpr::Let(
                name.clone(),
                *is_mutable,
                Box::new(typed_val),
                ty,
                span.clone(),
            ))
        }

        Expr::Assign(name, value, span) => {
            let typed_val = type_check_expr(scopes, errors, type_ctx, value)?;

            if let Some(info) = scopes.lookup(name) {
                if !info.is_mutable {
                    errors.push(SemanticError {
                        message: format!("Cannot reassign immutable variable '{name}'"),
                        label: format!("Variable '{name}' is immutable"),
                        help: Some(format!(
                            "Consider declaring this variable as mutable: 'let mut {name}'"
                        )),
                        span: span.clone(),
                    });
                }

                // Optional: Check if typed_val.ty() matches info.ty!
                if typed_val.ty() != info.ty {
                    errors.push(SemanticError {
                        message: format!(
                            "Cannot assign type `{:?}` to variable '{name}' of type `{:?}`",
                            typed_val.ty(),
                            info.ty
                        ),
                        label: "Type mismatch".to_string(),
                        help: None,
                        span: span.clone(),
                    });
                }
            } else {
                errors.push(SemanticError {
                    message: format!("Cannot assign to undefined variable '{name}'"),
                    label: format!("Variable '{name}' does not exist in this scope"),
                    help: None,
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Assign(
                name.clone(),
                Box::new(typed_val),
                span.clone(),
            ))
        }

        Expr::Add(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
            let ty = check_binary_op("+", &t_lhs, &t_rhs, true, span, errors);
            Some(TypedExpr::Add(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Sub(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
            let ty = check_binary_op("-", &t_lhs, &t_rhs, true, span, errors);
            Some(TypedExpr::Sub(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Mul(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
            let ty = check_binary_op("*", &t_lhs, &t_rhs, true, span, errors);
            Some(TypedExpr::Mul(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Div(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
            let ty = check_binary_op("/", &t_lhs, &t_rhs, true, span, errors);
            Some(TypedExpr::Div(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Pipe(lhs, rhs, span) => {
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

        Expr::Ampersand(lhs, rhs, span) => {
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

        Expr::Caret(lhs, rhs, span) => {
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

        Expr::Shl(lhs, rhs, span) => {
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

        Expr::Shr(lhs, rhs, span) => {
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

        Expr::Mod(lhs, rhs, span) => {
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

        Expr::Neg(val, span) => {
            let t_val = type_check_expr(scopes, errors, type_ctx, val)?;
            let ty = t_val.ty();

            if ty != Type::Int && ty != Type::Float {
                errors.push(SemanticError {
                    message: format!("Cannot negate non-numeric type `{:?}`", ty),
                    label: "Invalid negation".into(),
                    help: Some("The '-' operator can only be used on integers and floats".into()),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Neg(Box::new(t_val), ty, span.clone()))
        }

        Expr::Not(val, span) => {
            let t_val = type_check_expr(scopes, errors, type_ctx, val)?;

            if t_val.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!(
                        "Cannot apply logical NOT to non-boolean type `{:?}`",
                        t_val.ty()
                    ),
                    label: "Expected boolean expression".into(),
                    help: None,
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Not(Box::new(t_val), span.clone()))
        }

        Expr::GreaterThan(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
            Some(TypedExpr::GreaterThan(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::LessThan(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;
            Some(TypedExpr::LessThan(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::GreaterEqual(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

            let l_ty = t_lhs.ty();
            let r_ty = t_rhs.ty();

            // Ensure both sides are numeric (Int or Float)
            if !(l_ty == Type::Int || l_ty == Type::Float)
                || !(r_ty == Type::Int || r_ty == Type::Float)
            {
                errors.push(SemanticError {
                    message: format!("Cannot compare types `{l_ty:?}` and `{r_ty:?}` with '>='"),
                    label: "Invalid comparison operator".into(),
                    help: Some(
                        "Ordering comparisons can only be used on numbers (`Int` or `Float`)"
                            .into(),
                    ),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::LessEqual(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::LessEqual(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

            let l_ty = t_lhs.ty();
            let r_ty = t_rhs.ty();

            // Ensure both sides are numeric (Int or Float)
            if !(l_ty == Type::Int || l_ty == Type::Float)
                || !(r_ty == Type::Int || r_ty == Type::Float)
            {
                errors.push(SemanticError {
                    message: format!("Cannot compare types `{l_ty:?}` and `{r_ty:?}` with '<='"),
                    label: "Invalid comparison operator".into(),
                    help: Some(
                        "Ordering comparisons can only be used on numbers (`Int` or `Float`)"
                            .into(),
                    ),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::LessEqual(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::Equal(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

            let l_ty = t_lhs.ty();
            let r_ty = t_rhs.ty();

            if l_ty != r_ty {
                errors.push(SemanticError {
                    message: format!(
                        "Cannot compare distinct types `{l_ty:?}` and `{r_ty:?}` for equality"
                    ),
                    label: format!("Type mismatch: `{l_ty:?}` vs `{r_ty:?}`"),
                    help: Some(
                        "Both operands must be the exact same type to check for equality".into(),
                    ),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Equal(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::NotEqual(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

            let l_ty = t_lhs.ty();
            let r_ty = t_rhs.ty();

            if l_ty != r_ty {
                errors.push(SemanticError {
                    message: format!(
                        "Cannot compare distinct types `{l_ty:?}` and `{r_ty:?}` for equality"
                    ),
                    label: format!("Type mismatch: `{l_ty:?}` vs `{r_ty:?}`"),
                    help: Some(
                        "Both operands must be the exact same type to check for equality".into(),
                    ),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::NotEqual(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::And(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

            if t_lhs.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!(
                        "Left side of '&&' must be a `Bool`, found `{:?}`",
                        t_lhs.ty()
                    ),
                    label: "Expected boolean".into(),
                    help: None,
                    span: t_lhs.span().clone(),
                });
            }

            if t_rhs.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!(
                        "Right side of '&&' must be a `Bool`, found `{:?}`",
                        t_rhs.ty()
                    ),
                    label: "Expected boolean".into(),
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

        Expr::Or(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, type_ctx, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, type_ctx, rhs)?;

            if t_lhs.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!(
                        "Left side of '||' must be a `Bool`, found `{:?}`",
                        t_lhs.ty()
                    ),
                    label: "Expected boolean".into(),
                    help: None,
                    span: t_lhs.span().clone(),
                });
            }

            if t_rhs.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!(
                        "Right side of '||' must be a `Bool`, found `{:?}`",
                        t_rhs.ty()
                    ),
                    label: "Expected boolean".into(),
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

        Expr::Block(stmts, span) => {
            scopes.push_scope();
            let mut typed_stmts = Vec::new();
            for stmt in stmts {
                if let Some(t_stmt) = type_check_expr(scopes, errors, type_ctx, stmt) {
                    typed_stmts.push(t_stmt);
                }
            }
            scopes.pop_scope();
            let block_ty = typed_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
            Some(TypedExpr::Block(typed_stmts, block_ty, span.clone()))
        }

        Expr::Unsafe(stmts, span) => {
            scopes.push_scope();
            let mut unsafe_ctx = type_ctx.clone();
            unsafe_ctx.is_unsafe = true;
            let mut typed_stmts = Vec::new();
            for stmt in stmts {
                if let Some(t_stmt) = type_check_expr(scopes, errors, &unsafe_ctx, stmt) {
                    typed_stmts.push(t_stmt);
                }
            }
            scopes.pop_scope();
            let block_ty = typed_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
            Some(TypedExpr::Unsafe(typed_stmts, block_ty, span.clone()))
        }

        Expr::While(cond, body, span) => {
            let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
            let t_body = type_check_expr(scopes, errors, type_ctx, body)?;

            if t_cond.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!(
                        "`while` condition must be a `Bool`, found `{:?}`",
                        t_cond.ty()
                    ),
                    label: "Expected boolean condition".into(),
                    help: None,
                    span: t_cond.span().clone(),
                });
            }

            Some(TypedExpr::While(
                Box::new(t_cond),
                Box::new(t_body),
                span.clone(),
            ))
        }

        Expr::If(cond, body, span) => {
            let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
            let t_body = type_check_expr(scopes, errors, type_ctx, body)?;

            // 1. Condition must be a boolean
            if t_cond.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!("`if` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
                    label: "Expected boolean expression".into(),
                    help: Some("Try using a comparison operator like ==, <, or >".into()),
                    span: t_cond.span().clone(),
                });
            }

            Some(TypedExpr::If(
                Box::new(t_cond),
                Box::new(t_body),
                span.clone(),
            ))
        }

        Expr::IfElse(cond, then_b, else_b, span) => {
            let t_cond = type_check_expr(scopes, errors, type_ctx, cond)?;
            let t_then = type_check_expr(scopes, errors, type_ctx, then_b)?;
            let t_else = type_check_expr(scopes, errors, type_ctx, else_b)?;

            // 1. Condition check
            if t_cond.ty() != Type::Bool {
                errors.push(SemanticError {
                    message: format!("`if` condition must be a `Bool`, found `{:?}`", t_cond.ty()),
                    label: "Expected boolean expression".into(),
                    help: None,
                    span: t_cond.span().clone(),
                });
            }

            // 2. Both branches must produce the same type!
            if t_then.ty() != t_else.ty() {
                errors.push(SemanticError {
                    message: format!(
                        "`if` and `else` branches have incompatible types (`{:?}` vs `{:?}`)",
                        t_then.ty(),
                        t_else.ty()
                    ),
                    label: format!("Expected `{:?}` because of `if` branch", t_then.ty()),
                    help: Some(
                        "Both branches of an if/else expression must yield the exact same type"
                            .into(),
                    ),
                    span: t_else.span().clone(),
                });
            }

            let res_ty = t_then.ty();
            Some(TypedExpr::IfElse(
                Box::new(t_cond),
                Box::new(t_then),
                Box::new(t_else),
                res_ty,
                span.clone(),
            ))
        }

        Expr::Return(opt_expr, span) => {
            let t_opt = match opt_expr {
                Some(e) => Some(Box::new(type_check_expr(scopes, errors, type_ctx, e)?)),
                None => None,
            };
            Some(TypedExpr::Return(t_opt, span.clone()))
        }

        Expr::MacroCall(name, args, span) => {
            let mut typed_args = Vec::new();
            for arg in args {
                if let Some(t_arg) = type_check_expr(scopes, errors, type_ctx, arg) {
                    typed_args.push(t_arg);
                }
            }
            Some(TypedExpr::MacroCall(name.clone(), typed_args, span.clone()))
        }

        Expr::Call(raw_name, args, span) => {
            let name = raw_name.replace("::", "_");
            let mut typed_args = Vec::new();
            for arg in args {
                if let Some(t_arg) = type_check_expr(scopes, errors, type_ctx, arg) {
                    typed_args.push(t_arg);
                }
            }
            if name == "push_str" || name == "push" || name == "pop" {
                if !typed_args.is_empty() {
                    if let TypedExpr::Ident(var_name, _, _) = &typed_args[0] {
                        if let Some(target_info) = scopes.lookup(var_name) {
                            if !target_info.is_mutable {
                                errors.push(SemanticError {
                                    message: format!("Cannot call mutating method '{name}' on immutable variable '{var_name}'"),
                                    label: format!("'{var_name}' is immutable"),
                                    help: Some(format!("Declare as mutable: 'let mut {var_name}'")),
                                    span: span.clone(),
                                });
                            }
                        }
                    }
                }
                return Some(TypedExpr::MacroCall(name.clone(), typed_args, span.clone()));
            }
            let mut resolved_name = name.clone();
            if let Some((target_or_var, method_name)) = name.split_once('.') {
                if let Some((static_enum_name, variants)) = type_ctx.enum_map.get(target_or_var) {
                    if let Some((disc, _)) = variants.get(method_name) {
                        return Some(TypedExpr::EnumConstruct(
                            target_or_var.to_string(),
                            method_name.to_string(),
                            *disc as usize,
                            typed_args,
                            Type::Enum(static_enum_name),
                            span.clone(),
                        ));
                    }
                }

                let mangled = format!("{}_{}", target_or_var, method_name);
                if method_name == "len" || method_name == "push" || method_name == "pop" || method_name == "push_str" {
                    if let Some(target_info) = scopes.lookup(target_or_var) {
                        if (method_name == "push" || method_name == "push_str" || method_name == "pop") && !target_info.is_mutable {
                            errors.push(SemanticError {
                                message: format!("Cannot call mutating method '{method_name}' on immutable variable '{target_or_var}'"),
                                label: format!("'{target_or_var}' is immutable"),
                                help: Some(format!("Declare as mutable: 'let mut {target_or_var}'")),
                                span: span.clone(),
                            });
                        }
                    }
                    if let Some(target_expr) = type_check_expr(
                        scopes,
                        errors,
                        type_ctx,
                        &Expr::Ident(target_or_var.to_string(), span.clone()),
                    ) {
                        typed_args.insert(0, target_expr);
                        return Some(TypedExpr::MacroCall(method_name.to_string(), typed_args, span.clone()));
                    }
                }
                if type_ctx.fn_map.contains_key(&mangled) {
                    resolved_name = mangled;
                } else if let Some(var_info) = scopes.lookup(target_or_var) {
                    match var_info.ty {
                        Type::DynTrait(trait_name) => {
                            let target_expr = Expr::Ident(target_or_var.to_string(), span.clone());
                            if let Some(t_target) = type_check_expr(scopes, errors, type_ctx, &target_expr) {
                                return Some(TypedExpr::DynCall(
                                    Box::new(t_target),
                                    method_name.to_string(),
                                    typed_args,
                                    Type::Bool,
                                    span.clone(),
                                ));
                            }
                        }
                        Type::Generic(_g_name) => {
                            let target_expr = Expr::Ident(target_or_var.to_string(), span.clone());
                            if let Some(t_target) = type_check_expr(scopes, errors, type_ctx, &target_expr) {
                                typed_args.insert(0, t_target);
                                return Some(TypedExpr::Call(
                                    method_name.to_string(),
                                    typed_args,
                                    Type::Bool,
                                    span.clone(),
                                ));
                            }
                        }
                        Type::Obj(tn) | Type::Enum(tn) => {
                            let var_mangled = format!("{}_{}", tn, method_name);
                            if type_ctx.fn_map.contains_key(&var_mangled) {
                                resolved_name = var_mangled;
                                if let Some(target_expr) = type_check_expr(
                                    scopes,
                                    errors,
                                    type_ctx,
                                    &Expr::Ident(target_or_var.to_string(), span.clone()),
                                ) {
                                    typed_args.insert(0, target_expr);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            } else if !type_ctx.fn_map.contains_key(&name) && !typed_args.is_empty() {
                if let Type::DynTrait(_trait_name) = typed_args[0].ty() {
                    let receiver = typed_args.remove(0);
                    return Some(TypedExpr::DynCall(
                        Box::new(receiver),
                        name.to_string(),
                        typed_args,
                        Type::Bool,
                        span.clone(),
                    ));
                }
                if let TypedExpr::Ident(target_name, _, _) = &typed_args[0] {
                    let normalized_target = target_name.replace("::", "_");
                    let mangled = format!("{}_{}", normalized_target, name);
                    if type_ctx.fn_map.contains_key(&mangled) {
                        resolved_name = mangled;
                        if type_ctx.struct_map.contains_key(&normalized_target) || type_ctx.enum_map.contains_key(&normalized_target) {
                            typed_args.remove(0);
                        }
                    }
                }
                if resolved_name == name {
                    let first_arg_ty = typed_args[0].ty();
                    let type_name = match first_arg_ty {
                        Type::Obj(n) => Some(n),
                        Type::Enum(n) => Some(n),
                        _ => None,
                    };
                    if let Some(tn) = type_name {
                        let mangled = format!("{}_{}", tn, name);
                        let mono_mangled = format!("{}_{}", name, tn);
                        if type_ctx.fn_map.contains_key(&mangled) {
                            resolved_name = mangled;
                        } else if type_ctx.fn_map.contains_key(&mono_mangled) {
                            resolved_name = mono_mangled;
                        }
                    }
                }
            }

            if let Some(target_func) = type_ctx.fn_map.get(&resolved_name) {
                if target_func.where_clause.is_some() || target_func.params.iter().any(|p| matches!(p.ty, Type::Generic(_))) {
                    if !typed_args.is_empty() {
                        let tn = typed_args[0].ty().name_or_default();
                        let mono_mangled = format!("{}_{}", resolved_name, tn);
                        if type_ctx.fn_map.contains_key(&mono_mangled) {
                            resolved_name = mono_mangled;
                        }
                    }
                }
            }

            if type_ctx.extern_fn_names.contains(&resolved_name) && !type_ctx.is_unsafe {
                errors.push(SemanticError {
                    message: format!("Call to extern C function '{resolved_name}' requires an 'unsafe:' block"),
                    label: "Foreign C function call requires 'unsafe:' block".to_string(),
                    help: Some("Wrap this call inside an 'unsafe:' block".to_string()),
                    span: span.clone(),
                });
            }

            let ret_ty = if let Some(target_func) = type_ctx.fn_map.get(&resolved_name) {
                if target_func.params.len() != typed_args.len() {
                    errors.push(SemanticError {
                        message: format!(
                            "Function '{resolved_name}' expects {} arguments, found {}",
                            target_func.params.len(),
                            typed_args.len()
                        ),
                        label: format!("Expected {} args", target_func.params.len()),
                        help: None,
                        span: span.clone(),
                    });
                }
                if target_func.params.len() == typed_args.len() {
                    for (param, arg) in target_func.params.iter().zip(typed_args.iter_mut()) {
                        if let Type::DynTrait(t_name) = param.ty {
                            *arg = TypedExpr::CoerceToDyn(Box::new(arg.clone()), t_name, span.clone());
                        }
                    }
                }
                target_func.return_type
            } else {
                errors.push(SemanticError {
                    message: format!("Undefined function '{resolved_name}'"),
                    label: "Function does not exist".to_string(),
                    help: None,
                    span: span.clone(),
                });
                Type::Unit
            };

            Some(TypedExpr::Call(
                resolved_name,
                typed_args,
                ret_ty,
                span.clone(),
            ))
        }

        Expr::ArrayInit(elems, span) => {
            let mut typed_elems = Vec::new();
            for e in elems {
                if let Some(te) = type_check_expr(scopes, errors, type_ctx, e) {
                    typed_elems.push(te);
                }
            }

            let elem_ty = if !typed_elems.is_empty() {
                typed_elems[0].ty()
            } else {
                Type::Int
            };

            // Verify all array elements match the first element's type
            for (i, elem) in typed_elems.iter().enumerate().skip(1) {
                if elem.ty() != elem_ty {
                    errors.push(SemanticError {
                message: format!(
                    "Array elements must all have the same type. Expected `{:?}`, element {} has type `{:?}`",
                    elem_ty, i + 1, elem.ty()
                ),
                label: format!("Expected `{:?}`", elem_ty),
                help: Some("Arrays are homogeneous and cannot hold mixed types".into()),
                span: elem.span().clone(),
            });
                }
            }

            let arr_ty = Type::Array(crate::ast::intern_type(elem_ty), typed_elems.len());
            Some(TypedExpr::ArrayInit(typed_elems, arr_ty, span.clone()))
        }

        Expr::IndexAccess(target, idx, span) => {
            let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
            let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;

            // 1. Validate index is an integer
            if t_idx.ty() != Type::Int {
                errors.push(SemanticError {
                    message: format!("Array index must be an `Int`, found `{:?}`", t_idx.ty()),
                    label: "Invalid index type".into(),
                    help: None,
                    span: t_idx.span().clone(),
                });
            }

            // 2. Validate target is indexable
            let elem_ty = match t_target.ty() {
                Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => *e_ty,
                other_ty => {
                    errors.push(SemanticError {
                        message: format!("Cannot index into non-array type `{:?}`", other_ty),
                        label: "Not an array".into(),
                        help: None,
                        span: t_target.span().clone(),
                    });
                    Type::Int // Fallback recovery type
                }
            };

            Some(TypedExpr::IndexAccess(
                Box::new(t_target),
                Box::new(t_idx),
                elem_ty,
                span.clone(),
            ))
        }

        Expr::IndexAssign(target, idx, val, span) => {
            let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
            let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;
            let t_val = type_check_expr(scopes, errors, type_ctx, val)?;

            if t_idx.ty() != Type::Int {
                errors.push(SemanticError {
                    message: format!("Array index must be an `Int`, found `{:?}`", t_idx.ty()),
                    label: "Invalid index type".into(),
                    help: None,
                    span: t_idx.span().clone(),
                });
            }

            let opt_elem_ty = match t_target.ty() {
                Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => Some(*e_ty),
                _ => None,
            };
            if let Some(elem_ty) = opt_elem_ty {
                if elem_ty != t_val.ty() {
                    errors.push(SemanticError {
                        message: format!(
                            "Cannot assign type `{:?}` to array holding `{:?}`",
                            t_val.ty(),
                            elem_ty
                        ),
                        label: "Type mismatch".into(),
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

        Expr::ObjInit(raw_name, fields, span) => {
            let name = &raw_name.replace("::", "_");
            let mut typed_fields = Vec::new();
            for (f_name, f_expr) in fields {
                let t_expr = type_check_expr(scopes, errors, type_ctx, f_expr)?;
                typed_fields.push((f_name.clone(), t_expr));
            }

            if let Some(layout) = type_ctx.struct_map.get(name) {
                // A. Check for missing required fields
                for (expected_field, (_, expected_ty)) in &layout.field_offsets {
                    if !typed_fields.iter().any(|(f, _)| f == expected_field) {
                        errors.push(SemanticError {
                    message: format!("Missing field '{expected_field}' in struct initialization of '{name}'"),
                    label: format!("Field '{expected_field}: {expected_ty:?}' is missing"),
                    help: None,
                    span: span.clone(),
                });
                    }
                }

                // B. Check field types and unknown fields
                for (f_name, f_expr) in &typed_fields {
                    if let Some((_, expected_ty)) = layout.field_offsets.get(f_name) {
                        if expected_ty != &f_expr.ty() {
                            errors.push(SemanticError {
                        message: format!(
                            "Field '{f_name}' in struct '{name}' expects type `{:?}`, found `{:?}`",
                            expected_ty, f_expr.ty()
                        ),
                        label: format!("Expected `{:?}`", expected_ty),
                        help: None,
                        span: f_expr.span().clone(),
                    });
                        }
                    } else {
                        errors.push(SemanticError {
                            message: format!("Struct '{name}' has no field named '{f_name}'"),
                            label: "Unknown field".into(),
                            help: None,
                            span: f_expr.span().clone(),
                        });
                    }
                }
            } else {
                errors.push(SemanticError {
                    message: format!("Undefined struct '{name}'"),
                    label: "Struct does not exist".into(),
                    help: None,
                    span: span.clone(),
                });
            }

            let obj_ty = Type::Obj(intern_str(name));
            Some(TypedExpr::ObjInit(
                name.clone(),
                typed_fields,
                obj_ty,
                span.clone(),
            ))
        }

        Expr::FieldAccess(target, field_name, span) => {
            if let Expr::Ident(ref enum_name, _) = **target {
                if let Some((static_enum_name, variants)) = type_ctx.enum_map.get(enum_name) {
                    if let Some((disc, _)) = variants.get(field_name) {
                        return Some(TypedExpr::EnumConstruct(
                            enum_name.clone(),
                            field_name.clone(),
                            *disc as usize,
                            vec![],
                            Type::Enum(static_enum_name),
                            span.clone(),
                        ));
                    }
                }
            }

            let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
            let mut field_ty = Type::Int;

            if let Type::Obj(struct_name) = t_target.ty() {
                if let Some(layout) = type_ctx.struct_map.get(struct_name) {
                    if let Some((_, fty)) = layout.field_offsets.get(field_name) {
                        field_ty = *fty;
                    } else {
                        errors.push(SemanticError {
                            message: format!("Struct '{struct_name}' has no field '{field_name}'"),
                            label: "Field not found".to_string(),
                            help: None,
                            span: span.clone(),
                        });
                    }
                }
            } else {
                errors.push(SemanticError {
                    message: format!("Cannot access field on non-object type {:?}", t_target.ty()),
                    label: "Not a struct object".to_string(),
                    help: None,
                    span: span.clone(),
                });
            }

            Some(TypedExpr::FieldAccess(
                Box::new(t_target),
                field_name.clone(),
                field_ty,
                span.clone(),
            ))
        }

        Expr::FieldAssign(target, field_name, val, span) => {
            let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
            let t_val = type_check_expr(scopes, errors, type_ctx, val)?;

            if let Expr::Ident(var_name, _) = target.as_ref() {
                if let Some(info) = scopes.lookup(var_name) {
                    if !info.is_mutable {
                        errors.push(SemanticError {
                            message: format!(
                                "Cannot mutate field of immutable object '{var_name}'"
                            ),
                            label: "Object is immutable".to_string(),
                            help: Some(format!("Declare as mutable: 'let mut {var_name}'")),
                            span: span.clone(),
                        });
                    }
                }
            }

            Some(TypedExpr::FieldAssign(
                Box::new(t_target),
                field_name.clone(),
                Box::new(t_val),
                span.clone(),
            ))
        }

        Expr::EnumConstruct(enum_name, variant_name, args, span) => {
            let mut typed_args = Vec::new();
            for a in args {
                if let Some(ta) = type_check_expr(scopes, errors, type_ctx, a) {
                    typed_args.push(ta);
                }
            }

            let mut disc = 0;
            let mut static_enum_name = intern_str(enum_name);

            if let Some((static_name, variants)) = type_ctx.enum_map.get(enum_name) {
                static_enum_name = *static_name;
                if let Some((d, _)) = variants.get(variant_name) {
                    disc = *d as usize;
                }
            }

            Some(TypedExpr::EnumConstruct(
                enum_name.clone(),
                variant_name.clone(),
                disc,
                typed_args,
                Type::Enum(static_enum_name),
                span.clone(),
            ))
        }
    }
}

fn check_binary_op(
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
        (Type::Int, Type::Int) => Type::Int,
        (Type::Float, Type::Float) if allow_float => Type::Float,

        // Mixed Int and Float (if you allow implicit promotion)
        (Type::Int, Type::Float) | (Type::Float, Type::Int) if allow_float => Type::Float,

        // Invalid types for math/bitwise
        _ => {
            errors.push(SemanticError {
                message: format!("Cannot perform '{op_name}' on types `{l_ty:?}` and `{r_ty:?}`"),
                label: format!("Type mismatch: `{l_ty:?}` vs `{r_ty:?}`"),
                help: if !allow_float && (l_ty == Type::Float || r_ty == Type::Float) {
                    Some("Bitwise operations can only be used on integers.".into())
                } else {
                    Some("Both operands must be numeric types.".into())
                },
                span: span.clone(),
            });
            Type::Int // Fallback error recovery type
        }
    }
}
