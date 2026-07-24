use crate::{
    ast::{Expr, FuncDecl, Type, TypedExpr, intern_str},
    sanal::{ScopeStack, SemanticError, StructLayout},
};
use std::collections::HashMap;

/// Type checks an untyped Expr and produces a TypedExpr
pub fn type_check_expr(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    fn_map: &HashMap<String, &FuncDecl>,
    struct_map: &HashMap<String, StructLayout>,
    enum_map: &HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>,
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
                errors.push(SemanticError {
                    message: format!("Undefined variable '{name}'"),
                    label: "Variable does not exist in this scope".to_string(),
                    help: None,
                    span: span.clone(),
                });
                None
            }
        }

        Expr::Let(name, is_mutable, value, span) => {
            let typed_val = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, value)?;
            let ty = typed_val.ty();
            scopes.declare(name.clone(), *is_mutable, ty);
            Some(TypedExpr::Let(
                name.clone(),
                *is_mutable,
                Box::new(typed_val),
                ty,
                span.clone(),
            ))
        }

        Expr::Assign(name, value, span) => match scopes.lookup(name) {
            Some(info) => {
                let err = format!("Cannot reassign immutable variable '{name}'");
                if !info.is_mutable {
                    errors.push(SemanticError {
                        message: err.clone(),
                        label: err,
                        help: Some(format!(
                            "Consider declaring this variable as mutable: 'let mut {name}'"
                        )),
                        span: span.clone(),
                    });
                }
                let typed_val = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, value)?;
                Some(TypedExpr::Assign(
                    name.clone(),
                    Box::new(typed_val),
                    span.clone(),
                ))
            }
            None => {
                errors.push(SemanticError {
                    message: format!("Cannot assign to undefined variable '{name}'"),
                    label: format!("Variable '{name}' does not exist in this scope"),
                    help: None,
                    span: span.clone(),
                });
                let typed_val = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, value)?;
                errors.retain(|err| !(err.message == format!("Undefined variable '{name}'")));
                Some(TypedExpr::Assign(
                    name.clone(),
                    Box::new(typed_val),
                    span.clone(),
                ))
            }
        },

        Expr::Add(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };
            Some(TypedExpr::Add(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Sub(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };
            Some(TypedExpr::Sub(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Mul(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };
            Some(TypedExpr::Mul(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Div(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };
            Some(TypedExpr::Div(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Pipe(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };

            if ty != Type::Int {
                errors.push(SemanticError {
                    message: "You can only use bitwise operators on integers.".into(),
                    label: "Invalid Use of Bitwise Operator".into(),
                    help: Some("Use an integer instead, or use: +, -, *, /".into()),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Pipe(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Ampersand(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };

            if ty != Type::Int {
                errors.push(SemanticError {
                    message: "You can only use bitwise operators on integers.".into(),
                    label: "Invalid Use of Bitwise Operator".into(),
                    help: Some("Use an integer instead, or use: +, -, *, /".into()),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Ampersand(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Caret(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };

            if ty != Type::Int {
                errors.push(SemanticError {
                    message: "You can only use bitwise operators on integers.".into(),
                    label: "Invalid Use of Bitwise Operator".into(),
                    help: Some("Use an integer instead, or use: +, -, *, /".into()),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Caret(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Shr(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };

            if ty != Type::Int {
                errors.push(SemanticError {
                    message: "You can only use bitwise operators on integers.".into(),
                    label: "Invalid Use of Bitwise Operator".into(),
                    help: Some("Use an integer instead, or use: +, -, *, /".into()),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Shr(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Shl(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };

            if ty != Type::Int {
                errors.push(SemanticError {
                    message: "You can only use bitwise operators on integers.".into(),
                    label: "Invalid Use of Bitwise Operator".into(),
                    help: Some("Use an integer instead, or use: +, -, *, /".into()),
                    span: span.clone(),
                });
            }

            Some(TypedExpr::Shl(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Mod(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            let ty = if t_lhs.ty() == Type::Float || t_rhs.ty() == Type::Float {
                Type::Float
            } else {
                Type::Int
            };
            Some(TypedExpr::Mod(
                Box::new(t_lhs),
                Box::new(t_rhs),
                ty,
                span.clone(),
            ))
        }

        Expr::Neg(val, span) => {
            let t_val = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, val)?;
            let ty = t_val.ty();
            Some(TypedExpr::Neg(Box::new(t_val), ty, span.clone()))
        }

        Expr::Not(val, span) => {
            let t_val = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, val)?;
            Some(TypedExpr::Not(Box::new(t_val), span.clone()))
        }

        Expr::GreaterThan(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            Some(TypedExpr::GreaterThan(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::LessThan(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            Some(TypedExpr::LessThan(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::GreaterEqual(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            Some(TypedExpr::GreaterEqual(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::LessEqual(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            Some(TypedExpr::LessEqual(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::Equal(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            Some(TypedExpr::Equal(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::NotEqual(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            Some(TypedExpr::NotEqual(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::And(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
            Some(TypedExpr::And(
                Box::new(t_lhs),
                Box::new(t_rhs),
                span.clone(),
            ))
        }

        Expr::Or(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, rhs)?;
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
                if let Some(t_stmt) = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, stmt) {
                    typed_stmts.push(t_stmt);
                }
            }
            scopes.pop_scope();
            let block_ty = typed_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
            Some(TypedExpr::Block(typed_stmts, block_ty, span.clone()))
        }

        Expr::While(cond, body, span) => {
            let t_cond = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, cond)?;
            let t_body = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, body)?;
            Some(TypedExpr::While(
                Box::new(t_cond),
                Box::new(t_body),
                span.clone(),
            ))
        }

        Expr::If(cond, body, span) => {
            let t_cond = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, cond)?;
            let t_body = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, body)?;
            Some(TypedExpr::If(
                Box::new(t_cond),
                Box::new(t_body),
                span.clone(),
            ))
        }

        Expr::IfElse(cond, then_b, else_b, span) => {
            let t_cond = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, cond)?;
            let t_then = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, then_b)?;
            let t_else = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, else_b)?;
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
                Some(e) => Some(Box::new(type_check_expr(
                    scopes, errors, fn_map, struct_map, enum_map, e,
                )?)),
                None => None,
            };
            Some(TypedExpr::Return(t_opt, span.clone()))
        }

        Expr::MacroCall(name, args, span) => {
            let mut typed_args = Vec::new();
            for arg in args {
                if let Some(t_arg) = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, arg) {
                    typed_args.push(t_arg);
                }
            }
            Some(TypedExpr::MacroCall(name.clone(), typed_args, span.clone()))
        }

        Expr::Call(name, args, span) => {
            let mut typed_args = Vec::new();
            for arg in args {
                if let Some(t_arg) = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, arg) {
                    typed_args.push(t_arg);
                }
            }
            if let Some((enum_name, variant_name)) = name.split_once('.') {
                if let Some((static_enum_name, variants)) = enum_map.get(enum_name) {
                    if let Some((disc, _)) = variants.get(variant_name) {
                        return Some(TypedExpr::EnumConstruct(
                            enum_name.to_string(),
                            variant_name.to_string(),
                            *disc as usize,
                            typed_args,
                            Type::Enum(static_enum_name),
                            span.clone(),
                        ));
                    }
                }
            }
            let ret_ty = if let Some(target_func) = fn_map.get(name) {
                if target_func.params.len() != typed_args.len() {
                    errors.push(SemanticError {
                        message: format!(
                            "Function '{name}' expects {} arguments, found {}",
                            target_func.params.len(),
                            typed_args.len()
                        ),
                        label: format!("Expected {} args", target_func.params.len()),
                        help: None,
                        span: span.clone(),
                    });
                }
                target_func.return_type
            } else {
                errors.push(SemanticError {
                    message: format!("Undefined function '{name}'"),
                    label: "Function does not exist".to_string(),
                    help: None,
                    span: span.clone(),
                });
                Type::Unit
            };

            Some(TypedExpr::Call(
                name.clone(),
                typed_args,
                ret_ty,
                span.clone(),
            ))
        }

        Expr::ArrayInit(elems, span) => {
            let mut typed_elems = Vec::new();
            for e in elems {
                if let Some(te) = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, e) {
                    typed_elems.push(te);
                }
            }
            let elem_ty = if !typed_elems.is_empty() {
                typed_elems[0].ty()
            } else {
                Type::Int
            };
            let arr_ty = Type::Array(crate::ast::intern_type(elem_ty), typed_elems.len());
            Some(TypedExpr::ArrayInit(typed_elems, arr_ty, span.clone()))
        }

        Expr::IndexAccess(target, idx, span) => {
            let t_target = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, target)?;
            let t_idx = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, idx)?;
            let elem_ty = match t_target.ty() {
                Type::Array(e_ty, _) => *e_ty,
                _ => Type::Int,
            };
            Some(TypedExpr::IndexAccess(
                Box::new(t_target),
                Box::new(t_idx),
                elem_ty,
                span.clone(),
            ))
        }

        Expr::IndexAssign(target, idx, val, span) => {
            let t_target = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, target)?;
            let t_idx = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, idx)?;
            let t_val = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, val)?;
            Some(TypedExpr::IndexAssign(
                Box::new(t_target),
                Box::new(t_idx),
                Box::new(t_val),
                span.clone(),
            ))
        }

        Expr::ObjInit(name, fields, span) => {
            let mut typed_fields = Vec::new();
            for (f_name, f_expr) in fields {
                let t_expr = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, f_expr)?;
                typed_fields.push((f_name.clone(), t_expr));
            }

            if !struct_map.contains_key(name) {
                errors.push(SemanticError {
                    message: format!("Undefined struct '{name}'"),
                    label: "Struct does not exist".to_string(),
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
                if let Some((static_enum_name, variants)) = enum_map.get(enum_name) {
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

            let t_target = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, target)?;
            let mut field_ty = Type::Int;

            if let Type::Obj(struct_name) = t_target.ty() {
                if let Some(layout) = struct_map.get(struct_name) {
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
            let t_target = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, target)?;
            let t_val = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, val)?;

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
                if let Some(ta) = type_check_expr(scopes, errors, fn_map, struct_map, enum_map, a) {
                    typed_args.push(ta);
                }
            }

            let mut disc = 0;
            let mut static_enum_name = intern_str(enum_name);

            if let Some((static_name, variants)) = enum_map.get(enum_name) {
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
