//! sanal/vars.rs
//! Type checking for variable lookup, let bindings, and assignments.

use crate::{
    ast::{intern_str, Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_ident<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    name: &str,
    span: &Span,
) -> Option<TypedExpr> {
    if let Some(info) = scopes.lookup(name) {
        Some(TypedExpr::Ident(name.to_string(), info.ty, span.clone()))
    } else if let Some((enum_part, variant_part)) = name.split_once("::") {
        let normalized_enum = enum_part.replace("::", "_");
        let found_enum = type_ctx
            .enum_map
            .iter()
            .find(|(k, _)| **k == normalized_enum || k.ends_with(&format!("_{normalized_enum}")));
        if let Some((_, (mangled_enum, v_map))) = found_enum {
            if let Some((tag, _p_types)) = v_map.get(variant_part) {
                return Some(TypedExpr::EnumConstruct(
                    mangled_enum.to_string(),
                    variant_part.to_string(),
                    *tag as usize,
                    Vec::new(),
                    Type::Enum(mangled_enum),
                    span.clone(),
                ));
            }
        }
        let normalized = name.replace("::", "_");
        let found_struct = type_ctx
            .struct_map
            .iter()
            .find(|(k, _)| **k == normalized || k.ends_with(&format!("_{normalized}")));
        let found_enum = type_ctx
            .enum_map
            .iter()
            .find(|(k, _)| **k == normalized || k.ends_with(&format!("_{normalized}")));
        if let Some((mangled_struct, _)) = found_struct {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Obj(intern_str(mangled_struct)),
                span.clone(),
            ))
        } else if let Some((mangled_enum, _)) = found_enum {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Enum(intern_str(mangled_enum)),
                span.clone(),
            ))
        } else if name == "rc"
            || name == "arc"
            || type_ctx.fn_map.contains_key(name)
            || type_ctx.fn_map.contains_key(&normalized)
            || type_ctx
                .fn_map
                .iter()
                .any(|(k, _)| **k == normalized || k.ends_with(&format!("_{normalized}")))
        {
            Some(TypedExpr::Ident(name.to_string(), Type::Int, span.clone()))
        } else {
            errors.push(SemanticError {
                message: format!("Undefined variable '{name}'"),
                label: "Variable does not exist in this scope".to_string(),
                help: None,
                span: span.clone(),
            });
            None
        }
    } else {
        let normalized = match name {
            "None" => "std_core_Option_None".to_string(),
            _ => name.replace("::", "_"),
        };
        if let Some((enum_part, variant_part)) = normalized.rsplit_once('_') {
            let found_enum = type_ctx
                .enum_map
                .iter()
                .find(|(k, _)| *k == enum_part || k.ends_with(&format!("_{enum_part}")));
            if let Some((_, (mangled_enum, v_map))) = found_enum {
                if let Some((tag, _p_types)) = v_map.get(variant_part) {
                    return Some(TypedExpr::EnumConstruct(
                        mangled_enum.to_string(),
                        variant_part.to_string(),
                        *tag as usize,
                        Vec::new(),
                        Type::Enum(mangled_enum),
                        span.clone(),
                    ));
                }
            }
        }
        let found_struct = type_ctx
            .struct_map
            .iter()
            .find(|(k, _)| **k == normalized || k.ends_with(&format!("_{normalized}")));
        let found_enum = type_ctx
            .enum_map
            .iter()
            .find(|(k, _)| **k == normalized || k.ends_with(&format!("_{normalized}")));
        if let Some((mangled_struct, _)) = found_struct {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Obj(intern_str(mangled_struct)),
                span.clone(),
            ))
        } else if let Some((mangled_enum, _)) = found_enum {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Enum(intern_str(mangled_enum)),
                span.clone(),
            ))
        } else if name == "rc"
            || name == "arc"
            || type_ctx.fn_map.contains_key(name)
            || type_ctx.fn_map.contains_key(&normalized)
            || type_ctx
                .fn_map
                .iter()
                .any(|(k, _)| **k == normalized || k.ends_with(&format!("_{normalized}")))
        {
            Some(TypedExpr::Ident(name.to_string(), Type::Int, span.clone()))
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

pub fn type_check_let<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    name: &str,
    explicit_ty: Option<&Type>,
    is_mutable: bool,
    value: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let typed_val = type_check_expr(scopes, errors, type_ctx, value)?;
    let inferred_ty = typed_val.ty();

    let final_ty = if let Some(annotated) = explicit_ty {
        let compatible = match (annotated, &inferred_ty) {
            (Type::I32 | Type::Int, Type::I32 | Type::Int) => true,
            (Type::F32 | Type::Float, Type::F32 | Type::Float) => true,
            (Type::F32 | Type::Float, Type::I32 | Type::Int) => true,
            (a, b) => a == b,
        };
        if !compatible {
            errors.push(SemanticError {
                message: format!(
                    "Cannot assign value of type `{inferred_ty:?}` to variable '{name}' declared as `{annotated:?}`"
                ),
                label: "Type mismatch in let binding".to_string(),
                help: None,
                span: span.clone(),
            });
        }
        annotated.clone()
    } else {
        let is_bare_int_literal = matches!(typed_val, TypedExpr::Int(..));
        let is_bare_float_literal = matches!(typed_val, TypedExpr::Float(..));
        let mut ty = match inferred_ty {
            Type::Int if is_bare_int_literal => Type::I32,
            Type::Float if is_bare_float_literal => Type::F32,
            other => other,
        };
        if is_mutable {
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
        ty
    };

    scopes.declare(name.to_string(), is_mutable, final_ty.clone());

    Some(TypedExpr::Let(
        name.to_string(),
        is_mutable,
        Box::new(typed_val),
        final_ty,
        span.clone(),
    ))
}

pub fn type_check_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    name: &str,
    value: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
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

        let val_ty = typed_val.ty();

        let is_compatible = match (&info.ty, &val_ty) {
            (a, b) if a == b => true,
            (Type::I32 | Type::Int, Type::I32 | Type::Int) => true,
            (Type::F32 | Type::Float, Type::F32 | Type::Float) => true,
            (Type::F32 | Type::Float, Type::I32 | Type::Int) => true,
            (Type::F32 | Type::Float | Type::I32 | Type::Int, Type::Generic(_)) => true,
            (Type::Generic(_), Type::F32 | Type::Float | Type::I32 | Type::Int) => true,
            (Type::Generic(_), Type::Generic(_)) => true,
            _ => false,
        };

        if !is_compatible {
            errors.push(SemanticError {
                message: format!(
                    "Cannot assign type `{:?}` to variable '{name}' of type `{:?}`",
                    val_ty, info.ty
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
        name.to_string(),
        Box::new(typed_val),
        span.clone(),
    ))
}
