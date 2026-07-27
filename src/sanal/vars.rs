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
        let normalized_enum = match enum_part {
            "Opt" | "Option" => "std_core_Option",
            "Res" | "Result" => "std_core_Result",
            other => other,
        };
        if let Some(te) = super::objects::type_check_enum_construct(
            scopes,
            errors,
            type_ctx,
            normalized_enum,
            variant_part,
            &[],
            span,
        ) {
            if matches!(te, TypedExpr::EnumConstruct(..)) {
                return Some(te);
            }
        }
        let normalized = name.replace("::", "_");
        let found_struct = type_ctx.get_struct(&normalized);
        let found_enum = type_ctx.get_enum(&normalized);
        if let Some(layout) = found_struct {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Obj(intern_str(&layout.name)),
                span.clone(),
            ))
        } else if let Some((mangled_enum, _)) = found_enum {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Enum(mangled_enum),
                span.clone(),
            ))
        } else if name == "rc"
            || name == "arc"
            || type_ctx.fn_map.borrow().contains_key(name)
            || type_ctx.fn_map.borrow().contains_key(&normalized)
        {
            Some(TypedExpr::Ident(name.to_string(), Type::Int, span.clone()))
        } else {
            errors.push(SemanticError {
                code: "E0425",
                message: format!("Undefined variable '{name}'"),
                label: "Variable does not exist in this scope".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
            None
        }
    } else {
        if name == "None" || name == "Some" {
            if let Some(te) = super::objects::type_check_enum_construct(
                scopes,
                errors,
                type_ctx,
                "std_core_Option",
                name,
                &[],
                span,
            ) {
                if matches!(te, TypedExpr::EnumConstruct(..)) {
                    return Some(te);
                }
            }
        }
        let normalized = name.replace("::", "_");
        if let Some((enum_part, variant_part)) = normalized.rsplit_once('_') {
            let norm_enum = match enum_part {
                "Opt" | "Option" => "std_core_Option",
                "Res" | "Result" => "std_core_Result",
                other => other,
            };
            if let Some(te) = super::objects::type_check_enum_construct(
                scopes,
                errors,
                type_ctx,
                norm_enum,
                variant_part,
                &[],
                span,
            ) {
                if matches!(te, TypedExpr::EnumConstruct(..)) {
                    return Some(te);
                }
            }
        }
        let found_struct = type_ctx.get_struct(&normalized).or_else(|| {
            let mono = type_ctx.mono.borrow();
            mono.struct_templates
                .get(&normalized)
                .or_else(|| {
                    mono.struct_templates
                        .iter()
                        .find(|(k, _)| k.as_str() == normalized || k.ends_with(&format!("_{normalized}")))
                        .map(|(_, v)| v)
                })
                .map(|decl| crate::sanal::StructLayout {
                    name: decl.name.clone(),
                    total_size: 0,
                    field_offsets: std::collections::HashMap::new(),
                })
        });
        let found_enum = type_ctx.get_enum(&normalized);
        if let Some(layout) = found_struct {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Obj(intern_str(&layout.name)),
                span.clone(),
            ))
        } else if let Some((mangled_enum, _)) = found_enum {
            Some(TypedExpr::Ident(
                name.to_string(),
                Type::Enum(mangled_enum),
                span.clone(),
            ))
        } else if name == "rc"
            || name == "arc"
            || type_ctx.fn_map.borrow().contains_key(name)
            || type_ctx.fn_map.borrow().contains_key(&normalized)
        {
            Some(TypedExpr::Ident(name.to_string(), Type::Int, span.clone()))
        } else {
            errors.push(SemanticError {
                code: "E0425",
                message: format!("Undefined variable '{name}'"),
                label: "Variable does not exist in this scope".to_string(),
                secondary_label: None,
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

    let mut final_ty = if let Some(annotated) = explicit_ty {
        let compatible = match (annotated, &inferred_ty) {
            (Type::I32 | Type::Int, Type::I32 | Type::Int) => true,
            (Type::F32 | Type::Float, Type::F32 | Type::Float) => true,
            (Type::F32 | Type::Float, Type::I32 | Type::Int) => true,
            (a, b) => a == b,
        };
        if !compatible {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot assign value of type `{inferred_ty:?}` to variable '{name}' declared as `{annotated:?}`"
                ),
                label: "Type mismatch in let binding".to_string(),
                secondary_label: None,
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

    if name.starts_with("__iter_") {
        if let TypedExpr::Call(_, args, _, _) = &typed_val {
            if !args.is_empty() {
                if let Type::Vec(elem_ty) = args[0].ty() {
                    final_ty = Type::Vec(elem_ty);
                }
            }
        }
    }

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

    if let Some(info) = scopes.lookup_mut(name) {
        if !info.is_mutable {
            errors.push(SemanticError {
                code: "E0382",
                message: format!("Cannot reassign immutable variable '{name}'"),
                label: format!("Variable '{name}' is immutable"),
                secondary_label: None,
                help: Some(format!(
                    "Consider declaring this variable as mutable: 'let mut {name}'"
                )),
                span: span.clone(),
            });
        }

        let val_ty = typed_val.ty();

        if let Type::Vec(elem_ty) = &val_ty {
            info.ty = Type::Vec(*elem_ty);
        } else if let TypedExpr::Call(c_name, c_args, _, _) = &typed_val {
            if c_name.ends_with("push") && c_args.len() >= 2 {
                let pushed_ty = c_args[1].ty();
                if pushed_ty != Type::Int && pushed_ty != Type::Unit {
                    info.ty = Type::Vec(crate::ast::intern_type(pushed_ty));
                }
            }
        } else if let Type::Obj(s) = &val_ty {
            let clean = s.split('_').last().unwrap_or(s);
            if clean == "Vec" || clean.starts_with("Vec_") {
                if let Type::Vec(elem_ty) = info.ty {
                    info.ty = Type::Vec(elem_ty);
                }
            }
        }

        let is_compatible = match (&info.ty, &val_ty) {
            (a, b) if a == b => true,
            (Type::I32 | Type::Int, Type::I32 | Type::Int) => true,
            (Type::F32 | Type::Float, Type::F32 | Type::Float) => true,
            (Type::F32 | Type::Float, Type::I32 | Type::Int) => true,
            (Type::Vec(_), Type::Obj(s)) | (Type::Obj(s), Type::Vec(_)) => {
                let clean = s.split('_').last().unwrap_or(s);
                clean == "Vec" || clean.starts_with("Vec_")
            }
            (Type::F32 | Type::Float | Type::I32 | Type::Int, Type::Generic(_)) => true,
            (Type::Generic(_), Type::F32 | Type::Float | Type::I32 | Type::Int) => true,
            (Type::Generic(_), Type::Generic(_)) => true,
            _ => false,
        };

        if !is_compatible {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot assign type `{:?}` to variable '{name}' of type `{:?}`",
                    val_ty, info.ty
                ),
                label: "Type mismatch".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
    } else {
        errors.push(SemanticError {
            code: "E0425",
            message: format!("Cannot assign to undefined variable '{name}'"),
            label: format!("Variable '{name}' does not exist in this scope"),
            secondary_label: None,
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
