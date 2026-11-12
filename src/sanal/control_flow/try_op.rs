//! sanal/control_flow/try_op.rs
//! Try operator (?) type checking and Result/Option desugaring.

use crate::{
    ast::{Expr, Span, Type, TypedExpr, TypedMatchArm},
    sanal::{
        compat::is_type_compatible,
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn type_check_try<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    inner_expr: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_inner = type_check_expr(scopes, errors, type_ctx, inner_expr)?;
    let inner_ty = t_inner.ty();

    let (is_option, is_result, enum_name) = match inner_ty {
        Type::Enum(name) | Type::Obj(name) => (
            name.contains("Option"),
            name.contains("Result"),
            name.to_string(),
        ),
        _ => (false, false, String::new()),
    };

    if !is_option && !is_result {
        errors.push(SemanticError {
            code: "E0308",
            message: format!(
                "The `?` operator can only be applied to `Option` or `Result`, found `{:?}`",
                inner_ty
            ),
            label: "Cannot apply `?` operator".into(),
            secondary_label: None,
            help: Some("Ensure expression returns an Option or Result type".into()),
            span: span.clone(),
        });
        return None;
    }

    let ret_enum_name = match type_ctx.current_return_type {
        Some(Type::Enum(ret_name)) | Some(Type::Obj(ret_name)) => {
            let compatible_kind = (is_option && ret_name.contains("Option"))
                || (is_result && ret_name.contains("Result"));
            if !compatible_kind {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Cannot use `?` on `{enum_name}` inside a function returning `{ret_name}`"
                    ),
                    label: "Incompatible enclosing return type for `?`".into(),
                    secondary_label: None,
                    help: Some(if is_option {
                        "Function must return `Option<...>` to propagate `Option` with `?`".into()
                    } else {
                        "Function must return `Result<...>` to propagate `Result` with `?`".into()
                    }),
                    span: span.clone(),
                });
            }
            ret_name.to_string()
        }
        Some(other) => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Cannot use `?` inside a function returning `{:?}`",
                    other
                ),
                label: "Enclosing function cannot propagate errors with `?`".into(),
                secondary_label: None,
                help: Some(if is_option {
                    "Change the function return type to `Option<...>`".into()
                } else {
                    "Change the function return type to `Result<...>`".into()
                }),
                span: span.clone(),
            });
            enum_name.clone()
        }
        None => enum_name.clone(),
    };

    let variant_info = type_ctx.get_enum(&enum_name);
    let ret_variant_info = type_ctx.get_enum(&ret_enum_name);

    if is_option {
        let (some_tag, payload_ty) = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("Some"))
            .map(|(tag, p)| (*tag, p.first().copied().unwrap_or(Type::Int)))
            .unwrap_or((0, Type::Int));
        let none_tag = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("None"))
            .map(|(tag, _)| *tag)
            .unwrap_or(1);
        let (ret_static, ret_none_disc) = ret_variant_info
            .as_ref()
            .map(|(static_name, v_map)| {
                let d = v_map.get("None").map(|(tag, _)| *tag as usize).unwrap_or(1);
                (*static_name, d)
            })
            .unwrap_or((crate::ast::intern_str(&ret_enum_name), 1));

        let arm_some = TypedMatchArm {
            variant_name: format!("{enum_name}::Some"),
            tag: some_tag,
            bindings: vec![("__try_val".to_string(), payload_ty)],
            body: vec![TypedExpr::Ident("__try_val".to_string(), payload_ty, span.clone())],
            span: span.clone(),
        };
        let arm_none = TypedMatchArm {
            variant_name: format!("{enum_name}::None"),
            tag: none_tag,
            bindings: vec![],
            body: vec![TypedExpr::Return(
                Some(Box::new(TypedExpr::EnumConstruct(
                    ret_static.to_string(),
                    "None".to_string(),
                    ret_none_disc,
                    vec![],
                    Type::Enum(ret_static),
                    span.clone(),
                ))),
                span.clone(),
            )],
            span: span.clone(),
        };
        Some(TypedExpr::Match(
            Box::new(t_inner),
            vec![arm_some, arm_none],
            payload_ty,
            span.clone(),
        ))
    } else {
        let (ok_tag, payload_ty) = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("Ok"))
            .map(|(tag, p)| (*tag, p.first().copied().unwrap_or(Type::Int)))
            .unwrap_or((0, Type::Int));
        let (err_tag, err_ty) = variant_info
            .as_ref()
            .and_then(|(_, v_map)| v_map.get("Err"))
            .map(|(tag, p)| (*tag, p.first().copied().unwrap_or(Type::Int)))
            .unwrap_or((1, Type::Int));
        let (ret_static, ret_err_disc) = ret_variant_info
            .as_ref()
            .map(|(static_name, v_map)| {
                let d = v_map.get("Err").map(|(tag, _)| *tag as usize).unwrap_or(1);
                (*static_name, d)
            })
            .unwrap_or((crate::ast::intern_str(&ret_enum_name), 1));

        let arm_ok = TypedMatchArm {
            variant_name: format!("{enum_name}::Ok"),
            tag: ok_tag,
            bindings: vec![("__try_val".to_string(), payload_ty)],
            body: vec![TypedExpr::Ident("__try_val".to_string(), payload_ty, span.clone())],
            span: span.clone(),
        };
        let arm_err = TypedMatchArm {
            variant_name: format!("{enum_name}::Err"),
            tag: err_tag,
            bindings: vec![("__try_err".to_string(), err_ty)],
            body: vec![TypedExpr::Return(
                Some(Box::new(TypedExpr::EnumConstruct(
                    ret_static.to_string(),
                    "Err".to_string(),
                    ret_err_disc,
                    vec![TypedExpr::Ident("__try_err".to_string(), err_ty, span.clone())],
                    Type::Enum(ret_static),
                    span.clone(),
                ))),
                span.clone(),
            )],
            span: span.clone(),
        };
        Some(TypedExpr::Match(
            Box::new(t_inner),
            vec![arm_ok, arm_err],
            payload_ty,
            span.clone(),
        ))
    }
}

