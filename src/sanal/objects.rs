//! sanal/objects.rs
//! Type checking for structs, field access/assignment, enum construction, arrays, and indexing.

use crate::{
    ast::{intern_str, Expr, Span, Type, TypedExpr},
    sanal::{
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError,
    },
};

pub fn is_obj_field_type_compatible(expected: &Type, found: &Type) -> bool {
    if expected == found {
        return true;
    }
    match (expected, found) {
        (Type::Generic(_), _) | (_, Type::Generic(_)) => true,
        (Type::Int | Type::I32, Type::Int | Type::I32) => true,
        (Type::Float | Type::F32, Type::Float | Type::F32) => true,
        (Type::Float | Type::F32, Type::Int | Type::I32) => true,
        (Type::Str | Type::Obj("String"), Type::Str | Type::Obj("String")) => true,
        (Type::Obj(e1), Type::Enum(e2)) | (Type::Enum(e1), Type::Obj(e2)) if e1 == e2 => true,
        _ => false,
    }
}

pub fn type_check_array_init<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    elems: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
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

    for (i, elem) in typed_elems.iter().enumerate().skip(1) {
        if elem.ty() != elem_ty {
            errors.push(SemanticError {
                code: "E0308",
                message: format!(
                    "Array elements must all have the same type. Expected `{:?}`, element {} has type `{:?}`",
                    elem_ty,
                    i + 1,
                    elem.ty()
                ),
                label: format!("Expected `{:?}`", elem_ty),
                secondary_label: None,
                help: Some("Arrays are homogeneous and cannot hold mixed types".into()),
                span: elem.span().clone(),
            });
        }
    }

    let arr_ty = Type::Array(crate::ast::intern_type(elem_ty), typed_elems.len());
    Some(TypedExpr::ArrayInit(typed_elems, arr_ty, span.clone()))
}

pub fn type_check_index_access<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    idx: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;

    if !matches!(t_idx.ty(), Type::Int | Type::I32) {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Array index must be an `Int`, found `{:?}`", t_idx.ty()),
            label: "Invalid index type".into(),
            secondary_label: None,
            help: None,
            span: t_idx.span().clone(),
        });
    }

    let elem_ty = match t_target.ty() {
        Type::Array(e_ty, _) | Type::Slice(e_ty) | Type::Vec(e_ty) => *e_ty,
        other_ty => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Cannot index into non-array type `{:?}`", other_ty),
                label: "Not an array".into(),
                secondary_label: None,
                help: None,
                span: t_target.span().clone(),
            });
            Type::Int
        }
    };

    Some(TypedExpr::IndexAccess(
        Box::new(t_target),
        Box::new(t_idx),
        elem_ty,
        span.clone(),
    ))
}

pub fn type_check_index_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    idx: &Expr,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_idx = type_check_expr(scopes, errors, type_ctx, idx)?;
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;

    if !matches!(t_idx.ty(), Type::Int | Type::I32) {
        errors.push(SemanticError {
            code: "E0308",
            message: format!("Array index must be an `Int`, found `{:?}`", t_idx.ty()),
            label: "Invalid index type".into(),
            secondary_label: None,
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
                code: "E0308",
                message: format!(
                    "Cannot assign type `{:?}` to array holding `{:?}`",
                    t_val.ty(),
                    elem_ty
                ),
                label: "Type mismatch".into(),
                secondary_label: None,
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

pub fn type_check_obj_init<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    raw_name: &str,
    fields: &[(String, Expr)],
    span: &Span,
) -> Option<TypedExpr> {
    let name = &raw_name.replace("::", "_");
    let mut typed_fields = Vec::new();
    for (f_name, f_expr) in fields {
        let t_expr = type_check_expr(scopes, errors, type_ctx, f_expr)?;
        typed_fields.push((f_name.clone(), t_expr));
    }

    let found_struct = type_ctx
        .struct_map
        .iter()
        .find(|(k, _)| *k == name || k.ends_with(&format!("_{name}")));
    let obj_ty_name = if let Some((mangled_name, layout)) = found_struct {
        for (expected_field, (_, expected_ty)) in &layout.field_offsets {
            if !typed_fields.iter().any(|(f, _)| f == expected_field) {
                errors.push(SemanticError {
                    code: "E0063",
                    message: format!(
                        "Missing field '{expected_field}' in struct initialization of '{name}'"
                    ),
                    label: format!("Field '{expected_field}: {expected_ty:?}' is missing"),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
        }

        for (f_name, f_expr) in &typed_fields {
            if let Some((_, expected_ty)) = layout.field_offsets.get(f_name) {
                if !is_obj_field_type_compatible(expected_ty, &f_expr.ty()) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Field '{f_name}' in struct '{name}' expects type `{:?}`, found `{:?}`",
                            expected_ty,
                            f_expr.ty()
                        ),
                        label: format!("Expected `{:?}`", expected_ty),
                        secondary_label: None,
                        help: None,
                        span: f_expr.span().clone(),
                    });
                }
            } else {
                errors.push(SemanticError {
                    code: "E0599",
                    message: format!("Struct '{name}' has no field named '{f_name}'"),
                    label: "Unknown field".into(),
                    secondary_label: None,
                    help: None,
                    span: f_expr.span().clone(),
                });
            }
        }
        mangled_name.as_str()
    } else {
        errors.push(SemanticError {
            code: "E0425",
            message: format!("Undefined struct '{name}'"),
            label: "Struct does not exist".into(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
        name.as_str()
    };

    let obj_ty = Type::Obj(intern_str(obj_ty_name));
    Some(TypedExpr::ObjInit(
        obj_ty_name.to_string(),
        typed_fields,
        obj_ty,
        span.clone(),
    ))
}

pub fn type_check_field_access<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    field_name: &str,
    span: &Span,
) -> Option<TypedExpr> {
    if let Expr::Ident(ref enum_name, _) = *target {
        if let Some((static_enum_name, variants)) = type_ctx.enum_map.get(enum_name) {
            if let Some((disc, _)) = variants.get(field_name) {
                return Some(TypedExpr::EnumConstruct(
                    enum_name.clone(),
                    field_name.to_string(),
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

    let target_ty = t_target.ty();
    let struct_name_opt = match target_ty {
        Type::Obj(s) => Some(s),
        Type::Ref(inner) | Type::MutRef(inner) => match *inner {
            Type::Obj(s) => Some(s),
            _ => None,
        },
        _ => None,
    };

    if let Some(struct_name) = struct_name_opt {
        if let Some(layout) = type_ctx.struct_map.get(struct_name) {
            if let Some((_, fty)) = layout.field_offsets.get(field_name) {
                field_ty = *fty;
            } else {
                errors.push(SemanticError {
                    code: "E0599",
                    message: format!("Struct '{struct_name}' has no field '{field_name}'"),
                    label: "Field not found".to_string(),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
            }
        }
    } else {
        errors.push(SemanticError {
            code: "E0599",
            message: format!("Cannot access field on non-object type {:?}", t_target.ty()),
            label: "Not a struct object".to_string(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
    }

    Some(TypedExpr::FieldAccess(
        Box::new(t_target),
        field_name.to_string(),
        field_ty,
        span.clone(),
    ))
}

pub fn type_check_field_assign<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    target: &Expr,
    field_name: &str,
    val: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let t_target = type_check_expr(scopes, errors, type_ctx, target)?;
    let t_val = type_check_expr(scopes, errors, type_ctx, val)?;

    let mut curr = target;
    while let Expr::FieldAccess(inner, _, _) = curr {
        curr = inner.as_ref();
    }
    if let Expr::Ident(var_name, _) = curr {
        if let Some(info) = scopes.lookup(var_name) {
            let is_ref = matches!(info.ty, Type::Ref(_) | Type::MutRef(_));
            if !info.is_mutable && !is_ref {
                errors.push(SemanticError {
                    code: "E0382",
                    message: format!("Cannot mutate field of immutable object '{var_name}'"),
                    label: "Object is immutable".to_string(),
                    secondary_label: None,
                    help: Some(format!("Declare as mutable: 'let mut {var_name}'")),
                    span: span.clone(),
                });
            }
        }
    }

    Some(TypedExpr::FieldAssign(
        Box::new(t_target),
        field_name.to_string(),
        Box::new(t_val),
        span.clone(),
    ))
}

pub fn type_check_enum_construct<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    enum_name: &str,
    variant_name: &str,
    args: &[Expr],
    span: &Span,
) -> Option<TypedExpr> {
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
        enum_name.to_string(),
        variant_name.to_string(),
        disc,
        typed_args,
        Type::Enum(static_enum_name),
        span.clone(),
    ))
}
