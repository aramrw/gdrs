//! sanal/resolve.rs
//! Semantic type resolution and `Self` substitution.

use crate::{
    ast::{intern_str, Span, Type},
    sanal::SemanticError,
};

pub(crate) fn substitute_self_type(ty: Type, target_ty: Type) -> Type {
    match ty {
        Type::Obj("Self") => target_ty,
        Type::Obj(name) | Type::Enum(name) => {
            if let Some((base, args)) = crate::sanal::mono::lookup_mangled(name) {
                let sub_args: Vec<Type> = args
                    .into_iter()
                    .map(|a| substitute_self_type(a, target_ty))
                    .collect();
                let remangled = crate::sanal::mono::mangle_name(&base, &sub_args);
                if matches!(ty, Type::Enum(_)) {
                    Type::Enum(intern_str(&remangled))
                } else {
                    Type::Obj(intern_str(&remangled))
                }
            } else {
                ty
            }
        }
        Type::Ref(inner) => Type::Ref(crate::ast::intern_type(substitute_self_type(*inner, target_ty))),
        Type::MutRef(inner) => Type::MutRef(crate::ast::intern_type(substitute_self_type(*inner, target_ty))),
        Type::Ptr(inner) => Type::Ptr(crate::ast::intern_type(substitute_self_type(*inner, target_ty))),
        Type::Box(inner) => Type::Box(crate::ast::intern_type(substitute_self_type(*inner, target_ty))),
        Type::Rc(inner) => Type::Rc(crate::ast::intern_type(substitute_self_type(*inner, target_ty))),
        Type::Arc(inner) => Type::Arc(crate::ast::intern_type(substitute_self_type(*inner, target_ty))),
        Type::FnPtr(params, ret) => Type::FnPtr(
            crate::ast::intern_tuple(
                &params
                    .iter()
                    .map(|p| substitute_self_type(*p, target_ty))
                    .collect::<Vec<_>>(),
            ),
            crate::ast::intern_type(substitute_self_type(*ret, target_ty)),
        ),
        Type::Tuple(tys) => Type::Tuple(Box::leak(
            tys.iter()
                .map(|t| substitute_self_type(*t, target_ty))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        )),
        other => other,
    }
}

pub(crate) fn resolve_type(
    ty: Type,
    enum_names: &std::collections::HashSet<String>,
    span: Span,
    errors: &mut Vec<SemanticError>,
) -> Type {
    match ty {
        Type::Obj("Result_bare") | Type::Obj("std_core_Result_bare") => {
            errors.push(SemanticError {
                code: "E0107",
                message: "Type `Result` requires generic parameter(s), e.g. `Result<T>` or `Result<T, E>`".to_string(),
                label: "Missing generic parameter for `Result`".to_string(),
                secondary_label: None,
                help: Some("Specify generic types: `Result<T>` or `Result<T, E>`".to_string()),
                span,
            });
            Type::Enum(intern_str("std_core_Result"))
        }
        Type::Obj("Option_bare") | Type::Obj("std_core_Option_bare") => {
            errors.push(SemanticError {
                code: "E0107",
                message: "Type `Option` requires a generic parameter, e.g. `Option<T>`".to_string(),
                label: "Missing generic parameter for `Option`".to_string(),
                secondary_label: None,
                help: Some("Specify generic type: `Option<T>`".to_string()),
                span,
            });
            Type::Enum(intern_str("std_core_Option"))
        }
        Type::Obj("Option") | Type::Obj("Opt") => Type::Enum(intern_str("std_core_Option")),
        Type::Obj("Result") | Type::Obj("Res") => Type::Enum(intern_str("std_core_Result")),
        Type::Obj(name) if name == "Vec" || name == "std_vec_Vec" => {
            Type::Vec(crate::ast::intern_type(Type::Int))
        }
        Type::Obj(name) if name.contains("Option") || name.contains("Result") || enum_names.contains(name) => {
            Type::Enum(intern_str(name))
        }
        Type::Array(elem_ty, len) => Type::Array(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
            len,
        ),
        Type::Tuple(elems) => {
            let resolved: Vec<Type> = elems
                .iter()
                .map(|t| resolve_type(*t, enum_names, span.clone(), errors))
                .collect();
            Type::Tuple(crate::ast::intern_tuple(&resolved))
        }
        Type::Slice(elem_ty) => Type::Slice(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Vec(elem_ty) => Type::Vec(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Ptr(elem_ty) => Type::Ptr(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Ref(elem_ty) => Type::Ref(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::MutRef(elem_ty) => Type::MutRef(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Box(elem_ty) => Type::Box(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Rc(elem_ty) => Type::Rc(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Arc(elem_ty) => Type::Arc(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::FnPtr(params, ret) => {
            let resolved_params: Vec<Type> = params
                .iter()
                .map(|p| resolve_type(*p, enum_names, span.clone(), errors))
                .collect();
            let resolved_ret = resolve_type(*ret, enum_names, span, errors);
            Type::FnPtr(
                crate::ast::intern_tuple(&resolved_params),
                crate::ast::intern_type(resolved_ret),
            )
        }
        other => other,
    }
}
