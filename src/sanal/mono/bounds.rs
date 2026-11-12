//! sanal/mono/bounds.rs
//! Trait bound satisfaction checking and where clause validation.

use std::{cell::RefCell, collections::HashMap};
use crate::{
    ast::{FuncDecl, Type},
    sanal::mono::{lookup_mangled, Monomorphizer},
};

pub fn type_satisfies_bound(
    ty: Type,
    bound: &str,
    trait_methods: &HashMap<String, Vec<(String, Vec<Type>, Type)>>,
    trait_impls: &std::collections::HashSet<(String, String)>,
    fn_map: &HashMap<String, FuncDecl>,
) -> bool {
    let short_bound = bound.rsplit_once("::").map(|(_, s)| s).unwrap_or(bound);
    let clean_bound = short_bound.rsplit_once('_').map(|(_, s)| s).unwrap_or(short_bound);

    let type_name_opt = match ty {
        Type::Obj(s) | Type::Enum(s) => Some(s),
        Type::String => Some("std_string_String"),
        Type::Vec(_) => Some("std_vec_Vec"),
        _ => None,
    };

    let has_impl_for_type = |tname: &str, tr: &str| -> bool {
        let short_t = tname.rsplit_once('_').map(|(_, s)| s).unwrap_or(tname);
        let base_t = lookup_mangled(tname).map(|(b, _)| b);
        let base_short = base_t
            .as_deref()
            .and_then(|b| b.rsplit_once('_').map(|(_, s)| s))
            .or(base_t.as_deref());
        trait_impls.iter().any(|(imp_ty, imp_tr)| {
            let imp_tr_short = imp_tr.rsplit_once('_').map(|(_, s)| s).unwrap_or(imp_tr);
            let tr_match = imp_tr == tr || imp_tr_short == tr;
            let ty_match = imp_ty == tname
                || imp_ty == short_t
                || tname.ends_with(&format!("_{imp_ty}"))
                || base_t.as_deref() == Some(imp_ty.as_str())
                || base_short == Some(imp_ty.as_str());
            tr_match && ty_match
        })
    };

    match clean_bound {
        "Copy" => return ty.is_copy(),
        "Clone" => {
            if ty.is_copy()
                || matches!(
                    ty,
                    Type::String | Type::Rc(_) | Type::Arc(_) | Type::Obj("String") | Type::Obj("std_string_String")
                )
            {
                return true;
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Clone", trait_methods, trait_impls, fn_map));
            }
        }
        "Send" => {
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Send", trait_methods, trait_impls, fn_map));
            }
            return !matches!(ty, Type::Rc(_) | Type::Ref(_) | Type::MutRef(_) | Type::Ptr(_));
        }
        "Add" | "Sub" | "Mul" | "Div" => {
            if ty.is_numeric() {
                return true;
            }
            if let Some(tname) = type_name_opt {
                let m = clean_bound.to_lowercase();
                if fn_map.contains_key(&format!("{tname}_{m}")) {
                    return true;
                }
            }
        }
        "Display" => {
            if ty.is_numeric()
                || matches!(
                    ty,
                    Type::Bool
                        | Type::Str
                        | Type::String
                        | Type::Obj("String")
                        | Type::Obj("std_string_String")
                )
            {
                return true;
            }
        }
        "PartialEq" => {
            if ty.is_numeric()
                || matches!(
                    ty,
                    Type::Bool
                        | Type::Str
                        | Type::String
                        | Type::Unit
                        | Type::Ptr(_)
                        | Type::Enum(_)
                        | Type::Obj("String")
                        | Type::Obj("std_string_String")
                )
            {
                return true;
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "PartialEq", trait_methods, trait_impls, fn_map));
            }
            if let Type::Ref(inner) | Type::MutRef(inner) = ty {
                return type_satisfies_bound(*inner, "PartialEq", trait_methods, trait_impls, fn_map);
            }
            if let Some(tname) = type_name_opt {
                if fn_map.contains_key(&format!("{tname}_eq")) {
                    return true;
                }
            }
        }
        "Eq" => {
            if ty.is_integer()
                || matches!(
                    ty,
                    Type::Bool
                        | Type::Str
                        | Type::String
                        | Type::Unit
                        | Type::Ptr(_)
                        | Type::Obj("String")
                        | Type::Obj("std_string_String")
                )
            {
                return true;
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Eq", trait_methods, trait_impls, fn_map));
            }
            if let Type::Ref(inner) | Type::MutRef(inner) = ty {
                return type_satisfies_bound(*inner, "Eq", trait_methods, trait_impls, fn_map);
            }
        }
        "Display" => {
            if matches!(
                ty,
                Type::Int
                    | Type::I32
                    | Type::Float
                    | Type::F32
                    | Type::Bool
                    | Type::Str
                    | Type::String
                    | Type::Obj("String")
                    | Type::Obj("std_string_String")
            ) {
                return true;
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Display", trait_methods, trait_impls, fn_map));
            }
        }
        _ => {}
    }

    let Some(tname) = type_name_opt else {
        return false;
    };

    if has_impl_for_type(tname, bound) || has_impl_for_type(tname, clean_bound) {
        return true;
    }

    let methods_opt = trait_methods
        .get(bound)
        .or_else(|| trait_methods.get(clean_bound))
        .or_else(|| {
            trait_methods
                .iter()
                .find(|(k, _)| k.ends_with(&format!("_{clean_bound}")))
                .map(|(_, v)| v)
        });
    if let Some(methods) = methods_opt {
        if !methods.is_empty() {
            return methods.iter().all(|(m_name, _, _)| {
                let sym = format!("{tname}_{m_name}");
                fn_map.contains_key(&sym)
                    || fn_map.keys().any(|k| k.ends_with(&format!("_{sym}")))
            });
        }
    }

    false
}

pub fn check_where_clause_bounds(
    mono: &RefCell<Monomorphizer>,
    where_clause: Option<&crate::ast::WhereClause>,
    env: &HashMap<String, Type>,
    item_desc: &str,
    fn_map: &HashMap<String, FuncDecl>,
) {
    let Some(w) = where_clause else {
        return;
    };
    let clean = w.target_param.trim_start_matches('$');
    let Some(&concrete_ty) = env.get(clean).or_else(|| env.get(&w.target_param)) else {
        return;
    };
    if crate::sanal::compat::type_contains_generic(&concrete_ty)
        || crate::sanal::compat::type_contains_infer(&concrete_ty)
    {
        return;
    }
    let mut m = mono.borrow_mut();
    for bound in &w.bounds {
        if !type_satisfies_bound(concrete_ty, bound, &m.trait_methods, &m.trait_impls, fn_map) {
            m.bound_violations.push(crate::sanal::SemanticError {
                code: "E0277",
                message: format!(
                    "The trait bound `{concrete_ty:?}: {bound}` is not satisfied for `{item_desc}`"
                ),
                label: format!("`{concrete_ty:?}` does not implement `{bound}`"),
                secondary_label: None,
                help: Some(format!("Implement `{bound}` for `{concrete_ty:?}` or use a type that satisfies `where {}: {bound}`", w.target_param)),
                span: w.span.clone(),
            });
        }
    }
}

