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
        let mangled = lookup_mangled(tname);
        let base_t = mangled.as_ref().map(|(b, _)| b.as_str());
        let base_short = base_t
            .and_then(|b| b.rsplit_once('_').map(|(_, s)| s))
            .or(base_t);

        if let Some((_, ref args)) = mangled {
            let base_has_impl = trait_impls.iter().any(|(imp_ty, imp_tr)| {
                let imp_tr_short = imp_tr.rsplit_once('_').map(|(_, s)| s).unwrap_or(imp_tr);
                let tr_match = imp_tr == tr || imp_tr_short == tr;
                let ty_match = base_t == Some(imp_ty.as_str()) || base_short == Some(imp_ty.as_str());
                tr_match && ty_match
            });
            if base_has_impl {
                return args.iter().all(|arg| type_satisfies_bound(*arg, tr, trait_methods, trait_impls, fn_map));
            }
        }

        trait_impls.iter().any(|(imp_ty, imp_tr)| {
            let imp_tr_short = imp_tr.rsplit_once('_').map(|(_, s)| s).unwrap_or(imp_tr);
            let tr_match = imp_tr == tr || imp_tr_short == tr;
            let ty_match = imp_ty == tname
                || imp_ty == short_t
                || tname.ends_with(&format!("_{imp_ty}"))
                || base_t == Some(imp_ty.as_str())
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
            if let Type::Box(inner) = ty {
                return type_satisfies_bound(*inner, "Clone", trait_methods, trait_impls, fn_map);
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Clone", trait_methods, trait_impls, fn_map));
            }
        }
        "Send" => {
            if let Type::Box(inner) = ty {
                return type_satisfies_bound(*inner, "Send", trait_methods, trait_impls, fn_map);
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Send", trait_methods, trait_impls, fn_map));
            }
            return !matches!(ty, Type::Rc(_) | Type::Ref(_) | Type::MutRef(_) | Type::Ptr(_));
        }
        "Add" | "Sub" | "Mul" | "Div" | "Rem" | "Neg" | "BitAnd" | "BitOr" | "BitXor" | "Shl"
        | "Shr" | "AddAssign" | "SubAssign" | "MulAssign" | "DivAssign" => {
            if ty.is_numeric() && !matches!(clean_bound, "AddAssign" | "SubAssign" | "MulAssign" | "DivAssign") {
                return true;
            }
            if let Some(tname) = type_name_opt {
                let m = match clean_bound {
                    "AddAssign" => "add_assign".to_string(),
                    "SubAssign" => "sub_assign".to_string(),
                    "MulAssign" => "mul_assign".to_string(),
                    "DivAssign" => "div_assign".to_string(),
                    other => other.to_lowercase(),
                };
                if fn_map.contains_key(&format!("{tname}_{m}")) {
                    return true;
                }
            }
        }
        "Index" => {
            if matches!(ty, Type::Array(..) | Type::Slice(_) | Type::Vec(_)) {
                return true;
            }
            if let Some(tname) = type_name_opt {
                if fn_map.contains_key(&format!("{tname}_index")) {
                    return true;
                }
            }
        }
        "IndexMut" => {
            if matches!(ty, Type::Array(..) | Type::Slice(_) | Type::Vec(_)) {
                return true;
            }
            if let Some(tname) = type_name_opt {
                if fn_map.contains_key(&format!("{tname}_index_mut")) {
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
            if let Type::Box(inner) | Type::Rc(inner) | Type::Arc(inner) | Type::Ref(inner) | Type::MutRef(inner) = ty {
                return type_satisfies_bound(*inner, "Display", trait_methods, trait_impls, fn_map);
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Display", trait_methods, trait_impls, fn_map));
            }
        }
        "Debug" => {
            if ty.is_numeric()
                || matches!(
                    ty,
                    Type::Bool
                        | Type::Str
                        | Type::String
                        | Type::Unit
                        | Type::Ptr(_)
                        | Type::FnPtr(..)
                        | Type::Obj("String")
                        | Type::Obj("std_string_String")
                )
            {
                return true;
            }
            if let Type::Tuple(tys) = ty {
                return tys
                    .iter()
                    .all(|t| type_satisfies_bound(*t, "Debug", trait_methods, trait_impls, fn_map));
            }
            if let Type::Ref(inner) | Type::MutRef(inner) | Type::Box(inner) = ty {
                return type_satisfies_bound(*inner, "Debug", trait_methods, trait_impls, fn_map);
            }
            if let Type::Array(elem, _) | Type::Slice(elem) | Type::Vec(elem) | Type::Rc(elem) | Type::Arc(elem) = ty {
                return type_satisfies_bound(*elem, "Debug", trait_methods, trait_impls, fn_map);
            }
            if let Type::DynTrait(tr) = ty {
                if tr == "Debug" || tr.ends_with("_Debug") || tr.ends_with("::Debug") {
                    return true;
                }
            }
            if let Some(tname) = type_name_opt {
                if fn_map.contains_key(&format!("{tname}__Debug_fmt"))
                    || fn_map.contains_key(&format!("{tname}_Debug_fmt"))
                    || fn_map.contains_key(&format!("{tname}_fmt"))
                {
                    return true;
                }
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
                        | Type::FnPtr(..)
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
            if let Type::Ref(inner) | Type::MutRef(inner) | Type::Box(inner) | Type::Rc(inner) | Type::Arc(inner) = ty {
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
                        | Type::FnPtr(..)
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
            if let Type::Ref(inner) | Type::MutRef(inner) | Type::Box(inner) | Type::Rc(inner) | Type::Arc(inner) = ty {
                return type_satisfies_bound(*inner, "Eq", trait_methods, trait_impls, fn_map);
            }
        }
        _ => {
            // Check closure trait bounds: `Fn(Args) -> Ret`, `FnMut(Args) -> Ret`, `FnOnce(Args) -> Ret`
            if let Some((trait_prefix, rest)) = bound
                .strip_prefix("FnOnce")
                .map(|r| ("FnOnce", r))
                .or_else(|| bound.strip_prefix("FnMut").map(|r| ("FnMut", r)))
                .or_else(|| bound.strip_prefix("Fn").map(|r| ("Fn", r)))
            {
                if rest.starts_with('(') {
                    if let Type::FnPtr(..) = ty {
                        return true;
                    }
                    if let Some(tname) = type_name_opt {
                        let ok = match trait_prefix {
                            "Fn" => fn_map.contains_key(&format!("{tname}_call_ref")),
                            "FnMut" => {
                                fn_map.contains_key(&format!("{tname}_call_mut"))
                                    || fn_map.contains_key(&format!("{tname}_call_ref"))
                            }
                            _ => {
                                fn_map.contains_key(&format!("{tname}_call_once"))
                                    || fn_map.contains_key(&format!("{tname}_call_mut"))
                                    || fn_map.contains_key(&format!("{tname}_call_ref"))
                            }
                        };
                        if ok {
                            return true;
                        }
                    }
                    return false;
                }
            }
        }
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
    let mut all_preds = Vec::with_capacity(1 + w.predicates.len());
    all_preds.push((&w.target_param, &w.bounds));
    for (tp, bs) in &w.predicates {
        all_preds.push((tp, bs));
    }
    let mut m = mono.borrow_mut();
    for (target_param, bounds) in all_preds {
        let clean = target_param.trim_start_matches('$');
        let Some(&concrete_ty) = env.get(clean).or_else(|| env.get(target_param)) else {
            continue;
        };
        if crate::sanal::compat::type_contains_generic(&concrete_ty)
            || crate::sanal::compat::type_contains_infer(&concrete_ty)
        {
            continue;
        }
        for bound in bounds {
            if !type_satisfies_bound(concrete_ty, bound, &m.trait_methods, &m.trait_impls, fn_map) {
                m.bound_violations.push(crate::sanal::SemanticError {
                    code: "E0277",
                    message: format!(
                        "The trait bound `{concrete_ty:?}: {bound}` is not satisfied for `{item_desc}`"
                    ),
                    label: format!("`{concrete_ty:?}` does not implement `{bound}`"),
                    secondary_label: None,
                    help: Some(format!(
                        "Implement `{bound}` for `{concrete_ty:?}` or use a type that satisfies `where {target_param}: {bound}`"
                    )),
                    span: w.span.clone(),
                });
            }
        }
    }
}

