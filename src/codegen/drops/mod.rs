//! codegen/drops/mod.rs
//! Cranelift Drop Flag allocation, LIFO scope drop emission, and Drop Glue calls
//! (including synthesized recursive field drops for user structs without custom `Drop`).

pub mod flags;
pub mod synthesis;

pub use flags::*;
pub use synthesis::resolve_or_synthesize_drop_fn;

use std::collections::{HashMap, HashSet};

use crate::ast::Type;
use crate::codegen::layout::find_struct_layout;
use crate::sanal::StructLayout;

pub type EnumLayoutMap = HashMap<String, Vec<(String, i64, Vec<Type>)>>;

#[inline]
pub fn is_npo_enum(name: &str) -> bool {
    name.starts_with("std_core_Option_ptr")
        || name.starts_with("std_core_Option_void")
        || name.contains("_ptr_")
        || name.contains("_void")
}

pub fn find_enum_layout<'a>(
    name: &str,
    enum_layouts: &'a EnumLayoutMap,
) -> Option<&'a Vec<(String, i64, Vec<Type>)>> {
    enum_layouts.get(name).or_else(|| {
        enum_layouts
            .iter()
            .find(|(k, _)| **k == name || k.ends_with(&format!("_{name}")))
            .map(|(_, v)| v)
    })
}

pub(crate) fn explicit_drop_fn_name(ty: &Type, known_drop_fns: &HashSet<String>) -> Option<String> {
    match ty {
        Type::String | Type::Obj("String") | Type::Obj("std_string_String") => {
            Some("std_string_String_drop".to_string())
        }
        Type::Vec(_) | Type::Obj("Vec") | Type::Obj("std_vec_Vec") => {
            Some("std_vec_Vec_drop".to_string())
        }
        Type::Obj(name) if name.starts_with("std_vec_Vec_") => {
            Some("std_vec_Vec_drop".to_string())
        }
        Type::Rc(_) => Some("intrinsic_rc_drop".to_string()),
        Type::Arc(_) => Some("intrinsic_arc_drop".to_string()),
        Type::Obj(name) => {
            let candidate = format!("{name}_drop");
            if known_drop_fns.contains(&candidate) {
                Some(candidate)
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(crate) fn find_layout<'a>(
    name: &str,
    struct_layouts: &'a HashMap<String, StructLayout>,
) -> Option<&'a StructLayout> {
    struct_layouts.get(name).or_else(|| {
        struct_layouts
            .iter()
            .find(|(k, _)| **k == name || k.ends_with(&format!("_{name}")))
            .map(|(_, v)| v)
    })
}

pub(crate) fn has_drop_glue_inner(
    ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    visited: &mut HashSet<String>,
) -> bool {
    if explicit_drop_fn_name(ty, known_drop_fns).is_some() {
        return true;
    }
    if matches!(ty, Type::DynTrait(_)) {
        return true;
    }
    if let Type::Array(elem, len) = ty {
        return *len > 0
            && has_drop_glue_inner(elem, known_drop_fns, struct_layouts, enum_layouts, visited);
    }
    if let Type::Tuple(elems) = ty {
        return elems
            .iter()
            .any(|e| has_drop_glue_inner(e, known_drop_fns, struct_layouts, enum_layouts, visited));
    }
    if let Type::Enum(name) = ty {
        if is_npo_enum(name) {
            return false;
        }
        let key = format!("enum:{name}");
        if !visited.insert(key.clone()) {
            return false;
        }
        let has = if let Some(variants) = find_enum_layout(name, enum_layouts) {
            variants.iter().any(|(_, _, p_tys)| {
                p_tys.iter().any(|p_ty| {
                    has_drop_glue_inner(p_ty, known_drop_fns, struct_layouts, enum_layouts, visited)
                })
            })
        } else {
            false
        };
        visited.remove(&key);
        return has;
    }
    if let Type::Obj(name) = ty {
        if !visited.insert((*name).to_string()) {
            return false;
        }
        let has = if let Some(layout) = find_layout(name, struct_layouts) {
            layout.field_offsets.values().any(|(_, f_ty)| {
                has_drop_glue_inner(f_ty, known_drop_fns, struct_layouts, enum_layouts, visited)
            })
        } else {
            false
        };
        visited.remove(*name);
        return has;
    }
    false
}

pub fn has_drop_glue(
    ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> bool {
    let mut visited = HashSet::new();
    has_drop_glue_inner(ty, known_drop_fns, struct_layouts, enum_layouts, &mut visited)
}

