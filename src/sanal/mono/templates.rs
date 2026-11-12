//! sanal/mono/templates.rs
//! Template lookup helpers for generic structs, enums, and impl blocks.

use crate::{
    ast::{EnumDecl, FuncDecl, StructDecl},
    sanal::mono::Monomorphizer,
};

pub fn find_struct_template(mono: &Monomorphizer, name: &str) -> Option<StructDecl> {
    mono.struct_templates
        .get(name)
        .or_else(|| {
            mono.struct_templates
                .iter()
                .find(|(k, _)| k.as_str() == name || k.ends_with(&format!("_{name}")))
                .map(|(_, v)| v)
        })
        .cloned()
}

pub fn find_enum_template(mono: &Monomorphizer, name: &str) -> Option<crate::ast::EnumDecl> {
    mono.enum_templates
        .get(name)
        .or_else(|| {
            mono.enum_templates
                .iter()
                .find(|(k, _)| k.as_str() == name || k.ends_with(&format!("_{name}")))
                .map(|(_, v)| v)
        })
        .cloned()
}

pub fn find_impl_method(mono: &Monomorphizer, type_name: &str, method_name: &str) -> Option<FuncDecl> {
    mono.impl_templates.iter().find_map(|imp| {
        let matches_type = imp.target_type == type_name
            || type_name.ends_with(&format!("_{}", imp.target_type))
            || imp.target_type.ends_with(&format!("_{type_name}"));
        if matches_type {
            imp.methods.iter().find(|m| m.name == method_name).cloned()
        } else {
            None
        }
    })
}

