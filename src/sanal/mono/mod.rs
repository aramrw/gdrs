//! sanal/mono/mod.rs
//! Generic Monomorphization engine: AST type & expression substitution, layout generation, and caching.

pub mod bounds;
pub mod instances;
pub mod mangle;
pub mod subst;
pub mod templates;

pub use bounds::{check_where_clause_bounds, type_satisfies_bound};
pub use instances::{monomorphize_enum, monomorphize_fn, monomorphize_struct};
pub use mangle::{lookup_mangled, mangle_name, type_suffix};
pub use subst::{
    collect_generics_from_type, extract_generic_params_enum, extract_generic_params_struct,
    substitute_expr, substitute_type,
};
pub use templates::{find_enum_template, find_impl_method, find_struct_template};

use crate::ast::{EnumDecl, FuncDecl, ImplDecl, StructDecl, Type};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericKey {
    pub name: String,
    pub type_args: Vec<Type>,
}

#[derive(Default)]
pub struct Monomorphizer {
    pub struct_templates: HashMap<String, StructDecl>,
    pub enum_templates: HashMap<String, EnumDecl>,
    pub impl_templates: Vec<ImplDecl>,
    pub fn_templates: HashMap<String, FuncDecl>,
    pub trait_methods: HashMap<String, Vec<(String, Vec<Type>, Type)>>,
    pub trait_impls: std::collections::HashSet<(String, String)>,
    pub bound_violations: Vec<crate::sanal::SemanticError>,

    pub struct_cache: HashMap<GenericKey, String>,
    pub enum_cache: HashMap<GenericKey, String>,
    pub fn_cache: HashMap<GenericKey, String>,
}
