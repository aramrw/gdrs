//! sanal/mono.rs
//! Generic Monomorphization engine: AST type & expression substitution, layout generation, and caching.

use crate::ast::{
    intern_str, intern_type, EnumDecl, Expr, FuncDecl, ImplDecl, MatchArm, Param, StructDecl,
    Type,
};
use crate::sanal::StructLayout;
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

static MANGLED_REGISTRY: LazyLock<Mutex<HashMap<String, (String, Vec<Type>)>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

pub fn lookup_mangled(mangled: &str) -> Option<(String, Vec<Type>)> {
    MANGLED_REGISTRY.lock().ok()?.get(mangled).cloned()
}

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
        "Eq" | "PartialEq" => {
            if ty.is_numeric()
                || matches!(
                    ty,
                    Type::Bool
                        | Type::Str
                        | Type::String
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
                    .all(|t| type_satisfies_bound(*t, "Eq", trait_methods, trait_impls, fn_map));
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

pub fn type_suffix(ty: &Type) -> String {
    match ty {
        Type::Int => "i64".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I8 => "i8".to_string(),
        Type::U64 => "u64".to_string(),
        Type::U32 => "u32".to_string(),
        Type::U16 => "u16".to_string(),
        Type::U8 => "u8".to_string(),
        Type::Float => "f64".to_string(),
        Type::F32 => "f32".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str => "str".to_string(),
        Type::String => "string".to_string(),
        Type::Unit => "unit".to_string(),
        Type::Obj(n) | Type::Enum(n) | Type::Generic(n) | Type::DynTrait(n) => {
            let clean = n.rsplit_once('_').map(|(_, s)| s).unwrap_or(n);
            clean.replace("::", "_").to_lowercase()
        }
        Type::Array(t, len) => format!("arr_{}_{len}", type_suffix(t)),
        Type::Tuple(tys) => {
            let parts: Vec<String> = tys.iter().map(type_suffix).collect();
            format!("tup_{}", parts.join("_"))
        }
        Type::Slice(t) => format!("slice_{}", type_suffix(t)),
        Type::Vec(t) => format!("vec_{}", type_suffix(t)),
        Type::Rc(t) => format!("rc_{}", type_suffix(t)),
        Type::Arc(t) => format!("arc_{}", type_suffix(t)),
        Type::Void => "void".to_string(),
        Type::Ptr(t) => format!("ptr_{}", type_suffix(t)),
        Type::Ref(t) => format!("ref_{}", type_suffix(t)),
        Type::MutRef(t) => format!("mutref_{}", type_suffix(t)),
        Type::Infer(id) => format!("infer_{id}"),
    }
}

pub fn mangle_name(base: &str, type_args: &[Type]) -> String {
    if type_args.is_empty() {
        base.to_string()
    } else {
        let suffixes: Vec<String> = type_args.iter().map(type_suffix).collect();
        let mangled = format!("{}_{}", base, suffixes.join("_"));
        if let Ok(mut reg) = MANGLED_REGISTRY.lock() {
            reg.entry(mangled.clone())
                .or_insert_with(|| (base.to_string(), type_args.to_vec()));
        }
        mangled
    }
}

pub fn extract_generic_params_struct(decl: &StructDecl, mono: &RefCell<Monomorphizer>) -> Vec<String> {
    let mut params = Vec::new();
    if let Some(w) = &decl.where_clause {
        let clean = w.target_param.trim_start_matches('$').to_string();
        if !params.contains(&clean) {
            params.push(clean);
        }
    }
    for field in &decl.fields {
        collect_generics_from_type(&field.ty, &mut params);
    }
    if params.is_empty() {
        let impls = mono.borrow().impl_templates.clone();
        for impl_block in &impls {
            if impl_block.target_type == decl.name
                || decl.name.ends_with(&format!("_{}", impl_block.target_type))
            {
                for m in &impl_block.methods {
                    for p in &m.params {
                        collect_generics_from_type(&p.ty, &mut params);
                    }
                    collect_generics_from_type(&m.return_type, &mut params);
                }
            }
        }
    }
    params
}

pub fn extract_generic_params_enum(decl: &EnumDecl) -> Vec<String> {
    let mut params = Vec::new();
    if let Some(w) = &decl.where_clause {
        let clean = w.target_param.trim_start_matches('$').to_string();
        if !params.contains(&clean) {
            params.push(clean);
        }
    }
    for variant in &decl.variants {
        for p_ty in &variant.payload_types {
            collect_generics_from_type(p_ty, &mut params);
        }
    }
    params
}

fn collect_generics_from_type(ty: &Type, params: &mut Vec<String>) {
    match ty {
        Type::Generic(g) => {
            let clean = g.trim_start_matches('$').to_string();
            if !params.contains(&clean) {
                params.push(clean);
            }
        }
        Type::Ref(inner) | Type::MutRef(inner) | Type::Rc(inner) | Type::Arc(inner)
        | Type::Ptr(inner) | Type::Vec(inner) | Type::Slice(inner) | Type::Array(inner, _) => {
            collect_generics_from_type(inner, params);
        }
        Type::Tuple(elems) => {
            for e in *elems {
                collect_generics_from_type(e, params);
            }
        }
        Type::Obj(name) | Type::Enum(name) => {
            if let Some((_, args)) = lookup_mangled(name) {
                for a in args {
                    collect_generics_from_type(&a, params);
                }
            }
        }
        _ => {}
    }
}

pub fn substitute_type(ty: Type, env: &HashMap<String, Type>) -> Type {
    match ty {
        Type::Generic(g) => {
            let clean = g.trim_start_matches('$');
            if let Some(sub) = env.get(clean).or_else(|| env.get(g)) {
                *sub
            } else {
                ty
            }
        }
        Type::Ptr(inner) => Type::Ptr(intern_type(substitute_type(*inner, env))),
        Type::Ref(inner) => Type::Ref(intern_type(substitute_type(*inner, env))),
        Type::MutRef(inner) => Type::MutRef(intern_type(substitute_type(*inner, env))),
        Type::Rc(inner) => Type::Rc(intern_type(substitute_type(*inner, env))),
        Type::Arc(inner) => Type::Arc(intern_type(substitute_type(*inner, env))),
        Type::Vec(inner) => Type::Vec(intern_type(substitute_type(*inner, env))),
        Type::Slice(inner) => Type::Slice(intern_type(substitute_type(*inner, env))),
        Type::Array(inner, len) => Type::Array(intern_type(substitute_type(*inner, env)), len),
        Type::Tuple(elems) => {
            let sub: Vec<Type> = elems.iter().map(|e| substitute_type(*e, env)).collect();
            Type::Tuple(crate::ast::intern_tuple(&sub))
        }
        Type::Obj(name) | Type::Enum(name) => {
            let s_name = name.to_string();
            if let Some((base, args)) = lookup_mangled(&s_name) {
                if !env.is_empty() {
                    let sub_args: Vec<Type> = args.into_iter().map(|a| substitute_type(a, env)).collect();
                    let mangled = mangle_name(&base, &sub_args);
                    if base == "std_core_Option" || base == "std_core_Result" || matches!(ty, Type::Enum(_)) {
                        return Type::Enum(intern_str(&mangled));
                    }
                    return Type::Obj(intern_str(&mangled));
                }
            }
            if (s_name.starts_with("std_core_Option_") || s_name.starts_with("std_core_Result_") || s_name == "Option" || s_name == "Result") && !env.is_empty() {
                let mut unique_vals = Vec::new();
                for val in env.values() {
                    if !unique_vals.contains(val) {
                        unique_vals.push(*val);
                    }
                }
                let type_args: Vec<String> = unique_vals.iter().map(type_suffix).collect();
                if !type_args.is_empty() {
                    let base = if s_name.contains("Option") { "std_core_Option" } else { "std_core_Result" };
                    let mangled = format!("{}_{}", base, type_args.join("_"));
                    return Type::Enum(crate::ast::intern_str(&mangled));
                }
            }
            ty
        }
        other => other,
    }
}

pub fn substitute_expr(expr: &Expr, env: &HashMap<String, Type>) -> Expr {
    match expr {
        Expr::Int(n, span) => Expr::Int(*n, span.clone()),
        Expr::Float(f, span) => Expr::Float(*f, span.clone()),
        Expr::Ident(name, span) => Expr::Ident(name.clone(), span.clone()),
        Expr::Bool(b, span) => Expr::Bool(*b, span.clone()),
        Expr::String(s, span) => Expr::String(s.clone(), span.clone()),
        Expr::Add(l, r, span) => Expr::Add(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Sub(l, r, span) => Expr::Sub(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Mul(l, r, span) => Expr::Mul(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Div(l, r, span) => Expr::Div(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Mod(l, r, span) => Expr::Mod(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Neg(v, span) => Expr::Neg(Box::new(substitute_expr(v, env)), span.clone()),
        Expr::Not(v, span) => Expr::Not(Box::new(substitute_expr(v, env)), span.clone()),
        Expr::GreaterThan(l, r, span) => Expr::GreaterThan(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::LessThan(l, r, span) => Expr::LessThan(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::GreaterEqual(l, r, span) => Expr::GreaterEqual(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::LessEqual(l, r, span) => Expr::LessEqual(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Equal(l, r, span) => Expr::Equal(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::NotEqual(l, r, span) => Expr::NotEqual(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::And(l, r, span) => Expr::And(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Or(l, r, span) => Expr::Or(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Pipe(l, r, span) => Expr::Pipe(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Ampersand(l, r, span) => Expr::Ampersand(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Caret(l, r, span) => Expr::Caret(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Shl(l, r, span) => Expr::Shl(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Shr(l, r, span) => Expr::Shr(
            Box::new(substitute_expr(l, env)),
            Box::new(substitute_expr(r, env)),
            span.clone(),
        ),
        Expr::Let(name, opt_ty, is_mut, val, span) => Expr::Let(
            name.clone(),
            opt_ty.map(|t| substitute_type(t, env)),
            *is_mut,
            Box::new(substitute_expr(val, env)),
            span.clone(),
        ),
        Expr::LetTuple(pat, opt_ty, val, span) => Expr::LetTuple(
            pat.clone(),
            opt_ty.map(|t| substitute_type(t, env)),
            Box::new(substitute_expr(val, env)),
            span.clone(),
        ),
        Expr::Block(stmts, span) => Expr::Block(
            stmts.iter().map(|s| substitute_expr(s, env)).collect(),
            span.clone(),
        ),
        Expr::Unsafe(stmts, span) => Expr::Unsafe(
            stmts.iter().map(|s| substitute_expr(s, env)).collect(),
            span.clone(),
        ),
        Expr::Assign(name, val, span) => Expr::Assign(
            name.clone(),
            Box::new(substitute_expr(val, env)),
            span.clone(),
        ),
        Expr::While(cond, body, span) => Expr::While(
            Box::new(substitute_expr(cond, env)),
            Box::new(substitute_expr(body, env)),
            span.clone(),
        ),
        Expr::If(cond, body, span) => Expr::If(
            Box::new(substitute_expr(cond, env)),
            Box::new(substitute_expr(body, env)),
            span.clone(),
        ),
        Expr::IfElse(cond, then_b, else_b, span) => Expr::IfElse(
            Box::new(substitute_expr(cond, env)),
            Box::new(substitute_expr(then_b, env)),
            Box::new(substitute_expr(else_b, env)),
            span.clone(),
        ),
        Expr::Return(opt_val, span) => Expr::Return(
            opt_val.as_ref().map(|v| Box::new(substitute_expr(v, env))),
            span.clone(),
        ),
        Expr::Break(span) => Expr::Break(span.clone()),
        Expr::Continue(span) => Expr::Continue(span.clone()),
        Expr::MacroCall(name, args, span) => Expr::MacroCall(
            name.clone(),
            args.iter().map(|a| substitute_expr(a, env)).collect(),
            span.clone(),
        ),
        Expr::Call(name, args, span) => {
            let mut unique_vals = Vec::new();
            for val in env.values() {
                if !unique_vals.contains(val) {
                    unique_vals.push(*val);
                }
            }
            let new_name = if !unique_vals.is_empty() {
                let (dot_prefix, stripped) = if let Some(rest) = name.strip_prefix('.') {
                    (".", rest)
                } else {
                    ("", name.as_str())
                };
                if stripped.starts_with("Vec::") || stripped.starts_with("Vec.") || stripped == "Vec::new" || stripped == "Vec.new" {
                    let method = stripped.rsplit("::").next().unwrap_or(stripped).rsplit('.').next().unwrap_or(stripped);
                    format!("{dot_prefix}{}_{method}", mangle_name("Vec", &unique_vals))
                } else {
                    name.clone()
                }
            } else {
                name.clone()
            };
            Expr::Call(
                new_name,
                args.iter().map(|a| substitute_expr(a, env)).collect(),
                span.clone(),
            )
        },
        Expr::Try(inner, span) => Expr::Try(Box::new(substitute_expr(inner, env)), span.clone()),
        Expr::ObjInit(name, fields, span) => {
            let mut unique_vals = Vec::new();
            for val in env.values() {
                if !unique_vals.contains(val) {
                    unique_vals.push(*val);
                }
            }
            let new_name = if !unique_vals.is_empty() {
                let clean = name.split('_').last().unwrap_or(name);
                if clean == "Vec" || clean == "Option" || clean == "Result" {
                    mangle_name(name, &unique_vals)
                } else {
                    name.clone()
                }
            } else {
                name.clone()
            };
            Expr::ObjInit(
                new_name,
                fields
                    .iter()
                    .map(|(n, e)| (n.clone(), substitute_expr(e, env)))
                    .collect(),
                span.clone(),
            )
        },
        Expr::FieldAccess(target, field_name, span) => Expr::FieldAccess(
            Box::new(substitute_expr(target, env)),
            field_name.clone(),
            span.clone(),
        ),
        Expr::FieldAssign(target, field_name, val, span) => Expr::FieldAssign(
            Box::new(substitute_expr(target, env)),
            field_name.clone(),
            Box::new(substitute_expr(val, env)),
            span.clone(),
        ),
        Expr::ArrayInit(elems, span) => Expr::ArrayInit(
            elems.iter().map(|e| substitute_expr(e, env)).collect(),
            span.clone(),
        ),
        Expr::TupleInit(elems, span) => Expr::TupleInit(
            elems.iter().map(|e| substitute_expr(e, env)).collect(),
            span.clone(),
        ),
        Expr::IndexAccess(target, idx, span) => Expr::IndexAccess(
            Box::new(substitute_expr(target, env)),
            Box::new(substitute_expr(idx, env)),
            span.clone(),
        ),
        Expr::IndexAssign(target, idx, val, span) => Expr::IndexAssign(
            Box::new(substitute_expr(target, env)),
            Box::new(substitute_expr(idx, env)),
            Box::new(substitute_expr(val, env)),
            span.clone(),
        ),
        Expr::EnumConstruct(enum_name, variant_name, args, span) => Expr::EnumConstruct(
            enum_name.clone(),
            variant_name.clone(),
            args.iter().map(|a| substitute_expr(a, env)).collect(),
            span.clone(),
        ),
        Expr::Match(target, arms, span) => Expr::Match(
            Box::new(substitute_expr(target, env)),
            arms.iter()
                .map(|arm| MatchArm {
                    variant_name: arm.variant_name.clone(),
                    bindings: arm.bindings.clone(),
                    body: arm.body.iter().map(|s| substitute_expr(s, env)).collect(),
                    span: arm.span.clone(),
                })
                .collect(),
            span.clone(),
        ),
        Expr::Ref(inner, is_mut, span) => Expr::Ref(
            Box::new(substitute_expr(inner, env)),
            *is_mut,
            span.clone(),
        ),
        Expr::Deref(inner, span) => Expr::Deref(Box::new(substitute_expr(inner, env)), span.clone()),
        Expr::DerefAssign(ptr, val, span) => Expr::DerefAssign(
            Box::new(substitute_expr(ptr, env)),
            Box::new(substitute_expr(val, env)),
            span.clone(),
        ),
        Expr::Closure(params, body, span) => Expr::Closure(
            params.clone(),
            Box::new(substitute_expr(body, env)),
            span.clone(),
        ),
        Expr::Cast(inner, target_ty, span) => Expr::Cast(
            Box::new(substitute_expr(inner, env)),
            substitute_type(*target_ty, env),
            span.clone(),
        ),
        Expr::Range(start, end, span) => Expr::Range(
            Box::new(substitute_expr(start, env)),
            Box::new(substitute_expr(end, env)),
            span.clone(),
        ),
    }
}

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

pub fn monomorphize_struct(
    mono: &RefCell<Monomorphizer>,
    base_name: &str,
    type_args: &[Type],
    struct_map: &RefCell<HashMap<String, StructLayout>>,
    enum_map: &RefCell<HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>>,
    fn_map: &RefCell<HashMap<String, FuncDecl>>,
    worklist: &RefCell<Vec<FuncDecl>>,
) -> Option<String> {
    if type_args.iter().any(crate::sanal::compat::type_contains_infer)
        || type_args.iter().any(crate::sanal::compat::type_contains_generic)
    {
        return None;
    }
    let key = GenericKey {
        name: base_name.to_string(),
        type_args: type_args.to_vec(),
    };

    if let Some(cached) = mono.borrow().struct_cache.get(&key) {
        return Some(cached.clone());
    }

    let decl = {
        let borrowed = mono.borrow();
        borrowed
            .struct_templates
            .get(base_name)
            .or_else(|| {
                borrowed
                    .struct_templates
                    .iter()
                    .find(|(k, _)| k.as_str() == base_name || k.ends_with(&format!("_{base_name}")))
                    .map(|(_, v)| v)
            })
            .cloned()?
    };

    let params = extract_generic_params_struct(&decl, mono);
    let mut env = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        if i < type_args.len() {
            env.insert(p.clone(), type_args[i]);
            env.insert(format!("${p}"), type_args[i]);
        }
    }

    let mangled_name = mangle_name(&decl.name, type_args);

    let mut total_size = 0u32;
    let mut field_offsets = HashMap::new();
    for field in &decl.fields {
        let field_ty = substitute_type(field.ty, &env);
        field_offsets.insert(field.name.clone(), (total_size, field_ty));
        total_size += 8;
    }

    struct_map.borrow_mut().insert(
        mangled_name.clone(),
        StructLayout {
            name: mangled_name.clone(),
            total_size,
            field_offsets,
        },
    );

    mono.borrow_mut()
        .struct_cache
        .insert(key, mangled_name.clone());

    {
        let fns = fn_map.borrow();
        check_where_clause_bounds(mono, decl.where_clause.as_ref(), &env, &decl.name, &fns);
    }

    // Impl Block Coupling
    let impls = mono.borrow().impl_templates.clone();
    for impl_block in &impls {
        if impl_block.target_type == decl.name
            || impl_block.target_type == base_name
            || decl.name.ends_with(&format!("_{}", impl_block.target_type))
        {
            for method in &impl_block.methods {
                if method.name == "from_slice"
                    && type_args.first().is_some_and(|t| !t.is_copy())
                {
                    continue;
                }
                let method_mangled = format!("{}_{}", mangled_name, method.name);
                let target_ty = Type::Obj(intern_str(&mangled_name));

                let mut params = Vec::new();
                for p in &method.params {
                    if p.name == "self" {
                        let self_ty = match p.ty {
                            Type::Unit => target_ty,
                            Type::Ref(inner) if *inner == Type::Unit => {
                                Type::Ref(intern_type(target_ty))
                            }
                            Type::MutRef(inner) if *inner == Type::Unit => {
                                Type::MutRef(intern_type(target_ty))
                            }
                            _ => substitute_type(p.ty, &env),
                        };
                        params.push(Param {
                            name: "self".to_string(),
                            is_mutable: p.is_mutable,
                            ty: self_ty,
                            span: p.span.clone(),
                        });
                    } else {
                        let mut p_ty = substitute_type(p.ty, &env);
                        if let Type::Obj(tn) = p_ty {
                            if tn == decl.name || tn == base_name {
                                p_ty = target_ty;
                            }
                        }
                        params.push(Param {
                            name: p.name.clone(),
                            is_mutable: p.is_mutable,
                            ty: p_ty,
                            span: p.span.clone(),
                        });
                    }
                }

                fn suffix_part_to_type(s: &str) -> Type {
                    match s {
                        "i64" | "int" | "isize" => Type::Int,
                        "i32" => Type::I32,
                        "i16" => Type::I16,
                        "i8" => Type::I8,
                        "u64" | "uint" | "usize" => Type::U64,
                        "u32" => Type::U32,
                        "u16" => Type::U16,
                        "u8" | "byte" => Type::U8,
                        "f64" | "float" => Type::Float,
                        "f32" => Type::F32,
                        "bool" => Type::Bool,
                        "str" => Type::Str,
                        "string" => Type::Obj(intern_str("std_string_String")),
                        "unit" => Type::Unit,
                        _ => Type::Obj(intern_str(s)),
                    }
                }

                let mut ret_ty = substitute_type(method.return_type, &env);
                if decl.name == "std_vec_Vec" && method.name == "from_slice" {
                    if let Some(&elem_ty) = type_args.first() {
                        ret_ty = Type::Vec(intern_type(elem_ty));
                    }
                }
                if let Type::Obj(tn) = ret_ty {
                    if tn == decl.name || tn == base_name {
                        ret_ty = target_ty;
                    } else {
                        let tn_str = tn.to_string();
                        if let Some((base_s, reg_tys)) = lookup_mangled(&tn_str) {
                            let clean_b = base_s.split('_').last().unwrap_or(&base_s);
                            monomorphize_struct(
                                mono,
                                clean_b,
                                &reg_tys,
                                struct_map,
                                enum_map,
                                fn_map,
                                worklist,
                            );
                        } else if let Some((b_name, suffix)) = tn_str.rsplit_once('_') {
                            let sub_tys: Vec<Type> = suffix
                                .split('_')
                                .map(suffix_part_to_type)
                                .collect();
                            let clean_b = b_name.split('_').last().unwrap_or(b_name);
                            monomorphize_struct(
                                mono,
                                clean_b,
                                &sub_tys,
                                struct_map,
                                enum_map,
                                fn_map,
                                worklist,
                            );
                        }
                    }
                }
                if let Type::Enum(mangled_enum) = ret_ty {
                    let m_str = mangled_enum.to_string();
                    if m_str.starts_with("std_core_Option_") || m_str.starts_with("std_core_Result_") {
                        let base_e = if m_str.starts_with("std_core_Option_") { "std_core_Option" } else { "std_core_Result" };
                        let sub_tys: Vec<Type> = if let Some((_, reg_tys)) = lookup_mangled(&m_str) {
                            reg_tys
                        } else {
                            m_str[base_e.len() + 1..]
                                .split('_')
                                .map(suffix_part_to_type)
                                .collect()
                        };
                        monomorphize_enum(mono, base_e, &sub_tys, enum_map, fn_map, worklist);
                    }
                }

                let body: Vec<Expr> = method
                    .body
                    .iter()
                    .map(|e| {
                        let sub = substitute_expr(e, &env);
                        rewrite_self_obj_init(sub, &decl.name, &mangled_name)
                    })
                    .collect();

                let specialized_func = FuncDecl {
                    name: method_mangled.clone(),
                    params,
                    return_type: ret_ty,
                    where_clause: None,
                    body,
                    is_track_caller: method.is_track_caller,
                };

                fn_map
                    .borrow_mut()
                    .insert(method_mangled.clone(), specialized_func.clone());
                worklist.borrow_mut().push(specialized_func);
            }
        }
    }

    Some(mangled_name)
}

fn rewrite_self_obj_init(expr: Expr, decl_name: &str, mangled_name: &str) -> Expr {
    let short_decl = decl_name.rsplit_once('_').map(|(_, s)| s).unwrap_or(decl_name);
    let rw = |e: Expr| rewrite_self_obj_init(e, decl_name, mangled_name);
    let rwb = |b: Box<Expr>| Box::new(rewrite_self_obj_init(*b, decl_name, mangled_name));
    match expr {
        Expr::Int(..) | Expr::Float(..) | Expr::Ident(..) | Expr::Bool(..) | Expr::String(..)
        | Expr::Break(..) | Expr::Continue(..) => expr,
        Expr::ObjInit(name, fields, span) => {
            let new_name = if name == decl_name || name == short_decl {
                mangled_name.to_string()
            } else {
                name
            };
            Expr::ObjInit(
                new_name,
                fields.into_iter().map(|(k, v)| (k, rw(v))).collect(),
                span,
            )
        }
        Expr::Block(stmts, span) => Expr::Block(stmts.into_iter().map(rw).collect(), span),
        Expr::Unsafe(stmts, span) => Expr::Unsafe(stmts.into_iter().map(rw).collect(), span),
        Expr::Return(opt, span) => Expr::Return(opt.map(rwb), span),
        Expr::Let(n, ty, m, val, span) => Expr::Let(n, ty, m, rwb(val), span),
        Expr::LetTuple(p, ty, val, span) => Expr::LetTuple(p, ty, rwb(val), span),
        Expr::Assign(n, val, span) => Expr::Assign(n, rwb(val), span),
        Expr::While(c, b, span) => Expr::While(rwb(c), rwb(b), span),
        Expr::If(c, b, span) => Expr::If(rwb(c), rwb(b), span),
        Expr::IfElse(c, t, e, span) => Expr::IfElse(rwb(c), rwb(t), rwb(e), span),
        Expr::Match(t, arms, span) => Expr::Match(
            rwb(t),
            arms.into_iter()
                .map(|arm| MatchArm {
                    variant_name: arm.variant_name,
                    bindings: arm.bindings,
                    body: arm.body.into_iter().map(rw).collect(),
                    span: arm.span,
                })
                .collect(),
            span,
        ),
        Expr::Try(inner, span) => Expr::Try(rwb(inner), span),
        Expr::Neg(inner, span) => Expr::Neg(rwb(inner), span),
        Expr::Not(inner, span) => Expr::Not(rwb(inner), span),
        Expr::Add(l, r, span) => Expr::Add(rwb(l), rwb(r), span),
        Expr::Sub(l, r, span) => Expr::Sub(rwb(l), rwb(r), span),
        Expr::Mul(l, r, span) => Expr::Mul(rwb(l), rwb(r), span),
        Expr::Div(l, r, span) => Expr::Div(rwb(l), rwb(r), span),
        Expr::Mod(l, r, span) => Expr::Mod(rwb(l), rwb(r), span),
        Expr::GreaterThan(l, r, span) => Expr::GreaterThan(rwb(l), rwb(r), span),
        Expr::LessThan(l, r, span) => Expr::LessThan(rwb(l), rwb(r), span),
        Expr::GreaterEqual(l, r, span) => Expr::GreaterEqual(rwb(l), rwb(r), span),
        Expr::LessEqual(l, r, span) => Expr::LessEqual(rwb(l), rwb(r), span),
        Expr::Equal(l, r, span) => Expr::Equal(rwb(l), rwb(r), span),
        Expr::NotEqual(l, r, span) => Expr::NotEqual(rwb(l), rwb(r), span),
        Expr::And(l, r, span) => Expr::And(rwb(l), rwb(r), span),
        Expr::Or(l, r, span) => Expr::Or(rwb(l), rwb(r), span),
        Expr::Pipe(l, r, span) => Expr::Pipe(rwb(l), rwb(r), span),
        Expr::Ampersand(l, r, span) => Expr::Ampersand(rwb(l), rwb(r), span),
        Expr::Caret(l, r, span) => Expr::Caret(rwb(l), rwb(r), span),
        Expr::Shl(l, r, span) => Expr::Shl(rwb(l), rwb(r), span),
        Expr::Shr(l, r, span) => Expr::Shr(rwb(l), rwb(r), span),
        Expr::MacroCall(n, args, span) => Expr::MacroCall(n, args.into_iter().map(rw).collect(), span),
        Expr::Call(n, args, span) => Expr::Call(n, args.into_iter().map(rw).collect(), span),
        Expr::FieldAccess(t, f, span) => Expr::FieldAccess(rwb(t), f, span),
        Expr::FieldAssign(t, f, v, span) => Expr::FieldAssign(rwb(t), f, rwb(v), span),
        Expr::ArrayInit(elems, span) => Expr::ArrayInit(elems.into_iter().map(rw).collect(), span),
        Expr::TupleInit(elems, span) => Expr::TupleInit(elems.into_iter().map(rw).collect(), span),
        Expr::IndexAccess(t, i, span) => Expr::IndexAccess(rwb(t), rwb(i), span),
        Expr::IndexAssign(t, i, v, span) => Expr::IndexAssign(rwb(t), rwb(i), rwb(v), span),
        Expr::EnumConstruct(e, v, args, span) => {
            Expr::EnumConstruct(e, v, args.into_iter().map(rw).collect(), span)
        }
        Expr::Ref(inner, is_mut, span) => Expr::Ref(rwb(inner), is_mut, span),
        Expr::Deref(inner, span) => Expr::Deref(rwb(inner), span),
        Expr::DerefAssign(p, v, span) => Expr::DerefAssign(rwb(p), rwb(v), span),
        Expr::Closure(p, body, span) => Expr::Closure(p, rwb(body), span),
        Expr::Cast(inner, ty, span) => Expr::Cast(rwb(inner), ty, span),
        Expr::Range(s, e, span) => Expr::Range(rwb(s), rwb(e), span),
    }
}

pub fn monomorphize_enum(
    mono: &RefCell<Monomorphizer>,
    base_name: &str,
    type_args: &[Type],
    enum_map: &RefCell<HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>>,
    fn_map: &RefCell<HashMap<String, FuncDecl>>,
    worklist: &RefCell<Vec<FuncDecl>>,
) -> Option<String> {
    if type_args.iter().any(crate::sanal::compat::type_contains_infer)
        || type_args.iter().any(crate::sanal::compat::type_contains_generic)
    {
        return None;
    }
    let key = GenericKey {
        name: base_name.to_string(),
        type_args: type_args.to_vec(),
    };

    if let Some(cached) = mono.borrow().enum_cache.get(&key) {
        return Some(cached.clone());
    }

    let decl = {
        let borrowed = mono.borrow();
        borrowed
            .enum_templates
            .get(base_name)
            .or_else(|| {
                borrowed
                    .enum_templates
                    .iter()
                    .find(|(k, _)| k.as_str() == base_name || k.ends_with(&format!("_{base_name}")))
                    .map(|(_, v)| v)
            })
            .cloned()?
    };

    let params = extract_generic_params_enum(&decl);
    let mut env = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        if i < type_args.len() {
            env.insert(p.clone(), type_args[i]);
            env.insert(format!("${p}"), type_args[i]);
        }
    }

    let mangled_name = mangle_name(&decl.name, type_args);
    let static_mangled_name = intern_str(&mangled_name);

    let mut variant_map = HashMap::new();
    for (i, variant) in decl.variants.iter().enumerate() {
        let payload_types = variant
            .payload_types
            .iter()
            .map(|t| substitute_type(*t, &env))
            .collect();
        variant_map.insert(variant.name.clone(), (i as i64, payload_types));
    }

    enum_map
        .borrow_mut()
        .insert(mangled_name.clone(), (static_mangled_name, variant_map));

    mono.borrow_mut()
        .enum_cache
        .insert(key, mangled_name.clone());

    {
        let fns = fn_map.borrow();
        check_where_clause_bounds(mono, decl.where_clause.as_ref(), &env, &decl.name, &fns);
    }

    // Impl Block Coupling
    let impls = mono.borrow().impl_templates.clone();
    for impl_block in &impls {
        if impl_block.target_type == decl.name
            || impl_block.target_type == base_name
            || decl.name.ends_with(&format!("_{}", impl_block.target_type))
        {
            for method in &impl_block.methods {
                if method.name == "from_slice"
                    && type_args.first().is_some_and(|t| !t.is_copy())
                {
                    continue;
                }
                let method_mangled = format!("{}_{}", mangled_name, method.name);
                let target_ty = Type::Enum(static_mangled_name);

                let mut params = Vec::new();
                for p in &method.params {
                    if p.name == "self" {
                        let self_ty = match p.ty {
                            Type::Unit => target_ty,
                            Type::Ref(inner) if *inner == Type::Unit => {
                                Type::Ref(intern_type(target_ty))
                            }
                            Type::MutRef(inner) if *inner == Type::Unit => {
                                Type::MutRef(intern_type(target_ty))
                            }
                            _ => substitute_type(p.ty, &env),
                        };
                        params.push(Param {
                            name: "self".to_string(),
                            is_mutable: p.is_mutable,
                            ty: self_ty,
                            span: p.span.clone(),
                        });
                    } else {
                        let mut p_ty = substitute_type(p.ty, &env);
                        if let Type::Obj(tn) = p_ty {
                            if tn == decl.name || tn == base_name {
                                p_ty = target_ty;
                            }
                        }
                        params.push(Param {
                            name: p.name.clone(),
                            is_mutable: p.is_mutable,
                            ty: p_ty,
                            span: p.span.clone(),
                        });
                    }
                }

                let ret_ty = substitute_type(method.return_type, &env);

                let body: Vec<Expr> = method
                    .body
                    .iter()
                    .map(|e| {
                        let sub = substitute_expr(e, &env);
                        rewrite_self_obj_init(sub, &decl.name, &mangled_name)
                    })
                    .collect();

                let specialized_func = FuncDecl {
                    name: method_mangled.clone(),
                    params,
                    return_type: ret_ty,
                    where_clause: None,
                    body,
                    is_track_caller: method.is_track_caller,
                };

                fn_map
                    .borrow_mut()
                    .insert(method_mangled.clone(), specialized_func.clone());
                worklist.borrow_mut().push(specialized_func);
            }
        }
    }

    Some(mangled_name)
}

fn unify_generic_types(param_ty: Type, arg_ty: Type, env: &mut HashMap<String, Type>) {
    match (param_ty, arg_ty) {
        (Type::Generic(g), actual) => {
            if !matches!(actual, Type::Generic(_)) {
                let clean = g.trim_start_matches('$').to_string();
                env.entry(clean.clone()).or_insert(actual);
                env.entry(format!("${clean}")).or_insert(actual);
            }
        }
        (Type::Ptr(p), Type::Ptr(a))
        | (Type::Ref(p), Type::Ref(a))
        | (Type::MutRef(p), Type::MutRef(a))
        | (Type::Rc(p), Type::Rc(a))
        | (Type::Arc(p), Type::Arc(a))
        | (Type::Vec(p), Type::Vec(a))
        | (Type::Slice(p), Type::Slice(a)) => unify_generic_types(*p, *a, env),
        (Type::Ref(p), actual) | (Type::MutRef(p), actual) => {
            unify_generic_types(*p, actual, env);
        }
        (Type::Array(p, _), Type::Array(a, _)) => unify_generic_types(*p, *a, env),
        (Type::Tuple(ps), Type::Tuple(as_)) if ps.len() == as_.len() => {
            for (p, a) in ps.iter().zip(as_.iter()) {
                unify_generic_types(*p, *a, env);
            }
        }
        (Type::Enum(pe) | Type::Obj(pe), Type::Enum(ae) | Type::Obj(ae)) => {
            if let (Some((pb, p_args)), Some((ab, a_args))) =
                (lookup_mangled(pe), lookup_mangled(ae))
            {
                if pb == ab && p_args.len() == a_args.len() {
                    for (pa, aa) in p_args.into_iter().zip(a_args) {
                        unify_generic_types(pa, aa, env);
                    }
                }
            }
        }
        _ => {}
    }
}

fn extract_generic_params_fn(decl: &FuncDecl) -> Vec<String> {
    let mut params = Vec::new();
    if let Some(w) = &decl.where_clause {
        let clean = w.target_param.trim_start_matches('$').to_string();
        if !params.contains(&clean) {
            params.push(clean);
        }
    }
    for p in &decl.params {
        collect_generics_from_type(&p.ty, &mut params);
    }
    collect_generics_from_type(&decl.return_type, &mut params);
    params
}

pub fn monomorphize_fn(
    mono: &RefCell<Monomorphizer>,
    base_name: &str,
    arg_types: &[Type],
    fn_map: &RefCell<HashMap<String, FuncDecl>>,
    _struct_map: &RefCell<HashMap<String, StructLayout>>,
    enum_map: &RefCell<HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>>,
    worklist: &RefCell<Vec<FuncDecl>>,
) -> Option<String> {
    let decl = {
        let borrowed = mono.borrow();
        borrowed
            .fn_templates
            .get(base_name)
            .cloned()
            .or_else(|| fn_map.borrow().get(base_name).cloned())?
    };

    let mut env = HashMap::new();
    for (p, &a_ty) in decl.params.iter().zip(arg_types.iter()) {
        unify_generic_types(p.ty, a_ty, &mut env);
    }

    let gen_params = extract_generic_params_fn(&decl);
    if gen_params.is_empty() {
        return None;
    }

    let mut type_args = Vec::with_capacity(gen_params.len());
    for gp in &gen_params {
        let ty = env.get(gp).copied()?;
        if crate::sanal::compat::type_contains_generic(&ty)
            || crate::sanal::compat::type_contains_infer(&ty)
        {
            return None;
        }
        type_args.push(ty);
    }

    let key = GenericKey {
        name: decl.name.clone(),
        type_args: type_args.clone(),
    };
    if let Some(cached) = mono.borrow().fn_cache.get(&key) {
        return Some(cached.clone());
    }

    let mangled_name = mangle_name(&decl.name, &type_args);
    mono.borrow_mut()
        .fn_cache
        .insert(key, mangled_name.clone());

    {
        let fns = fn_map.borrow();
        check_where_clause_bounds(mono, decl.where_clause.as_ref(), &env, &decl.name, &fns);
    }

    let params: Vec<Param> = decl
        .params
        .iter()
        .map(|p| Param {
            name: p.name.clone(),
            is_mutable: p.is_mutable,
            ty: substitute_type(p.ty, &env),
            span: p.span.clone(),
        })
        .collect();
    let ret_ty = substitute_type(decl.return_type, &env);

    if let Type::Enum(mangled_enum) = ret_ty {
        let m_str = mangled_enum.to_string();
        if m_str.starts_with("std_core_Option_") || m_str.starts_with("std_core_Result_") {
            let base_e = if m_str.starts_with("std_core_Option_") {
                "std_core_Option"
            } else {
                "std_core_Result"
            };
            if let Some((_, reg_tys)) = lookup_mangled(&m_str) {
                monomorphize_enum(mono, base_e, &reg_tys, enum_map, fn_map, worklist);
            }
        }
    }

    let body: Vec<Expr> = decl
        .body
        .iter()
        .map(|e| substitute_expr(e, &env))
        .collect();

    let specialized_func = FuncDecl {
        name: mangled_name.clone(),
        params,
        return_type: ret_ty,
        where_clause: None,
        body,
        is_track_caller: decl.is_track_caller,
    };

    fn_map
        .borrow_mut()
        .insert(mangled_name.clone(), specialized_func.clone());
    worklist.borrow_mut().push(specialized_func);

    Some(mangled_name)
}
