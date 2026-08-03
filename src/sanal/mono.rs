//! sanal/mono.rs
//! Generic Monomorphization engine: AST type & expression substitution, layout generation, and caching.

use crate::ast::{
    intern_str, intern_type, EnumDecl, Expr, FuncDecl, ImplDecl, MatchArm, Param, Span,
    StructDecl, Type, WhereClause,
};
use crate::sanal::StructLayout;
use std::cell::RefCell;
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

    pub struct_cache: HashMap<GenericKey, String>,
    pub enum_cache: HashMap<GenericKey, String>,
    pub fn_cache: HashMap<GenericKey, String>,
}

pub fn type_suffix(ty: &Type) -> String {
    match ty {
        Type::Int => "i64".to_string(),
        Type::I32 => "i32".to_string(),
        Type::Float => "f64".to_string(),
        Type::F32 => "f32".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str | Type::String => "str".to_string(),
        Type::Unit => "unit".to_string(),
        Type::Obj(n) | Type::Enum(n) | Type::Generic(n) | Type::DynTrait(n) => {
            n.replace("::", "_").to_lowercase()
        }
        Type::Array(t, len) => format!("arr_{}_{len}", type_suffix(t)),
        Type::Slice(t) => format!("slice_{}", type_suffix(t)),
        Type::Vec(t) => format!("vec_{}", type_suffix(t)),
        Type::Rc(t) => format!("rc_{}", type_suffix(t)),
        Type::Arc(t) => format!("arc_{}", type_suffix(t)),
        Type::Void => "void".to_string(),
        Type::Ptr(t) => format!("ptr_{}", type_suffix(t)),
        Type::Ref(t) => format!("ref_{}", type_suffix(t)),
        Type::MutRef(t) => format!("mutref_{}", type_suffix(t)),
    }
}

pub fn mangle_name(base: &str, type_args: &[Type]) -> String {
    if type_args.is_empty() {
        base.to_string()
    } else {
        let suffixes: Vec<String> = type_args.iter().map(type_suffix).collect();
        format!("{}_{}", base, suffixes.join("_"))
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
        Type::Obj(name) | Type::Enum(name) => {
            let s_name = name.to_string();
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
                if name.starts_with("Vec::") || name.starts_with("Vec.") || name == "Vec::new" || name == "Vec.new" {
                    let method = name.rsplit("::").next().unwrap_or(name).rsplit('.').next().unwrap_or(name);
                    format!("{}_{method}", mangle_name("Vec", &unique_vals))
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

pub fn monomorphize_struct(
    mono: &RefCell<Monomorphizer>,
    base_name: &str,
    type_args: &[Type],
    struct_map: &RefCell<HashMap<String, StructLayout>>,
    enum_map: &RefCell<HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>>,
    fn_map: &RefCell<HashMap<String, FuncDecl>>,
    worklist: &RefCell<Vec<FuncDecl>>,
) -> Option<String> {
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

    // Impl Block Coupling
    let impls = mono.borrow().impl_templates.clone();
    for impl_block in &impls {
        if impl_block.target_type == decl.name
            || impl_block.target_type == base_name
            || decl.name.ends_with(&format!("_{}", impl_block.target_type))
        {
            for method in &impl_block.methods {
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
                        params.push(Param {
                            name: p.name.clone(),
                            is_mutable: p.is_mutable,
                            ty: substitute_type(p.ty, &env),
                            span: p.span.clone(),
                        });
                    }
                }

                let mut ret_ty = substitute_type(method.return_type, &env);
                if let Type::Obj(tn) = ret_ty {
                    if tn == decl.name || tn == base_name {
                        ret_ty = target_ty;
                    } else {
                        let tn_str = tn.to_string();
                        if let Some((b_name, suffix)) = tn_str.rsplit_once('_') {
                            let sub_tys: Vec<Type> = suffix
                                .split('_')
                                .map(|s| {
                                    if s == "i64" || s == "int" {
                                        Type::Int
                                    } else if s == "i32" {
                                        Type::I32
                                    } else if s == "bool" {
                                        Type::Bool
                                    } else {
                                        Type::Obj(intern_str(s))
                                    }
                                })
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
                        let sub_strs: Vec<&str> = m_str[base_e.len() + 1..].split('_').collect();
                        let sub_tys: Vec<Type> = sub_strs
                            .iter()
                            .map(|s| {
                                if *s == "i64" || *s == "int" {
                                    Type::Int
                                } else if *s == "i32" {
                                    Type::I32
                                } else if *s == "bool" {
                                    Type::Bool
                                } else {
                                    Type::Obj(intern_str(s))
                                }
                            })
                            .collect();
                        monomorphize_enum(mono, base_e, &sub_tys, enum_map, fn_map, worklist);
                    }
                }

                let body: Vec<Expr> = method
                    .body
                    .iter()
                    .map(|e| substitute_expr(e, &env))
                    .collect();

                let specialized_func = FuncDecl {
                    name: method_mangled.clone(),
                    params,
                    return_type: ret_ty,
                    where_clause: None,
                    body,
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

pub fn monomorphize_enum(
    mono: &RefCell<Monomorphizer>,
    base_name: &str,
    type_args: &[Type],
    enum_map: &RefCell<HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>>,
    fn_map: &RefCell<HashMap<String, FuncDecl>>,
    worklist: &RefCell<Vec<FuncDecl>>,
) -> Option<String> {
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

    // Impl Block Coupling
    let impls = mono.borrow().impl_templates.clone();
    for impl_block in &impls {
        if impl_block.target_type == decl.name
            || impl_block.target_type == base_name
            || decl.name.ends_with(&format!("_{}", impl_block.target_type))
        {
            for method in &impl_block.methods {
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
                        params.push(Param {
                            name: p.name.clone(),
                            is_mutable: p.is_mutable,
                            ty: substitute_type(p.ty, &env),
                            span: p.span.clone(),
                        });
                    }
                }

                let ret_ty = substitute_type(method.return_type, &env);

                let body: Vec<Expr> = method
                    .body
                    .iter()
                    .map(|e| substitute_expr(e, &env))
                    .collect();

                let specialized_func = FuncDecl {
                    name: method_mangled.clone(),
                    params,
                    return_type: ret_ty,
                    where_clause: None,
                    body,
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
