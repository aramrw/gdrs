//! sanal/mono/subst.rs
//! AST type and expression substitution with concrete generic parameters.

use std::{cell::RefCell, collections::HashMap};
use crate::{
    ast::{intern_str, intern_type, EnumDecl, Expr, MatchArm, StructDecl, Type},
    sanal::mono::{lookup_mangled, mangle_name, type_suffix, Monomorphizer},
};

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

pub fn collect_generics_from_type(ty: &Type, params: &mut Vec<String>) {
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

