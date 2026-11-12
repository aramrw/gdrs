//! sanal/mono/instances.rs
//! Concrete type monomorphization for structs, enums, and functions.

use std::{cell::RefCell, collections::HashMap};
use crate::{
    ast::{intern_str, intern_type, EnumDecl, Expr, FuncDecl, MatchArm, Param, StructDecl, Type},
    sanal::{
        mono::{
            check_where_clause_bounds, collect_generics_from_type, extract_generic_params_enum,
            extract_generic_params_struct, find_enum_template, find_struct_template, lookup_mangled,
            mangle_name, substitute_expr, substitute_type, GenericKey, Monomorphizer,
        },
        StructLayout,
    },
};

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
    let mut field_vis = HashMap::new();
    for field in &decl.fields {
        let field_ty = substitute_type(field.ty, &env);
        field_offsets.insert(field.name.clone(), (total_size, field_ty));
        field_vis.insert(field.name.clone(), field.vis);
        total_size += 8;
    }

    struct_map.borrow_mut().insert(
        mangled_name.clone(),
        StructLayout {
            name: mangled_name.clone(),
            total_size,
            field_offsets,
            vis: decl.vis,
            module_path: decl.module_path.clone(),
            field_vis,
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
                    vis: method.vis,
                    module_path: method.module_path.clone(),
                    is_trait_impl: method.is_trait_impl,
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
                    vis: method.vis,
                    module_path: method.module_path.clone(),
                    is_trait_impl: method.is_trait_impl,
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
        vis: decl.vis,
        module_path: decl.module_path.clone(),
        is_trait_impl: decl.is_trait_impl,
    };

    fn_map
        .borrow_mut()
        .insert(mangled_name.clone(), specialized_func.clone());
    worklist.borrow_mut().push(specialized_func);

    Some(mangled_name)
}
