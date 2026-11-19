//! sanal/mono/instances.rs
//! Concrete type monomorphization for structs, enums, and functions.

use std::{cell::RefCell, collections::HashMap};
use crate::{
    ast::{intern_str, intern_type, EnumDecl, Expr, FuncDecl, MatchArm, Param, StructDecl, Type},
    sanal::{
        mono::{
            check_where_clause_bounds, collect_generics_from_type, extract_generic_params_enum,
            extract_generic_params_struct, find_enum_template, find_struct_template, lookup_mangled,
            mangle_name, substitute_expr, substitute_type, type_satisfies_bound, GenericKey, Monomorphizer,
        },
        StructLayout,
    },
};

/// Resolves nested `Obj` enum aliases into `Type::Enum` and ensures monomorphization of field/payload types.
fn normalize_instantiated_type(
    ty: Type,
    mono: &RefCell<Monomorphizer>,
    struct_map: Option<&RefCell<HashMap<String, StructLayout>>>,
    enum_map: &RefCell<HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>>,
    fn_map: &RefCell<HashMap<String, FuncDecl>>,
    worklist: &RefCell<Vec<FuncDecl>>,
) -> Type {
    match ty {
        Type::Ptr(inner) => Type::Ptr(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::Ref(inner) => Type::Ref(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::MutRef(inner) => Type::MutRef(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::Box(inner) => Type::Box(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::Rc(inner) => Type::Rc(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::Arc(inner) => Type::Arc(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::Vec(inner) => Type::Vec(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::Slice(inner) => Type::Slice(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist))),
        Type::Array(inner, len) => Type::Array(intern_type(normalize_instantiated_type(*inner, mono, struct_map, enum_map, fn_map, worklist)), len),
        Type::FnPtr(params, ret) => {
            let norm_params: Vec<Type> = params
                .iter()
                .map(|p| normalize_instantiated_type(*p, mono, struct_map, enum_map, fn_map, worklist))
                .collect();
            let norm_ret = normalize_instantiated_type(*ret, mono, struct_map, enum_map, fn_map, worklist);
            Type::FnPtr(crate::ast::intern_tuple(&norm_params), intern_type(norm_ret))
        }
        Type::Tuple(elems) => {
            let norm: Vec<Type> = elems
                .iter()
                .map(|e| normalize_instantiated_type(*e, mono, struct_map, enum_map, fn_map, worklist))
                .collect();
            Type::Tuple(crate::ast::intern_tuple(&norm))
        }
        Type::Obj(name) | Type::Enum(name) => {
            let is_enum = matches!(ty, Type::Enum(_))
                || enum_map.borrow().contains_key(name)
                || find_enum_template(&mono.borrow(), name).is_some()
                || name.contains("Option")
                || name.contains("Result")
                || lookup_mangled(name).is_some_and(|(b, _)| find_enum_template(&mono.borrow(), &b).is_some());
            if let Some((base, args)) = lookup_mangled(name) {
                let norm_args: Vec<Type> = args
                    .iter()
                    .map(|a| normalize_instantiated_type(*a, mono, struct_map, enum_map, fn_map, worklist))
                    .collect();
                if is_enum {
                    if let Some(mangled) = monomorphize_enum(mono, &base, &norm_args, enum_map, fn_map, worklist) {
                        return Type::Enum(intern_str(&mangled));
                    }
                    return Type::Enum(name);
                } else if let Some(s_map) = struct_map {
                    if let Some(mangled) = monomorphize_struct(mono, &base, &norm_args, s_map, enum_map, fn_map, worklist) {
                        return Type::Obj(intern_str(&mangled));
                    }
                }
            }
            if is_enum {
                Type::Enum(name)
            } else {
                Type::Obj(name)
            }
        }
        other => other,
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
    populate_iter_adapter_env(&mut env, &decl.name, &mangled_name, type_args, &fn_map.borrow());

    let mut total_size = 0u32;
    let mut field_offsets = HashMap::new();
    let mut field_vis = HashMap::new();
    for field in &decl.fields {
        let field_ty = normalize_instantiated_type(
            substitute_type(field.ty, &env),
            mono,
            Some(struct_map),
            enum_map,
            fn_map,
            worklist,
        );
        field_offsets.insert(field.name.clone(), (total_size, field_ty));
        field_vis.insert(field.name.clone(), field.vis);
        total_size += 8;
    }

    let (repr_align, repr_packed) = crate::sanal::parse_struct_repr(&decl.attributes, &mut Vec::new());

    struct_map.borrow_mut().insert(
        mangled_name.clone(),
        StructLayout {
            name: mangled_name.clone(),
            total_size,
            field_offsets,
            vis: decl.vis,
            module_path: decl.module_path.clone(),
            field_vis,
            repr_align,
            repr_packed,
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
                if let Some(w) = &method.where_clause {
                    let clean = w.target_param.trim_start_matches('$');
                    if let Some(&concrete_ty) = env.get(clean).or_else(|| env.get(&w.target_param)) {
                        let m = mono.borrow();
                        let fns = fn_map.borrow();
                        let satisfied = w.bounds.iter().all(|b| {
                            type_satisfies_bound(concrete_ty, b, &m.trait_methods, &m.trait_impls, &fns)
                        });
                        if !satisfied {
                            continue;
                        }
                    }
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
                            if !reg_tys.iter().any(|t| {
                                crate::sanal::compat::type_contains_generic(t)
                                    || crate::sanal::compat::type_contains_infer(t)
                            }) {
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
                            }
                        } else if let Some((b_name, suffix)) = tn_str.rsplit_once('_') {
                            let sub_tys: Vec<Type> = suffix
                                .split('_')
                                .map(suffix_part_to_type)
                                .collect();
                            if !sub_tys.iter().any(|t| {
                                crate::sanal::compat::type_contains_generic(t)
                                    || crate::sanal::compat::type_contains_infer(t)
                            }) {
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
                } else if let Type::Vec(elem_ty) = ret_ty {
                    if !crate::sanal::compat::type_contains_generic(&elem_ty)
                        && !crate::sanal::compat::type_contains_infer(&elem_ty)
                    {
                        monomorphize_struct(
                            mono,
                            "std_vec_Vec",
                            &[*elem_ty],
                            struct_map,
                            enum_map,
                            fn_map,
                            worklist,
                        );
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
        | Expr::Continue(..) => expr,
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
        Expr::Break(opt, span) => Expr::Break(opt.map(rwb), span),
        Expr::Let(n, ty, m, val, span) => Expr::Let(n, ty, m, rwb(val), span),
        Expr::LetTuple(p, ty, val, span) => Expr::LetTuple(p, ty, rwb(val), span),
        Expr::LetStruct(mut p, ty, val, span) => {
            if p.struct_path == decl_name || p.struct_path == short_decl {
                p.struct_path = mangled_name.to_string();
            }
            Expr::LetStruct(p, ty, rwb(val), span)
        }
        Expr::Assign(n, val, span) => Expr::Assign(n, rwb(val), span),
        Expr::While(c, b, span) => Expr::While(rwb(c), rwb(b), span),
        Expr::Loop(b, span) => Expr::Loop(rwb(b), span),
        Expr::If(c, b, span) => Expr::If(rwb(c), rwb(b), span),
        Expr::IfElse(c, t, e, span) => Expr::IfElse(rwb(c), rwb(t), rwb(e), span),
        Expr::Match(t, arms, span) => Expr::Match(
            rwb(t),
            arms.into_iter()
                .map(|arm| MatchArm {
                    variant_name: arm.variant_name,
                    bindings: arm.bindings,
                    alt_patterns: arm.alt_patterns,
                    guard: arm.guard.map(rwb),
                    body: arm.body.into_iter().map(rw).collect(),
                    span: arm.span,
                })
                .collect(),
            span,
        ),
        Expr::LetElse {
            variant_name,
            bindings,
            target,
            else_body,
            span,
        } => Expr::LetElse {
            variant_name,
            bindings,
            target: rwb(target),
            else_body: else_body.into_iter().map(rw).collect(),
            span,
        },
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
        Expr::CompoundAssign(op, l, r, span) => Expr::CompoundAssign(op, rwb(l), rwb(r), span),
        Expr::Closure(is_move, p, body, span) => Expr::Closure(is_move, p, rwb(body), span),
        Expr::Cast(inner, ty, span) => Expr::Cast(rwb(inner), ty, span),
        Expr::Range(s, e, inc, span) => Expr::Range(rwb(s), rwb(e), inc, span),
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
    populate_iter_adapter_env(&mut env, &decl.name, &mangled_name, type_args, &fn_map.borrow());
    let static_mangled_name = intern_str(&mangled_name);

    let mut variant_map = HashMap::new();
    for (i, variant) in decl.variants.iter().enumerate() {
        let payload_types = variant
            .payload_types
            .iter()
            .map(|t| {
                normalize_instantiated_type(
                    substitute_type(*t, &env),
                    mono,
                    None,
                    enum_map,
                    fn_map,
                    worklist,
                )
            })
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
                if let Some(w) = &method.where_clause {
                    let clean = w.target_param.trim_start_matches('$');
                    if let Some(&concrete_ty) = env.get(clean).or_else(|| env.get(&w.target_param)) {
                        let m = mono.borrow();
                        let fns = fn_map.borrow();
                        let satisfied = w.bounds.iter().all(|b| {
                            type_satisfies_bound(concrete_ty, b, &m.trait_methods, &m.trait_impls, &fns)
                        });
                        if !satisfied {
                            continue;
                        }
                    }
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
        | (Type::Box(p), Type::Box(a))
        | (Type::Rc(p), Type::Rc(a))
        | (Type::Arc(p), Type::Arc(a))
        | (Type::Vec(p), Type::Vec(a))
        | (Type::Slice(p), Type::Slice(a)) => unify_generic_types(*p, *a, env),
        (Type::Slice(p), Type::Ref(inner)) | (Type::Slice(p), Type::MutRef(inner)) => {
            if let Type::Array(a, _) | Type::Vec(a) | Type::Slice(a) = *inner {
                unify_generic_types(*p, *a, env);
            }
        }
        (Type::FnPtr(ps, pr), Type::FnPtr(as_, ar)) if ps.len() == as_.len() => {
            for (p, a) in ps.iter().zip(as_.iter()) {
                unify_generic_types(*p, *a, env);
            }
            unify_generic_types(*pr, *ar, env);
        }
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
    struct_map: &RefCell<HashMap<String, StructLayout>>,
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

    let mut rewrite_ret_obj: Option<(String, String)> = None;
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
    } else if let Type::Obj(mangled_obj) = ret_ty {
        if let Some((base_s, reg_tys)) = lookup_mangled(mangled_obj) {
            if !reg_tys.iter().any(|t| {
                crate::sanal::compat::type_contains_generic(t)
                    || crate::sanal::compat::type_contains_infer(t)
            }) {
                if let Some(actual_mangled) = monomorphize_struct(
                    mono,
                    &base_s,
                    &reg_tys,
                    struct_map,
                    enum_map,
                    fn_map,
                    worklist,
                ) {
                    rewrite_ret_obj = Some((base_s, actual_mangled));
                }
            }
        }
    } else if let Type::Vec(elem_ty) = ret_ty {
        if !crate::sanal::compat::type_contains_generic(&elem_ty)
            && !crate::sanal::compat::type_contains_infer(&elem_ty)
        {
            monomorphize_struct(mono, "std_vec_Vec", &[*elem_ty], struct_map, enum_map, fn_map, worklist);
        }
    }

    let body: Vec<Expr> = decl
        .body
        .iter()
        .map(|e| {
            let sub = substitute_expr(e, &env);
            if let Some((ref base_s, ref actual_mangled)) = rewrite_ret_obj {
                rewrite_self_obj_init(sub, base_s, actual_mangled)
            } else {
                sub
            }
        })
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

fn infer_iter_output_type(iter_ty: Type, fn_map: &HashMap<String, FuncDecl>) -> Option<Type> {
    match iter_ty {
        Type::Obj("Range") | Type::Obj("std_iter_Range") => Some(Type::Int),
        Type::Obj(s) => {
            if s.contains("VecRefIter_") {
                if let Some((_, args)) = lookup_mangled(s) {
                    if let Some(&first) = args.first() {
                        return Some(Type::Ref(crate::ast::intern_type(first)));
                    }
                }
            }
            if s.contains("VecIter_") {
                if let Some((_, args)) = lookup_mangled(s) {
                    if let Some(&first) = args.first() {
                        return Some(first);
                    }
                }
            }
            if let Some(f) = fn_map.get(&format!("{s}_next")) {
                if let Type::Enum(opt_name) = f.return_type {
                    if let Some((_, args)) = lookup_mangled(opt_name) {
                        if let Some(&item) = args.first() {
                            return Some(item);
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn infer_callable_output_type(fn_ty: Type, fn_map: &HashMap<String, FuncDecl>) -> Option<Type> {
    match fn_ty {
        Type::FnPtr(_, ret) => Some(*ret),
        Type::Obj(cname) => fn_map
            .get(&format!("{cname}_call_once"))
            .or_else(|| fn_map.get(&format!("{cname}_call_mut")))
            .or_else(|| fn_map.get(&format!("{cname}_call_ref")))
            .map(|f| f.return_type),
        _ => None,
    }
}

fn populate_iter_adapter_env(
    env: &mut HashMap<String, Type>,
    decl_name: &str,
    mangled_name: &str,
    type_args: &[Type],
    fn_map: &HashMap<String, FuncDecl>,
) {
    let self_ty = Type::Obj(intern_str(mangled_name));
    env.insert("Self".to_string(), self_ty);

    let short = decl_name.rsplit_once('_').map(|(_, s)| s).unwrap_or(decl_name);
    if type_args.len() >= 2 {
        match short {
            "Map" => {
                if let Some(out_ty) = infer_callable_output_type(type_args[1], fn_map) {
                    env.insert("U".to_string(), out_ty);
                    env.insert("$U".to_string(), out_ty);
                    env.insert("T".to_string(), out_ty);
                    env.insert("$T".to_string(), out_ty);
                }
            }
            "Filter" => {
                if let Some(item_ty) = infer_iter_output_type(type_args[0], fn_map) {
                    env.insert("T".to_string(), item_ty);
                    env.insert("$T".to_string(), item_ty);
                }
            }
            "FilterMap" => {
                if let Some(Type::Enum(opt_name)) = infer_callable_output_type(type_args[1], fn_map) {
                    if let Some((_, args)) = lookup_mangled(opt_name) {
                        if let Some(&inner_ty) = args.first() {
                            env.insert("U".to_string(), inner_ty);
                            env.insert("$U".to_string(), inner_ty);
                            env.insert("T".to_string(), inner_ty);
                            env.insert("$T".to_string(), inner_ty);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
