//! sanal/calls/resolution.rs
//! Target function and method resolution, template lookup, and monomorphization dispatch.

use crate::{
    ast::{FuncDecl, Span, Type, TypedExpr},
    sanal::{
        calls::helpers::build_substituted_method,
        types::TypeCtx,
    },
};

pub fn resolve_call_target<'a>(
    raw_name: &str,
    name: &str,
    mut resolved_name: String,
    is_direct_concrete_fn: bool,
    is_generic_fn: bool,
    typed_args: &[TypedExpr],
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) -> (String, Option<FuncDecl>) {
    let mut deferred_target_func: Option<FuncDecl> = None;

    if !is_direct_concrete_fn && (resolved_name == name || !type_ctx.contains_fn(&resolved_name) || is_generic_fn) {
        let target_type = if !typed_args.is_empty() {
            let t0 = match typed_args[0].ty() {
                Type::Ref(inner) | Type::MutRef(inner) => *inner,
                other => other,
            };
            match t0 {
                Type::Obj(s) | Type::Enum(s) => Some(s.to_string()),
                Type::Vec(_) => Some("Vec".to_string()),
                Type::String => Some("String".to_string()),
                _ => None,
            }
        } else {
            None
        };

        let (mut base_struct, method_name) = if name.starts_with("std_vec_Vec_") {
            ("std_vec_Vec".to_string(), name["std_vec_Vec_".len()..].to_string())
        } else if let Some(ref tt) = target_type {
            let mn = if name.starts_with(&format!("{tt}_")) {
                name[tt.len() + 1..].to_string()
            } else {
                name.to_string()
            };
            (tt.clone(), mn)
        } else if let Some((bs, mn)) = {
            let mono = type_ctx.mono.borrow();
            let mut found = None;
            for (idx, _) in name.match_indices('_') {
                let candidate = &name[..idx];
                let is_known = type_ctx.struct_map.borrow().contains_key(candidate)
                    || type_ctx.enum_map.borrow().contains_key(candidate)
                    || mono.struct_templates.contains_key(candidate)
                    || mono.enum_templates.contains_key(candidate)
                    || mono.struct_templates.iter().any(|(k, _)| k.ends_with(&format!("_{candidate}")))
                    || mono.enum_templates.iter().any(|(k, _)| k.ends_with(&format!("_{candidate}")));
                if is_known {
                    found = Some((candidate.to_string(), name[idx + 1..].to_string()));
                }
            }
            found.or_else(|| {
                if raw_name.contains("::") {
                    raw_name.rsplit_once("::").map(|(b, m)| (b.replace("::", "_"), m.to_string()))
                } else {
                    name.split_once('_').map(|(b, m)| (b.to_string(), m.to_string()))
                }
            })
        } {
            (bs, mn)
        } else {
            (String::new(), String::new())
        };

        if base_struct.ends_with("_t") || base_struct.ends_with("_T") {
            base_struct = base_struct[..base_struct.len() - 2].to_string();
        }
        if base_struct == "VecIter" || base_struct == "std_vec_VecIter" || base_struct.starts_with("std_vec_VecIter_") {
            base_struct = "std_vec_VecIter".to_string();
        } else if base_struct == "Vec" || base_struct == "std_vec_Vec" || base_struct.starts_with("std_vec_Vec_") {
            base_struct = "std_vec_Vec".to_string();
        } else if base_struct == "String" || base_struct == "std_string_String" || base_struct.starts_with("std_string_String_") {
            base_struct = "std_string_String".to_string();
        } else if base_struct.contains("Option") {
            base_struct = if type_ctx.mono.borrow().enum_templates.contains_key("Option") || type_ctx.enum_map.borrow().contains_key("Option") {
                "Option".to_string()
            } else {
                "std_core_Option".to_string()
            };
        } else if base_struct.contains("Result") {
            base_struct = if type_ctx.mono.borrow().enum_templates.contains_key("Result") || type_ctx.enum_map.borrow().contains_key("Result") {
                "Result".to_string()
            } else {
                "std_core_Result".to_string()
            };
        } else if base_struct.starts_with("std_") {
            if let Some((clean, _)) = base_struct.rsplit_once('_') {
                if type_ctx.struct_map.borrow().contains_key(clean) || type_ctx.enum_map.borrow().contains_key(clean) {
                    base_struct = clean.to_string();
                }
            }
        }

        if !type_ctx.struct_map.borrow().contains_key(&base_struct)
            && !type_ctx.enum_map.borrow().contains_key(&base_struct)
            && !type_ctx.mono.borrow().struct_templates.contains_key(&base_struct)
            && !type_ctx.mono.borrow().enum_templates.contains_key(&base_struct)
        {
            if let Some(clean) = base_struct.strip_prefix("std_core_").or_else(|| base_struct.strip_prefix("std_vec_")).or_else(|| base_struct.strip_prefix("std_string_")) {
                if type_ctx.mono.borrow().enum_templates.contains_key(clean) || type_ctx.enum_map.borrow().contains_key(clean) {
                    base_struct = clean.to_string();
                } else if type_ctx.mono.borrow().struct_templates.contains_key(clean) || type_ctx.struct_map.borrow().contains_key(clean) {
                    base_struct = clean.to_string();
                }
            }
            if let Some(k) = type_ctx.mono.borrow().struct_templates.keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            } else if let Some(k) = type_ctx.struct_map.borrow().keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            } else if let Some(k) = type_ctx.mono.borrow().enum_templates.keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            } else if let Some(k) = type_ctx.enum_map.borrow().keys().find(|k| k.ends_with(&format!("_{base_struct}"))).cloned() {
                base_struct = k;
            }
        }

        let is_struct_or_enum = type_ctx.struct_map.borrow().contains_key(&base_struct)
            || type_ctx.enum_map.borrow().contains_key(&base_struct)
            || type_ctx.mono.borrow().struct_templates.contains_key(&base_struct)
            || type_ctx.mono.borrow().enum_templates.contains_key(&base_struct);

        if !base_struct.is_empty() && is_struct_or_enum {
            let mut resolved_mangled = false;
            if !typed_args.is_empty() {
                let arg_ty = match typed_args[0].ty() {
                    Type::Ref(inner) | Type::MutRef(inner) => *inner,
                    other => other,
                };
                if let Type::Enum(mangled_enum) | Type::Obj(mangled_enum) = arg_ty {
                    let mangled_fn = format!("{mangled_enum}_{method_name}");
                    if type_ctx.contains_fn(&mangled_fn) {
                        resolved_name = mangled_fn;
                        resolved_mangled = true;
                    } else if mangled_enum.starts_with("std_core_")
                        || type_ctx.mono.borrow().enum_templates.contains_key(mangled_enum)
                    {
                        let base_e = if mangled_enum.contains("Option") { "Option" } else { "Result" };
                        let alt_base_e = if mangled_enum.contains("Option") { "std_core_Option" } else { "std_core_Result" };
                        let cache = type_ctx.mono.borrow().enum_cache.clone();
                        let cached_args = cache.iter()
                            .find(|(_, m)| *m == mangled_enum || mangled_enum.ends_with(m.as_str()) || m.ends_with(&format!("_{mangled_enum}")))
                            .map(|(k, _)| k.type_args.clone());

                        let type_args = cached_args
                            .or_else(|| crate::sanal::mono::lookup_mangled(mangled_enum).map(|(_, a)| a))
                            .unwrap_or_else(|| vec![Type::Int, Type::Int]);

                        if type_args.iter().any(|t| {
                            crate::sanal::compat::type_contains_infer(t)
                                || crate::sanal::compat::type_contains_generic(t)
                        }) {
                            let enum_tpl = {
                                let mono = type_ctx.mono.borrow();
                                crate::sanal::mono::find_enum_template(&mono, base_e)
                                    .or_else(|| crate::sanal::mono::find_enum_template(&mono, alt_base_e))
                                    .and_then(|d| {
                                        crate::sanal::mono::find_impl_method(&mono, &d.name, &method_name)
                                            .map(|m| (d, m))
                                    })
                            };
                            if let Some((tpl_decl, tpl_method)) = enum_tpl {
                                let gen_params =
                                    crate::sanal::mono::extract_generic_params_enum(&tpl_decl);
                                let self_ty = Type::Enum(crate::ast::intern_str(
                                    &crate::sanal::mono::mangle_name(&tpl_decl.name, &type_args),
                                ));
                                let placeholder = type_ctx.infer.borrow_mut().register_deferred_call(
                                    crate::sanal::infer::DeferredCall::EnumMethod {
                                        base_enum: tpl_decl.name.clone(),
                                        method_name: method_name.clone(),
                                        type_args: type_args.clone(),
                                    },
                                );
                                resolved_name = placeholder.clone();
                                deferred_target_func = Some(build_substituted_method(
                                    &tpl_decl.name,
                                    &gen_params,
                                    &tpl_method,
                                    &type_args,
                                    self_ty,
                                    placeholder,
                                ));
                                resolved_mangled = true;
                            }
                        } else {
                            let mangled = crate::sanal::mono::monomorphize_enum(
                                type_ctx.mono,
                                base_e,
                                &type_args,
                                type_ctx.enum_map,
                                type_ctx.fn_map,
                                type_ctx.worklist,
                            ).or_else(|| crate::sanal::mono::monomorphize_enum(
                                type_ctx.mono,
                                alt_base_e,
                                &type_args,
                                type_ctx.enum_map,
                                type_ctx.fn_map,
                                type_ctx.worklist,
                            ));

                            if let Some(m) = mangled {
                                let try_fn = format!("{m}_{method_name}");
                                if type_ctx.contains_fn(&try_fn) {
                                    resolved_name = try_fn;
                                    resolved_mangled = true;
                                }
                            }
                        }
                    }
                }
            }

            if !resolved_mangled {
                let mut type_args = Vec::new();
                if !typed_args.is_empty() {
                    let recv_ty = match typed_args[0].ty() {
                        Type::Ref(inner) | Type::MutRef(inner) => *inner,
                        other => other,
                    };
                    if let Type::Vec(inner) = recv_ty {
                        type_args.push(*inner);
                    }
                }
                if type_args.is_empty() && !typed_args.is_empty() {
                    let recv_ty = match typed_args[0].ty() {
                        Type::Ref(inner) | Type::MutRef(inner) => *inner,
                        other => other,
                    };
                    if let Type::Obj(obj_name) = recv_ty {
                        let name_str = obj_name.to_string();
                        if name_str.contains("Vec") && typed_args.len() >= 2 {
                            let elem_ty = typed_args[1].ty();
                            if !matches!(elem_ty, Type::Generic(_)) {
                                type_args.push(elem_ty);
                            }
                        } else if let Some((_, mangled_args)) = crate::sanal::mono::lookup_mangled(&name_str) {
                            type_args.extend(mangled_args);
                        } else if let Some((_, suffix)) = name_str.rsplit_once('_') {
                            if type_ctx.contains_struct(suffix) || type_ctx.contains_enum(suffix) {
                                type_args.push(Type::Obj(crate::ast::intern_str(suffix)));
                            }
                        }
                    }
                }
                if type_args.is_empty() {
                    let is_struct_tpl_static = {
                        let mono = type_ctx.mono.borrow();
                        crate::sanal::mono::find_struct_template(&mono, &base_struct)
                            .and_then(|d| {
                                crate::sanal::mono::find_impl_method(&mono, &d.name, &method_name)
                                    .map(|m| (d, m))
                            })
                    };
                    if let Some((tpl_decl, tpl_method)) = is_struct_tpl_static {
                        let gen_params = crate::sanal::mono::extract_generic_params_struct(
                            &tpl_decl,
                            type_ctx.mono,
                        );
                        if !gen_params.is_empty() {
                            let (p_env, mut p_tys) = type_ctx.infer.borrow_mut().instantiate_params(
                                &gen_params,
                                span,
                                &tpl_decl.name,
                            );
                            let self_obj = if tpl_decl.name == "std_vec_Vec" {
                                Type::Vec(crate::ast::intern_type(p_tys[0]))
                            } else {
                                Type::Obj(crate::ast::intern_str(&crate::sanal::mono::mangle_name(
                                    &tpl_decl.name,
                                    &p_tys,
                                )))
                            };
                            let mut sub_params = Vec::new();
                            for p in &tpl_method.params {
                                let p_ty = match p.ty {
                                    Type::Unit if p.name == "self" => self_obj,
                                    Type::Ref(inner) if *inner == Type::Unit && p.name == "self" => {
                                        Type::Ref(crate::ast::intern_type(self_obj))
                                    }
                                    Type::MutRef(inner) if *inner == Type::Unit && p.name == "self" => {
                                        Type::MutRef(crate::ast::intern_type(self_obj))
                                    }
                                    other => {
                                        let sub = crate::sanal::mono::substitute_type(other, &p_env);
                                        if let Type::Obj(tn) = sub {
                                            if tn == tpl_decl.name {
                                                self_obj
                                            } else {
                                                sub
                                            }
                                        } else {
                                            sub
                                        }
                                    }
                                };
                                sub_params.push(p_ty);
                            }
                            for (p_ty, arg) in sub_params.iter().zip(typed_args.iter()) {
                                let _ = type_ctx.infer.borrow_mut().unify(*p_ty, arg.ty());
                            }
                            let mut ret_sub = crate::sanal::mono::substitute_type(tpl_method.return_type, &p_env);
                            if let Type::Obj(tn) = ret_sub {
                                let short = tpl_decl.name.rsplit_once('_').map(|(_, s)| s).unwrap_or(&tpl_decl.name);
                                if tn == tpl_decl.name || tn == short {
                                    ret_sub = self_obj;
                                }
                            }
                            if let Some(exp) = type_ctx.current_expected_type {
                                let _ = type_ctx.infer.borrow_mut().unify(exp, ret_sub);
                            }
                            for t in &mut p_tys {
                                *t = type_ctx.infer.borrow_mut().resolve(*t);
                            }
                            type_args = p_tys;
                        }
                    }
                }
                if type_args.is_empty() {
                    let actual_args = if !typed_args.is_empty()
                        && matches!(
                            typed_args[0].ty(),
                            Type::Obj(_) | Type::Enum(_) | Type::Ref(_) | Type::MutRef(_)
                        )
                    {
                        &typed_args[1..]
                    } else {
                        &typed_args[..]
                    };
                    for a in actual_args {
                        let mut t = a.ty();
                        if let Type::Array(elem_ty, _) | Type::Slice(elem_ty) = t {
                            t = *elem_ty;
                        }
                        if !matches!(t, Type::Unit) && !type_args.contains(&t) {
                            type_args.push(t);
                        }
                    }
                }
                for t in &mut type_args {
                    *t = type_ctx.infer.borrow_mut().resolve(*t);
                }
                let direct_method = format!("{base_struct}_{method_name}");
                let clean_base = base_struct.strip_prefix("std_core_")
                    .or_else(|| base_struct.strip_prefix("std_vec_"))
                    .or_else(|| base_struct.strip_prefix("std_string_"))
                    .or_else(|| base_struct.strip_prefix("std_fs_"))
                    .unwrap_or(&base_struct);

                let is_generic_template = type_ctx.get_fn(&direct_method).map(|f| {
                    f.params.iter().any(|p| matches!(p.ty, Type::Generic(_))) || matches!(f.return_type, Type::Generic(_))
                }).unwrap_or(false)
                    || type_ctx.mono.borrow().struct_templates.contains_key(&base_struct)
                    || type_ctx.mono.borrow().struct_templates.contains_key(clean_base)
                    || type_ctx.mono.borrow().enum_templates.contains_key(&base_struct)
                    || type_ctx.mono.borrow().enum_templates.contains_key(clean_base);

                if !typed_args.is_empty() {
                    let arg_ty = match typed_args[0].ty() {
                        Type::Ref(inner) | Type::MutRef(inner) => *inner,
                        other => other,
                    };
                    if let Type::Enum(mangled_enum) = arg_ty {
                        let try_fn = format!("{mangled_enum}_{method_name}");
                        if type_ctx.contains_fn(&try_fn) {
                            resolved_name = try_fn;
                        }
                    }
                }

                if resolved_name == name && !type_args.is_empty() {
                    let has_infer = type_args.iter().any(|t| {
                        crate::sanal::compat::type_contains_infer(t)
                            || crate::sanal::compat::type_contains_generic(t)
                    });
                    if has_infer {
                        if base_struct == "std_vec_Vec" && method_name == "new" {
                            resolved_name = "std_vec_Vec_new".to_string();
                        } else {
                            let tpl_opt = {
                                let mono = type_ctx.mono.borrow();
                                crate::sanal::mono::find_struct_template(&mono, &base_struct)
                                    .and_then(|d| {
                                        crate::sanal::mono::find_impl_method(&mono, &d.name, &method_name)
                                            .map(|m| (d, m))
                                    })
                            };
                            if let Some((tpl_decl, tpl_method)) = tpl_opt {
                                let gen_params = crate::sanal::mono::extract_generic_params_struct(
                                    &tpl_decl,
                                    type_ctx.mono,
                                );
                                let self_obj = if tpl_decl.name == "std_vec_Vec" {
                                    Type::Vec(crate::ast::intern_type(type_args[0]))
                                } else {
                                    Type::Obj(crate::ast::intern_str(
                                        &crate::sanal::mono::mangle_name(&tpl_decl.name, &type_args),
                                    ))
                                };
                                let placeholder = type_ctx.infer.borrow_mut().register_deferred_call(
                                    crate::sanal::infer::DeferredCall::StructMethod {
                                        base_struct: tpl_decl.name.clone(),
                                        method_name: method_name.clone(),
                                        type_args: type_args.clone(),
                                    },
                                );
                                resolved_name = placeholder.clone();
                                deferred_target_func = Some(build_substituted_method(
                                    &tpl_decl.name,
                                    &gen_params,
                                    &tpl_method,
                                    &type_args,
                                    self_obj,
                                    placeholder,
                                ));
                            }
                        }
                    } else {
                        let lookup_base = base_struct.clone();
                        if let Some(mangled_struct) = crate::sanal::mono::monomorphize_struct(
                            type_ctx.mono,
                            &lookup_base,
                            &type_args,
                            type_ctx.struct_map,
                            type_ctx.enum_map,
                            type_ctx.fn_map,
                            type_ctx.worklist,
                        ) {
                            let mangled_fn = format!("{mangled_struct}_{method_name}");
                            resolved_name = mangled_fn;
                        } else if !is_generic_template && type_ctx.contains_fn(&direct_method) {
                            resolved_name = direct_method;
                        }
                    }
                } else if resolved_name == name && !is_generic_template && type_ctx.contains_fn(&direct_method) {
                    resolved_name = direct_method;
                }
            }
        }
    }

    // 3. Fallback to direct fn_map lookup if not already resolved to a method
    if resolved_name == name && !type_ctx.extern_signatures.contains_key(name) && !type_ctx.extern_fn_names.contains(name) {
        if let Some(target_func) = type_ctx.get_fn(name) {
            resolved_name = target_func.name;
        }
    }

    // 4. Monomorphize standalone generic functions (and generic methods on non-generic types)
    let needs_fn_mono = deferred_target_func.is_none()
        && type_ctx.get_fn(&resolved_name).is_some_and(|f| {
            f.params
                .iter()
                .any(|p| crate::sanal::compat::type_contains_generic(&p.ty))
                || crate::sanal::compat::type_contains_generic(&f.return_type)
        });
    if needs_fn_mono {
        let arg_types: Vec<Type> = typed_args
            .iter()
            .map(|a| type_ctx.infer.borrow_mut().resolve(a.ty()))
            .collect();
        let has_infer = arg_types
            .iter()
            .any(crate::sanal::compat::type_contains_infer);
        if has_infer {
            if let Some(tpl_fn) = type_ctx.get_fn(&resolved_name) {
                let mut gen_params = Vec::new();
                for p in &tpl_fn.params {
                    if let Type::Generic(g) = p.ty {
                        let clean = g.trim_start_matches('$').to_string();
                        if !gen_params.contains(&clean) {
                            gen_params.push(clean);
                        }
                    }
                }
                if let Type::Generic(g) = tpl_fn.return_type {
                    let clean = g.trim_start_matches('$').to_string();
                    if !gen_params.contains(&clean) {
                        gen_params.push(clean);
                    }
                }
                let (p_env, _) = type_ctx.infer.borrow_mut().instantiate_params(
                    &gen_params,
                    span,
                    &tpl_fn.name,
                );
                let sub_params: Vec<crate::ast::Param> = tpl_fn
                    .params
                    .iter()
                    .map(|p| crate::ast::Param {
                        name: p.name.clone(),
                        is_mutable: p.is_mutable,
                        ty: crate::sanal::mono::substitute_type(p.ty, &p_env),
                        span: p.span.clone(),
                    })
                    .collect();
                let ret_sub = crate::sanal::mono::substitute_type(tpl_fn.return_type, &p_env);
                for (p, a) in sub_params.iter().zip(arg_types.iter()) {
                    let _ = type_ctx.infer.borrow_mut().unify(p.ty, *a);
                }
                let placeholder = type_ctx.infer.borrow_mut().register_deferred_call(
                    crate::sanal::infer::DeferredCall::GenericFn {
                        base_fn: resolved_name.clone(),
                        type_args: Vec::new(),
                    },
                );
                resolved_name = placeholder.clone();
                deferred_target_func = Some(crate::ast::FuncDecl {
                    name: placeholder,
                    params: sub_params,
                    return_type: ret_sub,
                    where_clause: tpl_fn.where_clause.clone(),
                    body: Vec::new(),
                    is_track_caller: tpl_fn.is_track_caller,
                    vis: tpl_fn.vis,
                    module_path: tpl_fn.module_path.clone(),
                    is_trait_impl: tpl_fn.is_trait_impl,
                });
            }
        } else if let Some(mangled_fn) = crate::sanal::mono::monomorphize_fn(
            type_ctx.mono,
            &resolved_name,
            &arg_types,
            type_ctx.fn_map,
            type_ctx.struct_map,
            type_ctx.enum_map,
            type_ctx.worklist,
        ) {
            resolved_name = mangled_fn;
        }
    }

    (resolved_name, deferred_target_func)
}
