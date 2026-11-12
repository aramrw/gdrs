//! sanal/calls/helpers.rs
//! Helper routines for substituted method declarations.

use crate::ast::Type;

pub fn build_substituted_method(
    tpl_name: &str,
    gen_params: &[String],
    tpl_method: &crate::ast::FuncDecl,
    type_args: &[Type],
    self_ty: Type,
    placeholder_name: String,
) -> crate::ast::FuncDecl {
    let mut p_env = std::collections::HashMap::new();
    for (idx, p) in gen_params.iter().enumerate() {
        if let Some(&arg_t) = type_args.get(idx) {
            p_env.insert(p.clone(), arg_t);
            p_env.insert(format!("${p}"), arg_t);
        }
    }
    let short_decl = tpl_name.rsplit_once('_').map(|(_, s)| s).unwrap_or(tpl_name);
    let replace_self_obj = |sub: Type| -> Type {
        if let Type::Obj(tn) = sub {
            if tn == tpl_name || tn == short_decl {
                return self_ty;
            }
        }
        sub
    };
    let sub_params = tpl_method
        .params
        .iter()
        .map(|p| {
            let new_ty = if p.name == "self" {
                match p.ty {
                    Type::Unit => self_ty,
                    Type::Ref(inner) if *inner == Type::Unit => {
                        Type::Ref(crate::ast::intern_type(self_ty))
                    }
                    Type::MutRef(inner) if *inner == Type::Unit => {
                        Type::MutRef(crate::ast::intern_type(self_ty))
                    }
                    other => replace_self_obj(crate::sanal::mono::substitute_type(other, &p_env)),
                }
            } else {
                replace_self_obj(crate::sanal::mono::substitute_type(p.ty, &p_env))
            };
            crate::ast::Param {
                name: p.name.clone(),
                is_mutable: p.is_mutable,
                ty: new_ty,
                span: p.span.clone(),
            }
        })
        .collect();

    let mut ret_sub = replace_self_obj(crate::sanal::mono::substitute_type(
        tpl_method.return_type,
        &p_env,
    ));
    if tpl_name == "std_vec_Vec" && tpl_method.name == "from_slice" {
        if let Some(&elem) = type_args.first() {
            ret_sub = Type::Vec(crate::ast::intern_type(elem));
        }
    }
    crate::ast::FuncDecl {
        name: placeholder_name,
        params: sub_params,
        return_type: ret_sub,
        where_clause: None,
        body: Vec::new(),
        is_track_caller: tpl_method.is_track_caller,
        vis: tpl_method.vis,
        module_path: tpl_method.module_path.clone(),
        is_trait_impl: tpl_method.is_trait_impl,
    }
}
