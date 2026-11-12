use crate::ast::*;

fn has_derive(attrs: &[Attribute], trait_name: &str) -> bool {
    attrs
        .iter()
        .any(|a| a.name == "derive" && a.args.iter().any(|arg| arg == trait_name))
}

fn build_eq_fn(target_name: &str, is_enum: bool, module_path: Vec<String>, body: Vec<Expr>, span: &Span) -> FuncDecl {
    let leaked_name: &'static str = Box::leak(target_name.to_string().into_boxed_str());
    let target_ty = if is_enum {
        Type::Enum(leaked_name)
    } else {
        Type::Obj(leaked_name)
    };
    FuncDecl {
        name: "eq".to_string(),
        params: vec![
            Param {
                name: "self".to_string(),
                is_mutable: false,
                ty: Type::Ref(intern_type(Type::Unit)),
                span: span.clone(),
            },
            Param {
                name: "other".to_string(),
                is_mutable: false,
                ty: Type::Ref(intern_type(target_ty)),
                span: span.clone(),
            },
        ],
        return_type: Type::Bool,
        where_clause: None,
        is_track_caller: false,
        vis: Visibility::Pub,
        module_path,
        is_trait_impl: true,
        body,
    }
}

pub fn expand_derives(program: &mut Program) {
    let mut synthesized_impls = Vec::new();

    // 1. Expand Enums with #[derive(Error)], #[derive(PartialEq)], #[derive(Eq)]
    for e in &program.enums {
        if has_derive(&e.attributes, "PartialEq") {
            let e_span = e.span.clone();
            let mut outer_arms = Vec::new();
            for v in &e.variants {
                let v_span = v.span.clone();
                let mut lhs_bindings = Vec::new();
                let mut rhs_bindings = Vec::new();
                for i in 0..v.payload_types.len() {
                    lhs_bindings.push(format!("__lhs_{i}"));
                    rhs_bindings.push(format!("__rhs_{i}"));
                }

                let mut inner_body = Vec::new();
                for i in 0..v.payload_types.len() {
                    let neq = Expr::NotEqual(
                        Box::new(Expr::Ident(lhs_bindings[i].clone(), v_span.clone())),
                        Box::new(Expr::Ident(rhs_bindings[i].clone(), v_span.clone())),
                        v_span.clone(),
                    );
                    inner_body.push(Expr::If(
                        Box::new(neq),
                        Box::new(Expr::Return(
                            Some(Box::new(Expr::Bool(false, v_span.clone()))),
                            v_span.clone(),
                        )),
                        v_span.clone(),
                    ));
                }
                inner_body.push(Expr::Bool(true, v_span.clone()));

                let inner_match = Expr::Match(
                    Box::new(Expr::Ident("other".to_string(), v_span.clone())),
                    vec![
                        MatchArm {
                            variant_name: format!("{}::{}", e.name, v.name),
                            bindings: rhs_bindings,
                            body: inner_body,
                            span: v_span.clone(),
                        },
                        MatchArm {
                            variant_name: "_".to_string(),
                            bindings: Vec::new(),
                            body: vec![Expr::Bool(false, v_span.clone())],
                            span: v_span.clone(),
                        },
                    ],
                    v_span.clone(),
                );

                outer_arms.push(MatchArm {
                    variant_name: format!("{}::{}", e.name, v.name),
                    bindings: lhs_bindings,
                    body: vec![inner_match],
                    span: v_span,
                });
            }

            let eq_body = if outer_arms.is_empty() {
                vec![Expr::Return(
                    Some(Box::new(Expr::Bool(true, e_span.clone()))),
                    e_span.clone(),
                )]
            } else {
                vec![Expr::Return(
                    Some(Box::new(Expr::Match(
                        Box::new(Expr::Ident("self".to_string(), e_span.clone())),
                        outer_arms,
                        e_span.clone(),
                    ))),
                    e_span.clone(),
                )]
            };

            synthesized_impls.push(ImplDecl {
                trait_name: Some("PartialEq".to_string()),
                target_type: e.name.clone(),
                methods: vec![build_eq_fn(&e.name, true, e.module_path.clone(), eq_body, &e_span)],
                where_clause: None,
                span: e_span,
            });
        }
        if has_derive(&e.attributes, "Eq") {
            synthesized_impls.push(ImplDecl {
                trait_name: Some("Eq".to_string()),
                target_type: e.name.clone(),
                methods: Vec::new(),
                where_clause: None,
                span: e.span.clone(),
            });
        }

        let has_derive_error = has_derive(&e.attributes, "Error");

        if has_derive_error {
            let e_span = e.span.clone();
            let mut match_arms = Vec::new();
            for v in &e.variants {
                let err_attr = v.attributes.iter().find(|a| a.name == "error" || a.name == "err");
                let v_err_span = err_attr.map(|a| a.span.clone()).unwrap_or_else(|| v.span.clone());
                let tmpl = if let Some(attr) = err_attr {
                    attr.args.first().cloned().unwrap_or_else(|| v.name.clone())
                } else {
                    v.name.clone()
                };

                let mut bindings = Vec::new();
                for i in 0..v.payload_types.len() {
                    bindings.push(format!("arg{i}"));
                }

                let mut fmt_str = String::new();
                let mut fmt_args = Vec::new();
                let chars: Vec<char> = tmpl.chars().collect();
                let mut ci = 0;
                while ci < chars.len() {
                    if chars[ci] == '{' {
                        if let Some(close_rel) = chars[ci + 1..].iter().position(|&c| c == '}') {
                            let inner: String = chars[ci + 1..ci + 1 + close_rel].iter().collect();
                            if !inner.is_empty() && inner.chars().all(|c| c.is_ascii_digit()) {
                                if let Ok(idx) = inner.parse::<usize>() {
                                    if idx < v.payload_types.len() {
                                        fmt_str.push_str("{}");
                                        fmt_args.push(Expr::Ident(format!("arg{idx}"), v_err_span.clone()));
                                    } else {
                                        fmt_str.push_str(&format!("<oob:{idx}>"));
                                    }
                                    ci += close_rel + 2;
                                    continue;
                                }
                            }
                        }
                    }
                    fmt_str.push(chars[ci]);
                    ci += 1;
                }

                let arm_body_expr = if fmt_args.is_empty() {
                    let s = if fmt_str.is_empty() { v.name.clone() } else { fmt_str };
                    Expr::String(s, v_err_span.clone())
                } else {
                    let mut all_args = Vec::with_capacity(1 + fmt_args.len());
                    all_args.push(Expr::String(format!("\"{fmt_str}\""), v_err_span.clone()));
                    all_args.extend(fmt_args);
                    Expr::MacroCall("format".to_string(), all_args, v_err_span.clone())
                };

                match_arms.push(MatchArm {
                    variant_name: format!("{}::{}", e.name, v.name),
                    bindings,
                    body: vec![arm_body_expr],
                    span: v_err_span,
                });
            }

            let to_string_body = Expr::Match(
                Box::new(Expr::Ident("self".to_string(), e_span.clone())),
                match_arms,
                e_span.clone(),
            );

            let to_string_fn = FuncDecl {
                name: "to_string".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: e_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: e.module_path.clone(),
                is_trait_impl: false,
                body: vec![to_string_body],
            };

            let fmt_fn = FuncDecl {
                name: "fmt".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: e_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: e.module_path.clone(),
                is_trait_impl: false,
                body: vec![Expr::Call(".to_string".to_string(), vec![Expr::Ident("self".to_string(), e_span.clone())], e_span.clone())],
            };

            synthesized_impls.push(ImplDecl {
                trait_name: None,
                target_type: e.name.clone(),
                methods: vec![to_string_fn, fmt_fn],
                where_clause: None,
                span: e_span,
            });
        }
    }

    // 2. Expand Structs (obj) with #[derive(Error)], #[derive(PartialEq)], #[derive(Eq)]
    for s in &program.structs {
        if has_derive(&s.attributes, "PartialEq") {
            let s_span = s.span.clone();
            let mut body_stmts = Vec::new();
            for field in &s.fields {
                let f_span = field.span.clone();
                let lhs = Expr::FieldAccess(
                    Box::new(Expr::Ident("self".to_string(), f_span.clone())),
                    field.name.clone(),
                    f_span.clone(),
                );
                let rhs = Expr::FieldAccess(
                    Box::new(Expr::Ident("other".to_string(), f_span.clone())),
                    field.name.clone(),
                    f_span.clone(),
                );
                let neq = Expr::NotEqual(Box::new(lhs), Box::new(rhs), f_span.clone());
                body_stmts.push(Expr::If(
                    Box::new(neq),
                    Box::new(Expr::Return(
                        Some(Box::new(Expr::Bool(false, f_span.clone()))),
                        f_span.clone(),
                    )),
                    f_span,
                ));
            }
            body_stmts.push(Expr::Return(
                Some(Box::new(Expr::Bool(true, s_span.clone()))),
                s_span.clone(),
            ));

            let eq_fn = build_eq_fn(&s.name, false, s.module_path.clone(), body_stmts, &s_span);

            synthesized_impls.push(ImplDecl {
                trait_name: Some("PartialEq".to_string()),
                target_type: s.name.clone(),
                methods: vec![eq_fn],
                where_clause: None,
                span: s_span,
            });
        }

        if has_derive(&s.attributes, "Eq") {
            synthesized_impls.push(ImplDecl {
                trait_name: Some("Eq".to_string()),
                target_type: s.name.clone(),
                methods: Vec::new(),
                where_clause: None,
                span: s.span.clone(),
            });
        }

        let has_derive_error = has_derive(&s.attributes, "Error");

        if has_derive_error {
            let top_err_attr = s.attributes.iter().find(|a| a.name == "error" || a.name == "err");
            let s_err_span = top_err_attr.map(|a| a.span.clone()).unwrap_or_else(|| s.span.clone());
            let mut fmt_str = String::new();
            let mut fmt_args = Vec::new();

            if let Some(attr) = top_err_attr {
                let mut curr_tmpl = attr.args.first().cloned().unwrap_or_else(|| s.name.clone());

                for field in &s.fields {
                    let placeholder = format!("{{{}}}", field.name);
                    let field_attr = field.attributes.iter().find(|a| a.name == "error" || a.name == "err");

                    if curr_tmpl.contains(&placeholder) {
                        let parts: Vec<&str> = curr_tmpl.splitn(2, &placeholder).collect();
                        fmt_str.push_str(parts[0]);
                        if let Some(f_attr) = field_attr {
                            if let Some(f_tmpl) = f_attr.args.first() {
                                fmt_str.push_str(f_tmpl);
                            }
                        }
                        fmt_str.push_str("{}");
                        let field_access = Expr::FieldAccess(
                            Box::new(Expr::Ident("self".to_string(), field.span.clone())),
                            field.name.clone(),
                            field.span.clone(),
                        );
                        fmt_args.push(field_access);
                        curr_tmpl = parts.get(1).unwrap_or(&"").to_string();
                    }
                }
                fmt_str.push_str(&curr_tmpl);
            } else {
                for (idx, field) in s.fields.iter().enumerate() {
                    let field_attr = field.attributes.iter().find(|a| a.name == "error" || a.name == "err");
                    if let Some(f_attr) = field_attr {
                        if let Some(f_tmpl) = f_attr.args.first() {
                            if idx > 0 {
                                fmt_str.push_str(": ");
                            }
                            fmt_str.push_str(f_tmpl);
                        }
                    }
                }
            }

            let to_string_body = if fmt_args.is_empty() {
                let st = if fmt_str.is_empty() { s.name.clone() } else { fmt_str };
                Expr::String(st, s_err_span.clone())
            } else {
                let mut all_args = Vec::with_capacity(1 + fmt_args.len());
                all_args.push(Expr::String(format!("\"{fmt_str}\""), s_err_span.clone()));
                all_args.extend(fmt_args);
                Expr::MacroCall("format".to_string(), all_args, s_err_span.clone())
            };

            let to_string_fn = FuncDecl {
                name: "to_string".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: s_err_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: s.module_path.clone(),
                is_trait_impl: false,
                body: vec![to_string_body],
            };

            let fmt_fn = FuncDecl {
                name: "fmt".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: s_err_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: s.module_path.clone(),
                is_trait_impl: false,
                body: vec![Expr::Call(".to_string".to_string(), vec![Expr::Ident("self".to_string(), s_err_span.clone())], s_err_span.clone())],
            };

            synthesized_impls.push(ImplDecl {
                trait_name: None,
                target_type: s.name.clone(),
                methods: vec![to_string_fn, fmt_fn],
                where_clause: None,
                span: s_err_span,
            });
        }
    }

    program.impls.extend(synthesized_impls);
}
