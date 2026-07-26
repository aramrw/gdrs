use crate::ast::*;

pub fn expand_derives(program: &mut Program) {
    let dummy_span = 0..0;
    let mut synthesized_impls = Vec::new();

    // 1. Expand Enums with #[derive(Error)]
    for e in &program.enums {
        let has_derive_error = e.attributes.iter().any(|a| {
            a.name == "derive" && a.args.iter().any(|arg| arg == "Error")
        });

        if has_derive_error {
            let mut match_arms = Vec::new();
            for v in &e.variants {
                let err_attr = v.attributes.iter().find(|a| a.name == "error" || a.name == "err");
                let tmpl = if let Some(attr) = err_attr {
                    attr.args.first().cloned().unwrap_or_else(|| v.name.clone())
                } else {
                    v.name.clone()
                };

                let mut bindings = Vec::new();
                let mut expr_parts = Vec::new();

                let mut curr_tmpl = tmpl;
                for i in 0..v.payload_types.len() {
                    let binding = format!("arg{i}");
                    bindings.push(binding.clone());
                    let placeholder = format!("{{{i}}}");
                    if curr_tmpl.contains(&placeholder) {
                        let parts: Vec<&str> = curr_tmpl.splitn(2, &placeholder).collect();
                        if !parts[0].is_empty() {
                            expr_parts.push(Expr::String(parts[0].to_string(), dummy_span.clone()));
                        }
                        expr_parts.push(Expr::Ident(binding, dummy_span.clone()));
                        curr_tmpl = parts.get(1).unwrap_or(&"").to_string();
                    }
                }
                if !curr_tmpl.is_empty() {
                    expr_parts.push(Expr::String(curr_tmpl, dummy_span.clone()));
                }

                let arm_body_expr = if expr_parts.is_empty() {
                    Expr::String(v.name.clone(), dummy_span.clone())
                } else if expr_parts.len() == 1 {
                    expr_parts.remove(0)
                } else {
                    Expr::MacroCall("format".to_string(), expr_parts, dummy_span.clone())
                };

                match_arms.push(MatchArm {
                    variant_name: format!("{}::{}", e.name, v.name),
                    bindings,
                    body: vec![arm_body_expr],
                    span: dummy_span.clone(),
                });
            }

            let to_string_body = Expr::Match(
                Box::new(Expr::Ident("self".to_string(), dummy_span.clone())),
                match_arms,
                dummy_span.clone(),
            );

            let to_string_fn = FuncDecl {
                name: "to_string".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: dummy_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                body: vec![to_string_body],
            };

            let fmt_fn = FuncDecl {
                name: "fmt".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: dummy_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                body: vec![Expr::Call("to_string".to_string(), vec![Expr::Ident("self".to_string(), dummy_span.clone())], dummy_span.clone())],
            };

            synthesized_impls.push(ImplDecl {
                trait_name: None,
                target_type: e.name.clone(),
                methods: vec![to_string_fn, fmt_fn],
                where_clause: None,
                span: dummy_span.clone(),
            });
        }
    }

    // 2. Expand Structs (obj) with #[derive(Error)]
    for s in &program.structs {
        let has_derive_error = s.attributes.iter().any(|a| {
            a.name == "derive" && a.args.iter().any(|arg| arg == "Error")
        });

        if has_derive_error {
            let top_err_attr = s.attributes.iter().find(|a| a.name == "error" || a.name == "err");
            let mut expr_parts = Vec::new();

            if let Some(attr) = top_err_attr {
                let tmpl = attr.args.first().cloned().unwrap_or_else(|| s.name.clone());
                let mut curr_tmpl = tmpl;

                for field in &s.fields {
                    let placeholder = format!("{{{}}}", field.name);
                    let field_attr = field.attributes.iter().find(|a| a.name == "error" || a.name == "err");

                    if curr_tmpl.contains(&placeholder) {
                        let parts: Vec<&str> = curr_tmpl.splitn(2, &placeholder).collect();
                        if !parts[0].is_empty() {
                            expr_parts.push(Expr::String(parts[0].to_string(), dummy_span.clone()));
                        }
                        if let Some(f_attr) = field_attr {
                            if let Some(f_tmpl) = f_attr.args.first() {
                                expr_parts.push(Expr::String(f_tmpl.clone(), dummy_span.clone()));
                            }
                        }
                        let field_access = Expr::FieldAccess(Box::new(Expr::Ident("self".to_string(), dummy_span.clone())), field.name.clone(), dummy_span.clone());
                        expr_parts.push(field_access);
                        curr_tmpl = parts.get(1).unwrap_or(&"").to_string();
                    }
                }
                if !curr_tmpl.is_empty() {
                    expr_parts.push(Expr::String(curr_tmpl, dummy_span.clone()));
                }
            } else {
                for (idx, field) in s.fields.iter().enumerate() {
                    let field_attr = field.attributes.iter().find(|a| a.name == "error" || a.name == "err");
                    if let Some(f_attr) = field_attr {
                        if let Some(f_tmpl) = f_attr.args.first() {
                            if idx > 0 {
                                expr_parts.push(Expr::String(": ".to_string(), dummy_span.clone()));
                            }
                            expr_parts.push(Expr::String(f_tmpl.clone(), dummy_span.clone()));
                        }
                    }
                }
            }

            let to_string_body = if expr_parts.is_empty() {
                Expr::String(s.name.clone(), dummy_span.clone())
            } else if expr_parts.len() == 1 {
                expr_parts.remove(0)
            } else {
                Expr::MacroCall("format".to_string(), expr_parts, dummy_span.clone())
            };

            let to_string_fn = FuncDecl {
                name: "to_string".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: dummy_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                body: vec![to_string_body],
            };

            let fmt_fn = FuncDecl {
                name: "fmt".to_string(),
                params: vec![Param {
                    name: "self".to_string(),
                    is_mutable: false,
                    ty: Type::Unit,
                    span: dummy_span.clone(),
                }],
                return_type: Type::Str,
                where_clause: None,
                body: vec![Expr::Call("to_string".to_string(), vec![Expr::Ident("self".to_string(), dummy_span.clone())], dummy_span.clone())],
            };

            synthesized_impls.push(ImplDecl {
                trait_name: None,
                target_type: s.name.clone(),
                methods: vec![to_string_fn, fmt_fn],
                where_clause: None,
                span: dummy_span.clone(),
            });
        }
    }

    program.impls.extend(synthesized_impls);
}
