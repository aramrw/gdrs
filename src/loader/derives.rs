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
                let mut fmt_str = String::new();
                let mut fmt_args = Vec::new();

                let mut curr_tmpl = tmpl;
                for i in 0..v.payload_types.len() {
                    let binding = format!("arg{i}");
                    bindings.push(binding.clone());
                    let placeholder = format!("{{{i}}}");
                    if curr_tmpl.contains(&placeholder) {
                        let parts: Vec<&str> = curr_tmpl.splitn(2, &placeholder).collect();
                        fmt_str.push_str(parts[0]);
                        fmt_str.push_str("{}");
                        fmt_args.push(Expr::Ident(binding, dummy_span.clone()));
                        curr_tmpl = parts.get(1).unwrap_or(&"").to_string();
                    }
                }
                fmt_str.push_str(&curr_tmpl);

                let arm_body_expr = if fmt_args.is_empty() {
                    let s = if fmt_str.is_empty() { v.name.clone() } else { fmt_str };
                    Expr::String(s, dummy_span.clone())
                } else {
                    let mut all_args = Vec::with_capacity(1 + fmt_args.len());
                    all_args.push(Expr::String(format!("\"{fmt_str}\""), dummy_span.clone()));
                    all_args.extend(fmt_args);
                    Expr::MacroCall("format".to_string(), all_args, dummy_span.clone())
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
                body: vec![Expr::Call(".to_string".to_string(), vec![Expr::Ident("self".to_string(), dummy_span.clone())], dummy_span.clone())],
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
                            Box::new(Expr::Ident("self".to_string(), dummy_span.clone())),
                            field.name.clone(),
                            dummy_span.clone(),
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
                Expr::String(st, dummy_span.clone())
            } else {
                let mut all_args = Vec::with_capacity(1 + fmt_args.len());
                all_args.push(Expr::String(format!("\"{fmt_str}\""), dummy_span.clone()));
                all_args.extend(fmt_args);
                Expr::MacroCall("format".to_string(), all_args, dummy_span.clone())
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
                body: vec![Expr::Call(".to_string".to_string(), vec![Expr::Ident("self".to_string(), dummy_span.clone())], dummy_span.clone())],
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
