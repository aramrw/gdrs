//! loader/mod.rs
//! Handles multi-file module resolution and parsing for GDRS without mod.gdrs files.

use crate::ast::*;
use crate::parser::parser;
use chumsky::Parser;
use logos::Logos;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

pub fn load_program(entry_file: &Path) -> Result<Program, String> {
    let mut loaded_files = HashSet::new();
    let mut merged_program = Program {
        mods: Vec::new(),
        uses: Vec::new(),
        traits: Vec::new(),
        trait_aliases: Vec::new(),
        externs: Vec::new(),
        structs: Vec::new(),
        enums: Vec::new(),
        impls: Vec::new(),
        functions: Vec::new(),
    };

    let base_dir = entry_file
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();

    let std_core_path = Path::new("std/core.gdrs");
    if std_core_path.exists() {
        let _ = load_file_recursive(
            std_core_path,
            Path::new("."),
            &["std".to_string(), "core".to_string()],
            &mut loaded_files,
            &mut merged_program,
        );
    }

    let std_time_path = Path::new("std/time.gdrs");
    if std_time_path.exists() {
        let _ = load_file_recursive(
            std_time_path,
            Path::new("."),
            &["std".to_string(), "time".to_string()],
            &mut loaded_files,
            &mut merged_program,
        );
    }

    load_file_recursive(entry_file, &base_dir, &[], &mut loaded_files, &mut merged_program)?;

    expand_derives(&mut merged_program);

    Ok(merged_program)
}

pub fn inject_indentation(tokens: Vec<(Token, Span)>) -> Vec<(Token, Span)> {
    let mut processed = Vec::new();
    let mut indent_stack = vec![0];

    let mut iter = tokens.into_iter().peekable();

    while let Some((token, span)) = iter.next() {
        if let Token::NewlineWithIndent(spaces) = token {
            if matches!(iter.peek(), Some((Token::NewlineWithIndent(_), _)) | None) {
                continue;
            }

            let current_indent = *indent_stack.last().unwrap();

            if let Some((last_tok, _)) = processed.last() {
                if !matches!(last_tok, Token::Newline | Token::Indent | Token::Dedent) {
                    processed.push((Token::Newline, span.clone()));
                }
            }

            if spaces > current_indent {
                indent_stack.push(spaces);
                processed.push((Token::Indent, span.clone()));
            } else if spaces < current_indent {
                while *indent_stack.last().unwrap() > spaces {
                    indent_stack.pop();
                    processed.push((Token::Dedent, span.clone()));
                }
            }
        } else {
            processed.push((token, span));
        }
    }

    let eof_span = processed.last().map(|(_, s)| s.clone()).unwrap_or(0..0);
    while indent_stack.len() > 1 {
        indent_stack.pop();
        processed.push((Token::Dedent, eof_span.clone()));
    }

    processed
}

fn load_file_recursive(
    file_path: &Path,
    base_dir: &Path,
    mod_prefix: &[String],
    loaded_files: &mut HashSet<PathBuf>,
    merged_program: &mut Program,
) -> Result<(), String> {
    let canonical = fs::canonicalize(file_path)
        .map_err(|e| format!("Failed to find module file '{}': {}", file_path.display(), e))?;

    if loaded_files.contains(&canonical) {
        return Ok(());
    }
    loaded_files.insert(canonical.clone());

    let source = fs::read_to_string(&canonical)
        .map_err(|e| format!("Failed to read file '{}': {}", canonical.display(), e))?;

    let raw_tokens: Vec<(Token, Span)> = Token::lexer(&source)
        .spanned()
        .filter_map(|(res, span)| match res {
            Ok(token) => Some((token, span)),
            Err(_) => None,
        })
        .collect();

    let processed_tokens = inject_indentation(raw_tokens);

    let eof_span = source.len()..source.len();
    let stream = chumsky::Stream::from_iter(eof_span, processed_tokens.into_iter());

    let program = parser()
        .parse(stream)
        .map_err(|errs| format!("Parse error in '{}': {:?}", canonical.display(), errs))?;

    let prefix_str = if mod_prefix.is_empty() {
        "".to_string()
    } else {
        format!("{}_", mod_prefix.join("_"))
    };

    let mut local_types = HashSet::new();
    for s in &program.structs {
        local_types.insert(s.name.clone());
    }
    for e in &program.enums {
        local_types.insert(e.name.clone());
    }

    // Process `use` declarations in this file
    let mut use_aliases = HashMap::new();
    for u in &program.uses {
        if u.path.is_empty() {
            continue;
        }

        let mut found_file: Option<(PathBuf, Vec<String>, usize)> = None;
        for i in (1..=u.path.len()).rev() {
            let mod_parts = &u.path[0..i];
            let rel_path = format!("{}.gdrs", mod_parts.join("/"));

            let candidates = vec![
                base_dir.join(&rel_path),
                Path::new(".").join(&rel_path),
                Path::new("std").join(format!("{}.gdrs", mod_parts[1..].join("/"))),
                Path::new("std").join(&rel_path),
            ];

            for cand in candidates {
                if cand.exists() {
                    let mut prefix = mod_parts.to_vec();
                    if cand.to_string_lossy().contains("std/") && prefix.first().map(|s| s.as_str()) != Some("std") {
                        prefix.insert(0, "std".to_string());
                    }
                    found_file = Some((cand, prefix, i));
                    break;
                }
            }
            if found_file.is_some() {
                break;
            }
        }

        if let Some((sub_file, sub_prefix, matched_len)) = found_file {
            let sub_base = sub_file.parent().unwrap_or_else(|| Path::new("."));
            load_file_recursive(&sub_file, sub_base, &sub_prefix, loaded_files, merged_program)?;

            let sub_prefix_str = format!("{}_", sub_prefix.join("_"));
            if matched_len < u.path.len() {
                let sym = &u.path[matched_len];
                let alias = u.alias.as_ref().unwrap_or(sym);
                use_aliases.insert(alias.clone(), format!("{}{}", sub_prefix_str, sym));
            } else {
                let sym = u.path.last().unwrap();
                let alias = u.alias.as_ref().unwrap_or(sym);
                use_aliases.insert(alias.clone(), sub_prefix_str.trim_end_matches('_').to_string());
            }
        }
    }

    for mut t in program.traits {
        if !prefix_str.is_empty() {
            t.name = format!("{}{}", prefix_str, t.name);
        }
        merged_program.traits.push(t);
    }

    for mut ta in program.trait_aliases {
        if !prefix_str.is_empty() {
            ta.name = format!("{}{}", prefix_str, ta.name);
        }
        merged_program.trait_aliases.push(ta);
    }

    merged_program.externs.extend(program.externs);

    // Mangle and push structs
    for mut s in program.structs {
        if !prefix_str.is_empty() {
            s.name = format!("{}{}", prefix_str, s.name);
            for field in &mut s.fields {
                rewrite_type(&mut field.ty, &local_types, &use_aliases, &prefix_str);
            }
        }
        merged_program.structs.push(s);
    }

    // Mangle and push enums
    for mut e in program.enums {
        if !prefix_str.is_empty() {
            e.name = format!("{}{}", prefix_str, e.name);
            for v in &mut e.variants {
                for p_ty in &mut v.payload_types {
                    rewrite_type(p_ty, &local_types, &use_aliases, &prefix_str);
                }
            }
        }
        merged_program.enums.push(e);
    }

    // Mangle and push impls
    for mut i in program.impls {
        if use_aliases.contains_key(&i.target_type) {
            i.target_type = use_aliases[&i.target_type].clone();
        } else if !prefix_str.is_empty() && local_types.contains(&i.target_type) {
            i.target_type = format!("{}{}", prefix_str, i.target_type);
        }

        if let Some(t_name) = &mut i.trait_name {
            if use_aliases.contains_key(t_name) {
                *t_name = use_aliases[t_name].clone();
            } else if !prefix_str.is_empty() && local_types.contains(t_name) {
                *t_name = format!("{}{}", prefix_str, t_name);
            }
        }

        for method in &mut i.methods {
            rewrite_type(&mut method.return_type, &local_types, &use_aliases, &prefix_str);
            for p in &mut method.params {
                rewrite_type(&mut p.ty, &local_types, &use_aliases, &prefix_str);
            }
            for expr in &mut method.body {
                rewrite_expr(expr, &local_types, &use_aliases, &prefix_str);
            }
        }
        merged_program.impls.push(i);
    }

    // Mangle and push functions
    for mut f in program.functions {
        if !prefix_str.is_empty() && f.name != "main" {
            f.name = format!("{}{}", prefix_str, f.name);
        }
        rewrite_type(&mut f.return_type, &local_types, &use_aliases, &prefix_str);
        for p in &mut f.params {
            rewrite_type(&mut p.ty, &local_types, &use_aliases, &prefix_str);
        }
        for expr in &mut f.body {
            rewrite_expr(expr, &local_types, &use_aliases, &prefix_str);
        }
        merged_program.functions.push(f);
    }

    // Process sub-modules declared via `mod path::to::sub`
    for m in program.mods {
        let sub_prefix = m.path.clone();
        let rel_path = format!("{}.gdrs", m.path.join("/"));
        let sub_file = base_dir.join(rel_path);

        load_file_recursive(&sub_file, base_dir, &sub_prefix, loaded_files, merged_program)?;
    }

    Ok(())
}

fn resolve_name_alias(
    name: &str,
    aliases: &HashMap<String, String>,
    local_types: &HashSet<String>,
    prefix: &str,
) -> Option<String> {
    if aliases.contains_key(name) {
        return Some(aliases[name].clone());
    }
    if let Some((mod_part, item_part)) = name.split_once("::") {
        if aliases.contains_key(mod_part) {
            return Some(format!("{}_{}", aliases[mod_part], item_part));
        }
        if local_types.contains(mod_part) {
            return Some(format!("{}{}_{}", prefix, mod_part, item_part));
        }
    }
    if local_types.contains(name) {
        return Some(format!("{}{}", prefix, name));
    }
    None
}

fn rewrite_type(
    ty: &mut Type,
    local_types: &HashSet<String>,
    aliases: &HashMap<String, String>,
    prefix: &str,
) {
    match ty {
        Type::Obj(name) => {
            if let Some(r) = resolve_name_alias(&**name, aliases, local_types, prefix) {
                *ty = Type::Obj(intern_str(&r));
            }
        }
        Type::Enum(name) => {
            if let Some(r) = resolve_name_alias(&**name, aliases, local_types, prefix) {
                *ty = Type::Enum(intern_str(&r));
            }
        }
        Type::Array(elem_ty, size) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Array(intern_type(inner), *size);
        }
        Type::Slice(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Slice(intern_type(inner));
        }
        Type::Vec(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Vec(intern_type(inner));
        }
        _ => {}
    }
}

fn rewrite_expr(
    expr: &mut Expr,
    local_types: &HashSet<String>,
    aliases: &HashMap<String, String>,
    prefix: &str,
) {
    match expr {
        Expr::Ident(name, _) => {
            if let Some(r) = resolve_name_alias(name, aliases, local_types, prefix) {
                *name = r;
            }
        }
        Expr::ObjInit(name, fields, _) => {
            if let Some(r) = resolve_name_alias(name, aliases, local_types, prefix) {
                *name = r;
            }
            for (_, f_expr) in fields {
                rewrite_expr(f_expr, local_types, aliases, prefix);
            }
        }
        Expr::Call(name, args, _) => {
            if let Some(r) = resolve_name_alias(name, aliases, local_types, prefix) {
                *name = r;
            } else if name.contains('.') {
                if let Some((target, method)) = name.split_once('.') {
                    if let Some(r) = resolve_name_alias(target, aliases, local_types, prefix) {
                        *name = format!("{}.{}", r, method);
                    }
                }
            }
            for arg in args {
                rewrite_expr(arg, local_types, aliases, prefix);
            }
        }
        Expr::Block(stmts, _) => {
            for s in stmts {
                rewrite_expr(s, local_types, aliases, prefix);
            }
        }
        Expr::If(cond, body, _) => {
            rewrite_expr(cond, local_types, aliases, prefix);
            rewrite_expr(body, local_types, aliases, prefix);
        }
        Expr::IfElse(cond, then_b, else_b, _) => {
            rewrite_expr(cond, local_types, aliases, prefix);
            rewrite_expr(then_b, local_types, aliases, prefix);
            rewrite_expr(else_b, local_types, aliases, prefix);
        }
        Expr::While(cond, body, _) => {
            rewrite_expr(cond, local_types, aliases, prefix);
            rewrite_expr(body, local_types, aliases, prefix);
        }
        Expr::Let(_, _, _, val, _) => rewrite_expr(val, local_types, aliases, prefix),
        Expr::Assign(_, val, _) => rewrite_expr(val, local_types, aliases, prefix),
        Expr::Return(opt_expr, _) => {
            if let Some(e) = opt_expr {
                rewrite_expr(e, local_types, aliases, prefix);
            }
        }
        Expr::Add(lhs, rhs, _)
        | Expr::Sub(lhs, rhs, _)
        | Expr::Mul(lhs, rhs, _)
        | Expr::Div(lhs, rhs, _)
        | Expr::Mod(lhs, rhs, _)
        | Expr::Shl(lhs, rhs, _)
        | Expr::Shr(lhs, rhs, _)
        | Expr::Ampersand(lhs, rhs, _)
        | Expr::Pipe(lhs, rhs, _)
        | Expr::Caret(lhs, rhs, _)
        | Expr::Equal(lhs, rhs, _)
        | Expr::NotEqual(lhs, rhs, _)
        | Expr::LessThan(lhs, rhs, _)
        | Expr::GreaterThan(lhs, rhs, _)
        | Expr::LessEqual(lhs, rhs, _)
        | Expr::GreaterEqual(lhs, rhs, _)
        | Expr::And(lhs, rhs, _)
        | Expr::Or(lhs, rhs, _) => {
            rewrite_expr(lhs, local_types, aliases, prefix);
            rewrite_expr(rhs, local_types, aliases, prefix);
        }
        Expr::FieldAccess(target, _, _) => {
            rewrite_expr(target, local_types, aliases, prefix);
        }
        Expr::FieldAssign(target, _, val, _) => {
            rewrite_expr(target, local_types, aliases, prefix);
            rewrite_expr(val, local_types, aliases, prefix);
        }
        Expr::MacroCall(_, args, _) => {
            for arg in args {
                rewrite_expr(arg, local_types, aliases, prefix);
            }
        }
        _ => {}
    }
}

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
