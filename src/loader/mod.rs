//! loader/mod.rs
//! Handles multi-file module resolution and parsing for GDRS without mod.gdrs files.

use crate::ast::*;
use crate::parser::parser;
use chumsky::Parser;
use logos::Logos;
use std::collections::HashSet;
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

    load_file_recursive(entry_file, &base_dir, &[], &mut loaded_files, &mut merged_program)?;

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
                rewrite_type(&mut field.ty, &local_types, &prefix_str);
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
                    rewrite_type(p_ty, &local_types, &prefix_str);
                }
            }
        }
        merged_program.enums.push(e);
    }

    // Mangle and push impls
    for mut i in program.impls {
        if !prefix_str.is_empty() {
            if local_types.contains(&i.target_type) {
                i.target_type = format!("{}{}", prefix_str, i.target_type);
            }
            for method in &mut i.methods {
                rewrite_type(&mut method.return_type, &local_types, &prefix_str);
                for p in &mut method.params {
                    rewrite_type(&mut p.ty, &local_types, &prefix_str);
                }
                for expr in &mut method.body {
                    rewrite_expr(expr, &local_types, &prefix_str);
                }
            }
        }
        merged_program.impls.push(i);
    }

    // Mangle and push functions
    for mut f in program.functions {
        if !prefix_str.is_empty() && f.name != "main" {
            f.name = format!("{}{}", prefix_str, f.name);
            rewrite_type(&mut f.return_type, &local_types, &prefix_str);
            for p in &mut f.params {
                rewrite_type(&mut p.ty, &local_types, &prefix_str);
            }
            for expr in &mut f.body {
                rewrite_expr(expr, &local_types, &prefix_str);
            }
        }
        merged_program.functions.push(f);
    }

    // Process sub-modules declared via `mod path::to::sub`
    for m in program.mods {
        let sub_prefix = m.path.clone();

        // Resolve file path: e.g. base_dir / "math.gdrs" or base_dir / "geometry/rect.gdrs"
        let rel_path = format!("{}.gdrs", m.path.join("/"));
        let sub_file = base_dir.join(rel_path);

        load_file_recursive(&sub_file, base_dir, &sub_prefix, loaded_files, merged_program)?;
    }

    Ok(())
}

fn rewrite_type(ty: &mut Type, local_types: &HashSet<String>, prefix: &str) {
    match ty {
        Type::Obj(name) => {
            if local_types.contains(*name) {
                *ty = Type::Obj(intern_str(&format!("{}{}", prefix, name)));
            }
        }
        Type::Enum(name) => {
            if local_types.contains(*name) {
                *ty = Type::Enum(intern_str(&format!("{}{}", prefix, name)));
            }
        }
        Type::Array(elem_ty, size) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, prefix);
            *ty = Type::Array(intern_type(inner), *size);
        }
        Type::Slice(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, prefix);
            *ty = Type::Slice(intern_type(inner));
        }
        Type::Vec(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, prefix);
            *ty = Type::Vec(intern_type(inner));
        }
        _ => {}
    }
}

fn rewrite_expr(expr: &mut Expr, local_types: &HashSet<String>, prefix: &str) {
    match expr {
        Expr::Ident(name, _) => {
            if local_types.contains(name) {
                *name = format!("{}{}", prefix, name);
            }
        }
        Expr::ObjInit(name, fields, _) => {
            if local_types.contains(name) {
                *name = format!("{}{}", prefix, name);
            }
            for (_, f_expr) in fields {
                rewrite_expr(f_expr, local_types, prefix);
            }
        }
        Expr::Call(name, args, _) => {
            if local_types.contains(name) {
                *name = format!("{}{}", prefix, name);
            }
            for arg in args {
                rewrite_expr(arg, local_types, prefix);
            }
        }
        Expr::Block(stmts, _) => {
            for s in stmts {
                rewrite_expr(s, local_types, prefix);
            }
        }
        Expr::If(cond, body, _) => {
            rewrite_expr(cond, local_types, prefix);
            rewrite_expr(body, local_types, prefix);
        }
        Expr::IfElse(cond, then_b, else_b, _) => {
            rewrite_expr(cond, local_types, prefix);
            rewrite_expr(then_b, local_types, prefix);
            rewrite_expr(else_b, local_types, prefix);
        }
        Expr::While(cond, body, _) => {
            rewrite_expr(cond, local_types, prefix);
            rewrite_expr(body, local_types, prefix);
        }
        Expr::Let(_, _, val, _) => rewrite_expr(val, local_types, prefix),
        Expr::Assign(_, val, _) => rewrite_expr(val, local_types, prefix),
        Expr::Return(opt_expr, _) => {
            if let Some(e) = opt_expr {
                rewrite_expr(e, local_types, prefix);
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
            rewrite_expr(lhs, local_types, prefix);
            rewrite_expr(rhs, local_types, prefix);
        }
        Expr::FieldAccess(target, _, _) => {
            rewrite_expr(target, local_types, prefix);
        }
        Expr::FieldAssign(target, _, val, _) => {
            rewrite_expr(target, local_types, prefix);
            rewrite_expr(val, local_types, prefix);
        }
        Expr::MacroCall(_, args, _) => {
            for arg in args {
                rewrite_expr(arg, local_types, prefix);
            }
        }
        _ => {}
    }
}
