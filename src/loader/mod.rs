//! loader/mod.rs
//! Handles multi-file module resolution and parsing for GDRS without mod.gdrs files.

pub mod derives;
pub mod files;

use crate::ast::*;
use crate::loader::derives::expand_derives;
use crate::loader::files::load_file_recursive;
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

    let std_dir = if let Ok(env_path) = std::env::var("GDRS_STD_PATH") {
        PathBuf::from(env_path)
    } else if let Ok(exe_path) = std::env::current_exe() {
        let exe_dir = exe_path.parent().unwrap_or_else(|| Path::new("."));
        if exe_dir.join("std").exists() {
            exe_dir.join("std")
        } else if exe_dir.join("../std").exists() {
            exe_dir.join("../std")
        } else {
            let default_repo_std = PathBuf::from("/Users/aramsamifanni/Programming/gdrsc/std");
            if default_repo_std.exists() {
                default_repo_std
            } else {
                PathBuf::from("std")
            }
        }
    } else {
        PathBuf::from("std")
    };

    let std_files = [
        ("libc.gdrs", vec!["std".to_string(), "libc".to_string()]),
        ("core.gdrs", vec!["std".to_string(), "core".to_string()]),
        ("iter.gdrs", vec!["std".to_string(), "iter".to_string()]),
        ("vec.gdrs", vec!["std".to_string(), "vec".to_string()]),
        ("string.gdrs", vec!["std".to_string(), "string".to_string()]),
        ("time.gdrs", vec!["std".to_string(), "time".to_string()]),
        ("env.gdrs", vec!["std".to_string(), "env".to_string()]),
        ("fs.gdrs", vec!["std".to_string(), "fs".to_string()]),
    ];
    for (file_name, prefix) in std_files {
        let path = std_dir.join(file_name);
        if path.exists() {
            let _ = load_file_recursive(
                &path,
                &std_dir,
                &prefix,
                &mut loaded_files,
                &mut merged_program,
            );
        }
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

