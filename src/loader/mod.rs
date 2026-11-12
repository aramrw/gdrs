//! loader/mod.rs
//! Handles multi-file module resolution and parsing for GDRS without mod.gdrs files.

pub mod derives;
pub mod files;

use crate::ast::*;
use crate::loader::derives::expand_derives;
use crate::loader::files::load_file_recursive;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

pub struct SourceFile {
    pub path: PathBuf,
    pub source: String,
    pub start: usize,
    pub end: usize,
}

pub struct SourceMap {
    pub files: Vec<SourceFile>,
    pub entry_index: usize,
    next_offset: usize,
}

impl SourceMap {
    pub fn new() -> Self {
        Self {
            files: Vec::new(),
            entry_index: 0,
            // Reserve 0..16 so synthetic 0..1 spans resolve to the entry file
            next_offset: 16,
        }
    }

    pub fn add_file(&mut self, path: PathBuf, source: String) -> usize {
        let start = self.next_offset;
        let end = start + source.len();
        self.next_offset = end + 1;
        self.files.push(SourceFile {
            path,
            source,
            start,
            end,
        });
        start
    }

    pub fn resolve(&self, span: &Span) -> (String, Span) {
        if span.start >= 16 {
            for f in &self.files {
                if span.start >= f.start && span.start <= f.end {
                    let local_start = span.start - f.start;
                    let local_end = span.end.min(f.end).saturating_sub(f.start).max(local_start);
                    return (
                        f.path.to_string_lossy().to_string(),
                        local_start..local_end,
                    );
                }
            }
        }
        if let Some(entry) = self.files.get(self.entry_index) {
            let local_end = span.end.min(entry.source.len()).max(span.start.min(entry.source.len()));
            let local_start = span.start.min(entry.source.len());
            return (entry.path.to_string_lossy().to_string(), local_start..local_end);
        }
        ("<unknown>".to_string(), 0..1)
    }

    /// Returns `(file_path, line, column)` with 1-based line and column numbers.
    pub fn get_location(&self, span: &Span) -> (String, usize, usize) {
        let (file, local_span) = self.resolve(span);
        for f in &self.files {
            if f.path.to_string_lossy() == file {
                let clamped_start = local_span.start.min(f.source.len());
                let prefix = &f.source[..clamped_start];
                let line = prefix.matches('\n').count() + 1;
                let col = prefix
                    .rfind('\n')
                    .map(|p| clamped_start - p)
                    .unwrap_or(clamped_start + 1);
                return (file, line, col);
            }
        }
        (file, 1, 1)
    }

    /// Extracts the original source text for `span`.
    pub fn get_snippet(&self, span: &Span) -> String {
        let (file, local_span) = self.resolve(span);
        for f in &self.files {
            if f.path.to_string_lossy() == file {
                let start = local_span.start.min(f.source.len());
                let end = local_span.end.min(f.source.len()).max(start);
                return f.source[start..end].trim().to_string();
            }
        }
        "<unknown>".to_string()
    }
}

pub fn load_program(entry_file: &Path) -> Result<(Program, SourceMap), String> {
    let mut loaded_files = HashSet::new();
    let mut source_map = SourceMap::new();
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
        ("mem.gdrs", vec!["std".to_string(), "mem".to_string()]),
        ("iter.gdrs", vec!["std".to_string(), "iter".to_string()]),
        ("convert.gdrs", vec!["std".to_string(), "convert".to_string()]),
        ("vec.gdrs", vec!["std".to_string(), "vec".to_string()]),
        ("string.gdrs", vec!["std".to_string(), "string".to_string()]),
        ("time.gdrs", vec!["std".to_string(), "time".to_string()]),
        ("env.gdrs", vec!["std".to_string(), "env".to_string()]),
        ("fs.gdrs", vec!["std".to_string(), "fs".to_string()]),
        ("math.gdrs", vec!["std".to_string(), "math".to_string()]),
    ];
    for (file_name, prefix) in std_files {
        let path = std_dir.join(file_name);
        if path.exists() {
            load_file_recursive(
                &path,
                &std_dir,
                &prefix,
                &mut loaded_files,
                &mut merged_program,
                &mut source_map,
            )?;
        }
    }

    source_map.entry_index = source_map.files.len();
    load_file_recursive(
        entry_file,
        &base_dir,
        &[],
        &mut loaded_files,
        &mut merged_program,
        &mut source_map,
    )?;

    expand_derives(&mut merged_program);

    Ok((merged_program, source_map))
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
        Type::Obj("std_core_Option_bare") if local_types.contains("Option") => {
            *ty = Type::Enum(intern_str(&format!("{prefix}Option")));
        }
        Type::Obj("std_core_Result_bare") if local_types.contains("Result") => {
            *ty = Type::Enum(intern_str(&format!("{prefix}Result")));
        }
        Type::Obj(name) => {
            if let Some((base, mut t_args)) = crate::sanal::mono::lookup_mangled(&**name) {
                for arg in &mut t_args {
                    rewrite_type(arg, local_types, aliases, prefix);
                }
                let new_base =
                    resolve_name_alias(&base, aliases, local_types, prefix).unwrap_or(base);
                let remangled = crate::sanal::mono::mangle_name(&new_base, &t_args);
                *ty = Type::Obj(intern_str(&remangled));
            } else if let Some(r) = resolve_name_alias(&**name, aliases, local_types, prefix) {
                *ty = Type::Obj(intern_str(&r));
            }
        }
        Type::Enum(name) => {
            if let Some((base, mut t_args)) = crate::sanal::mono::lookup_mangled(&**name) {
                for arg in &mut t_args {
                    rewrite_type(arg, local_types, aliases, prefix);
                }
                let new_base =
                    resolve_name_alias(&base, aliases, local_types, prefix).unwrap_or(base);
                let remangled = crate::sanal::mono::mangle_name(&new_base, &t_args);
                *ty = Type::Enum(intern_str(&remangled));
            } else if let Some(r) = resolve_name_alias(&**name, aliases, local_types, prefix) {
                *ty = Type::Enum(intern_str(&r));
            }
        }
        Type::Array(elem_ty, size) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Array(intern_type(inner), *size);
        }
        Type::Tuple(elem_tys) => {
            let rewritten: Vec<Type> = elem_tys
                .iter()
                .map(|t| {
                    let mut copy = *t;
                    rewrite_type(&mut copy, local_types, aliases, prefix);
                    copy
                })
                .collect();
            *ty = Type::Tuple(intern_tuple(&rewritten));
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
        Type::Ptr(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Ptr(intern_type(inner));
        }
        Type::Ref(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Ref(intern_type(inner));
        }
        Type::MutRef(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::MutRef(intern_type(inner));
        }
        Type::Rc(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Rc(intern_type(inner));
        }
        Type::Arc(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Arc(intern_type(inner));
        }
        Type::Int
        | Type::I32
        | Type::I16
        | Type::I8
        | Type::U64
        | Type::U32
        | Type::U16
        | Type::U8
        | Type::Float
        | Type::F32
        | Type::Bool
        | Type::Str
        | Type::String
        | Type::Unit
        | Type::Void
        | Type::Generic(_)
        | Type::DynTrait(_)
        | Type::Infer(_) => {}
    }
}

fn rewrite_expr(
    expr: &mut Expr,
    local_types: &HashSet<String>,
    aliases: &HashMap<String, String>,
    prefix: &str,
) {
    match expr {
        Expr::Int(_, _) | Expr::Float(_, _) | Expr::Bool(_, _) | Expr::String(_, _)
        | Expr::Break(_) | Expr::Continue(_) => {}
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
        Expr::EnumConstruct(enum_name, _, args, _) => {
            if let Some(r) = resolve_name_alias(enum_name, aliases, local_types, prefix) {
                *enum_name = r;
            }
            for arg in args {
                rewrite_expr(arg, local_types, aliases, prefix);
            }
        }
        Expr::Call(name, args, _) => {
            if !name.starts_with('.') {
                if let Some(r) = resolve_name_alias(name, aliases, local_types, prefix) {
                    *name = r;
                } else if let Some((target, method)) = name.split_once('.') {
                    if let Some(r) = resolve_name_alias(target, aliases, local_types, prefix) {
                        *name = format!("{}.{}", r, method);
                    }
                }
            }
            for arg in args {
                rewrite_expr(arg, local_types, aliases, prefix);
            }
        }
        Expr::Block(stmts, _) | Expr::Unsafe(stmts, _) => {
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
        Expr::Match(target, arms, _) => {
            rewrite_expr(target, local_types, aliases, prefix);
            for arm in arms {
                if let Some((enum_part, variant_part)) = arm.variant_name.split_once("::") {
                    if let Some(r) = resolve_name_alias(enum_part, aliases, local_types, prefix) {
                        arm.variant_name = format!("{r}::{variant_part}");
                    }
                }
                for stmt in &mut arm.body {
                    rewrite_expr(stmt, local_types, aliases, prefix);
                }
            }
        }
        Expr::Let(_, opt_ty, _, val, _) | Expr::LetTuple(_, opt_ty, val, _) => {
            if let Some(ty) = opt_ty {
                rewrite_type(ty, local_types, aliases, prefix);
            }
            rewrite_expr(val, local_types, aliases, prefix);
        }
        Expr::Assign(_, val, _) => rewrite_expr(val, local_types, aliases, prefix),
        Expr::Return(opt_expr, _) => {
            if let Some(e) = opt_expr {
                rewrite_expr(e, local_types, aliases, prefix);
            }
        }
        Expr::Neg(inner, _)
        | Expr::Not(inner, _)
        | Expr::Try(inner, _)
        | Expr::Ref(inner, _, _)
        | Expr::Deref(inner, _) => {
            rewrite_expr(inner, local_types, aliases, prefix);
        }
        Expr::Cast(inner, ty, _) => {
            rewrite_expr(inner, local_types, aliases, prefix);
            rewrite_type(ty, local_types, aliases, prefix);
        }
        Expr::Closure(_, body, _) => {
            rewrite_expr(body, local_types, aliases, prefix);
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
        | Expr::Or(lhs, rhs, _)
        | Expr::IndexAccess(lhs, rhs, _)
        | Expr::DerefAssign(lhs, rhs, _)
        | Expr::Range(lhs, rhs, _) => {
            rewrite_expr(lhs, local_types, aliases, prefix);
            rewrite_expr(rhs, local_types, aliases, prefix);
        }
        Expr::IndexAssign(target, idx, val, _) => {
            rewrite_expr(target, local_types, aliases, prefix);
            rewrite_expr(idx, local_types, aliases, prefix);
            rewrite_expr(val, local_types, aliases, prefix);
        }
        Expr::ArrayInit(elems, _) | Expr::TupleInit(elems, _) | Expr::MacroCall(_, elems, _) => {
            for elem in elems {
                rewrite_expr(elem, local_types, aliases, prefix);
            }
        }
        Expr::FieldAccess(target, _, _) => {
            rewrite_expr(target, local_types, aliases, prefix);
        }
        Expr::FieldAssign(target, _, val, _) => {
            rewrite_expr(target, local_types, aliases, prefix);
            rewrite_expr(val, local_types, aliases, prefix);
        }
    }
}

