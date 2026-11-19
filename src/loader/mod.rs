//! loader/mod.rs
//! Handles multi-file module resolution and parsing for GDRS without mod.gdrs files.

pub mod derives;
pub mod files;

use crate::ast::*;
use crate::loader::derives::expand_derives;
use crate::loader::files::{load_file_recursive, load_source_str, load_source_str_with_ctx, LoaderContext};
use crate::rlib::{decode_rlib, RlibPackage, RlibSourceFile};
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

#[derive(Debug, Clone, Default)]
pub struct LoadCrateOptions {
    pub crate_name: Option<String>,
    pub root_mod_prefix: Vec<String>,
    pub externs: Vec<(String, PathBuf)>,
}

#[derive(Debug)]
pub struct LoadedCrateResult {
    pub program: Program,
    pub source_map: SourceMap,
    pub crate_sources: Vec<RlibSourceFile>,
    pub extern_objects: Vec<(String, Vec<u8>)>,
    pub extern_alias_pairs: Vec<(String, String)>,
    pub extern_lib_dirs: Vec<String>,
    pub extern_libs: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    pub source: String,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone)]
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

static STD_PRELUDE_CACHE: OnceLock<Result<(Program, SourceMap, HashSet<PathBuf>), String>> =
    OnceLock::new();

pub(crate) fn resolve_std_dir() -> PathBuf {
    if let Ok(env_path) = std::env::var("GDRS_STD_PATH") {
        let p = PathBuf::from(env_path);
        if !p.as_os_str().is_empty() {
            return p;
        }
    }

    let mut candidates = Vec::new();
    if let Ok(exe_path) = std::env::current_exe() {
        let exe_dir = exe_path.parent().unwrap_or_else(|| Path::new("."));
        candidates.push(exe_dir.join("std"));
        candidates.push(exe_dir.join("../std"));
        candidates.push(exe_dir.join("../share/gdrs/std"));
        candidates.push(exe_dir.join("../lib/gdrs/std"));
    }
    if let Ok(gdrs_home) = std::env::var("GDRS_HOME") {
        if !gdrs_home.is_empty() {
            candidates.push(PathBuf::from(gdrs_home).join("std"));
        }
    }
    if let Ok(home) = std::env::var("HOME") {
        if !home.is_empty() {
            candidates.push(PathBuf::from(home).join(".gdrs/std"));
        }
    }
    if let Some(manifest_dir) = option_env!("CARGO_MANIFEST_DIR") {
        candidates.push(PathBuf::from(manifest_dir).join("std"));
    }
    candidates.push(PathBuf::from("std"));

    for cand in &candidates {
        if cand.join("core.gdrs").exists() {
            return cand.clone();
        }
    }

    PathBuf::from("std")
}

fn load_std_prelude() -> Result<(Program, SourceMap, HashSet<PathBuf>), String> {
    let mut loaded_files = HashSet::new();
    let mut source_map = SourceMap::new();
    let mut merged_program = Program {
        mods: Vec::new(),
        uses: Vec::new(),
        traits: Vec::new(),
        trait_aliases: Vec::new(),
        externs: Vec::new(),
        consts: Vec::new(),
        statics: Vec::new(),
        structs: Vec::new(),
        enums: Vec::new(),
        impls: Vec::new(),
        functions: Vec::new(),
        extern_crate_names: HashSet::new(),
    };

    let std_dir = resolve_std_dir();
    if !std_dir.join("core.gdrs").exists() {
        return Err(format!(
            "Failed to locate GDRS std library directory (checked '{}', missing core.gdrs). Set GDRS_STD_PATH=/path/to/gdrsc/std or place std/ next to the gdrsc binary or at ~/.gdrs/std.",
            std_dir.display()
        ));
    }

    let std_files = [
        ("libc.gdrs", vec!["std".to_string(), "libc".to_string()]),
        ("core.gdrs", vec!["std".to_string(), "core".to_string()]),
        ("mem.gdrs", vec!["std".to_string(), "mem".to_string()]),
        ("iter.gdrs", vec!["std".to_string(), "iter".to_string()]),
        ("convert.gdrs", vec!["std".to_string(), "convert".to_string()]),
        ("vec.gdrs", vec!["std".to_string(), "vec".to_string()]),
        ("boxed.gdrs", vec!["std".to_string(), "boxed".to_string()]),
        ("rc.gdrs", vec!["std".to_string(), "rc".to_string()]),
        ("sync.gdrs", vec!["std".to_string(), "sync".to_string()]),
        ("string.gdrs", vec!["std".to_string(), "string".to_string()]),
        ("collections.gdrs", vec!["std".to_string(), "collections".to_string()]),
        ("fmt.gdrs", vec!["std".to_string(), "fmt".to_string()]),
        ("time.gdrs", vec!["std".to_string(), "time".to_string()]),
        ("env.gdrs", vec!["std".to_string(), "env".to_string()]),
        ("fs.gdrs", vec!["std".to_string(), "fs".to_string()]),
        ("net.gdrs", vec!["std".to_string(), "net".to_string()]),
        ("process.gdrs", vec!["std".to_string(), "process".to_string()]),
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

    Ok((merged_program, source_map, loaded_files))
}

pub fn load_program(entry_file: &Path) -> Result<(Program, SourceMap), String> {
    let loaded = load_program_with_options(entry_file, &LoadCrateOptions::default())?;
    Ok((loaded.program, loaded.source_map))
}

pub fn load_program_with_options(
    entry_file: &Path,
    opts: &LoadCrateOptions,
) -> Result<LoadedCrateResult, String> {
    let (mut merged_program, mut source_map, mut loaded_files) = load_std_prelude()?;

    let mut extern_aliases: HashMap<String, String> = HashMap::new();
    let mut extern_alias_pairs: Vec<(String, String)> = Vec::new();
    let mut decoded_by_crate: HashMap<String, RlibPackage> = HashMap::new();
    let mut crate_order: Vec<String> = Vec::new();

    for (alias, rlib_path) in &opts.externs {
        let bytes = std::fs::read(rlib_path).map_err(|e| {
            format!(
                "Failed to read extern library `{}` at '{}': {}",
                alias,
                rlib_path.display(),
                e
            )
        })?;
        let pkg = decode_rlib(&bytes).map_err(|e| {
            format!(
                "Failed to decode extern library `{}` ('{}'): {}",
                alias,
                rlib_path.display(),
                e
            )
        })?;

        if let Some(prev) = extern_aliases.insert(alias.clone(), pkg.crate_name.clone()) {
            if prev != pkg.crate_name {
                return Err(format!(
                    "Conflicting --extern definitions for `{}`: `{}` vs `{}`",
                    alias, prev, pkg.crate_name
                ));
            }
        } else {
            extern_alias_pairs.push((alias.clone(), pkg.crate_name.clone()));
        }
        merged_program.extern_crate_names.insert(pkg.crate_name.clone());

        if !decoded_by_crate.contains_key(&pkg.crate_name) {
            crate_order.push(pkg.crate_name.clone());
            decoded_by_crate.insert(pkg.crate_name.clone(), pkg);
        }
    }

    // Topologically order decoded .rlib crates so transitive dependencies always load first.
    fn topo_visit(
        crate_name: &str,
        by_crate: &HashMap<String, RlibPackage>,
        visiting: &mut HashSet<String>,
        visited: &mut HashSet<String>,
        out: &mut Vec<String>,
    ) {
        if visited.contains(crate_name) || visiting.contains(crate_name) {
            return;
        }
        visiting.insert(crate_name.to_string());
        if let Some(pkg) = by_crate.get(crate_name) {
            for (_, dep_crate) in &pkg.extern_aliases {
                topo_visit(dep_crate, by_crate, visiting, visited, out);
            }
        }
        visiting.remove(crate_name);
        visited.insert(crate_name.to_string());
        out.push(crate_name.to_string());
    }

    let mut topo_order = Vec::with_capacity(crate_order.len());
    let mut visiting = HashSet::new();
    let mut visited = HashSet::new();
    for cname in &crate_order {
        topo_visit(cname, &decoded_by_crate, &mut visiting, &mut visited, &mut topo_order);
    }

    let mut extern_objects: Vec<(String, Vec<u8>)> = Vec::new();
    let mut extern_lib_dirs: Vec<String> = Vec::new();
    let mut extern_libs: Vec<String> = Vec::new();

    for cname in topo_order {
        let Some(pkg) = decoded_by_crate.remove(&cname) else {
            continue;
        };
        extern_objects.push((pkg.crate_name.clone(), pkg.object_bytes));
        for d in pkg.lib_dirs {
            if !extern_lib_dirs.contains(&d) {
                extern_lib_dirs.push(d);
            }
        }
        for l in pkg.libs {
            if !extern_libs.contains(&l) {
                extern_libs.push(l);
            }
        }

        let bundled_mod_prefixes: HashSet<Vec<String>> =
            pkg.sources.iter().map(|s| s.mod_prefix.clone()).collect();
        let pkg_aliases: HashMap<String, String> = pkg.extern_aliases.into_iter().collect();
        for ext_src in &pkg.sources {
            let mut dummy_recorded = Vec::new();
            let mut ext_ctx = LoaderContext {
                root_mod_prefix: std::slice::from_ref(&pkg.crate_name),
                extern_aliases: &pkg_aliases,
                bundled_mod_prefixes: &bundled_mod_prefixes,
                recorded_sources: &mut dummy_recorded,
                record_sources: false,
            };
            let virtual_path = PathBuf::from(format!("<extern:{}>/{}", pkg.crate_name, ext_src.rel_name));
            load_source_str_with_ctx(
                &ext_src.source,
                &virtual_path,
                Path::new("."),
                &ext_src.mod_prefix,
                &mut loaded_files,
                &mut merged_program,
                &mut source_map,
                true,
                Some(&mut ext_ctx),
            )?;
        }
    }

    let base_dir = entry_file
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();

    source_map.entry_index = source_map.files.len();
    let mut crate_sources = Vec::new();
    let empty_bundled = HashSet::new();
    let mut ctx = LoaderContext {
        root_mod_prefix: &opts.root_mod_prefix,
        extern_aliases: &extern_aliases,
        bundled_mod_prefixes: &empty_bundled,
        recorded_sources: &mut crate_sources,
        record_sources: true,
    };
    crate::loader::files::load_file_recursive_with_ctx(
        entry_file,
        &base_dir,
        &opts.root_mod_prefix,
        &mut loaded_files,
        &mut merged_program,
        &mut source_map,
        Some(&mut ctx),
    )?;

    expand_derives(&mut merged_program);

    Ok(LoadedCrateResult {
        program: merged_program,
        source_map,
        crate_sources,
        extern_objects,
        extern_alias_pairs,
        extern_lib_dirs,
        extern_libs,
    })
}

pub fn load_program_from_str(source: &str, quiet: bool) -> Result<(Program, SourceMap), String> {
    let cached = STD_PRELUDE_CACHE.get_or_init(load_std_prelude);
    let (mut merged_program, mut source_map, mut loaded_files) = match cached {
        Ok(data) => data.clone(),
        Err(e) => return Err(e.clone()),
    };

    source_map.entry_index = source_map.files.len();
    load_source_str(
        source,
        Path::new("<memory>.gdrs"),
        Path::new("."),
        &[],
        &mut loaded_files,
        &mut merged_program,
        &mut source_map,
        quiet,
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
            return Some(format!("{}_{}", aliases[mod_part], item_part.replace("::", "_")));
        }
        if local_types.contains(mod_part) {
            return Some(format!("{}{}_{}", prefix, mod_part, item_part.replace("::", "_")));
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
        Type::Box(elem_ty) => {
            let mut inner = **elem_ty;
            rewrite_type(&mut inner, local_types, aliases, prefix);
            *ty = Type::Box(intern_type(inner));
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
        Type::FnPtr(params, ret) => {
            let rewritten_params: Vec<Type> = params
                .iter()
                .map(|p| {
                    let mut copy = *p;
                    rewrite_type(&mut copy, local_types, aliases, prefix);
                    copy
                })
                .collect();
            let mut rewritten_ret = **ret;
            rewrite_type(&mut rewritten_ret, local_types, aliases, prefix);
            *ty = Type::FnPtr(intern_tuple(&rewritten_params), intern_type(rewritten_ret));
        }
        Type::DynTrait(name) => {
            if let Some(r) = resolve_name_alias(name, aliases, local_types, prefix) {
                *ty = Type::DynTrait(intern_str(&r));
            }
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
        | Type::Infer(_)
        | Type::Error => {}
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
        | Expr::Continue(_) => {}
        Expr::Break(opt_expr, _) => {
            if let Some(e) = opt_expr {
                rewrite_expr(e, local_types, aliases, prefix);
            }
        }
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
            if let Some((base, mut ty_args)) = crate::sanal::mono::lookup_mangled(name) {
                for arg in &mut ty_args {
                    rewrite_type(arg, local_types, aliases, prefix);
                }
                let resolved_base = if !base.starts_with('.') {
                    if let Some(r) = resolve_name_alias(&base, aliases, local_types, prefix) {
                        r
                    } else if let Some((target, method)) = base.split_once('.') {
                        if let Some(r) = resolve_name_alias(target, aliases, local_types, prefix) {
                            format!("{}.{}", r, method)
                        } else {
                            base
                        }
                    } else {
                        base
                    }
                } else {
                    base
                };
                *name = crate::sanal::mono::mangle_name_update(&resolved_base, &ty_args);
            } else if !name.starts_with('.') {
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
        Expr::Loop(body, _) => {
            rewrite_expr(body, local_types, aliases, prefix);
        }
        Expr::Match(target, arms, _) => {
            rewrite_expr(target, local_types, aliases, prefix);
            for arm in arms {
                if let Some((enum_part, variant_part)) = arm.variant_name.rsplit_once("::") {
                    if let Some(r) = resolve_name_alias(enum_part, aliases, local_types, prefix) {
                        arm.variant_name = format!("{r}::{variant_part}");
                    }
                }
                for (alt_v, _) in &mut arm.alt_patterns {
                    if let Some((enum_part, variant_part)) = alt_v.rsplit_once("::") {
                        if let Some(r) = resolve_name_alias(enum_part, aliases, local_types, prefix) {
                            *alt_v = format!("{r}::{variant_part}");
                        }
                    }
                }
                if let Some(g) = &mut arm.guard {
                    rewrite_expr(g, local_types, aliases, prefix);
                }
                for stmt in &mut arm.body {
                    rewrite_expr(stmt, local_types, aliases, prefix);
                }
            }
        }
        Expr::LetElse {
            variant_name,
            target,
            else_body,
            ..
        } => {
            if let Some((enum_part, variant_part)) = variant_name.rsplit_once("::") {
                if let Some(r) = resolve_name_alias(enum_part, aliases, local_types, prefix) {
                    *variant_name = format!("{r}::{variant_part}");
                }
            }
            rewrite_expr(target, local_types, aliases, prefix);
            for stmt in else_body {
                rewrite_expr(stmt, local_types, aliases, prefix);
            }
        }
        Expr::Let(_, opt_ty, _, val, _) | Expr::LetTuple(_, opt_ty, val, _) => {
            if let Some(ty) = opt_ty {
                rewrite_type(ty, local_types, aliases, prefix);
            }
            rewrite_expr(val, local_types, aliases, prefix);
        }
        Expr::LetStruct(pat, opt_ty, val, _) => {
            if let Some(r) = resolve_name_alias(&pat.struct_path, aliases, local_types, prefix) {
                pat.struct_path = r;
            }
            if let Some(ty) = opt_ty {
                rewrite_type(ty, local_types, aliases, prefix);
            }
            rewrite_expr(val, local_types, aliases, prefix);
        }
        Expr::Assign(name, val, _) => {
            if let Some(r) = resolve_name_alias(name, aliases, local_types, prefix) {
                *name = r;
            }
            rewrite_expr(val, local_types, aliases, prefix);
        }
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
        Expr::Closure(_, _, body, _) => {
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
        | Expr::CompoundAssign(_, lhs, rhs, _)
        | Expr::Range(lhs, rhs, _, _) => {
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

