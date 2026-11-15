use crate::ast::*;
use crate::loader::{inject_indentation, rewrite_expr, rewrite_type};
use crate::parser::parser;
use chumsky::Parser;
use logos::Logos;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

fn file_declares_symbol(source: &str, sym: &str) -> bool {
    let raw_tokens: Vec<(Token, Span)> = Token::lexer(source)
        .spanned()
        .filter_map(|(res, span)| res.ok().map(|t| (t, span)))
        .collect();
    let processed = inject_indentation(raw_tokens);
    let eof = source.len()..source.len();
    let Ok(prog) = parser().parse(chumsky::Stream::from_iter(eof, processed.into_iter())) else {
        return false;
    };
    prog.structs.iter().any(|s| s.name == sym)
        || prog.enums.iter().any(|e| e.name == sym)
        || prog.functions.iter().any(|f| f.name == sym)
        || prog.traits.iter().any(|t| t.name == sym)
        || prog.trait_aliases.iter().any(|ta| ta.name == sym)
        || prog.consts.iter().any(|c| c.name == sym)
        || prog.statics.iter().any(|s| s.name == sym)
        || prog.externs.iter().any(|ext| ext.functions.iter().any(|ef| ef.name == sym))
        || prog.uses.iter().any(|u| {
            u.vis == Visibility::Pub
                && u.alias.as_deref().or_else(|| u.path.last().map(|s| s.as_str())) == Some(sym)
        })
}


pub struct LoaderContext<'a> {
    pub root_mod_prefix: &'a [String],
    pub extern_aliases: &'a HashMap<String, String>,
    pub bundled_mod_prefixes: &'a HashSet<Vec<String>>,
    pub recorded_sources: &'a mut Vec<crate::rlib::RlibSourceFile>,
    pub record_sources: bool,
}

pub fn load_file_recursive(
    file_path: &Path,
    base_dir: &Path,
    mod_prefix: &[String],
    loaded_files: &mut HashSet<PathBuf>,
    merged_program: &mut Program,
    source_map: &mut crate::loader::SourceMap,
) -> Result<(), String> {
    load_file_recursive_with_ctx(
        file_path,
        base_dir,
        mod_prefix,
        loaded_files,
        merged_program,
        source_map,
        None,
    )
}

pub fn load_file_recursive_with_ctx(
    file_path: &Path,
    base_dir: &Path,
    mod_prefix: &[String],
    loaded_files: &mut HashSet<PathBuf>,
    merged_program: &mut Program,
    source_map: &mut crate::loader::SourceMap,
    ctx: Option<&mut LoaderContext<'_>>,
) -> Result<(), String> {
    let canonical = fs::canonicalize(file_path)
        .map_err(|e| format!("Failed to find module file '{}': {}", file_path.display(), e))?;

    if loaded_files.contains(&canonical) {
        return Ok(());
    }
    loaded_files.insert(canonical.clone());

    let source = fs::read_to_string(&canonical)
        .map_err(|e| format!("Failed to read file '{}': {}", canonical.display(), e))?;

    load_source_str_with_ctx(
        &source,
        &canonical,
        base_dir,
        mod_prefix,
        loaded_files,
        merged_program,
        source_map,
        false,
        ctx,
    )
}

pub fn load_source_str(
    source: &str,
    canonical: &Path,
    base_dir: &Path,
    mod_prefix: &[String],
    loaded_files: &mut HashSet<PathBuf>,
    merged_program: &mut Program,
    source_map: &mut crate::loader::SourceMap,
    quiet: bool,
) -> Result<(), String> {
    load_source_str_with_ctx(
        source,
        canonical,
        base_dir,
        mod_prefix,
        loaded_files,
        merged_program,
        source_map,
        quiet,
        None,
    )
}

pub fn load_source_str_with_ctx(
    source: &str,
    canonical: &Path,
    base_dir: &Path,
    mod_prefix: &[String],
    loaded_files: &mut HashSet<PathBuf>,
    merged_program: &mut Program,
    source_map: &mut crate::loader::SourceMap,
    quiet: bool,
    mut ctx: Option<&mut LoaderContext<'_>>,
) -> Result<(), String> {
    let canonical = canonical.to_path_buf();
    if let Some(ref mut c) = ctx {
        if c.record_sources {
            let rel_name = canonical
                .file_name()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| "lib.gdrs".to_string());
            c.recorded_sources.push(crate::rlib::RlibSourceFile {
                rel_name,
                mod_prefix: mod_prefix.to_vec(),
                source: source.to_string(),
            });
        }
    }
    let base_offset = source_map.add_file(canonical.clone(), source.to_string());

    let raw_tokens: Vec<(Token, Span)> = Token::lexer(source)
        .spanned()
        .filter_map(|(res, span)| match res {
            Ok(token) => Some((token, (span.start + base_offset)..(span.end + base_offset))),
            Err(_) => None,
        })
        .collect();

    let processed_tokens = inject_indentation(raw_tokens);

    let eof_span = (base_offset + source.len())..(base_offset + source.len());
    let stream = chumsky::Stream::from_iter(eof_span, processed_tokens.into_iter());

    let program = match parser().parse(stream) {
        Ok(prog) => prog,
        Err(errs) => {
            if !quiet {
                crate::diagnostics::print_syntax_errors(&canonical, source, base_offset, errs);
            }
            return Err(format!("Parse error in '{}'", canonical.display()));
        }
    };

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
    for t in &program.traits {
        local_types.insert(t.name.clone());
    }
    for ta in &program.trait_aliases {
        local_types.insert(ta.name.clone());
    }
    for c in &program.consts {
        local_types.insert(c.name.clone());
    }
    for st in &program.statics {
        local_types.insert(st.name.clone());
    }

    // Process `use` declarations in this file
    let mut use_aliases = HashMap::new();
    if let Some(ref c) = ctx {
        for (alias, crate_name) in c.extern_aliases {
            use_aliases.insert(alias.clone(), crate_name.clone());
        }
    }
    for u in &program.uses {
        if u.path.is_empty() {
            continue;
        }

        if let Some(ext_crate) = ctx.as_ref().and_then(|c| c.extern_aliases.get(&u.path[0])) {
            let resolved_target = if u.path.len() == 1 {
                let alias = u.alias.as_ref().unwrap_or(&u.path[0]);
                use_aliases.insert(alias.clone(), ext_crate.clone());
                ext_crate.clone()
            } else {
                let mut target = format!("{}_{}", ext_crate, u.path[1..].join("_"));
                let sym = u.path.last().unwrap();
                let mod_sub = if u.path.len() == 2 {
                    vec![ext_crate.clone()]
                } else {
                    let mut p = vec![ext_crate.clone()];
                    p.extend_from_slice(&u.path[1..u.path.len() - 1]);
                    p
                };
                if let Some(reexport) = merged_program.uses.iter().find(|ru| {
                    ru.vis == Visibility::Pub
                        && ru.module_path == mod_sub
                        && ru.alias.as_deref().or_else(|| ru.path.last().map(|s| s.as_str()))
                            == Some(sym.as_str())
                }) {
                    target = reexport.resolved_target.clone();
                }
                let alias = u.alias.as_ref().unwrap_or(sym);
                use_aliases.insert(alias.clone(), target.clone());
                target
            };
            let mut recorded_use = u.clone();
            recorded_use.module_path = mod_prefix.to_vec();
            recorded_use.resolved_target = resolved_target;
            merged_program.uses.push(recorded_use);
            continue;
        }

        if let Some(ref c) = ctx {
            let mut matched_bundled: Option<(Vec<String>, usize)> = None;
            for i in (1..=u.path.len()).rev() {
                let mut cand_prefix = c.root_mod_prefix.to_vec();
                cand_prefix.extend_from_slice(&u.path[0..i]);
                if c.bundled_mod_prefixes.contains(&cand_prefix) {
                    matched_bundled = Some((cand_prefix, i));
                    break;
                }
            }
            if let Some((sub_prefix, matched_len)) = matched_bundled {
                let sub_prefix_str = format!("{}_", sub_prefix.join("_"));
                let resolved_target = if matched_len < u.path.len() {
                    let sym = &u.path[matched_len];
                    let alias = u.alias.as_ref().unwrap_or(sym);
                    let target = format!("{}{}", sub_prefix_str, sym);
                    use_aliases.insert(alias.clone(), target.clone());
                    target
                } else {
                    let sym = u.path.last().unwrap();
                    let alias = u.alias.as_ref().unwrap_or(sym);
                    let target = sub_prefix_str.trim_end_matches('_').to_string();
                    use_aliases.insert(alias.clone(), target.clone());
                    target
                };
                let mut recorded_use = u.clone();
                recorded_use.module_path = mod_prefix.to_vec();
                recorded_use.resolved_target = resolved_target;
                merged_program.uses.push(recorded_use);
                continue;
            }
        }

        let mut found_file: Option<(PathBuf, Vec<String>, usize)> = None;
        for i in (1..=u.path.len()).rev() {
            let mod_parts = &u.path[0..i];
            let rel_path = format!("{}.gdrs", mod_parts.join("/"));

            let std_dir = crate::loader::resolve_std_dir();
            let candidates = vec![
                base_dir.join(&rel_path),
                Path::new(".").join(&rel_path),
                std_dir.join(format!("{}.gdrs", mod_parts[1..].join("/"))),
                std_dir.join(&rel_path),
            ];

            for cand in candidates {
                if cand.exists() {
                    let is_std_cand = cand.to_string_lossy().contains("std/");
                    let mut prefix = mod_parts.to_vec();
                    if is_std_cand && prefix.first().map(|s| s.as_str()) != Some("std") {
                        prefix.insert(0, "std".to_string());
                    } else if !is_std_cand {
                        if let Some(ref c) = ctx {
                            if !c.root_mod_prefix.is_empty()
                                && !prefix.starts_with(c.root_mod_prefix)
                            {
                                let mut full = c.root_mod_prefix.to_vec();
                                full.extend(prefix);
                                prefix = full;
                            }
                        }
                    }
                    found_file = Some((cand, prefix, i));
                    break;
                }
            }
            if found_file.is_some() {
                break;
            }
        }

        // If not found as a direct file, check if mod_parts is a directory
        if found_file.is_none() {
            for i in (1..=u.path.len()).rev() {
                let mod_parts = &u.path[0..i];
                let dir_candidates = vec![
                    base_dir.join(mod_parts.join("/")),
                    Path::new(".").join(mod_parts.join("/")),
                    Path::new("std").join(mod_parts[1..].join("/")),
                    Path::new("std").join(mod_parts.join("/")),
                ];
                for dir in dir_candidates {
                    if dir.is_dir() {
                        if i == u.path.len() {
                            let self_file = dir.join(format!("{}.gdrs", dir.file_name().unwrap().to_string_lossy()));
                            if self_file.is_file() {
                                let is_std_dir = dir.to_string_lossy().contains("std/");
                                let mut prefix = mod_parts.to_vec();
                                if is_std_dir && prefix.first().map(|s| s.as_str()) != Some("std") {
                                    prefix.insert(0, "std".to_string());
                                } else if !is_std_dir {
                                    if let Some(ref c) = ctx {
                                        if !c.root_mod_prefix.is_empty()
                                            && !prefix.starts_with(c.root_mod_prefix)
                                        {
                                            let mut full = c.root_mod_prefix.to_vec();
                                            full.extend(prefix);
                                            prefix = full;
                                        }
                                    }
                                }
                                found_file = Some((self_file, prefix, i));
                                break;
                            }
                        } else {
                            let sym = &u.path[i];
                            if let Ok(entries) = std::fs::read_dir(&dir) {
                                for entry in entries.flatten() {
                                    let path = entry.path();
                                    if path.extension().map_or(false, |ext| ext == "gdrs") {
                                        if let Ok(content) = std::fs::read_to_string(&path) {
                                            if file_declares_symbol(&content, sym) {
                                                let file_stem = path.file_stem().unwrap().to_string_lossy().to_string();
                                                let is_std_dir = dir.to_string_lossy().contains("std/");
                                                let mut prefix = mod_parts.to_vec();
                                                if is_std_dir && prefix.first().map(|s| s.as_str()) != Some("std") {
                                                    prefix.insert(0, "std".to_string());
                                                } else if !is_std_dir {
                                                    if let Some(ref c) = ctx {
                                                        if !c.root_mod_prefix.is_empty()
                                                            && !prefix.starts_with(c.root_mod_prefix)
                                                        {
                                                            let mut full = c.root_mod_prefix.to_vec();
                                                            full.extend(prefix);
                                                            prefix = full;
                                                        }
                                                    }
                                                }
                                                prefix.push(file_stem);
                                                found_file = Some((path, prefix, i));
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if found_file.is_some() {
                        break;
                    }
                }
                if found_file.is_some() {
                    break;
                }
            }
        }

        if let Some((sub_file, sub_prefix, matched_len)) = found_file {
            let sub_base = sub_file.parent().unwrap_or_else(|| Path::new("."));
            load_file_recursive_with_ctx(
                &sub_file,
                sub_base,
                &sub_prefix,
                loaded_files,
                merged_program,
                source_map,
                ctx.as_deref_mut(),
            )?;

            let sub_prefix_str = format!("{}_", sub_prefix.join("_"));
            let resolved_target = if matched_len < u.path.len() {
                let sym = &u.path[matched_len];
                let alias = u.alias.as_ref().unwrap_or(sym);
                let mut target = format!("{}{}", sub_prefix_str, sym);
                if let Some(reexport) = merged_program.uses.iter().find(|ru| {
                    ru.vis == Visibility::Pub
                        && ru.module_path == sub_prefix
                        && ru.alias.as_deref().or_else(|| ru.path.last().map(|s| s.as_str()))
                            == Some(sym.as_str())
                }) {
                    target = reexport.resolved_target.clone();
                }
                use_aliases.insert(alias.clone(), target.clone());
                target
            } else {
                let sym = u.path.last().unwrap();
                let alias = u.alias.as_ref().unwrap_or(sym);
                let target = sub_prefix_str.trim_end_matches('_').to_string();
                use_aliases.insert(alias.clone(), target.clone());
                target
            };

            let mut recorded_use = u.clone();
            recorded_use.module_path = mod_prefix.to_vec();
            recorded_use.resolved_target = resolved_target;
            merged_program.uses.push(recorded_use);
        }
    }

    for mut t in program.traits {
        t.module_path = mod_prefix.to_vec();
        if !prefix_str.is_empty() {
            t.name = format!("{}{}", prefix_str, t.name);
        }
        merged_program.traits.push(t);
    }

    for mut ta in program.trait_aliases {
        ta.module_path = mod_prefix.to_vec();
        if !prefix_str.is_empty() {
            ta.name = format!("{}{}", prefix_str, ta.name);
        }
        merged_program.trait_aliases.push(ta);
    }

    for mut c in program.consts {
        c.module_path = mod_prefix.to_vec();
        if !prefix_str.is_empty() {
            c.name = format!("{}{}", prefix_str, c.name);
        }
        rewrite_type(&mut c.ty, &local_types, &use_aliases, &prefix_str);
        rewrite_expr(&mut c.value, &local_types, &use_aliases, &prefix_str);
        merged_program.consts.push(c);
    }

    for mut st in program.statics {
        st.module_path = mod_prefix.to_vec();
        if !prefix_str.is_empty() {
            st.name = format!("{}{}", prefix_str, st.name);
        }
        rewrite_type(&mut st.ty, &local_types, &use_aliases, &prefix_str);
        rewrite_expr(&mut st.value, &local_types, &use_aliases, &prefix_str);
        merged_program.statics.push(st);
    }

    for mut ext in program.externs {
        for ef in &mut ext.functions {
            ef.module_path = mod_prefix.to_vec();
        }
        if !prefix_str.is_empty() {
            let mut mangled_funcs = Vec::new();
            for ef in &ext.functions {
                mangled_funcs.push(crate::ast::ExternFnDecl {
                    name: format!("{}{}", prefix_str, ef.name),
                    c_name: ef.c_name.clone(),
                    params: ef.params.clone(),
                    return_type: ef.return_type.clone(),
                    vis: ef.vis,
                    module_path: ef.module_path.clone(),
                    span: ef.span.clone(),
                });
            }
            ext.functions.extend(mangled_funcs);
        }
        merged_program.externs.push(ext);
    }

    // Mangle and push structs
    for mut s in program.structs {
        s.module_path = mod_prefix.to_vec();
        if !prefix_str.is_empty() {
            s.name = format!("{}{}", prefix_str, s.name);
        }
        for field in &mut s.fields {
            rewrite_type(&mut field.ty, &local_types, &use_aliases, &prefix_str);
        }
        merged_program.structs.push(s);
    }

    // Mangle and push enums
    for mut e in program.enums {
        e.module_path = mod_prefix.to_vec();
        if !prefix_str.is_empty() {
            e.name = format!("{}{}", prefix_str, e.name);
        }
        for v in &mut e.variants {
            for p_ty in &mut v.payload_types {
                rewrite_type(p_ty, &local_types, &use_aliases, &prefix_str);
            }
        }
        merged_program.enums.push(e);
    }

    // Mangle and push impls
    for mut i in program.impls {
        let (ref_prefix, base_target) = if let Some(rest) = i.target_type.strip_prefix("&mut ") {
            ("&mut ", rest.to_string())
        } else if let Some(rest) = i.target_type.strip_prefix('&') {
            ("&", rest.to_string())
        } else {
            ("", i.target_type.clone())
        };
        let resolved_base = if use_aliases.contains_key(&base_target) {
            use_aliases[&base_target].clone()
        } else if !prefix_str.is_empty() && local_types.contains(&base_target) {
            format!("{}{}", prefix_str, base_target)
        } else {
            base_target
        };
        i.target_type = format!("{ref_prefix}{resolved_base}");

        if let Some(t_name) = &mut i.trait_name {
            if use_aliases.contains_key(t_name) {
                *t_name = use_aliases[t_name].clone();
            } else if !prefix_str.is_empty() && local_types.contains(t_name) {
                *t_name = format!("{}{}", prefix_str, t_name);
            }
        }

        for method in &mut i.methods {
            method.module_path = mod_prefix.to_vec();
            method.is_trait_impl = i.trait_name.is_some();
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
        f.module_path = mod_prefix.to_vec();
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
        let mut sub_prefix = m.path.clone();
        if let Some(ref c) = ctx {
            if !c.root_mod_prefix.is_empty() && !sub_prefix.starts_with(c.root_mod_prefix) {
                let mut full = c.root_mod_prefix.to_vec();
                full.extend(sub_prefix);
                sub_prefix = full;
            }
            if c.bundled_mod_prefixes.contains(&sub_prefix) {
                continue;
            }
        }
        let rel_path = format!("{}.gdrs", m.path.join("/"));
        let sub_file = base_dir.join(rel_path);

        load_file_recursive_with_ctx(
            &sub_file,
            base_dir,
            &sub_prefix,
            loaded_files,
            merged_program,
            source_map,
            ctx.as_deref_mut(),
        )?;
    }

    Ok(())
}
