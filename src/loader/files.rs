use crate::ast::*;
use crate::loader::{inject_indentation, rewrite_expr, rewrite_type};
use crate::parser::parser;
use chumsky::Parser;
use logos::Logos;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};


pub fn load_file_recursive(
    file_path: &Path,
    base_dir: &Path,
    mod_prefix: &[String],
    loaded_files: &mut HashSet<PathBuf>,
    merged_program: &mut Program,
    source_map: &mut crate::loader::SourceMap,
) -> Result<(), String> {
    let canonical = fs::canonicalize(file_path)
        .map_err(|e| format!("Failed to find module file '{}': {}", file_path.display(), e))?;

    if loaded_files.contains(&canonical) {
        return Ok(());
    }
    loaded_files.insert(canonical.clone());

    let source = fs::read_to_string(&canonical)
        .map_err(|e| format!("Failed to read file '{}': {}", canonical.display(), e))?;

    let base_offset = source_map.add_file(canonical.clone(), source.clone());

    let raw_tokens: Vec<(Token, Span)> = Token::lexer(&source)
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
            crate::diagnostics::print_syntax_errors(&canonical, &source, base_offset, errs);
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
                                let mut prefix = mod_parts.to_vec();
                                if dir.to_string_lossy().contains("std/") && prefix.first().map(|s| s.as_str()) != Some("std") {
                                    prefix.insert(0, "std".to_string());
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
                                            let pat_obj = format!("obj {sym}");
                                            let pat_enum = format!("enum {sym}");
                                            let pat_fn = format!("fn {sym}");
                                            let pat_trait = format!("trait {sym}");
                                            if content.contains(&pat_obj)
                                                || content.contains(&pat_enum)
                                                || content.contains(&pat_fn)
                                                || content.contains(&pat_trait)
                                            {
                                                let file_stem = path.file_stem().unwrap().to_string_lossy().to_string();
                                                let mut prefix = mod_parts.to_vec();
                                                if dir.to_string_lossy().contains("std/") && prefix.first().map(|s| s.as_str()) != Some("std") {
                                                    prefix.insert(0, "std".to_string());
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
            load_file_recursive(&sub_file, sub_base, &sub_prefix, loaded_files, merged_program, source_map)?;

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
        let sub_prefix = m.path.clone();
        let rel_path = format!("{}.gdrs", m.path.join("/"));
        let sub_file = base_dir.join(rel_path);

        load_file_recursive(&sub_file, base_dir, &sub_prefix, loaded_files, merged_program, source_map)?;
    }

    Ok(())
}
