use gdrs::{cli, codegen, diagnostics, loader, rlib, sanal};

use crate::cli::{Cli, Commands, CrateFlags, CrateType};
use crate::codegen::object::{CompileOptions, OptLevel};
use crate::loader::LoadCrateOptions;
use clap::Parser as ClapParser;
use std::path::Path;
use std::process::Command;

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Some(Commands::Build {
            src,
            output,
            lib_dirs,
            libs,
            opt,
            crate_flags,
        }) => {
            compile_artifact(&src, output.as_deref(), &lib_dirs, &libs, opt.resolved(), &crate_flags);
        }
        Some(Commands::Run {
            src,
            lib_dirs,
            libs,
            opt,
            crate_flags,
            args,
        }) => {
            if crate_flags.crate_type != CrateType::Bin {
                eprintln!("[CLI ERROR] `gdrs run` only supports `--crate-type bin`");
                std::process::exit(1);
            }
            build_and_run(&src, &lib_dirs, &libs, opt.resolved(), &crate_flags, &args);
        }
        Some(Commands::Check { src, crate_flags }) => {
            check_program(src.as_deref(), &crate_flags);
        }
        None => {
            if cli.srcs.is_empty() {
                eprintln!("Usage: gdrs run <file.gdrs> or gdrs build <file.gdrs> -o <binary>");
                std::process::exit(1);
            }
            if cli.crate_flags.crate_type != CrateType::Bin {
                eprintln!("[CLI ERROR] Direct execution only supports `--crate-type bin`");
                std::process::exit(1);
            }
            let opt_level = cli.opt.resolved();
            for src in &cli.srcs {
                build_and_run(src, &cli.lib_dirs, &cli.libs, opt_level, &cli.crate_flags, &[]);
            }
        }
    }
}

fn build_load_options(entry_path: Option<&Path>, crate_flags: &CrateFlags) -> LoadCrateOptions {
    let crate_name = crate_flags.resolve_crate_name(entry_path);
    let root_mod_prefix = if crate_flags.crate_type == CrateType::Bin {
        Vec::new()
    } else {
        vec![crate_name.clone()]
    };
    let externs = crate_flags
        .externs
        .iter()
        .map(|e| (e.alias.clone(), e.path.clone()))
        .collect();
    LoadCrateOptions {
        crate_name: Some(crate_name),
        root_mod_prefix,
        externs,
    }
}

fn ensure_parent_dir(path: &Path) {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            if let Err(e) = std::fs::create_dir_all(parent) {
                eprintln!("[BUILD ERROR] Failed to create output directory '{}': {}", parent.display(), e);
                std::process::exit(1);
            }
        }
    }
}

fn check_program(entry_path: Option<&Path>, crate_flags: &CrateFlags) {
    let dummy_path = std::env::temp_dir().join(format!("gdrs_check_std_{}.gdrs", std::process::id()));
    let (target_path, cleanup) = match entry_path {
        Some(p) => (p.to_path_buf(), false),
        None => {
            let _ = std::fs::write(&dummy_path, "");
            (dummy_path.clone(), true)
        }
    };

    let load_opts = build_load_options(entry_path, crate_flags);
    let loaded = match crate::loader::load_program_with_options(&target_path, &load_opts) {
        Ok(res) => res,
        Err(e) => {
            if cleanup {
                let _ = std::fs::remove_file(&dummy_path);
            }
            eprintln!("[LOAD ERROR] {}", e);
            std::process::exit(1);
        }
    };
    if cleanup {
        let _ = std::fs::remove_file(&dummy_path);
    }

    match crate::sanal::check_semantics(&loaded.program) {
        Ok(_) => match entry_path {
            Some(p) => println!("Check passed: {}", p.display()),
            None => println!("Check passed: std/"),
        },
        Err(errors) => {
            crate::diagnostics::print_semantic_errors(&loaded.source_map, errors);
            std::process::exit(1);
        }
    }
}

fn merge_unique_flags(primary: &[String], extra: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for item in primary.iter().chain(extra.iter()) {
        if !out.contains(item) {
            out.push(item.clone());
        }
    }
    out
}

fn compile_artifact(
    entry_path: &Path,
    explicit_output: Option<&str>,
    lib_dirs: &[String],
    libs: &[String],
    opt_level: OptLevel,
    crate_flags: &CrateFlags,
) {
    let (emit_obj, emit_link) = match crate_flags.emit_kinds() {
        Ok(kinds) => kinds,
        Err(e) => {
            eprintln!("[CLI ERROR] {}", e);
            std::process::exit(1);
        }
    };

    let load_opts = build_load_options(Some(entry_path), crate_flags);
    let loaded = match crate::loader::load_program_with_options(entry_path, &load_opts) {
        Ok(res) => res,
        Err(e) => {
            eprintln!("[LOAD ERROR] {}", e);
            std::process::exit(1);
        }
    };

    let (typed_tree, struct_layouts) = match crate::sanal::check_semantics(&loaded.program) {
        Ok(res) => res,
        Err(errors) => {
            crate::diagnostics::print_semantic_errors(&loaded.source_map, errors);
            std::process::exit(1);
        }
    };

    let crate_name = crate_flags.resolve_crate_name(Some(entry_path));
    let opts = CompileOptions {
        opt_level,
        crate_type: crate_flags.crate_type,
        extra_objects: loaded.extern_objects,
    };

    if emit_obj {
        let obj_path = crate_flags.resolve_obj_output(entry_path, explicit_output, emit_link);
        ensure_parent_dir(&obj_path);
        match crate::codegen::object::compile_program_to_object_bytes_with_options(
            &typed_tree,
            &struct_layouts,
            &loaded.source_map,
            &opts,
        ) {
            Ok(bytes) => {
                if let Err(e) = std::fs::write(&obj_path, bytes) {
                    eprintln!("[BUILD ERROR] Failed to write object '{}': {}", obj_path.display(), e);
                    std::process::exit(1);
                }
                println!("Successfully built object file: {}", obj_path.display());
            }
            Err(e) => {
                eprintln!("[BUILD ERROR] {}", e);
                std::process::exit(1);
            }
        }
    }

    if !emit_link {
        return;
    }

    let out_path = crate_flags.resolve_build_output(entry_path, explicit_output);
    ensure_parent_dir(&out_path);
    let out_str = out_path.to_string_lossy().to_string();

    let merged_lib_dirs = merge_unique_flags(lib_dirs, &loaded.extern_lib_dirs);
    let merged_libs = merge_unique_flags(libs, &loaded.extern_libs);

    match crate_flags.crate_type {
        CrateType::Bin => {
            if let Err(e) = crate::codegen::object::compile_program_to_binary_with_options(
                &typed_tree,
                &struct_layouts,
                &out_str,
                &merged_lib_dirs,
                &merged_libs,
                &loaded.source_map,
                &opts,
            ) {
                eprintln!("[BUILD ERROR] {}", e);
                std::process::exit(1);
            }
            println!("Successfully built standalone binary: {}", out_str);
        }
        CrateType::Lib => {
            let object_bytes = match crate::codegen::object::compile_program_to_object_bytes_with_options(
                &typed_tree,
                &struct_layouts,
                &loaded.source_map,
                &opts,
            ) {
                Ok(bytes) => bytes,
                Err(e) => {
                    eprintln!("[BUILD ERROR] {}", e);
                    std::process::exit(1);
                }
            };
            let pkg = rlib::RlibPackage {
                crate_name,
                extern_aliases: loaded.extern_alias_pairs,
                lib_dirs: merged_lib_dirs,
                libs: merged_libs,
                sources: loaded.crate_sources,
                object_bytes,
            };
            let encoded = rlib::encode_rlib(&pkg);
            if let Err(e) = std::fs::write(&out_path, encoded) {
                eprintln!("[BUILD ERROR] Failed to write .rlib '{}': {}", out_str, e);
                std::process::exit(1);
            }
            println!("Successfully built rlib library: {}", out_str);
        }
        CrateType::StaticLib => {
            let object_bytes = match crate::codegen::object::compile_program_to_object_bytes_with_options(
                &typed_tree,
                &struct_layouts,
                &loaded.source_map,
                &opts,
            ) {
                Ok(bytes) => bytes,
                Err(e) => {
                    eprintln!("[BUILD ERROR] {}", e);
                    std::process::exit(1);
                }
            };
            if let Err(e) =
                crate::codegen::object::write_staticlib_archive(&object_bytes, &crate_name, &out_str)
            {
                eprintln!("[BUILD ERROR] {}", e);
                std::process::exit(1);
            }
            println!("Successfully built staticlib archive: {}", out_str);
        }
    }
}

fn build_and_run(
    entry_path: &Path,
    lib_dirs: &[String],
    libs: &[String],
    opt_level: OptLevel,
    crate_flags: &CrateFlags,
    args: &[String],
) {
    let tmp_bin = std::env::temp_dir().join(format!("gdrs_run_{}", std::process::id()));
    let tmp_bin_str = tmp_bin.to_string_lossy().to_string();

    let load_opts = build_load_options(Some(entry_path), crate_flags);
    let loaded = match crate::loader::load_program_with_options(entry_path, &load_opts) {
        Ok(res) => res,
        Err(e) => {
            eprintln!("[LOAD ERROR] {}", e);
            std::process::exit(1);
        }
    };
    let (typed_tree, struct_layouts) = match crate::sanal::check_semantics(&loaded.program) {
        Ok(res) => res,
        Err(errors) => {
            crate::diagnostics::print_semantic_errors(&loaded.source_map, errors);
            std::process::exit(1);
        }
    };
    let opts = CompileOptions {
        opt_level,
        crate_type: CrateType::Bin,
        extra_objects: loaded.extern_objects,
    };
    let merged_lib_dirs = merge_unique_flags(lib_dirs, &loaded.extern_lib_dirs);
    let merged_libs = merge_unique_flags(libs, &loaded.extern_libs);
    if let Err(e) = crate::codegen::object::compile_program_to_binary_with_options(
        &typed_tree,
        &struct_layouts,
        &tmp_bin_str,
        &merged_lib_dirs,
        &merged_libs,
        &loaded.source_map,
        &opts,
    ) {
        eprintln!("[BUILD ERROR] {}", e);
        std::process::exit(1);
    }

    let status = Command::new(&tmp_bin).args(args).status();

    let _ = std::fs::remove_file(&tmp_bin);

    match status {
        Ok(s) => {
            if !s.success() {
                std::process::exit(s.code().unwrap_or(1));
            }
        }
        Err(e) => {
            eprintln!("[RUN ERROR] Failed to execute built binary: {}", e);
            std::process::exit(1);
        }
    }
}
