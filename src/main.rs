mod ast;
mod cli;
mod codegen;
mod diagnostics;
mod loader;
mod parser;
mod sanal;

use crate::cli::{Cli, Commands};
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
        }) => {
            compile_to_binary(&src, &output, &lib_dirs, &libs);
            println!("Successfully built standalone binary: {}", output);
        }
        Some(Commands::Run {
            src,
            lib_dirs,
            libs,
            args,
        }) => {
            build_and_run(&src, &lib_dirs, &libs, &args);
        }
        None => {
            if cli.srcs.is_empty() {
                eprintln!("Usage: gdrs run <file.gdrs> or gdrs build <file.gdrs> -o <binary>");
                std::process::exit(1);
            }
            for src in &cli.srcs {
                build_and_run(src, &cli.lib_dirs, &cli.libs, &[]);
            }
        }
    }
}

fn compile_to_binary(entry_path: &Path, output_path: &str, lib_dirs: &[String], libs: &[String]) {
    let (ast, source_map) = match crate::loader::load_program(entry_path) {
        Ok(res) => res,
        Err(e) => {
            eprintln!("[LOAD ERROR] {}", e);
            std::process::exit(1);
        }
    };

    match crate::sanal::check_semantics(&ast) {
        Ok((typed_tree, struct_layouts)) => {
            if let Err(e) = crate::codegen::object::compile_program_to_binary(
                &typed_tree,
                &struct_layouts,
                output_path,
                lib_dirs,
                libs,
                &source_map,
            ) {
                eprintln!("[BUILD ERROR] {}", e);
                std::process::exit(1);
            }
        }
        Err(errors) => {
            crate::diagnostics::print_semantic_errors(&source_map, errors);
            std::process::exit(1);
        }
    }
}

fn build_and_run(entry_path: &Path, lib_dirs: &[String], libs: &[String], args: &[String]) {
    let tmp_bin = std::env::temp_dir().join(format!("gdrs_run_{}", std::process::id()));
    let tmp_bin_str = tmp_bin.to_string_lossy().to_string();

    compile_to_binary(entry_path, &tmp_bin_str, lib_dirs, libs);

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
