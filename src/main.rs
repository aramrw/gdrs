mod ast;
mod cli;
mod codegen;
mod diagnostics;
mod loader;
mod parser;
mod sanal;

use crate::cli::Cli;
use clap::Parser as ClapParser;
use std::path::Path;

fn main() {
    let cli = Cli::parse();

    for src in cli.srcs {
        let entry_path = Path::new(&src);
        let ast = match crate::loader::load_program(entry_path) {
            Ok(program) => program,
            Err(e) => {
                eprintln!("[LOAD ERROR] {}", e);
                std::process::exit(1);
            }
        };

        match crate::sanal::check_semantics(&ast) {
            Ok(typed_tree) => {
                let mut jit = crate::codegen::JitCompiler::new();
                jit.compile_and_run(&typed_tree);
            }
            Err(errors) => {
                let fstring = std::fs::read_to_string(&src).unwrap_or_default();
                crate::diagnostics::print_semantic_errors(&src, &fstring, errors);
                std::process::exit(1);
            }
        }
    }
}
