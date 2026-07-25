mod ast;
mod cli;
mod codegen;
mod diagnostics;
mod loader;
mod parser;
mod sanal;

use crate::cli::{Cli, Commands};
use clap::Parser as ClapParser;
use cranelift_module::Module;
use std::path::Path;

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Some(Commands::Build { src, output }) => {
            compile_to_binary(&src, &output);
        }
        Some(Commands::Run { src, args }) => {
            crate::codegen::intrinsics::set_jit_args(args);
            jit_run(&src);
        }
        None => {
            if cli.srcs.is_empty() {
                eprintln!("Usage: gdrs run <file.gdrs> or gdrs build <file.gdrs> -o <binary>");
                std::process::exit(1);
            }
            for src in &cli.srcs {
                jit_run(src);
            }
        }
    }
}

fn jit_run(entry_path: &Path) {
    let ast = match crate::loader::load_program(entry_path) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("[LOAD ERROR] {}", e);
            std::process::exit(1);
        }
    };

    match crate::sanal::check_semantics(&ast) {
        Ok((typed_tree, struct_layouts)) => {
            let mut jit = crate::codegen::jit::create_jit_module();
            let mut ctx = jit.make_context();
            let mut builder_context = cranelift_frontend::FunctionBuilderContext::new();

            for func in &typed_tree.functions {
                crate::codegen::func::compile_func(
                    func,
                    &struct_layouts,
                    &mut jit,
                    &mut ctx,
                    &mut builder_context,
                );
            }

            jit.finalize_definitions().unwrap();
            let main_id = match jit.get_name("gdrs_main") {
                Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                _ => panic!("main function not found"),
            };
            let main_ptr = jit.get_finalized_function(main_id);
            let main_fn: extern "C" fn() = unsafe { std::mem::transmute(main_ptr) };
            main_fn();
        }
        Err(errors) => {
            let path_buf = entry_path.to_path_buf();
            let fstring = std::fs::read_to_string(entry_path).unwrap_or_default();
            crate::diagnostics::print_semantic_errors(&path_buf, &fstring, errors);
            std::process::exit(1);
        }
    }
}

fn compile_to_binary(entry_path: &Path, output_path: &str) {
    let ast = match crate::loader::load_program(entry_path) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("[LOAD ERROR] {}", e);
            std::process::exit(1);
        }
    };

    match crate::sanal::check_semantics(&ast) {
        Ok((typed_tree, struct_layouts)) => {
            match crate::codegen::object::compile_program_to_binary(
                &typed_tree,
                &struct_layouts,
                output_path,
            ) {
                Ok(_) => {
                    println!("Successfully built standalone binary: {}", output_path);
                }
                Err(e) => {
                    eprintln!("[BUILD ERROR] {}", e);
                    std::process::exit(1);
                }
            }
        }
        Err(errors) => {
            let path_buf = entry_path.to_path_buf();
            let fstring = std::fs::read_to_string(entry_path).unwrap_or_default();
            crate::diagnostics::print_semantic_errors(&path_buf, &fstring, errors);
            std::process::exit(1);
        }
    }
}
