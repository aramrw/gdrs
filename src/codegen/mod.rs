//! codegen/mod.rs
//! Main entry point for Cranelift JIT code generation.

pub mod expr;
pub mod func;
pub mod intrinsics;
pub mod jit;

use std::mem;

use cranelift_codegen::Context;
use cranelift_frontend::FunctionBuilderContext;
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::ast::TypedProgram;
use crate::codegen::func::compile_func;
use crate::codegen::jit::create_jit_module;

pub struct JitCompiler {
    builder_context: FunctionBuilderContext,
    ctx: Context,
    module: JITModule,
}

impl JitCompiler {
    pub fn new() -> Self {
        let module = create_jit_module();
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            module,
        }
    }

    /// Compiles a `TypedProgram` and executes the `main()` function natively in memory.
    pub fn compile_and_run(&mut self, program: &TypedProgram) -> i64 {
        let mut main_fn_ptr = None;

        for func in &program.functions {
            let code_ptr = compile_func(
                func,
                &mut self.module,
                &mut self.ctx,
                &mut self.builder_context,
            );
            if func.name == "main" {
                main_fn_ptr = Some(code_ptr);
            }
        }

        if let Some(ptr) = main_fn_ptr {
            unsafe {
                let code_fn: extern "C" fn() -> i64 = mem::transmute(ptr);
                code_fn()
            }
        } else {
            panic!("No main function found to execute");
        }
    }
}
