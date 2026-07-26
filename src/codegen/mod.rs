//! codegen/mod.rs
//! Main entry point for Cranelift JIT code generation.

pub mod expr;
pub mod func;
pub mod intrinsics;
pub mod jit;
pub mod object;

use std::collections::HashMap;
use std::mem;

use cranelift_codegen::Context;
use cranelift_frontend::FunctionBuilderContext;
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::ast::TypedProgram;
use crate::codegen::func::compile_func;
use crate::codegen::jit::create_jit_module;
use crate::sanal::StructLayout;

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

        let mut struct_layouts = HashMap::new();
        for s in &program.structs {
            let mut total_size = 0u32;
            let mut field_offsets = HashMap::new();
            for field in &s.fields {
                field_offsets.insert(field.name.clone(), (total_size, field.ty));
                total_size += 8;
            }
            struct_layouts.insert(
                s.name.clone(),
                StructLayout {
                    name: s.name.clone(),
                    total_size,
                    field_offsets,
                },
            );
        }

        use cranelift_codegen::ir::AbiParam;
        use cranelift_module::Linkage;
        use crate::codegen::expr::cranelift_type_of;

        for func in &program.functions {
            let export_name = if func.name == "main" { "gdrs_main" } else { &func.name };
            if self.module.get_name(export_name).is_none() {
                let mut sig = self.module.make_signature();
                for param in &func.params {
                    sig.params.push(AbiParam::new(cranelift_type_of(&param.ty)));
                }
                if func.return_type != crate::ast::Type::Unit {
                    sig.returns.push(AbiParam::new(cranelift_type_of(&func.return_type)));
                }
                let _ = self.module.declare_function(export_name, Linkage::Export, &sig);
            }
        }

        for func in &program.functions {
            let code_ptr = compile_func(
                func,
                &struct_layouts,
                &mut self.module,
                &mut self.ctx,
                &mut self.builder_context,
            );
            if func.name == "main" {
                main_fn_ptr = Some(code_ptr);
            }
        }

        self.module.finalize_definitions();

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

