use std::collections::HashMap;
use std::fs;
use std::process::Command;

use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_module::{default_libcall_names, Module};
use cranelift_native::builder as native_builder;
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::ast::TypedProgram;
use crate::codegen::func::compile_func;
use crate::sanal::StructLayout;

pub const RUNTIME_C_SOURCE: &str = include_str!("runtime.c");

pub fn compile_program_to_binary(
    program: &TypedProgram,
    struct_layouts: &HashMap<String, StructLayout>,
    output_binary_path: &str,
) -> Result<(), String> {
    let mut flag_builder = settings::builder();
    flag_builder.set("is_pic", "true").map_err(|e| format!("Setting is_pic error: {}", e))?;
    let isa_builder = native_builder().map_err(|e| format!("Host target architecture error: {}", e))?;
    let target_isa = isa_builder.finish(Flags::new(flag_builder)).map_err(|e| format!("Target ISA error: {}", e))?;

    let object_builder = ObjectBuilder::new(target_isa, "gdrs_app", default_libcall_names())
        .map_err(|e| format!("ObjectBuilder error: {}", e))?;

    let mut module = ObjectModule::new(object_builder);
    let mut ctx = module.make_context();
    let mut builder_context = cranelift_frontend::FunctionBuilderContext::new();

    // Compile all functions into the ObjectModule
    for func in &program.functions {
        compile_func(
            func,
            struct_layouts,
            &mut module,
            &mut ctx,
            &mut builder_context,
        );
    }

    // Finish object generation
    let product = module.finish();
    let object_bytes = product.emit().map_err(|e| format!("Failed to emit object bytes: {}", e))?;

    let temp_dir = std::env::temp_dir();
    let obj_path = temp_dir.join("gdrs_main.o");
    let runtime_c_path = temp_dir.join("gdrs_runtime.c");

    fs::write(&obj_path, object_bytes).map_err(|e| format!("Failed to write object file: {}", e))?;
    fs::write(&runtime_c_path, RUNTIME_C_SOURCE).map_err(|e| format!("Failed to write runtime C source: {}", e))?;

    // Link into native executable via clang
    let clang_output = Command::new("clang")
        .args([
            obj_path.to_str().unwrap(),
            runtime_c_path.to_str().unwrap(),
            "-o",
            output_binary_path,
            "-lpthread",
        ])
        .output()
        .map_err(|e| format!("Failed to execute clang linker: {}", e))?;

    if !clang_output.status.success() {
        return Err(format!("clang linking failed:\n{}", String::from_utf8_lossy(&clang_output.stderr)));
    }

    Ok(())
}
