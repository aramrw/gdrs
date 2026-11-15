pub mod ast;
pub mod cli;
pub mod codegen;
pub mod diagnostics;
pub mod loader;
pub mod parser;
pub mod rlib;
pub mod sanal;

use std::collections::HashMap;

pub fn check_source_in_memory(
    source: &str,
) -> Result<(ast::TypedProgram, HashMap<String, sanal::StructLayout>, loader::SourceMap), String> {
    let (program, source_map) = loader::load_program_from_str(source, true)?;
    let (typed_program, struct_layouts) = sanal::check_semantics(&program).map_err(|errs| {
        errs.into_iter()
            .map(|e| format!("[{}] {}", e.code, e.message))
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    Ok((typed_program, struct_layouts, source_map))
}

pub fn compile_source_in_memory(source: &str) -> Result<Vec<u8>, String> {
    let (typed_program, struct_layouts, source_map) = check_source_in_memory(source)?;
    codegen::object::compile_program_to_object_bytes(&typed_program, &struct_layouts, &source_map)
}
