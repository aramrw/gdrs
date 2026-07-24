//! codegen/func.rs
//! Translates TypedAST function declarations into native compiled functions using Cranelift JIT.

use std::collections::HashMap;

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};

use crate::ast::TypedFuncDecl;
use crate::codegen::expr::compile_expr;

/// Compiles a single function declaration to native machine code in the JITModule.
pub fn compile_func(
    func: &TypedFuncDecl,
    module: &mut JITModule,
    ctx: &mut Context,
    builder_context: &mut FunctionBuilderContext,
) -> *const u8 {
    ctx.func.clear();
    ctx.func.signature = module.make_signature();

    // Add parameter signatures to Cranelift function
    for _param in &func.params {
        ctx.func.signature.params.push(AbiParam::new(types::I64));
    }

    // Return type for our compiled function: i64 integer
    ctx.func.signature.returns.push(AbiParam::new(types::I64));

    let mut builder = FunctionBuilder::new(&mut ctx.func, builder_context);

    // Entry basic block
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    builder.seal_block(entry_block);

    let mut vars = HashMap::new();
    let mut var_counter = 0;

    // Bind function parameters to Cranelift SSA variables
    let block_params = builder.block_params(entry_block).to_vec();
    for (i, param) in func.params.iter().enumerate() {
        let var = Variable::from_u32(var_counter as u32);
        var_counter += 1;
        builder.declare_var(var, types::I64);
        builder.def_var(var, block_params[i]);
        vars.insert(param.name.clone(), var);
    }

    let ret_var = Variable::from_u32(var_counter as u32);
    var_counter += 1;
    builder.declare_var(ret_var, types::I64);

    let zero = builder.ins().iconst(types::I64, 0);
    builder.def_var(ret_var, zero);

    for expr in &func.body {
        let val = compile_expr(&mut builder, expr, &mut vars, &mut var_counter, module);
        builder.def_var(ret_var, val);
    }

    // Return the result of the last statement cleanly across blocks
    let final_ret = builder.use_var(ret_var);
    builder.ins().return_(&[final_ret]);

    builder.finalize();

    // Declare & compile native function
    let func_id = module
        .declare_function(&func.name, Linkage::Export, &ctx.func.signature)
        .unwrap();

    module.define_function(func_id, ctx).unwrap();
    module.clear_context(ctx);
    module.finalize_definitions().unwrap();

    module.get_finalized_function(func_id)
}
