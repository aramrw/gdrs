//! codegen/func.rs
//! Translates TypedAST function declarations into native compiled functions using Cranelift JIT.

use std::collections::HashMap;

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedFuncDecl};
use crate::codegen::expr::compile_expr;
use crate::sanal::StructLayout;

/// Compiles a single function declaration to native machine code in the JITModule.
pub fn compile_func(
    func: &TypedFuncDecl,
    struct_layouts: &HashMap<String, StructLayout>,
    module: &mut JITModule,
    ctx: &mut Context,
    builder_context: &mut FunctionBuilderContext,
) -> *const u8 {
    ctx.func.clear();
    ctx.func.signature = module.make_signature();

    // Add parameter signatures to Cranelift function
    for param in &func.params {
        let param_ty = match param.ty {
            Type::Float => types::F64,
            _ => types::I64,
        };
        ctx.func.signature.params.push(AbiParam::new(param_ty));
    }

    // --- FIX 1: Handle Type::Unit for Void Returns ---
    match func.return_type {
        Type::Float => {
            ctx.func.signature.returns.push(AbiParam::new(types::F64));
        }
        Type::Unit => {
            // Void return: signature.returns remains empty ([])
        }
        _ => {
            ctx.func.signature.returns.push(AbiParam::new(types::I64));
        }
    }

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
        let param_ty = match param.ty {
            Type::Float => types::F64,
            _ => types::I64,
        };
        builder.declare_var(var, param_ty);
        builder.def_var(var, block_params[i]);
        vars.insert(param.name.clone(), var);
    }

    let ret_var = Variable::from_u32(var_counter as u32);
    var_counter += 1;

    // Only declare and initialize ret_var if function actually returns a value
    if func.return_type != Type::Unit {
        let ret_cranelift_ty = match func.return_type {
            Type::Float => types::F64,
            _ => types::I64,
        };
        builder.declare_var(ret_var, ret_cranelift_ty);

        let zero = match func.return_type {
            Type::Float => builder.ins().f64const(0.0),
            _ => builder.ins().iconst(types::I64, 0),
        };
        builder.def_var(ret_var, zero);
    }

    for expr in &func.body {
        let val = compile_expr(&mut builder, expr, &mut vars, &mut var_counter, module, struct_layouts);
        if !builder.is_unreachable() && func.return_type != Type::Unit {
            builder.def_var(ret_var, val);
        }
    }

    // --- FIX 2: Return empty slice for Type::Unit ---
    if !builder.is_unreachable() {
        if func.return_type == Type::Unit {
            builder.ins().return_(&[]);
        } else {
            let final_ret = builder.use_var(ret_var);
            builder.ins().return_(&[final_ret]);
        }
    }

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
