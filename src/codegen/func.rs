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
use crate::codegen::expr::{compile_expr, cranelift_type_of};
use crate::sanal::StructLayout;

/// Compiles a single function declaration to native machine code in the Module.
pub fn compile_func<M: Module>(
    func: &TypedFuncDecl,
    struct_layouts: &HashMap<String, StructLayout>,
    module: &mut M,
    ctx: &mut Context,
    builder_context: &mut FunctionBuilderContext,
) -> Option<cranelift_module::FuncId> {
    let export_name = if func.name == "main" { "gdrs_main" } else { &func.name };

    let mut sig = module.make_signature();
    for param in &func.params {
        sig.params.push(AbiParam::new(cranelift_type_of(&param.ty)));
    }
    let ret_cranelift_ty = cranelift_type_of(&func.return_type);
    if func.return_type != Type::Unit {
        sig.returns.push(AbiParam::new(ret_cranelift_ty));
    }

    let func_id = match module.get_name(export_name) {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        _ => module
            .declare_function(export_name, Linkage::Export, &sig)
            .unwrap(),
    };

    ctx.func.clear();
    *builder_context = FunctionBuilderContext::new();
    ctx.func.signature = sig.clone();

    let mut builder = FunctionBuilder::new(&mut ctx.func, builder_context);

    // Entry basic block
    let entry_block = builder.create_block();
    builder.switch_to_block(entry_block);
    builder.append_block_params_for_function_params(entry_block);

    let mut vars = HashMap::new();
    let mut var_counter = 0;

    // Bind function parameters to Cranelift SSA variables
    let block_params = builder.block_params(entry_block).to_vec();
    for (i, param) in func.params.iter().enumerate() {
        let var = Variable::from_u32(var_counter as u32);
        var_counter += 1;
        let param_ty = cranelift_type_of(&param.ty);
        builder.declare_var(var, param_ty);
        builder.def_var(var, block_params[i]);
        vars.insert(param.name.clone(), var);
    }

    let is_void = func.return_type == Type::Unit;

    // For non-void functions, declare a ret_var to accumulate the return value.
    let ret_var = if !is_void {
        let v = Variable::from_u32(var_counter as u32);
        var_counter += 1;
        builder.declare_var(v, ret_cranelift_ty);
        let zero = match ret_cranelift_ty {
            types::F32 => builder.ins().f32const(0.0),
            types::F64 => builder.ins().f64const(0.0),
            _ => builder.ins().iconst(ret_cranelift_ty, 0),
        };
        builder.def_var(v, zero);
        Some(v)
    } else {
        None
    };

    for expr in &func.body {
        if builder.is_unreachable() {
            break;
        }
        let val = compile_expr(&mut builder, expr, &mut vars, &mut var_counter, module, struct_layouts);
        if builder.is_unreachable() || expr_is_return(expr) {
            break;
        }
        if !builder.is_unreachable() {
            if let Some(ret_var) = ret_var {
                // Coerce the returned body value to match the function's return type.
                let val_ty = builder.func.dfg.value_type(val);
                let coerced = if val_ty == ret_cranelift_ty {
                    val
                } else {
                    match (val_ty, ret_cranelift_ty) {
                        (types::I32, types::I64) => builder.ins().sextend(types::I64, val),
                        (types::I64, types::I32) => builder.ins().ireduce(types::I32, val),
                        (types::I32, types::F32) => builder.ins().fcvt_from_sint(types::F32, val),
                        (types::I32, types::F64) => builder.ins().fcvt_from_sint(types::F64, val),
                        (types::I64, types::F32) => builder.ins().fcvt_from_sint(types::F32, val),
                        (types::I64, types::F64) => builder.ins().fcvt_from_sint(types::F64, val),
                        (types::F32, types::F64) => builder.ins().fpromote(types::F64, val),
                        (types::F64, types::F32) => builder.ins().fdemote(types::F32, val),
                        (types::F32, types::I32) => builder.ins().fcvt_to_sint(types::I32, val),
                        (types::F32, types::I64) => builder.ins().fcvt_to_sint(types::I64, val),
                        (types::F64, types::I32) => builder.ins().fcvt_to_sint(types::I32, val),
                        (types::F64, types::I64) => builder.ins().fcvt_to_sint(types::I64, val),
                        _ if val_ty.is_int() && ret_cranelift_ty.is_int() && val_ty.bits() < ret_cranelift_ty.bits() => {
                            builder.ins().sextend(ret_cranelift_ty, val)
                        }
                        _ if val_ty.is_int() && ret_cranelift_ty.is_int() && val_ty.bits() > ret_cranelift_ty.bits() => {
                            builder.ins().ireduce(ret_cranelift_ty, val)
                        }
                        _ => val,
                    }
                };
                builder.def_var(ret_var, coerced);
            }
        }
    }

fn expr_is_return(expr: &crate::ast::TypedExpr) -> bool {
    match expr {
        crate::ast::TypedExpr::Return(..) => true,
        crate::ast::TypedExpr::Block(stmts, _, _) | crate::ast::TypedExpr::Unsafe(stmts, _, _) => {
            stmts.last().map(expr_is_return).unwrap_or(false)
        }
        _ => false,
    }
}

    let is_last_ret = func.body.last().map(expr_is_return).unwrap_or(false);
    if !builder.is_unreachable() && !is_last_ret {
        if let Some(ret_var) = ret_var {
            let final_ret = builder.use_var(ret_var);
            builder.ins().return_(&[final_ret]);
        } else {
            builder.ins().return_(&[]);
        }
    }
    builder.seal_all_blocks();
    builder.finalize();

    // Declare & compile native function
    if let Err(e) = module.define_function(func_id, ctx) {
        match e {
            cranelift_module::ModuleError::DuplicateDefinition(_) => {
                module.clear_context(ctx);
                return Some(func_id);
            }
            err => panic!("define_function error: {:?}", err),
        }
    }
    module.clear_context(ctx);

    Some(func_id)
}
