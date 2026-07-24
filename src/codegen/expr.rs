//! codegen/expr.rs
//! Translates TypedAST expressions into Cranelift IR instructions.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{InstBuilder, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};

use crate::ast::TypedExpr;

/// Recursively compiles a `TypedExpr` into a Cranelift IR `Value`.
pub fn compile_expr(
    builder: &mut FunctionBuilder,
    expr: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut JITModule,
) -> Value {
    match expr {
        // Integer literal -> Cranelift I64 constant instruction
        TypedExpr::Int(n, _) => builder.ins().iconst(types::I64, *n),

        // Addition -> Cranelift iadd instruction
        TypedExpr::Add(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module);
            let right = compile_expr(builder, rhs, vars, var_counter, module);
            builder.ins().iadd(left, right)
        }

        // Subtraction -> Cranelift isub instruction
        TypedExpr::Sub(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module);
            let right = compile_expr(builder, rhs, vars, var_counter, module);
            builder.ins().isub(left, right)
        }

        // Greater Than Comparison (>)
        TypedExpr::GreaterThan(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module);
            let right = compile_expr(builder, rhs, vars, var_counter, module);
            let cmp = builder.ins().icmp(IntCC::SignedGreaterThan, left, right);
            builder.ins().uextend(types::I64, cmp)
        }

        // Less Than Comparison (<)
        TypedExpr::LessThan(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module);
            let right = compile_expr(builder, rhs, vars, var_counter, module);
            let cmp = builder.ins().icmp(IntCC::SignedLessThan, left, right);
            builder.ins().uextend(types::I64, cmp)
        }

        TypedExpr::Equal(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module);
            let right = compile_expr(builder, rhs, vars, var_counter, module);
            let cmp = builder.ins().icmp(IntCC::Equal, left, right);
            builder.ins().uextend(types::I64, cmp)
        }

        // Variable Declaration -> Create variable and assign value
        TypedExpr::Let(name, _is_mutable, value, _ty, _) => {
            let val = compile_expr(builder, value, vars, var_counter, module);

            let var = Variable::from_u32(*var_counter as u32);
            *var_counter += 1;

            builder.declare_var(var, types::I64);
            builder.def_var(var, val);
            vars.insert(name.clone(), var);

            val
        }

        // Variable Reassignment -> Update Cranelift variable value
        TypedExpr::Assign(name, value, _) => {
            let val = compile_expr(builder, value, vars, var_counter, module);
            let var = vars.get(name).expect("Undefined variable during codegen");
            builder.def_var(*var, val);
            val
        }

        // Variable Lookup -> Read value from variable
        TypedExpr::Ident(name, _, _) => {
            let var = vars.get(name).expect("Undefined variable during codegen");
            builder.use_var(*var)
        }

        // Nested Block -> Evaluate statements in sequence
        TypedExpr::Block(stmts, _, _) => {
            let mut last = builder.ins().iconst(types::I64, 0);
            for stmt in stmts {
                last = compile_expr(builder, stmt, vars, var_counter, module);
            }
            last
        }

        // Conditional If Statement
        TypedExpr::If(cond, body, _) => {
            let then_block = builder.create_block();
            let exit_block = builder.create_block();

            let cond_val = compile_expr(builder, cond, vars, var_counter, module);
            builder
                .ins()
                .brif(cond_val, then_block, &[], exit_block, &[]);

            // 1. THEN BLOCK
            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            compile_expr(builder, body, vars, var_counter, module);
            builder.ins().jump(exit_block, &[]);

            // 2. EXIT BLOCK
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);

            builder.ins().iconst(types::I64, 0)
        }

        TypedExpr::While(cond, body, _) => {
            let header_block = builder.create_block();
            let body_block = builder.create_block();
            let exit_block = builder.create_block();

            builder.ins().jump(header_block, &[]);

            // 1. HEADER BLOCK
            builder.switch_to_block(header_block);
            let cond_val = compile_expr(builder, cond, vars, var_counter, module);
            builder
                .ins()
                .brif(cond_val, body_block, &[], exit_block, &[]);

            // 2. BODY BLOCK
            builder.switch_to_block(body_block);
            builder.seal_block(body_block);
            compile_expr(builder, body, vars, var_counter, module);
            builder.ins().jump(header_block, &[]);

            builder.seal_block(header_block);

            // 3. EXIT BLOCK
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);

            builder.ins().iconst(types::I64, 0)
        }

        // Intrinsic Macro: name!(args...) -> Central intrinsic dispatcher
        TypedExpr::MacroCall(name, args, _) => {
            crate::codegen::intrinsics::compile_macro_call(builder, name, args, vars, var_counter, module)
        }

        // String literal -> Allocate string data in JITModule and return pointer
        TypedExpr::String(raw_s, _) => {
            use cranelift_module::DataDescription;
            let s = raw_s.trim_matches('"');
            let mut data_ctx = DataDescription::new();
            let mut bytes = s.as_bytes().to_vec();
            bytes.push(0);
            data_ctx.define(bytes.into_boxed_slice());

            let name = format!("__str_{}", var_counter);
            *var_counter += 1;

            let data_id = module
                .declare_data(&name, Linkage::Export, true, false)
                .unwrap();
            module.define_data(data_id, &data_ctx).unwrap();

            let local_data = module.declare_data_in_func(data_id, builder.func);
            builder.ins().symbol_value(types::I64, local_data)
        }

        // Function Call -> Invoke compiled user-defined function
        TypedExpr::Call(name, args, _, _) => {
            use cranelift_codegen::ir::AbiParam;
            let mut compiled_args = Vec::new();
            for arg in args {
                compiled_args.push(compile_expr(builder, arg, vars, var_counter, module));
            }

            let mut sig = module.make_signature();
            for _ in args {
                sig.params.push(AbiParam::new(types::I64));
            }
            sig.returns.push(AbiParam::new(types::I64));

            let callee = module
                .declare_function(name, Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &compiled_args);
            builder.inst_results(call_inst)[0]
        }

        // Boolean literal (1 for true, 0 for false)
        TypedExpr::Bool(b, _) => builder.ins().iconst(types::I64, if *b { 1 } else { 0 }),
    }
}
