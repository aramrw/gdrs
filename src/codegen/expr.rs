//! codegen/expr.rs
//! Translates TypedAST expressions into Cranelift IR instructions.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

static STR_COUNTER: AtomicUsize = AtomicUsize::new(0);

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::sanal::StructLayout;

/// Recursively compiles a `TypedExpr` into a Cranelift IR `Value`.
pub fn compile_expr(
    builder: &mut FunctionBuilder,
    expr: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut JITModule,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    match expr {
        // Integer literal -> Cranelift I64 constant instruction
        TypedExpr::Int(n, _) => builder.ins().iconst(types::I64, *n),

        // Float literal -> Cranelift F64 constant instruction
        TypedExpr::Float(f, _) => builder.ins().f64const(*f),

        // Addition -> Cranelift iadd / fadd instruction
        TypedExpr::Add(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            if *ty == Type::Float {
                builder.ins().fadd(left, right)
            } else {
                builder.ins().iadd(left, right)
            }
        }

        // Subtraction -> Cranelift isub / fsub instruction
        TypedExpr::Sub(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            if *ty == Type::Float {
                builder.ins().fsub(left, right)
            } else {
                builder.ins().isub(left, right)
            }
        }

        // Multiplication -> Cranelift imul / fmul instruction
        TypedExpr::Mul(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            if *ty == Type::Float {
                builder.ins().fmul(left, right)
            } else {
                builder.ins().imul(left, right)
            }
        }

        // Division -> Cranelift sdiv / fdiv instruction
        TypedExpr::Div(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            if *ty == Type::Float {
                builder.ins().fdiv(left, right)
            } else {
                builder.ins().sdiv(left, right)
            }
        }

        TypedExpr::Pipe(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            builder.ins().bor(left, right)
        }

        TypedExpr::Ampersand(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            builder.ins().band(left, right)
        }

        TypedExpr::Caret(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            builder.ins().bxor(left, right)
        }

        TypedExpr::Shr(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            builder.ins().sshr(left, right)
        }

        TypedExpr::Shl(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            builder.ins().ishl(left, right)
        }

        // Modulo -> Cranelift srem / float modulo instruction
        TypedExpr::Mod(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            if *ty == Type::Float {
                let div = builder.ins().fdiv(left, right);
                let flr = builder.ins().floor(div);
                let mul = builder.ins().fmul(flr, right);
                builder.ins().fsub(left, mul)
            } else {
                builder.ins().srem(left, right)
            }
        }

        // Unary Negation -> Cranelift ineg / fneg instruction
        TypedExpr::Neg(val, ty, _) => {
            let inner = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
            if *ty == Type::Float {
                builder.ins().fneg(inner)
            } else {
                builder.ins().ineg(inner)
            }
        }

        // Logical NOT -> Cranelift icmp_imm(Equal, val, 0)
        TypedExpr::Not(val, _) => {
            let inner = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
            let cmp = builder.ins().icmp_imm(IntCC::Equal, inner, 0);
            builder.ins().uextend(types::I64, cmp)
        }

        // Greater Than Or Equal (>=)
        TypedExpr::GreaterEqual(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let cmp = if lhs.ty() == Type::Float {
                builder.ins().fcmp(FloatCC::GreaterThanOrEqual, left, right)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, left, right)
            };
            builder.ins().uextend(types::I64, cmp)
        }

        // Less Than Or Equal (<=)
        TypedExpr::LessEqual(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let cmp = if lhs.ty() == Type::Float {
                builder.ins().fcmp(FloatCC::LessThanOrEqual, left, right)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, left, right)
            };
            builder.ins().uextend(types::I64, cmp)
        }

        // Not Equal (!=)
        TypedExpr::NotEqual(lhs, rhs, _) => {
            let left_raw = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right_raw = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);

            let (left, right) = if let Type::Enum(_) = lhs.ty() {
                let l_tag = builder.ins().load(types::I64, MemFlags::new(), left_raw, 0);
                let r_tag = builder.ins().load(types::I64, MemFlags::new(), right_raw, 0);
                (l_tag, r_tag)
            } else {
                (left_raw, right_raw)
            };

            let cmp = if lhs.ty() == Type::Float {
                builder.ins().fcmp(FloatCC::NotEqual, left, right)
            } else {
                builder.ins().icmp(IntCC::NotEqual, left, right)
            };
            builder.ins().uextend(types::I64, cmp)
        }

        // Logical AND
        TypedExpr::And(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            builder.ins().band(left, right)
        }

        // Logical OR
        TypedExpr::Or(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            builder.ins().bor(left, right)
        }

        // Return statement
        TypedExpr::Return(opt_expr, _) => {
            let ret_val = match opt_expr {
                Some(e) => compile_expr(builder, e, vars, var_counter, module, struct_layouts),
                None => builder.ins().iconst(types::I64, 0),
            };
            builder.ins().return_(&[ret_val]);

            let dead_block = builder.create_block();
            builder.switch_to_block(dead_block);
            builder.seal_block(dead_block);

            ret_val
        }

        // If-Else Expression / Statement
        TypedExpr::IfElse(cond, then_b, else_b, ty, _) => {
            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let exit_block = builder.create_block();

            let cranelift_ty = match ty {
                Type::Float => types::F64,
                _ => types::I64,
            };
            builder.append_block_param(exit_block, cranelift_ty);

            let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
            builder
                .ins()
                .brif(cond_val, then_block, &[], else_block, &[]);

            // THEN
            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            let then_val = compile_expr(builder, then_b, vars, var_counter, module, struct_layouts);
            builder.ins().jump(exit_block, &[then_val]);

            // ELSE
            builder.switch_to_block(else_block);
            builder.seal_block(else_block);
            let else_val = compile_expr(builder, else_b, vars, var_counter, module, struct_layouts);
            builder.ins().jump(exit_block, &[else_val]);

            // EXIT
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            builder.block_params(exit_block)[0]
        }

        // Greater Than Comparison (>)
        TypedExpr::GreaterThan(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let cmp = if lhs.ty() == Type::Float {
                builder.ins().fcmp(FloatCC::GreaterThan, left, right)
            } else {
                builder.ins().icmp(IntCC::SignedGreaterThan, left, right)
            };
            builder.ins().uextend(types::I64, cmp)
        }

        // Less Than Comparison (<)
        TypedExpr::LessThan(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let cmp = if lhs.ty() == Type::Float {
                builder.ins().fcmp(FloatCC::LessThan, left, right)
            } else {
                builder.ins().icmp(IntCC::SignedLessThan, left, right)
            };
            builder.ins().uextend(types::I64, cmp)
        }

        TypedExpr::Equal(lhs, rhs, _) => {
            let left_raw = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right_raw = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);

            let (left, right) = if let Type::Enum(_) = lhs.ty() {
                let l_tag = builder.ins().load(types::I64, MemFlags::new(), left_raw, 0);
                let r_tag = builder.ins().load(types::I64, MemFlags::new(), right_raw, 0);
                (l_tag, r_tag)
            } else {
                (left_raw, right_raw)
            };

            let cmp = if lhs.ty() == Type::Float {
                builder.ins().fcmp(FloatCC::Equal, left, right)
            } else {
                builder.ins().icmp(IntCC::Equal, left, right)
            };
            builder.ins().uextend(types::I64, cmp)
        }

        // Variable Declaration -> Create variable and assign value
        TypedExpr::Let(name, _is_mutable, value, ty, _) => {
            let val = compile_expr(builder, value, vars, var_counter, module, struct_layouts);

            let var = Variable::from_u32(*var_counter as u32);
            *var_counter += 1;

            let cranelift_ty = match ty {
                Type::Float => types::F64,
                _ => types::I64,
            };
            builder.declare_var(var, cranelift_ty);

            let stored_val = match ty {
                Type::Obj(struct_name) => {
                    let total_bytes = struct_layouts.get(*struct_name).map(|l| l.total_size).unwrap_or(16);
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        if total_bytes == 0 { 8 } else { total_bytes },
                        0,
                    ));
                    let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);

                    let num_words = if total_bytes == 0 { 1 } else { (total_bytes + 7) / 8 };
                    for i in 0..num_words {
                        let offset = (i * 8) as i32;
                        let word = builder.ins().load(types::I64, MemFlags::new(), val, offset);
                        builder.ins().store(MemFlags::new(), word, dst_ptr, offset);
                    }
                    dst_ptr
                }
                Type::Str => {
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        16,
                        0,
                    ));
                    let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().store(MemFlags::new(), zero, dst_ptr, 8);
                    dst_ptr
                }
                Type::String => {
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        24,
                        0,
                    ));
                    let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().store(MemFlags::new(), zero, dst_ptr, 8);
                    builder.ins().store(MemFlags::new(), zero, dst_ptr, 16); // cap = 0 sentinel!
                    dst_ptr
                }
                Type::Slice(_) => {
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        16,
                        0,
                    ));
                    let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
                    let len_val = match value.as_ref() {
                        TypedExpr::ArrayInit(elems, _, _) => builder.ins().iconst(types::I64, elems.len() as i64),
                        _ => builder.ins().iconst(types::I64, 0),
                    };
                    builder.ins().store(MemFlags::new(), len_val, dst_ptr, 8);
                    dst_ptr
                }
                Type::Vec(_) => {
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        24,
                        0,
                    ));
                    let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    builder.ins().store(MemFlags::new(), val, dst_ptr, 0);
                    let len_val = match value.as_ref() {
                        TypedExpr::ArrayInit(elems, _, _) => builder.ins().iconst(types::I64, elems.len() as i64),
                        _ => builder.ins().iconst(types::I64, 0),
                    };
                    builder.ins().store(MemFlags::new(), len_val, dst_ptr, 8);
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().store(MemFlags::new(), zero, dst_ptr, 16); // cap = 0 sentinel!
                    dst_ptr
                }
                _ => val,
            };

            builder.def_var(var, stored_val);
            vars.insert(name.clone(), var);

            stored_val
        }

        // Variable Reassignment -> Update Cranelift variable value
        TypedExpr::Assign(name, value, _) => {
            let val = compile_expr(builder, value, vars, var_counter, module, struct_layouts);
            let var = vars.get(name).expect("Undefined variable during codegen");
            let dest_ptr = builder.use_var(*var);
            if let Type::Obj(struct_name) = value.ty() {
                if let Some(layout) = struct_layouts.get(struct_name) {
                    for i in 0..(layout.total_size / 8) {
                        let offset = (i * 8) as i32;
                        let field_val = builder.ins().load(types::I64, MemFlags::new(), val, offset);
                        builder.ins().store(MemFlags::new(), field_val, dest_ptr, offset);
                    }
                }
            } else {
                builder.def_var(*var, val);
            }
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
                last = compile_expr(builder, stmt, vars, var_counter, module, struct_layouts);
            }
            last
        }

        // Conditional If Statement
        TypedExpr::If(cond, body, _) => {
            let then_block = builder.create_block();
            let exit_block = builder.create_block();

            let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
            builder
                .ins()
                .brif(cond_val, then_block, &[], exit_block, &[]);

            // 1. THEN BLOCK
            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            compile_expr(builder, body, vars, var_counter, module, struct_layouts);
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
            let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
            builder
                .ins()
                .brif(cond_val, body_block, &[], exit_block, &[]);

            // 2. BODY BLOCK
            builder.switch_to_block(body_block);
            builder.seal_block(body_block);
            compile_expr(builder, body, vars, var_counter, module, struct_layouts);
            builder.ins().jump(header_block, &[]);

            builder.seal_block(header_block);

            // 3. EXIT BLOCK
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);

            builder.ins().iconst(types::I64, 0)
        }

        // Intrinsic Macro: name!(args...) -> Central intrinsic dispatcher
        TypedExpr::MacroCall(name, args, _) => crate::codegen::intrinsics::compile_macro_call(
            builder,
            name,
            args,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // String literal -> Allocate string data in JITModule and return pointer
        TypedExpr::String(raw_s, _) => {
            use cranelift_module::DataDescription;
            let s = raw_s.trim_matches('"');
            let mut data_ctx = DataDescription::new();
            let mut bytes = s.as_bytes().to_vec();
            bytes.push(0);
            data_ctx.define(bytes.into_boxed_slice());

            let name = format!("__str_{}", STR_COUNTER.fetch_add(1, Ordering::SeqCst));

            let data_id = module
                .declare_data(&name, Linkage::Export, true, false)
                .unwrap();
            module.define_data(data_id, &data_ctx).unwrap();

            let local_data = module.declare_data_in_func(data_id, builder.func);
            builder.ins().symbol_value(types::I64, local_data)
        }

        // Function Call -> Invoke compiled user-defined function
        TypedExpr::Call(name, args, ret_ty, _) => {
            use cranelift_codegen::ir::AbiParam;
            let mut compiled_args = Vec::new();
            let mut sig = module.make_signature();

            for arg in args {
                let compiled_arg =
                    compile_expr(builder, arg, vars, var_counter, module, struct_layouts);
                compiled_args.push(compiled_arg);
                let param_ty = match arg.ty() {
                    Type::Float => types::F64,
                    _ => types::I64,
                };
                sig.params.push(AbiParam::new(param_ty));
            }

            let ret_cranelift_ty = match ret_ty {
                Type::Float => types::F64,
                _ => types::I64,
            };
            sig.returns.push(AbiParam::new(ret_cranelift_ty));

            let callee = module
                .declare_function(name, Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &compiled_args);
            builder.inst_results(call_inst)[0]
        }

        // Boolean literal (1 for true, 0 for false)
        TypedExpr::Bool(b, _) => builder.ins().iconst(types::I64, if *b { 1 } else { 0 }),

        TypedExpr::ObjInit(_struct_name, fields, _ty, _) => {
            let slot_size = (fields.len() * 8) as u32;
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                if slot_size == 0 { 8 } else { slot_size },
                0,
            ));
            let base_ptr = builder.ins().stack_addr(types::I64, slot, 0);

            for (i, (_field_name, field_expr)) in fields.iter().enumerate() {
                let val = compile_expr(
                    builder,
                    field_expr,
                    vars,
                    var_counter,
                    module,
                    struct_layouts,
                );
                let offset = (i * 8) as i32;
                builder.ins().store(MemFlags::new(), val, base_ptr, offset);
            }

            base_ptr
        }

        TypedExpr::FieldAccess(target, field_name, field_ty, _) => {
            let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
            let mut offset = 0i32;

            if let crate::ast::Type::Obj(struct_name) = target.ty() {
                if let Some(layout) = struct_layouts.get(struct_name) {
                    if let Some((f_offset, _)) = layout.field_offsets.get(field_name) {
                        offset = *f_offset as i32;
                    }
                }
            }

            let field_cranelift_ty = match field_ty {
                Type::Float => types::F64,
                _ => types::I64,
            };

            builder
                .ins()
                .load(field_cranelift_ty, MemFlags::new(), base_ptr, offset)
        }

        TypedExpr::FieldAssign(target, field_name, val, _) => {
            let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
            let new_val = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
            let mut offset = 0i32;

            if let crate::ast::Type::Obj(struct_name) = target.ty() {
                if let Some(layout) = struct_layouts.get(struct_name) {
                    if let Some((f_offset, _)) = layout.field_offsets.get(field_name) {
                        offset = *f_offset as i32;
                    }
                }
            }

            builder
                .ins()
                .store(MemFlags::new(), new_val, base_ptr, offset);
            new_val
        }

        TypedExpr::ArrayInit(elems, _, _) => {
            let slot_bytes = (elems.len() * 8) as u32;
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                if slot_bytes == 0 { 8 } else { slot_bytes },
                0,
            ));
            let base_ptr = builder.ins().stack_addr(types::I64, slot, 0);

            for (i, elem) in elems.iter().enumerate() {
                let val = compile_expr(builder, elem, vars, var_counter, module, struct_layouts);
                let offset = (i * 8) as i32;
                builder.ins().store(MemFlags::new(), val, base_ptr, offset);
            }

            base_ptr
        }

        TypedExpr::IndexAccess(target, idx, elem_ty, _) => {
            let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
            let buffer_ptr = match target.as_ref() {
                TypedExpr::Ident(_, _, _) => match target.ty() {
                    Type::Slice(_) | Type::Vec(_) => builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0),
                    _ => base_ptr,
                },
                _ => base_ptr,
            };
            let idx_val = compile_expr(builder, idx, vars, var_counter, module, struct_layouts);
            let elem_size = builder.ins().iconst(types::I64, 8);
            let offset = builder.ins().imul(idx_val, elem_size);
            let elem_addr = builder.ins().iadd(buffer_ptr, offset);

            let cranelift_ty = match elem_ty {
                Type::Float => types::F64,
                _ => types::I64,
            };

            builder
                .ins()
                .load(cranelift_ty, MemFlags::new(), elem_addr, 0)
        }

        TypedExpr::IndexAssign(target, idx, val, _) => {
            let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
            let buffer_ptr = match target.as_ref() {
                TypedExpr::Ident(_, _, _) => match target.ty() {
                    Type::Slice(_) | Type::Vec(_) => builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0),
                    _ => base_ptr,
                },
                _ => base_ptr,
            };
            let idx_val = compile_expr(builder, idx, vars, var_counter, module, struct_layouts);
            let new_val = compile_expr(builder, val, vars, var_counter, module, struct_layouts);

            let elem_size = builder.ins().iconst(types::I64, 8);
            let offset = builder.ins().imul(idx_val, elem_size);
            let elem_addr = builder.ins().iadd(buffer_ptr, offset);

            builder.ins().store(MemFlags::new(), new_val, elem_addr, 0);
            new_val
        }

        TypedExpr::EnumConstruct(_enum_name, _variant_name, disc, payload_exprs, _ty, _) => {
            let total_bytes = ((1 + payload_exprs.len()) * 8) as u32;
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                if total_bytes == 0 { 8 } else { total_bytes },
                0,
            ));
            let base_ptr = builder.ins().stack_addr(types::I64, slot, 0);

            // Store discriminant tag at offset 0
            let disc_val = builder.ins().iconst(types::I64, *disc as i64);
            builder.ins().store(MemFlags::new(), disc_val, base_ptr, 0);

            // Store payload fields at offsets 8, 16, ...
            for (i, expr) in payload_exprs.iter().enumerate() {
                let val = compile_expr(builder, expr, vars, var_counter, module, struct_layouts);
                let offset = ((i + 1) * 8) as i32;
                builder.ins().store(MemFlags::new(), val, base_ptr, offset);
            }

            base_ptr
        }

        TypedExpr::CoerceToDyn(inner_expr, _trait_name, _) => {
            let data_ptr = compile_expr(builder, inner_expr, vars, var_counter, module, struct_layouts);
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                16,
                0,
            ));
            let fat_ptr = builder.ins().stack_addr(types::I64, slot, 0);

            // Store data pointer at offset 0
            builder.ins().store(MemFlags::new(), data_ptr, fat_ptr, 0);

            // Vtable pointer at offset 8
            let vtable_dummy = builder.ins().iconst(types::I64, 0);
            builder.ins().store(MemFlags::new(), vtable_dummy, fat_ptr, 8);

            fat_ptr
        }

        TypedExpr::DynCall(receiver_expr, method_name, args, ret_ty, _) => {
            let fat_ptr = compile_expr(builder, receiver_expr, vars, var_counter, module, struct_layouts);
            let data_ptr = builder.ins().load(types::I64, MemFlags::new(), fat_ptr, 0);

            let mut compiled_args = vec![data_ptr];
            for arg in args {
                let val = compile_expr(builder, arg, vars, var_counter, module, struct_layouts);
                compiled_args.push(val);
            }

            let type_name = match receiver_expr.as_ref() {
                TypedExpr::CoerceToDyn(inner, _, _) => inner.ty().name_or_default(),
                _ => "Button",
            };
            let func_name = format!("{}_{}", type_name, method_name);
            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64));
            for arg in args {
                let arg_ty = match arg.ty() {
                    Type::Float => types::F64,
                    _ => types::I64,
                };
                sig.params.push(AbiParam::new(arg_ty));
            }
            if *ret_ty != Type::Unit {
                let ret_c_ty = match ret_ty {
                    Type::Float => types::F64,
                    _ => types::I64,
                };
                sig.returns.push(AbiParam::new(ret_c_ty));
            }

            let callee = module
                .declare_function(&func_name, Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &compiled_args);
            if *ret_ty != Type::Unit {
                builder.inst_results(call_inst)[0]
            } else {
                builder.ins().iconst(types::I64, 0)
            }
        }
    }
}
