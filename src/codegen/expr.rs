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

/// True for any floating-point Type variant.
#[inline]
fn is_float_ty(ty: &Type) -> bool {
    matches!(ty, Type::Float | Type::F32)
}

#[inline]
fn is_float_val(builder: &FunctionBuilder, val: Value) -> bool {
    builder.func.dfg.value_type(val).is_float()
}

/// True for any integer Type variant.
#[inline]
fn is_int_ty(ty: &Type) -> bool {
    matches!(ty, Type::Int | Type::I32)
}

/// Map a gdrs Type to the correct Cranelift scalar type.
#[inline]
pub fn cranelift_type_of(ty: &Type) -> cranelift_codegen::ir::Type {
    match ty {
        Type::I32 => types::I32,
        Type::Int => types::I64,
        Type::F32 => types::F32,
        Type::Float => types::F64,
        Type::Bool => types::I8,
        _ => types::I64, // pointers / heap handles
    }
}

/// Widen two operand Values so they share the same Cranelift type before
/// emitting a binary instruction. Follows Rust promotion rules:
///   i32 + i64  → both i64
///   f32 + f64  → both f64
///   int + float → both float (using the wider float)
fn coerce_operands(
    builder: &mut FunctionBuilder,
    mut lhs: Value,
    mut rhs: Value,
) -> (Value, Value) {
    let lt = builder.func.dfg.value_type(lhs);
    let rt = builder.func.dfg.value_type(rhs);
    if lt == rt {
        return (lhs, rhs);
    }
    match (lt, rt) {
        // int widening
        (types::I32, types::I64) => {
            lhs = builder.ins().sextend(types::I64, lhs);
        }
        (types::I64, types::I32) => {
            rhs = builder.ins().sextend(types::I64, rhs);
        }
        // float widening
        (types::F32, types::F64) => {
            lhs = builder.ins().fpromote(types::F64, lhs);
        }
        (types::F64, types::F32) => {
            rhs = builder.ins().fpromote(types::F64, rhs);
        }
        // int-to-float promotion
        (types::I32, types::F32) => {
            lhs = builder.ins().fcvt_from_sint(types::F32, lhs);
        }
        (types::F32, types::I32) => {
            rhs = builder.ins().fcvt_from_sint(types::F32, rhs);
        }
        (types::I32, types::F64) => {
            lhs = builder.ins().fcvt_from_sint(types::F64, lhs);
        }
        (types::F64, types::I32) => {
            rhs = builder.ins().fcvt_from_sint(types::F64, rhs);
        }
        (types::I64, types::F64) => {
            lhs = builder.ins().fcvt_from_sint(types::F64, lhs);
        }
        (types::F64, types::I64) => {
            rhs = builder.ins().fcvt_from_sint(types::F64, rhs);
        }
        (types::I64, types::F32) => {
            lhs = builder.ins().fcvt_from_sint(types::F32, lhs);
        }
        (types::F32, types::I64) => {
            rhs = builder.ins().fcvt_from_sint(types::F32, rhs);
        }
        _ => {}
    }
    (lhs, rhs)
}

/// Recursively compiles a `TypedExpr` into a Cranelift IR `Value`.
pub fn compile_expr<M: Module>(
    builder: &mut FunctionBuilder,
    expr: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    match expr {
        // Integer literal — emits I32 if fits, I64 if the value exceeds i32 range.
        // The Let codegen widens I32 to I64 when needed via sextend.
        TypedExpr::Int(n, _) => {
            if *n >= i32::MIN as i64 && *n <= i32::MAX as i64 {
                builder.ins().iconst(types::I32, *n)
            } else {
                builder.ins().iconst(types::I64, *n)
            }
        }

        // Float literal — emits F32 by default (promoted by Let codegen if needed)
        TypedExpr::Float(f, _) => builder.ins().f32const(*f as f32),

        // Addition -> Cranelift iadd / fadd instruction
        TypedExpr::Add(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            if is_float_ty(ty) || is_float_val(builder, left) {
                builder.ins().fadd(left, right)
            } else {
                builder.ins().iadd(left, right)
            }
        }

        // Subtraction -> Cranelift isub / fsub instruction
        TypedExpr::Sub(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            if is_float_ty(ty) || is_float_val(builder, left) {
                builder.ins().fsub(left, right)
            } else {
                builder.ins().isub(left, right)
            }
        }

        // Multiplication -> Cranelift imul / fmul instruction
        TypedExpr::Mul(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            if is_float_ty(ty) || is_float_val(builder, left) {
                builder.ins().fmul(left, right)
            } else {
                builder.ins().imul(left, right)
            }
        }

        // Division -> Cranelift sdiv / fdiv instruction
        TypedExpr::Div(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            if is_float_ty(ty) || is_float_val(builder, left) {
                builder.ins().fdiv(left, right)
            } else {
                builder.ins().sdiv(left, right)
            }
        }

        TypedExpr::Pipe(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            builder.ins().bor(left, right)
        }

        TypedExpr::Ampersand(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            builder.ins().band(left, right)
        }

        TypedExpr::Caret(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            builder.ins().bxor(left, right)
        }

        TypedExpr::Shr(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            builder.ins().sshr(left, right)
        }

        TypedExpr::Shl(lhs, rhs, _, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            builder.ins().ishl(left, right)
        }

        // Modulo -> Cranelift srem / float modulo instruction
        TypedExpr::Mod(lhs, rhs, ty, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            if is_float_ty(ty) || is_float_val(builder, left) {
                let div = builder.ins().fdiv(left, right);
                let flr = builder.ins().floor(div);
                let mul = builder.ins().fmul(flr, right);
                builder.ins().fsub(left, mul)
            } else {
                builder.ins().srem(left, right)
            }
        }

        // Unary Negation
        TypedExpr::Neg(val, ty, _) => {
            let inner = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
            if is_float_ty(ty) || is_float_val(builder, inner) {
                builder.ins().fneg(inner)
            } else {
                builder.ins().ineg(inner)
            }
        }

        // Logical NOT
        TypedExpr::Not(val, _) => {
            let inner = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
            let cmp = builder.ins().icmp_imm(IntCC::Equal, inner, 0);
            builder.ins().uextend(types::I64, cmp)
        }

        // Greater Than Or Equal (>=)
        TypedExpr::GreaterEqual(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
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
            let (left, right) = coerce_operands(builder, left, right);
            let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
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
                let r_tag = builder
                    .ins()
                    .load(types::I64, MemFlags::new(), right_raw, 0);
                (l_tag, r_tag)
            } else {
                coerce_operands(builder, left_raw, right_raw)
            };

            let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
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
            if let Some(e) = opt_expr {
                let ret_val = compile_expr(builder, e, vars, var_counter, module, struct_layouts);
                builder.ins().return_(&[ret_val]);
            } else {
                // Bare `return` — void return (no value)
                builder.ins().return_(&[]);
            }
            // Unreachable dead block to satisfy Cranelift's "every block must be filled" invariant
            let dead_block = builder.create_block();
            builder.switch_to_block(dead_block);
            builder.seal_block(dead_block);

            // Emit a tombstone value so the block has a usable result, then trap to fill it
            let tombstone = builder.ins().iconst(types::I64, 0);
            builder
                .ins()
                .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
            tombstone
        }

        // Greater Than Comparison (>)
        TypedExpr::GreaterThan(lhs, rhs, _) => {
            let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
            let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
            let (left, right) = coerce_operands(builder, left, right);
            let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
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
            let (left, right) = coerce_operands(builder, left, right);
            let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
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
                let r_tag = builder
                    .ins()
                    .load(types::I64, MemFlags::new(), right_raw, 0);
                (l_tag, r_tag)
            } else {
                coerce_operands(builder, left_raw, right_raw)
            };

            let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
                builder.ins().fcmp(FloatCC::Equal, left, right)
            } else {
                builder.ins().icmp(IntCC::Equal, left, right)
            };
            builder.ins().uextend(types::I64, cmp)
        }

        // Variable Declaration -> Create variable and assign value
        TypedExpr::Let(name, _is_mutable, value, ty, _) => {
            let mut val = compile_expr(builder, value, vars, var_counter, module, struct_layouts);

            let var = Variable::from_u32(*var_counter as u32);
            *var_counter += 1;

            // Map gdrs Type to the precise Cranelift type
            let cranelift_ty = cranelift_type_of(ty);

            builder.declare_var(var, cranelift_ty);

            // Coerce: widen or convert the value if the literal type != declared type
            let val_ty = builder.func.dfg.value_type(val);
            if val_ty != cranelift_ty {
                val = match (val_ty, cranelift_ty) {
                    // i32 literal widened to i64 variable
                    (types::I32, types::I64) => builder.ins().sextend(types::I64, val),
                    // i64 narrowed to i32 variable (explicit annotation)
                    (types::I64, types::I32) => builder.ins().ireduce(types::I32, val),
                    // i32 int to f32
                    (types::I32, types::F32) => builder.ins().fcvt_from_sint(types::F32, val),
                    // i32 int to f64
                    (types::I32, types::F64) => builder.ins().fcvt_from_sint(types::F64, val),
                    // i64 int to f32
                    (types::I64, types::F32) => builder.ins().fcvt_from_sint(types::F32, val),
                    // i64 int to f64
                    (types::I64, types::F64) => builder.ins().fcvt_from_sint(types::F64, val),
                    // f32 widened to f64
                    (types::F32, types::F64) => builder.ins().fpromote(types::F64, val),
                    // f64 demoted to f32 (explicit annotation)
                    (types::F64, types::F32) => builder.ins().fdemote(types::F32, val),
                    _ => val,
                };
            }

            // 3. Handle stack slot layouts for composite types (Obj, Str, Vec, etc.)
            let stored_val = match ty {
                Type::Obj(struct_name) => {
                    let total_bytes = struct_layouts
                        .get(*struct_name)
                        .map(|l| l.total_size)
                        .unwrap_or(16);
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        if total_bytes == 0 { 8 } else { total_bytes },
                        0,
                    ));
                    let dst_ptr = builder.ins().stack_addr(types::I64, slot, 0);

                    let num_words = if total_bytes == 0 {
                        1
                    } else {
                        (total_bytes + 7) / 8
                    };
                    for i in 0..num_words {
                        let offset = (i * 8) as i32;
                        let word = builder.ins().load(types::I64, MemFlags::new(), val, offset);
                        builder.ins().store(MemFlags::new(), word, dst_ptr, offset);
                    }
                    dst_ptr
                }
                Type::Str => val,

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
                    builder.ins().store(MemFlags::new(), zero, dst_ptr, 16);
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
                        TypedExpr::ArrayInit(elems, _, _) => {
                            builder.ins().iconst(types::I64, elems.len() as i64)
                        }
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
                        TypedExpr::ArrayInit(elems, _, _) => {
                            builder.ins().iconst(types::I64, elems.len() as i64)
                        }
                        _ => builder.ins().iconst(types::I64, 0),
                    };
                    builder.ins().store(MemFlags::new(), len_val, dst_ptr, 8);
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().store(MemFlags::new(), zero, dst_ptr, 16);
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
            let mut val = compile_expr(builder, value, vars, var_counter, module, struct_layouts);
            let var = vars.get(name).expect("Undefined variable during codegen");
            let dest_ptr = builder.use_var(*var);

            if let Type::Obj(struct_name) = value.ty() {
                if let Some(layout) = struct_layouts.get(struct_name) {
                    for i in 0..(layout.total_size / 8) {
                        let offset = (i * 8) as i32;
                        let field_val =
                            builder.ins().load(types::I64, MemFlags::new(), val, offset);
                        builder
                            .ins()
                            .store(MemFlags::new(), field_val, dest_ptr, offset);
                    }
                }
            } else {
                // Use dest_ptr (Value) with value_type() instead of *var (Variable)
                let var_ty = builder.func.dfg.value_type(dest_ptr);
                let val_ty = builder.func.dfg.value_type(val);

                if val_ty != var_ty {
                    val = match (val_ty, var_ty) {
                        (types::I64, types::I32) => builder.ins().ireduce(types::I32, val),
                        (types::I32, types::I64) => builder.ins().sextend(types::I64, val),
                        (types::F64, types::F32) => builder.ins().fdemote(types::F32, val),
                        (types::F32, types::F64) => builder.ins().fpromote(types::F64, val),
                        _ => val,
                    };
                }

                builder.def_var(*var, val);
            }
            val
        }
        // Variable or Function Pointer Lookup
        TypedExpr::Ident(name, _, _) => {
            if let Some(var) = vars.get(name) {
                builder.use_var(*var)
            } else {
                if let Ok(c_name) = std::ffi::CString::new(name.as_str()) {
                    let p = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_name.as_ptr()) };
                    if !p.is_null() {
                        return builder.ins().iconst(types::I64, p as i64);
                    }
                }
                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                let callee = match module.get_name(name) {
                    Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                    _ => module
                        .declare_function(name, Linkage::Export, &sig)
                        .unwrap(),
                };
                let local_callee = module.declare_func_in_func(callee, builder.func);
                builder.ins().func_addr(types::I64, local_callee)
            }
        }

        TypedExpr::Return(opt_expr, _) => {
            let ret_val = if let Some(expr) = opt_expr {
                compile_expr(builder, expr, vars, var_counter, module, struct_layouts)
            } else {
                builder.ins().iconst(types::I64, 0)
            };
            builder.ins().return_(&[ret_val]);
            ret_val
        }

        // Nested Block -> Evaluate statements in sequence
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            let mut last = builder.ins().iconst(types::I64, 0);
            for stmt in stmts {
                if builder.is_unreachable() {
                    break;
                }
                last = compile_expr(builder, stmt, vars, var_counter, module, struct_layouts);
            }
            last
        }

        // Conditional If Statement
        // If Statement (no else)
        TypedExpr::If(cond, body, _) => {
            let then_block = builder.create_block();
            let exit_block = builder.create_block();

            let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
            builder
                .ins()
                .brif(cond_val, then_block, &[], exit_block, &[]);

            // THEN BLOCK
            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            compile_expr(builder, body, vars, var_counter, module, struct_layouts);
            if !builder.is_unreachable() {
                builder.ins().jump(exit_block, &[]);
            }

            // EXIT BLOCK
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);

            builder.ins().iconst(types::I64, 0)
        }

        // If-Else Expression / Statement
        TypedExpr::IfElse(cond, then_b, else_b, ty, _) => {
            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let exit_block = builder.create_block();

            let is_unit = *ty == Type::Unit;
            let cranelift_ty = cranelift_type_of(ty);

            // Only expect a block parameter if this expression yields a non-unit value
            if !is_unit {
                builder.append_block_param(exit_block, cranelift_ty);
            }

            let cond_val = compile_expr(builder, cond, vars, var_counter, module, struct_layouts);
            builder
                .ins()
                .brif(cond_val, then_block, &[], else_block, &[]);

            // THEN
            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            let then_val = compile_expr(builder, then_b, vars, var_counter, module, struct_layouts);
            let then_term = builder.is_unreachable();
            if !then_term {
                if is_unit {
                    builder.ins().jump(exit_block, &[]);
                } else {
                    let coerced = coerce_val(builder, then_val, cranelift_ty);
                    builder.ins().jump(exit_block, &[coerced]);
                }
            }

            // ELSE
            builder.switch_to_block(else_block);
            builder.seal_block(else_block);
            let else_val = compile_expr(builder, else_b, vars, var_counter, module, struct_layouts);
            let else_term = builder.is_unreachable();
            if !else_term {
                if is_unit {
                    builder.ins().jump(exit_block, &[]);
                } else {
                    let coerced = coerce_val(builder, else_val, cranelift_ty);
                    builder.ins().jump(exit_block, &[coerced]);
                }
            }

            // EXIT
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);

            if then_term && else_term {
                let dummy = builder.ins().iconst(cranelift_ty, 0);
                builder.ins().trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
                dummy
            } else if is_unit {
                builder.ins().iconst(types::I64, 0)
            } else {
                builder.block_params(exit_block)[0]
            }
        }
        TypedExpr::Match(target, arms, ty, _) => {
            use cranelift_codegen::ir::condcodes::IntCC;

            let is_unit = *ty == Type::Unit;
            let cranelift_ty = cranelift_type_of(ty);

            let target_ptr =
                compile_expr(builder, target, vars, var_counter, module, struct_layouts);
            let tag_val = builder
                .ins()
                .load(types::I64, MemFlags::new(), target_ptr, 0);

            let exit_block = builder.create_block();
            if !is_unit {
                builder.append_block_param(exit_block, cranelift_ty);
            }

            for arm in arms {
                let arm_block = builder.create_block();
                let next_check_block = builder.create_block();

                if arm.tag == -1 {
                    builder.ins().jump(arm_block, &[]);
                } else {
                    let expected_tag = builder.ins().iconst(types::I64, arm.tag);
                    let is_match = builder.ins().icmp(IntCC::Equal, tag_val, expected_tag);
                    builder
                        .ins()
                        .brif(is_match, arm_block, &[], next_check_block, &[]);
                }

                // Compile Arm Block
                builder.switch_to_block(arm_block);
                builder.seal_block(arm_block);

                for (idx, (b_name, _b_ty)) in arm.bindings.iter().enumerate() {
                    if b_name != "_" {
                        let offset = ((idx + 1) * 8) as i32;
                        let payload_val =
                            builder
                                .ins()
                                .load(types::I64, MemFlags::new(), target_ptr, offset);
                        let var = cranelift_frontend::Variable::from_u32(*var_counter as u32);
                        *var_counter += 1;
                        builder.declare_var(var, types::I64);
                        builder.def_var(var, payload_val);
                        vars.insert(b_name.clone(), var);
                    }
                }

                let mut arm_val = builder.ins().iconst(types::I64, 0);
                for stmt in &arm.body {
                    arm_val = compile_expr(builder, stmt, vars, var_counter, module, struct_layouts);
                }

                if !builder.is_unreachable() {
                    if is_unit {
                        builder.ins().jump(exit_block, &[]);
                    } else {
                        let coerced = coerce_val(builder, arm_val, cranelift_ty);
                        builder.ins().jump(exit_block, &[coerced]);
                    }
                }

                // Switch to Next Check Block
                builder.switch_to_block(next_check_block);
                builder.seal_block(next_check_block);
            }

            if !builder.is_unreachable() {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
            }

            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);

            if is_unit {
                builder.ins().iconst(types::I64, 0)
            } else {
                builder.block_params(exit_block)[0]
            }
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
        TypedExpr::MacroCall(name, args, _, _) => crate::codegen::intrinsics::compile_macro_call(
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
        TypedExpr::Call(name, args, ret_ty, span) => {
            use cranelift_codegen::ir::AbiParam;
            let mut compiled_args = Vec::new();
            let mut sig = module.make_signature();

            for arg in args {
                let mut compiled_arg =
                    compile_expr(builder, arg, vars, var_counter, module, struct_layouts);

                let param_ty = match arg.ty() {
                    Type::Bool => types::I8,
                    Type::Float => types::F64,
                    Type::F32 => types::F32,
                    Type::I32 => types::I32,
                    _ => types::I64,
                };

                let val_ty = builder.func.dfg.value_type(compiled_arg);
                if val_ty != param_ty {
                    compiled_arg = match (val_ty, param_ty) {
                        (types::I32, types::I64) => builder.ins().sextend(types::I64, compiled_arg),
                        (types::I64, types::I32) => builder.ins().ireduce(types::I32, compiled_arg),
                        (types::I32, types::F32) => {
                            builder.ins().fcvt_from_sint(types::F32, compiled_arg)
                        }
                        (types::I32, types::F64) => {
                            builder.ins().fcvt_from_sint(types::F64, compiled_arg)
                        }
                        (types::I64, types::F32) => {
                            builder.ins().fcvt_from_sint(types::F32, compiled_arg)
                        }
                        (types::I64, types::F64) => {
                            builder.ins().fcvt_from_sint(types::F64, compiled_arg)
                        }
                        (types::F32, types::F64) => {
                            builder.ins().fpromote(types::F64, compiled_arg)
                        }
                        (types::F64, types::F32) => builder.ins().fdemote(types::F32, compiled_arg),
                        (types::I8, t) if t.is_int() => builder.ins().sextend(t, compiled_arg),
                        (t, types::I8) if t.is_int() => builder.ins().ireduce(types::I8, compiled_arg),
                        _ => compiled_arg,
                    };
                }

                compiled_args.push(compiled_arg);
                sig.params.push(AbiParam::new(param_ty));
            }

            let ret_cranelift_ty = cranelift_type_of(ret_ty);
            if *ret_ty != Type::Unit {
                sig.returns.push(AbiParam::new(ret_cranelift_ty));
            }

            if let Some(var) = vars.get(name) {
                let func_ptr = builder.use_var(*var);
                let sig_ref = builder.import_signature(sig);
                let call_inst = builder
                    .ins()
                    .call_indirect(sig_ref, func_ptr, &compiled_args);
                if *ret_ty != Type::Unit {
                    return builder.inst_results(call_inst)[0];
                } else {
                    return builder.ins().iconst(types::I64, 0);
                }
            }

            let target_symbol_name = if name == "rc_new"
                || name == "arc_new"
                || name == "rc_clone"
                || name == "arc_clone"
            {
                format!("intrinsic_{}", name)
            } else {
                name.clone()
            };

            let known_in_module = module.get_name(&target_symbol_name).is_some();
            let sym_ptr = if !known_in_module {
                unsafe {
                    if let Ok(c_name) = std::ffi::CString::new(target_symbol_name.as_str()) {
                        let p = libc::dlsym(libc::RTLD_DEFAULT, c_name.as_ptr());
                        if p.is_null() {
                            let c_mangled =
                                std::ffi::CString::new(format!("_{}", target_symbol_name)).unwrap();
                            libc::dlsym(libc::RTLD_DEFAULT, c_mangled.as_ptr())
                        } else {
                            p
                        }
                    } else {
                        std::ptr::null_mut()
                    }
                }
            } else {
                std::ptr::null_mut()
            };

            if !sym_ptr.is_null() {
                let sig_ref = builder.import_signature(sig);
                let callee_val = builder.ins().iconst(types::I64, sym_ptr as i64);
                let call_inst = builder
                    .ins()
                    .call_indirect(sig_ref, callee_val, &compiled_args);
                if *ret_ty != Type::Unit {
                    builder.inst_results(call_inst)[0]
                } else {
                    builder.ins().iconst(types::I64, 0)
                }
            } else {
                let known_func_id = match module.get_name(&target_symbol_name) {
                Some(cranelift_module::FuncOrDataId::Func(id)) => Some(id),
                _ => None,
            };

            if let Some(callee) = known_func_id {
                let decl_sig = module.declarations().get_function_decl(callee);
                let mut matched_args = Vec::new();
                for (i, &arg_val) in compiled_args.iter().enumerate() {
                    if i < decl_sig.signature.params.len() {
                        let expected_ty = decl_sig.signature.params[i].value_type;
                        let actual_ty = builder.func.dfg.value_type(arg_val);
                        let coerced = if actual_ty == expected_ty {
                            arg_val
                        } else if actual_ty == types::I32 && expected_ty == types::I64 {
                            builder.ins().sextend(types::I64, arg_val)
                        } else if actual_ty == types::I64 && expected_ty == types::I32 {
                            builder.ins().ireduce(types::I32, arg_val)
                        } else if actual_ty == types::I32 && expected_ty == types::F32 {
                            builder.ins().fcvt_from_sint(types::F32, arg_val)
                        } else if actual_ty == types::I64 && expected_ty == types::F32 {
                            builder.ins().fcvt_from_sint(types::F32, arg_val)
                        } else if actual_ty == types::F32 && expected_ty == types::I32 {
                            builder.ins().fcvt_to_sint(types::I32, arg_val)
                        } else if actual_ty == types::F64 && expected_ty == types::I64 {
                            builder.ins().bitcast(types::I64, MemFlags::new(), arg_val)
                        } else if actual_ty == types::F32 && expected_ty == types::I64 {
                            let promoted = builder.ins().fpromote(types::F64, arg_val);
                            builder.ins().bitcast(types::I64, MemFlags::new(), promoted)
                        } else if actual_ty == types::I64 && expected_ty == types::F64 {
                            builder.ins().bitcast(types::F64, MemFlags::new(), arg_val)
                        } else {
                            arg_val
                        };
                        matched_args.push(coerced);
                    } else {
                        matched_args.push(arg_val);
                    }
                }
                let local_callee = module.declare_func_in_func(callee, builder.func);
                let call_inst = builder.ins().call(local_callee, &matched_args);
                if *ret_ty != Type::Unit {
                    builder.inst_results(call_inst)[0]
                } else {
                    builder.ins().iconst(types::I64, 0)
                }
            } else {
                let sym_str_expr = TypedExpr::String(target_symbol_name.clone(), span.clone());
                let str_ptr = compile_expr(builder, &sym_str_expr, vars, var_counter, module, struct_layouts);

                let mut resolve_sig = module.make_signature();
                resolve_sig.params.push(AbiParam::new(types::I64));
                resolve_sig.returns.push(AbiParam::new(types::I64));

                let resolve_callee = module.declare_function("gdrs_resolve_symbol", Linkage::Import, &resolve_sig).unwrap();
                let local_resolve = module.declare_func_in_func(resolve_callee, builder.func);
                let call_resolve = builder.ins().call(local_resolve, &[str_ptr]);
                let fn_ptr = builder.inst_results(call_resolve)[0];

                let sig_ref = builder.import_signature(sig);
                let call_inst = builder.ins().call_indirect(sig_ref, fn_ptr, &compiled_args);
                if *ret_ty != Type::Unit {
                    builder.inst_results(call_inst)[0]
                } else {
                    builder.ins().iconst(types::I64, 0)
                }
            }
        }
        }

        // Boolean literal (1 for true, 0 for false)
        TypedExpr::Bool(b, _) => builder.ins().iconst(types::I8, if *b { 1 } else { 0 }),

        TypedExpr::ObjInit(_struct_name, fields, _ty, _) => {
            use cranelift_codegen::ir::AbiParam;
            let slot_size = (fields.len() * 8) as i64;
            let size_val = builder.ins().iconst(types::I64, if slot_size == 0 { 8 } else { slot_size });

            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            let callee = module.declare_function("malloc", Linkage::Import, &sig).unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[size_val]);
            let base_ptr = builder.inst_results(call_inst)[0];

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

            let field_cranelift_ty = cranelift_type_of(field_ty);

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
                    Type::Slice(_) | Type::Vec(_) => {
                        builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0)
                    }
                    _ => base_ptr,
                },
                _ => base_ptr,
            };
            let idx_val = compile_expr(builder, idx, vars, var_counter, module, struct_layouts);
            let elem_size = builder.ins().iconst(types::I64, 8);
            let offset = builder.ins().imul(idx_val, elem_size);
            let elem_addr = builder.ins().iadd(buffer_ptr, offset);

            let cranelift_ty = cranelift_type_of(elem_ty);

            builder
                .ins()
                .load(cranelift_ty, MemFlags::new(), elem_addr, 0)
        }

        TypedExpr::IndexAssign(target, idx, val, _) => {
            let base_ptr = compile_expr(builder, target, vars, var_counter, module, struct_layouts);
            let buffer_ptr = match target.as_ref() {
                TypedExpr::Ident(_, _, _) => match target.ty() {
                    Type::Slice(_) | Type::Vec(_) => {
                        builder.ins().load(types::I64, MemFlags::new(), base_ptr, 0)
                    }
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
            use cranelift_codegen::ir::AbiParam;
            let total_bytes = ((1 + payload_exprs.len()) * 8) as i64;
            let size_val = builder.ins().iconst(types::I64, if total_bytes == 0 { 8 } else { total_bytes });

            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            let callee = module.declare_function("malloc", Linkage::Import, &sig).unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[size_val]);
            let base_ptr = builder.inst_results(call_inst)[0];

            // Store discriminant tag at offset 0
            let disc_val = builder.ins().iconst(types::I64, *disc as i64);
            builder.ins().store(MemFlags::new(), disc_val, base_ptr, 0);

            // Store payload fields at offsets 8, 16, ...
            for (i, expr) in payload_exprs.iter().enumerate() {
                let val = compile_expr(builder, expr, vars, var_counter, module, struct_layouts);
                let val_i64 = coerce_val(builder, val, types::I64);
                let offset = ((i + 1) * 8) as i32;
                builder.ins().store(MemFlags::new(), val_i64, base_ptr, offset);
            }

            base_ptr
        }

        TypedExpr::CastF32(inner, _) => {
            let val = compile_expr(builder, inner, vars, var_counter, module, struct_layouts);
            let val_ty = builder.func.dfg.value_type(val);
            match val_ty {
                t if t == types::F64 => builder.ins().fdemote(types::F32, val),
                t if t == types::I64 => builder.ins().fcvt_from_sint(types::F32, val),
                t if t == types::I32 => builder.ins().fcvt_from_sint(types::F32, val),
                _ => val, // already F32
            }
        }

        TypedExpr::CastI32(inner, _) => {
            let val = compile_expr(builder, inner, vars, var_counter, module, struct_layouts);
            let val_ty = builder.func.dfg.value_type(val);
            match val_ty {
                t if t == types::I64 => builder.ins().ireduce(types::I32, val),
                t if t == types::F32 => builder.ins().fcvt_to_sint(types::I32, val),
                t if t == types::F64 => builder.ins().fcvt_to_sint(types::I32, val),
                _ => val, // already I32
            }
        }

        TypedExpr::Deref(inner_expr, _ty, _) => {
            let heap_ptr = compile_expr(
                builder,
                inner_expr,
                vars,
                var_counter,
                module,
                struct_layouts,
            );
            let offset = match inner_expr.ty() {
                Type::Int | Type::I32 => 0,
                _ => 8,
            };
            builder.ins().load(types::I64, MemFlags::new(), heap_ptr, offset)
        }

        TypedExpr::DerefAssign(ptr_expr, val_expr, _) => {
            let heap_ptr =
                compile_expr(builder, ptr_expr, vars, var_counter, module, struct_layouts);
            let val = compile_expr(builder, val_expr, vars, var_counter, module, struct_layouts);
            builder.ins().store(MemFlags::new(), val, heap_ptr, 8);
            builder.ins().iconst(types::I64, 0)
        }

        TypedExpr::Closure(closure_name, params, body, ret_ty, span) => {
            use cranelift_frontend::FunctionBuilderContext;

            let mut func_params = Vec::new();
            for (p_name, p_ty) in params {
                func_params.push(crate::ast::Param {
                    name: p_name.clone(),
                    is_mutable: false,
                    ty: *p_ty,
                    span: span.clone(),
                });
            }

            let func_decl = crate::ast::TypedFuncDecl {
                name: closure_name.clone(),
                params: func_params,
                return_type: *ret_ty,
                where_clause: None,
                body: vec![body.as_ref().clone()],
            };

            let mut sig = module.make_signature();
            for _ in params {
                sig.params
                    .push(cranelift_codegen::ir::AbiParam::new(types::I64));
            }
            sig.returns
                .push(cranelift_codegen::ir::AbiParam::new(types::I64));

            let callee = match module.get_name(closure_name) {
                Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                _ => module
                    .declare_function(closure_name, Linkage::Export, &sig)
                    .unwrap(),
            };

            let mut new_ctx = module.make_context();
            let mut new_builder_ctx = FunctionBuilderContext::new();

            crate::codegen::func::compile_func(
                &func_decl,
                struct_layouts,
                module,
                &mut new_ctx,
                &mut new_builder_ctx,
            );

            let local_callee = module.declare_func_in_func(callee, builder.func);
            builder.ins().func_addr(types::I64, local_callee)
        }

        TypedExpr::Range(start_expr, end_expr, _, _) => {
            let start = compile_expr(
                builder,
                start_expr,
                vars,
                var_counter,
                module,
                struct_layouts,
            );
            let end = compile_expr(builder, end_expr, vars, var_counter, module, struct_layouts);

            let mut malloc_sig = module.make_signature();
            malloc_sig.params.push(AbiParam::new(types::I64));
            malloc_sig.returns.push(AbiParam::new(types::I64));
            let callee = module
                .declare_function("malloc", Linkage::Import, &malloc_sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let size_val = builder.ins().iconst(types::I64, 16);
            let call_inst = builder.ins().call(local_callee, &[size_val]);
            let heap_ptr = builder.inst_results(call_inst)[0];

            builder.ins().store(MemFlags::new(), start, heap_ptr, 0);
            builder.ins().store(MemFlags::new(), end, heap_ptr, 8);
            heap_ptr
        }

        TypedExpr::CoerceToDyn(inner_expr, _trait_name, _) => {
            let data_ptr = compile_expr(
                builder,
                inner_expr,
                vars,
                var_counter,
                module,
                struct_layouts,
            );
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
            builder
                .ins()
                .store(MemFlags::new(), vtable_dummy, fat_ptr, 8);

            fat_ptr
        }

        TypedExpr::DynCall(receiver_expr, method_name, args, ret_ty, _) => {
            let fat_ptr = compile_expr(
                builder,
                receiver_expr,
                vars,
                var_counter,
                module,
                struct_layouts,
            );
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

/// Helper to coerce Cranelift SSA values to match target block parameter types
fn coerce_val(
    builder: &mut cranelift_frontend::FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    target_ty: cranelift_codegen::ir::Type,
) -> cranelift_codegen::ir::Value {
    let val_ty = builder.func.dfg.value_type(val);
    if val_ty == target_ty {
        val
    } else if val_ty == types::I32 && target_ty == types::I64 {
        builder.ins().sextend(types::I64, val)
    } else if val_ty == types::I64 && target_ty == types::I32 {
        builder.ins().ireduce(types::I32, val)
    } else if val_ty == types::I64 && target_ty == types::I8 {
        builder.ins().ireduce(types::I8, val)
    } else if val_ty == types::I32 && target_ty == types::I8 {
        builder.ins().ireduce(types::I8, val)
    } else if val_ty == types::I8 && target_ty == types::I64 {
        builder.ins().uextend(types::I64, val)
    } else if val_ty == types::I8 && target_ty == types::I32 {
        builder.ins().uextend(types::I32, val)
    } else {
        val
    }
}
