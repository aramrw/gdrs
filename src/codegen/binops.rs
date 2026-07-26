//! codegen/binops.rs
//! Codegen for all binary and unary arithmetic, bitwise, logical, and comparison operators.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{InstBuilder, MemFlags, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr};
use crate::codegen::expr::{coerce_operands, compile_expr, is_float_ty, is_float_val};
use crate::sanal::StructLayout;

/// Helper used for every two-operand op: compile both sides, coerce, apply `op`.
macro_rules! bin_op {
    ($builder:expr, $lhs:expr, $rhs:expr, $vars:expr, $vc:expr, $mod:expr, $sl:expr, $op:expr) => {{
        let left = compile_expr($builder, $lhs, $vars, $vc, $mod, $sl);
        let right = compile_expr($builder, $rhs, $vars, $vc, $mod, $sl);
        let (left, right) = coerce_operands($builder, left, right);
        $op($builder, left, right)
    }};
}

// ── Arithmetic ───────────────────────────────────────────────────────────────

pub fn compile_add<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = coerce_operands(builder, left, right);
    if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fadd(left, right)
    } else {
        builder.ins().iadd(left, right)
    }
}

pub fn compile_sub<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = coerce_operands(builder, left, right);
    if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fsub(left, right)
    } else {
        builder.ins().isub(left, right)
    }
}

pub fn compile_mul<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = coerce_operands(builder, left, right);
    if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fmul(left, right)
    } else {
        builder.ins().imul(left, right)
    }
}

pub fn compile_div<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = coerce_operands(builder, left, right);
    if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fdiv(left, right)
    } else {
        builder.ins().sdiv(left, right)
    }
}

pub fn compile_mod<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
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

// ── Unary ────────────────────────────────────────────────────────────────────

pub fn compile_neg<M: Module>(
    builder: &mut FunctionBuilder,
    val: &TypedExpr,
    ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let inner = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
    if is_float_ty(ty) || is_float_val(builder, inner) {
        builder.ins().fneg(inner)
    } else {
        builder.ins().ineg(inner)
    }
}

pub fn compile_not<M: Module>(
    builder: &mut FunctionBuilder,
    val: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let inner = compile_expr(builder, val, vars, var_counter, module, struct_layouts);
    let cmp = builder.ins().icmp_imm(IntCC::Equal, inner, 0);
    builder.ins().uextend(types::I64, cmp)
}

// ── Bitwise ──────────────────────────────────────────────────────────────────

pub fn compile_pipe<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    bin_op!(builder, lhs, rhs, vars, var_counter, module, struct_layouts, |b: &mut FunctionBuilder, l, r| b.ins().bor(l, r))
}

pub fn compile_ampersand<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    bin_op!(builder, lhs, rhs, vars, var_counter, module, struct_layouts, |b: &mut FunctionBuilder, l, r| b.ins().band(l, r))
}

pub fn compile_caret<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    bin_op!(builder, lhs, rhs, vars, var_counter, module, struct_layouts, |b: &mut FunctionBuilder, l, r| b.ins().bxor(l, r))
}

pub fn compile_shr<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    bin_op!(builder, lhs, rhs, vars, var_counter, module, struct_layouts, |b: &mut FunctionBuilder, l, r| b.ins().sshr(l, r))
}

pub fn compile_shl<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    bin_op!(builder, lhs, rhs, vars, var_counter, module, struct_layouts, |b: &mut FunctionBuilder, l, r| b.ins().ishl(l, r))
}

// ── Logical ──────────────────────────────────────────────────────────────────

pub fn compile_and<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    builder.ins().band(left, right)
}

pub fn compile_or<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    builder.ins().bor(left, right)
}

// ── Comparisons ──────────────────────────────────────────────────────────────

pub fn compile_eq<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left_raw = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right_raw = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = if let Type::Enum(_) = lhs.ty() {
        let l_tag = builder.ins().load(types::I64, MemFlags::new(), left_raw, 0);
        let r_tag = builder.ins().load(types::I64, MemFlags::new(), right_raw, 0);
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

pub fn compile_neq<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left_raw = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right_raw = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = if let Type::Enum(_) = lhs.ty() {
        let l_tag = builder.ins().load(types::I64, MemFlags::new(), left_raw, 0);
        let r_tag = builder.ins().load(types::I64, MemFlags::new(), right_raw, 0);
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

pub fn compile_gt<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
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

pub fn compile_lt<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
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

pub fn compile_gte<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = coerce_operands(builder, left, right);
    let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
        builder.ins().fcmp(FloatCC::GreaterThanOrEqual, left, right)
    } else {
        builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left, right)
    };
    builder.ins().uextend(types::I64, cmp)
}

pub fn compile_lte<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let left = compile_expr(builder, lhs, vars, var_counter, module, struct_layouts);
    let right = compile_expr(builder, rhs, vars, var_counter, module, struct_layouts);
    let (left, right) = coerce_operands(builder, left, right);
    let cmp = if is_float_ty(&lhs.ty()) || is_float_val(builder, left) {
        builder.ins().fcmp(FloatCC::LessThanOrEqual, left, right)
    } else {
        builder.ins().icmp(IntCC::SignedLessThanOrEqual, left, right)
    };
    builder.ins().uextend(types::I64, cmp)
}
