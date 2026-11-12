//! codegen/binops.rs
//! Codegen for all binary and unary arithmetic, bitwise, logical, and comparison operators.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{find_enum_layout, is_npo_enum, EnumLayoutMap};
use crate::codegen::expr::{coerce_operands, coerce_val, compile_expr, cranelift_type_of, is_float_ty, is_float_val};
use crate::codegen::layout::{array_stride, enum_variant_offsets, is_aggregate_type, tuple_field_offsets};
use crate::sanal::StructLayout;

macro_rules! bin_op {
    ($builder:expr, $lhs:expr, $rhs:expr, $cg:expr, $mod:expr, $op:expr) => {{
        let left = compile_expr($builder, $lhs, $cg, $mod);
        let right = compile_expr($builder, $rhs, $cg, $mod);
        let (left, right) = coerce_operands($builder, left, right);
        $op($builder, left, right)
    }};
}

fn type_stride(
    ty: &Type,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> i64 {
    match ty {
        Type::Ptr(inner) => {
            if matches!(**inner, Type::Void | Type::Unit) {
                1
            } else {
                array_stride(inner, struct_layouts, enum_layouts).max(1) as i64
            }
        }
        _ => 1,
    }
}

pub fn compile_add<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let mut left = compile_expr(builder, lhs, cg, module);
    let mut right = compile_expr(builder, rhs, cg, module);

    if let Type::Ptr(_) = lhs.ty() {
        let stride = type_stride(&lhs.ty(), &cg.meta.struct_layouts, cg.meta.enum_layouts);
        let right_i64 = coerce_val(builder, right, types::I64);
        let scaled_right = if stride > 1 {
            builder.ins().imul_imm(right_i64, stride)
        } else {
            right_i64
        };
        let left_i64 = coerce_val(builder, left, types::I64);
        return builder.ins().iadd(left_i64, scaled_right);
    } else if let Type::Ptr(_) = rhs.ty() {
        let stride = type_stride(&rhs.ty(), &cg.meta.struct_layouts, cg.meta.enum_layouts);
        let left_i64 = coerce_val(builder, left, types::I64);
        let scaled_left = if stride > 1 {
            builder.ins().imul_imm(left_i64, stride)
        } else {
            left_i64
        };
        let right_i64 = coerce_val(builder, right, types::I64);
        return builder.ins().iadd(scaled_left, right_i64);
    }

    let (left_coerced, right_coerced) = coerce_operands(builder, left, right);
    left = left_coerced;
    right = right_coerced;

    let res = if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fadd(left, right)
    } else {
        builder.ins().iadd(left, right)
    };
    coerce_val(builder, res, cranelift_type_of(ty))
}

pub fn compile_sub<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let mut left = compile_expr(builder, lhs, cg, module);
    let mut right = compile_expr(builder, rhs, cg, module);

    if let Type::Ptr(_) = lhs.ty() {
        let stride = type_stride(&lhs.ty(), &cg.meta.struct_layouts, cg.meta.enum_layouts);
        let right_i64 = coerce_val(builder, right, types::I64);
        let scaled_right = if stride > 1 {
            builder.ins().imul_imm(right_i64, stride)
        } else {
            right_i64
        };
        let left_i64 = coerce_val(builder, left, types::I64);
        return builder.ins().isub(left_i64, scaled_right);
    }

    let (left_coerced, right_coerced) = coerce_operands(builder, left, right);
    left = left_coerced;
    right = right_coerced;

    let res = if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fsub(left, right)
    } else {
        builder.ins().isub(left, right)
    };
    coerce_val(builder, res, cranelift_type_of(ty))
}

pub fn compile_mul<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let left = compile_expr(builder, lhs, cg, module);
    let right = compile_expr(builder, rhs, cg, module);
    let (left, right) = coerce_operands(builder, left, right);
    let res = if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fmul(left, right)
    } else {
        builder.ins().imul(left, right)
    };
    coerce_val(builder, res, cranelift_type_of(ty))
}

pub fn compile_div<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let left = compile_expr(builder, lhs, cg, module);
    let right = compile_expr(builder, rhs, cg, module);
    let (left, right) = coerce_operands(builder, left, right);
    let res = if is_float_ty(ty) || is_float_val(builder, left) {
        builder.ins().fdiv(left, right)
    } else if ty.is_unsigned_integer() || lhs.ty().is_unsigned_integer() {
        builder.ins().udiv(left, right)
    } else {
        builder.ins().sdiv(left, right)
    };
    coerce_val(builder, res, cranelift_type_of(ty))
}

pub fn compile_mod<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let left = compile_expr(builder, lhs, cg, module);
    let right = compile_expr(builder, rhs, cg, module);
    let (left, right) = coerce_operands(builder, left, right);
    let res = if is_float_ty(ty) || is_float_val(builder, left) {
        let div = builder.ins().fdiv(left, right);
        let flr = builder.ins().floor(div);
        let mul = builder.ins().fmul(flr, right);
        builder.ins().fsub(left, mul)
    } else if ty.is_unsigned_integer() || lhs.ty().is_unsigned_integer() {
        builder.ins().urem(left, right)
    } else {
        builder.ins().srem(left, right)
    };
    coerce_val(builder, res, cranelift_type_of(ty))
}

pub fn compile_neg<M: Module>(
    builder: &mut FunctionBuilder,
    val: &TypedExpr,
    ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let inner = compile_expr(builder, val, cg, module);
    if is_float_ty(ty) || is_float_val(builder, inner) {
        builder.ins().fneg(inner)
    } else {
        builder.ins().ineg(inner)
    }
}

pub fn compile_not<M: Module>(
    builder: &mut FunctionBuilder,
    val: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let inner = compile_expr(builder, val, cg, module);
    let cmp = builder.ins().icmp_imm(IntCC::Equal, inner, 0);
    builder.ins().uextend(types::I64, cmp)
}

pub fn compile_pipe<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    bin_op!(builder, lhs, rhs, cg, module, |b: &mut FunctionBuilder, l, r| b.ins().bor(l, r))
}

pub fn compile_ampersand<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    bin_op!(builder, lhs, rhs, cg, module, |b: &mut FunctionBuilder, l, r| b.ins().band(l, r))
}

pub fn compile_caret<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    bin_op!(builder, lhs, rhs, cg, module, |b: &mut FunctionBuilder, l, r| b.ins().bxor(l, r))
}

pub fn compile_shr<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    if lhs.ty().is_unsigned_integer() {
        bin_op!(builder, lhs, rhs, cg, module, |b: &mut FunctionBuilder, l, r| b.ins().ushr(l, r))
    } else {
        bin_op!(builder, lhs, rhs, cg, module, |b: &mut FunctionBuilder, l, r| b.ins().sshr(l, r))
    }
}

pub fn compile_shl<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    bin_op!(builder, lhs, rhs, cg, module, |b: &mut FunctionBuilder, l, r| b.ins().ishl(l, r))
}

pub fn compile_and<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    let rhs_block = builder.create_block();
    let false_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I8);

    let left = compile_expr(builder, lhs, cg, module);
    if builder.is_unreachable() {
        builder.switch_to_block(false_block);
        builder.seal_block(false_block);
        builder.switch_to_block(rhs_block);
        builder.seal_block(rhs_block);
        builder.switch_to_block(merge_block);
        builder.seal_block(merge_block);
        return builder.ins().iconst(types::I8, 0);
    }
    builder.ins().brif(left, rhs_block, &[], false_block, &[]);

    builder.switch_to_block(false_block);
    builder.seal_block(false_block);
    let false_val = builder.ins().iconst(types::I8, 0);
    builder.ins().jump(merge_block, &[false_val]);

    builder.switch_to_block(rhs_block);
    builder.seal_block(rhs_block);
    let right = compile_expr(builder, rhs, cg, module);
    if !builder.is_unreachable() {
        let r_bool = builder.ins().icmp_imm(IntCC::NotEqual, right, 0);
        builder.ins().jump(merge_block, &[r_bool]);
    }

    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    builder.block_params(merge_block)[0]
}

pub fn compile_or<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    let rhs_block = builder.create_block();
    let true_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I8);

    let left = compile_expr(builder, lhs, cg, module);
    if builder.is_unreachable() {
        builder.switch_to_block(true_block);
        builder.seal_block(true_block);
        builder.switch_to_block(rhs_block);
        builder.seal_block(rhs_block);
        builder.switch_to_block(merge_block);
        builder.seal_block(merge_block);
        return builder.ins().iconst(types::I8, 0);
    }
    builder.ins().brif(left, true_block, &[], rhs_block, &[]);

    builder.switch_to_block(true_block);
    builder.seal_block(true_block);
    let true_val = builder.ins().iconst(types::I8, 1);
    builder.ins().jump(merge_block, &[true_val]);

    builder.switch_to_block(rhs_block);
    builder.seal_block(rhs_block);
    let right = compile_expr(builder, rhs, cg, module);
    if !builder.is_unreachable() {
        let r_bool = builder.ins().icmp_imm(IntCC::NotEqual, right, 0);
        builder.ins().jump(merge_block, &[r_bool]);
    }

    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    builder.block_params(merge_block)[0]
}

#[inline]
fn is_string_like_ty(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Str | Type::String | Type::Obj("String") | Type::Obj("std_string_String")
    )
}

#[inline]
fn is_string_obj_ty(ty: &Type) -> bool {
    matches!(
        ty,
        Type::String | Type::Obj("String") | Type::Obj("std_string_String")
    )
}

fn emit_str_eq_i8<M: Module>(
    builder: &mut FunctionBuilder,
    left: Value,
    left_ty: &Type,
    right: Value,
    right_ty: &Type,
    module: &mut M,
) -> Value {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I8));
    let callee = match module.get_name("intrinsic_str_eq") {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        _ => module
            .declare_function("intrinsic_str_eq", Linkage::Import, &sig)
            .unwrap(),
    };
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let l_i64 = coerce_val(builder, left, types::I64);
    let l_obj = builder
        .ins()
        .iconst(types::I64, if is_string_obj_ty(left_ty) { 1 } else { 0 });
    let r_i64 = coerce_val(builder, right, types::I64);
    let r_obj = builder
        .ins()
        .iconst(types::I64, if is_string_obj_ty(right_ty) { 1 } else { 0 });
    let inst = builder.ins().call(local_callee, &[l_i64, l_obj, r_i64, r_obj]);
    builder.inst_results(inst)[0]
}

fn emit_payload_eq_i8<M: Module>(
    builder: &mut FunctionBuilder,
    raw_l: Value,
    raw_r: Value,
    ty: &Type,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Value {
    if is_string_like_ty(ty) {
        return emit_str_eq_i8(builder, raw_l, ty, raw_r, ty, module);
    }
    if let Type::Enum(enum_name) = ty {
        if !is_npo_enum(enum_name) {
            if let Some(fid) =
                resolve_or_synthesize_enum_eq_fn(enum_name, struct_layouts, enum_layouts, module)
            {
                let local_callee = module.declare_func_in_func(fid, builder.func);
                let inst = builder.ins().call(local_callee, &[raw_l, raw_r]);
                return builder.inst_results(inst)[0];
            }
        }
        return builder.ins().icmp(IntCC::Equal, raw_l, raw_r);
    }
    if let Type::Tuple(elems) = ty {
        if let Some(fid) =
            resolve_or_synthesize_tuple_eq_fn(elems, struct_layouts, enum_layouts, module)
        {
            let local_callee = module.declare_func_in_func(fid, builder.func);
            let inst = builder.ins().call(local_callee, &[raw_l, raw_r]);
            return builder.inst_results(inst)[0];
        }
        return builder.ins().iconst(types::I8, 1);
    }
    let cl_ty = cranelift_type_of(ty);
    let l_val = coerce_val(builder, raw_l, cl_ty);
    let r_val = coerce_val(builder, raw_r, cl_ty);
    if is_float_ty(ty) || is_float_val(builder, l_val) {
        builder.ins().fcmp(FloatCC::Equal, l_val, r_val)
    } else {
        builder.ins().icmp(IntCC::Equal, l_val, r_val)
    }
}

fn resolve_or_synthesize_enum_eq_fn<M: Module>(
    enum_name: &str,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Option<FuncId> {
    if is_npo_enum(enum_name) {
        return None;
    }
    let synth_name = format!("__gdrs_eq_enum_{enum_name}");
    if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
        return Some(id);
    }

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I8));
    let func_id = module
        .declare_function(&synth_name, Linkage::Export, &sig)
        .ok()?;

    let variants = find_enum_layout(enum_name, enum_layouts).cloned().unwrap_or_default();

    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut builder_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = builder.create_block();
        builder.switch_to_block(entry);
        builder.append_block_params_for_function_params(entry);
        let a_ptr = builder.block_params(entry)[0];
        let b_ptr = builder.block_params(entry)[1];

        let ret_true = builder.create_block();
        let ret_false = builder.create_block();
        let check_null = builder.create_block();
        let check_tag = builder.create_block();

        let same_ptr = builder.ins().icmp(IntCC::Equal, a_ptr, b_ptr);
        builder.ins().brif(same_ptr, ret_true, &[], check_null, &[]);

        builder.switch_to_block(check_null);
        builder.seal_block(check_null);
        let a_null = builder.ins().icmp_imm(IntCC::Equal, a_ptr, 0);
        let b_null = builder.ins().icmp_imm(IntCC::Equal, b_ptr, 0);
        let any_null = builder.ins().bor(a_null, b_null);
        builder.ins().brif(any_null, ret_false, &[], check_tag, &[]);

        builder.switch_to_block(check_tag);
        builder.seal_block(check_tag);
        let tag_a = builder.ins().load(types::I64, MemFlags::new(), a_ptr, 0);
        let tag_b = builder.ins().load(types::I64, MemFlags::new(), b_ptr, 0);
        let tag_eq = builder.ins().icmp(IntCC::Equal, tag_a, tag_b);

        let payload_variants: Vec<(i64, Vec<Type>)> = variants
            .into_iter()
            .filter(|(_, _, pts)| !pts.is_empty())
            .map(|(_, tag, pts)| (tag, pts))
            .collect();

        if payload_variants.is_empty() {
            builder.ins().brif(tag_eq, ret_true, &[], ret_false, &[]);
        } else {
            let check_payloads = builder.create_block();
            builder.ins().brif(tag_eq, check_payloads, &[], ret_false, &[]);
            builder.switch_to_block(check_payloads);
            builder.seal_block(check_payloads);

            for (v_tag, p_tys) in payload_variants {
                let v_blk = builder.create_block();
                let next_blk = builder.create_block();
                let is_v = builder.ins().icmp_imm(IntCC::Equal, tag_a, v_tag);
                builder.ins().brif(is_v, v_blk, &[], next_blk, &[]);

                builder.switch_to_block(v_blk);
                builder.seal_block(v_blk);
                let (_, _, offsets) = enum_variant_offsets(&p_tys, struct_layouts, enum_layouts);
                for (i, p_ty) in p_tys.iter().enumerate() {
                    let off = offsets.get(i).copied().unwrap_or(((i + 1) * 8) as u32);
                    let (raw_l, raw_r) = if is_aggregate_type(p_ty, struct_layouts, enum_layouts) {
                        (
                            builder.ins().iadd_imm(a_ptr, off as i64),
                            builder.ins().iadd_imm(b_ptr, off as i64),
                        )
                    } else {
                        let cl_ty = cranelift_type_of(p_ty);
                        (
                            builder.ins().load(cl_ty, MemFlags::new(), a_ptr, off as i32),
                            builder.ins().load(cl_ty, MemFlags::new(), b_ptr, off as i32),
                        )
                    };
                    let eq_i8 = emit_payload_eq_i8(
                        &mut builder,
                        raw_l,
                        raw_r,
                        p_ty,
                        struct_layouts,
                        enum_layouts,
                        module,
                    );
                    let cont_field = builder.create_block();
                    builder.ins().brif(eq_i8, cont_field, &[], ret_false, &[]);
                    builder.switch_to_block(cont_field);
                    builder.seal_block(cont_field);
                }
                builder.ins().jump(ret_true, &[]);

                builder.switch_to_block(next_blk);
                builder.seal_block(next_blk);
            }
            builder.ins().jump(ret_true, &[]);
        }

        builder.switch_to_block(ret_true);
        builder.seal_block(ret_true);
        let one = builder.ins().iconst(types::I8, 1);
        builder.ins().return_(&[one]);

        builder.switch_to_block(ret_false);
        builder.seal_block(ret_false);
        let zero = builder.ins().iconst(types::I8, 0);
        builder.ins().return_(&[zero]);

        builder.seal_all_blocks();
        builder.finalize();
    }

    let _ = module.define_function(func_id, &mut ctx);
    module.clear_context(&mut ctx);
    Some(func_id)
}

fn resolve_or_synthesize_tuple_eq_fn<M: Module>(
    elems: &[Type],
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Option<FuncId> {
    if elems.is_empty() {
        return None;
    }
    let synth_name = format!(
        "__gdrs_eq_{}",
        crate::sanal::mono::type_suffix(&Type::Tuple(crate::ast::intern_tuple(elems)))
    );
    if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
        return Some(id);
    }

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I8));
    let func_id = module
        .declare_function(&synth_name, Linkage::Export, &sig)
        .ok()?;

    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut builder_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = builder.create_block();
        builder.switch_to_block(entry);
        builder.append_block_params_for_function_params(entry);
        let a_ptr = builder.block_params(entry)[0];
        let b_ptr = builder.block_params(entry)[1];

        let ret_true = builder.create_block();
        let ret_false = builder.create_block();
        let check_fields = builder.create_block();

        let same_ptr = builder.ins().icmp(IntCC::Equal, a_ptr, b_ptr);
        builder.ins().brif(same_ptr, ret_true, &[], check_fields, &[]);

        builder.switch_to_block(check_fields);
        builder.seal_block(check_fields);

        let (_, _, offsets) = tuple_field_offsets(elems, struct_layouts, enum_layouts);
        for (i, e_ty) in elems.iter().enumerate() {
            let off = offsets.get(i).copied().unwrap_or((i * 8) as u32);
            let (raw_l, raw_r) = if is_aggregate_type(e_ty, struct_layouts, enum_layouts) {
                (
                    builder.ins().iadd_imm(a_ptr, off as i64),
                    builder.ins().iadd_imm(b_ptr, off as i64),
                )
            } else {
                let cl_ty = cranelift_type_of(e_ty);
                (
                    builder.ins().load(cl_ty, MemFlags::new(), a_ptr, off as i32),
                    builder.ins().load(cl_ty, MemFlags::new(), b_ptr, off as i32),
                )
            };
            let eq_i8 =
                emit_payload_eq_i8(&mut builder, raw_l, raw_r, e_ty, struct_layouts, enum_layouts, module);
            let next_blk = builder.create_block();
            builder.ins().brif(eq_i8, next_blk, &[], ret_false, &[]);
            builder.switch_to_block(next_blk);
            builder.seal_block(next_blk);
        }
        builder.ins().jump(ret_true, &[]);

        builder.switch_to_block(ret_true);
        builder.seal_block(ret_true);
        let one = builder.ins().iconst(types::I8, 1);
        builder.ins().return_(&[one]);

        builder.switch_to_block(ret_false);
        builder.seal_block(ret_false);
        let zero = builder.ins().iconst(types::I8, 0);
        builder.ins().return_(&[zero]);

        builder.seal_all_blocks();
        builder.finalize();
    }

    let _ = module.define_function(func_id, &mut ctx);
    module.clear_context(&mut ctx);
    Some(func_id)
}

pub fn compile_equality_cmp<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    negate: bool,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let left_raw = compile_expr(builder, lhs, cg, module);
    let right_raw = compile_expr(builder, rhs, cg, module);
    let l_ty = lhs.ty();
    let r_ty = rhs.ty();
    compile_equality_cmp_vals(builder, left_raw, l_ty, right_raw, r_ty, negate, cg, module)
}

pub fn compile_equality_cmp_vals<M: Module>(
    builder: &mut FunctionBuilder,
    left_raw: Value,
    l_ty: Type,
    right_raw: Value,
    r_ty: Type,
    negate: bool,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {

    if is_string_like_ty(&l_ty) && is_string_like_ty(&r_ty) {
        let eq_i8 = emit_str_eq_i8(builder, left_raw, &l_ty, right_raw, &r_ty, module);
        let cmp = if negate {
            builder.ins().icmp_imm(IntCC::Equal, eq_i8, 0)
        } else {
            builder.ins().icmp_imm(IntCC::NotEqual, eq_i8, 0)
        };
        return builder.ins().uextend(types::I64, cmp);
    }

    if let Type::Enum(enum_name) = l_ty {
        if is_npo_enum(enum_name) {
            let cc = if negate { IntCC::NotEqual } else { IntCC::Equal };
            let cmp = builder.ins().icmp(cc, left_raw, right_raw);
            return builder.ins().uextend(types::I64, cmp);
        }
        if let Some(fid) = resolve_or_synthesize_enum_eq_fn(
            enum_name,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        ) {
            let local_callee = module.declare_func_in_func(fid, builder.func);
            let l_i64 = coerce_val(builder, left_raw, types::I64);
            let r_i64 = coerce_val(builder, right_raw, types::I64);
            let inst = builder.ins().call(local_callee, &[l_i64, r_i64]);
            let eq_i8 = builder.inst_results(inst)[0];
            let cmp = if negate {
                builder.ins().icmp_imm(IntCC::Equal, eq_i8, 0)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, eq_i8, 0)
            };
            return builder.ins().uextend(types::I64, cmp);
        }
    }

    if let Type::Tuple(elems) = l_ty {
        let eq_i8 = if let Some(fid) = resolve_or_synthesize_tuple_eq_fn(
            elems,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        ) {
            let local_callee = module.declare_func_in_func(fid, builder.func);
            let l_i64 = coerce_val(builder, left_raw, types::I64);
            let r_i64 = coerce_val(builder, right_raw, types::I64);
            let inst = builder.ins().call(local_callee, &[l_i64, r_i64]);
            builder.inst_results(inst)[0]
        } else {
            builder.ins().iconst(types::I8, 1)
        };
        let cmp = if negate {
            builder.ins().icmp_imm(IntCC::Equal, eq_i8, 0)
        } else {
            builder.ins().icmp_imm(IntCC::NotEqual, eq_i8, 0)
        };
        return builder.ins().uextend(types::I64, cmp);
    }

    let (left, right) = coerce_operands(builder, left_raw, right_raw);
    let cmp = if is_float_ty(&l_ty) || is_float_val(builder, left) {
        let fcc = if negate { FloatCC::NotEqual } else { FloatCC::Equal };
        builder.ins().fcmp(fcc, left, right)
    } else {
        let icc = if negate { IntCC::NotEqual } else { IntCC::Equal };
        builder.ins().icmp(icc, left, right)
    };
    builder.ins().uextend(types::I64, cmp)
}

pub fn compile_eq<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    compile_equality_cmp(builder, lhs, rhs, false, cg, module)
}

pub fn compile_neq<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    compile_equality_cmp(builder, lhs, rhs, true, cg, module)
}

fn compile_ord_cmp<M: Module>(
    builder: &mut FunctionBuilder,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
    fcc: FloatCC,
    icc: IntCC,
) -> Value {
    let left = compile_expr(builder, lhs, cg, module);
    let right = compile_expr(builder, rhs, cg, module);
    let (left, right) = coerce_operands(builder, left, right);
    let is_float = is_float_ty(&lhs.ty())
        || is_float_ty(&rhs.ty())
        || is_float_val(builder, left)
        || is_float_val(builder, right);
    let cmp = if is_float {
        builder.ins().fcmp(fcc, left, right)
    } else {
        builder.ins().icmp(icc, left, right)
    };
    builder.ins().uextend(types::I64, cmp)
}

pub fn compile_gt<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    let icc = if lhs.ty().is_unsigned_integer() { IntCC::UnsignedGreaterThan } else { IntCC::SignedGreaterThan };
    compile_ord_cmp(builder, lhs, rhs, cg, module, FloatCC::GreaterThan, icc)
}

pub fn compile_lt<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    let icc = if lhs.ty().is_unsigned_integer() { IntCC::UnsignedLessThan } else { IntCC::SignedLessThan };
    compile_ord_cmp(builder, lhs, rhs, cg, module, FloatCC::LessThan, icc)
}

pub fn compile_gte<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    let icc = if lhs.ty().is_unsigned_integer() { IntCC::UnsignedGreaterThanOrEqual } else { IntCC::SignedGreaterThanOrEqual };
    compile_ord_cmp(builder, lhs, rhs, cg, module, FloatCC::GreaterThanOrEqual, icc)
}

pub fn compile_lte<M: Module>(builder: &mut FunctionBuilder, lhs: &TypedExpr, rhs: &TypedExpr, cg: &mut CodegenCtx, module: &mut M) -> Value {
    let icc = if lhs.ty().is_unsigned_integer() { IntCC::UnsignedLessThanOrEqual } else { IntCC::SignedLessThanOrEqual };
    compile_ord_cmp(builder, lhs, rhs, cg, module, FloatCC::LessThanOrEqual, icc)
}
