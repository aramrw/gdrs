//! codegen/expr.rs
//! Translates TypedAST expressions into Cranelift IR instructions.

use std::sync::atomic::{AtomicUsize, Ordering};

static STR_COUNTER: AtomicUsize = AtomicUsize::new(0);

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::assign::{compile_assign, compile_let, compile_let_tuple};
use crate::codegen::branching::{compile_if, compile_if_else, compile_match, expr_is_terminator};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::loops::compile_while;
use crate::codegen::objects::compile_enum_construct;
use crate::codegen::refs::{compile_deref, compile_deref_assign, compile_ref};

/// True for any floating-point Type variant.
#[inline]
pub(crate) fn is_float_ty(ty: &Type) -> bool {
    matches!(ty, Type::Float | Type::F32)
}

#[inline]
pub(crate) fn is_float_val(builder: &FunctionBuilder, val: Value) -> bool {
    builder.func.dfg.value_type(val).is_float()
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
        Type::Obj(s) => {
            let normalized = crate::ast::normalize_type_name(s);
            if matches!(normalized.as_str(), "f64" | "float") {
                types::F64
            } else if matches!(normalized.as_str(), "f32") {
                types::F32
            } else {
                types::I64
            }
        }
        Type::Generic(_) => types::I64,
        _ => types::I64,
    }
}

/// Widen two operand Values so they share the same Cranelift type before
/// emitting a binary instruction.
pub(crate) fn coerce_operands(
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
        (types::I32, types::I64) => lhs = builder.ins().sextend(types::I64, lhs),
        (types::I64, types::I32) => rhs = builder.ins().sextend(types::I64, rhs),
        (types::F32, types::F64) => lhs = builder.ins().fpromote(types::F64, lhs),
        (types::F64, types::F32) => rhs = builder.ins().fpromote(types::F64, rhs),
        (types::I32, types::F32) => lhs = builder.ins().fcvt_from_sint(types::F32, lhs),
        (types::F32, types::I32) => rhs = builder.ins().fcvt_from_sint(types::F32, rhs),
        (types::I32, types::F64) => lhs = builder.ins().fcvt_from_sint(types::F64, lhs),
        (types::F64, types::I32) => rhs = builder.ins().fcvt_from_sint(types::F64, rhs),
        (types::I64, types::F64) => lhs = builder.ins().fcvt_from_sint(types::F64, lhs),
        (types::F64, types::I64) => rhs = builder.ins().fcvt_from_sint(types::F64, rhs),
        (types::I64, types::F32) => lhs = builder.ins().fcvt_from_sint(types::F32, lhs),
        (types::F32, types::I64) => rhs = builder.ins().fcvt_from_sint(types::F32, rhs),
        _ => {}
    }
    (lhs, rhs)
}

/// Declares and returns the address of a NUL-terminated static string constant.
pub(crate) fn compile_string_constant<M: Module>(
    builder: &mut FunctionBuilder,
    s: &str,
    module: &mut M,
) -> Value {
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

/// Recursively compiles a `TypedExpr` into a Cranelift IR `Value`.
pub fn compile_expr<M: Module>(
    builder: &mut FunctionBuilder,
    expr: &TypedExpr,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    match expr {
        TypedExpr::Int(n, _) => builder.ins().iconst(types::I64, *n),
        TypedExpr::Float(f, _) => builder.ins().f64const(*f),

        TypedExpr::Add(lhs, rhs, ty, _) => crate::codegen::binops::compile_add(builder, lhs, rhs, ty, cg, module),
        TypedExpr::Sub(lhs, rhs, ty, _) => crate::codegen::binops::compile_sub(builder, lhs, rhs, ty, cg, module),
        TypedExpr::Mul(lhs, rhs, ty, _) => crate::codegen::binops::compile_mul(builder, lhs, rhs, ty, cg, module),
        TypedExpr::Div(lhs, rhs, ty, _) => crate::codegen::binops::compile_div(builder, lhs, rhs, ty, cg, module),
        TypedExpr::Mod(lhs, rhs, ty, _) => crate::codegen::binops::compile_mod(builder, lhs, rhs, ty, cg, module),
        TypedExpr::Pipe(lhs, rhs, _, _) => crate::codegen::binops::compile_pipe(builder, lhs, rhs, cg, module),
        TypedExpr::Ampersand(lhs, rhs, _, _) => crate::codegen::binops::compile_ampersand(builder, lhs, rhs, cg, module),
        TypedExpr::Caret(lhs, rhs, _, _) => crate::codegen::binops::compile_caret(builder, lhs, rhs, cg, module),
        TypedExpr::Shr(lhs, rhs, _, _) => crate::codegen::binops::compile_shr(builder, lhs, rhs, cg, module),
        TypedExpr::Shl(lhs, rhs, _, _) => crate::codegen::binops::compile_shl(builder, lhs, rhs, cg, module),
        TypedExpr::Neg(val, ty, _) => crate::codegen::binops::compile_neg(builder, val, ty, cg, module),
        TypedExpr::Not(val, _) => crate::codegen::binops::compile_not(builder, val, cg, module),
        TypedExpr::GreaterEqual(lhs, rhs, _) => crate::codegen::binops::compile_gte(builder, lhs, rhs, cg, module),
        TypedExpr::LessEqual(lhs, rhs, _) => crate::codegen::binops::compile_lte(builder, lhs, rhs, cg, module),
        TypedExpr::NotEqual(lhs, rhs, _) => crate::codegen::binops::compile_neq(builder, lhs, rhs, cg, module),
        TypedExpr::GreaterThan(lhs, rhs, _) => crate::codegen::binops::compile_gt(builder, lhs, rhs, cg, module),
        TypedExpr::LessThan(lhs, rhs, _) => crate::codegen::binops::compile_lt(builder, lhs, rhs, cg, module),
        TypedExpr::Equal(lhs, rhs, _) => crate::codegen::binops::compile_eq(builder, lhs, rhs, cg, module),
        TypedExpr::And(lhs, rhs, _) => crate::codegen::binops::compile_and(builder, lhs, rhs, cg, module),
        TypedExpr::Or(lhs, rhs, _) => crate::codegen::binops::compile_or(builder, lhs, rhs, cg, module),

        TypedExpr::Cast(inner_expr, target_ty, _) => {
            let val = compile_expr(builder, inner_expr, cg, module);
            coerce_typed_val(builder, val, &inner_expr.ty(), cranelift_type_of(target_ty))
        }

        TypedExpr::Return(opt_expr, _) => {
            crate::codegen::func::emit_explicit_return(builder, opt_expr.as_deref(), cg, module)
        }

        TypedExpr::Break(_) => {
            let zero = builder.ins().iconst(types::I64, 0);
            if let Some((_, exit_block, loop_depth, loop_temp_depth)) = cg.loop_stack.last().copied() {
                cg.emit_temp_drops_down_to_depth(builder, module, loop_temp_depth);
                cg.emit_drops_down_to_depth(builder, module, loop_depth);
                builder.ins().jump(exit_block, &[]);
            }
            zero
        }

        TypedExpr::Continue(_) => {
            let zero = builder.ins().iconst(types::I64, 0);
            if let Some((header_block, _, loop_depth, loop_temp_depth)) = cg.loop_stack.last().copied() {
                cg.emit_temp_drops_down_to_depth(builder, module, loop_temp_depth);
                cg.emit_drops_down_to_depth(builder, module, loop_depth);
                builder.ins().jump(header_block, &[]);
            }
            zero
        }

        TypedExpr::Let(name, _is_mutable, value, ty, _) => {
            compile_let(builder, value, ty, cg, module, name)
        }
        TypedExpr::LetTuple(pat, _ty, value, _) => {
            compile_let_tuple(builder, pat, value, cg, module)
        }
        TypedExpr::Assign(name, value, _) => {
            compile_assign(builder, value, cg, module, name)
        }

        TypedExpr::Ident(name, _, _) => {
            if let Some(&(slot, slot_ty)) = cg.var_slots.get(name) {
                builder.ins().stack_load(slot_ty, slot, 0)
            } else if let Some(&var) = cg.vars.get(name) {
                builder.use_var(var)
            } else {
                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                let callee = match module.get_name(name) {
                    Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                    _ => module
                        .declare_function(name, Linkage::Import, &sig)
                        .unwrap(),
                };
                let local_callee = module.declare_func_in_func(callee, builder.func);
                builder.ins().func_addr(types::I64, local_callee)
            }
        }

        TypedExpr::Block(stmts, block_ty, _) | TypedExpr::Unsafe(stmts, block_ty, _) => {
            cg.push_scope();
            let mut last = builder.ins().iconst(types::I64, 0);
            let mut terminated = false;
            let len = stmts.len();
            for (idx, stmt) in stmts.iter().enumerate() {
                if builder.is_unreachable() {
                    terminated = true;
                    break;
                }
                cg.push_temp_scope();
                last = compile_expr(builder, stmt, cg, module);
                let is_yielded_tail = idx + 1 == len && *block_ty != Type::Unit;
                if builder.is_unreachable() || expr_is_terminator(stmt) {
                    cg.pop_temp_scope_without_drop();
                    terminated = true;
                    break;
                }
                if is_yielded_tail {
                    cg.cancel_temp(last);
                    if let TypedExpr::Ident(ret_name, ret_ty, _) = stmt {
                        if !ret_ty.is_copy() {
                            cg.mark_moved(builder, ret_name);
                        }
                    }
                }
                cg.pop_temp_scope_and_drop(builder, module);
            }
            if !terminated && !builder.is_unreachable() {
                cg.pop_scope_and_drop(builder, module);
            } else {
                cg.pop_scope_without_drop();
            }
            if !terminated && *block_ty != Type::Unit {
                cg.register_temp(last, block_ty);
            }
            last
        }

        TypedExpr::If(cond, body, _) => compile_if(builder, cg, module, cond, body),
        TypedExpr::IfElse(cond, then_b, else_b, ty, _) => {
            let val = compile_if_else(builder, cg, ty, module, cond, then_b, else_b);
            cg.register_temp(val, ty);
            val
        }
        TypedExpr::Match(target, arms, ty, _) => {
            let val = compile_match(builder, target, arms, cg, ty, module);
            cg.register_temp(val, ty);
            val
        }
        TypedExpr::While(cond, body, _) => compile_while(builder, cond, body, cg, module),

        TypedExpr::MacroCall(name, args, m_ty, span) => {
            let val = crate::codegen::intrinsics::compile_macro_call(builder, name, args, span, cg, module);
            cg.register_temp(val, m_ty);
            val
        }

        TypedExpr::String(raw_s, _) => {
            let s = crate::ast::unescape_string_literal(raw_s);
            compile_string_constant(builder, &s, module)
        }

        TypedExpr::Call(name, args, ret_ty, span) => {
            let val = crate::codegen::calls::compile_call(builder, name, args, ret_ty, span, cg, module);
            cg.register_temp(val, ret_ty);
            val
        }

        TypedExpr::Bool(b, _) => builder.ins().iconst(types::I8, if *b { 1 } else { 0 }),

        TypedExpr::ObjInit(struct_name, fields, ty, _) => {
            let val = crate::codegen::objects::compile_obj_init(builder, struct_name, fields, ty, cg, module);
            cg.register_temp(val, ty);
            val
        }
        TypedExpr::FieldAccess(target, field_name, field_ty, _) => {
            crate::codegen::objects::compile_field_access(builder, target, field_name, field_ty, cg, module)
        }
        TypedExpr::FieldAssign(target, field_name, val, _) => {
            crate::codegen::objects::compile_field_assign(builder, target, field_name, val, cg, module)
        }
        TypedExpr::ArrayInit(elems, arr_ty, _) => {
            let val = crate::codegen::arrays::compile_array_init(builder, elems, arr_ty, cg, module);
            cg.register_temp(val, arr_ty);
            val
        }
        TypedExpr::TupleInit(elems, tup_ty, _) => {
            let val = crate::codegen::objects::compile_tuple_init(builder, elems, tup_ty, cg, module);
            cg.register_temp(val, tup_ty);
            val
        }
        TypedExpr::IndexAccess(target, idx, elem_ty, _) => {
            crate::codegen::arrays::compile_index_access(builder, target, idx, elem_ty, cg, module)
        }
        TypedExpr::IndexAssign(target, idx, val, _) => {
            crate::codegen::arrays::compile_index_assign(builder, target, idx, val, cg, module)
        }
        TypedExpr::EnumConstruct(enum_name, variant_name, disc, payload_exprs, ty, _) => {
            let val = compile_enum_construct(builder, enum_name, variant_name, disc, payload_exprs, ty, cg, module);
            cg.register_temp(val, ty);
            val
        }

        TypedExpr::CastF32(inner, _) => {
            let val = compile_expr(builder, inner, cg, module);
            let val_ty = builder.func.dfg.value_type(val);
            match val_ty {
                t if t == types::F64 => builder.ins().fdemote(types::F32, val),
                t if t == types::I64 || t == types::I32 => builder.ins().fcvt_from_sint(types::F32, val),
                _ => val,
            }
        }
        TypedExpr::CastI32(inner, _) => {
            let val = compile_expr(builder, inner, cg, module);
            let val_ty = builder.func.dfg.value_type(val);
            match val_ty {
                t if t == types::I64 => builder.ins().ireduce(types::I32, val),
                t if t == types::F32 || t == types::F64 => builder.ins().fcvt_to_sint(types::I32, val),
                _ => val,
            }
        }

        TypedExpr::Ref(inner_expr, _is_mut, _ref_ty, _) => compile_ref(builder, inner_expr, cg, module),
        TypedExpr::Deref(inner_expr, ty, _) => compile_deref(builder, inner_expr, ty, cg, module),
        TypedExpr::DerefAssign(ptr_expr, val_expr, _) => {
            compile_deref_assign(builder, ptr_expr, val_expr, cg, module)
        }

        TypedExpr::Closure(closure_name, params, body, ret_ty, span) => {
            crate::codegen::closures::compile_closure(
                builder,
                closure_name,
                params,
                body,
                ret_ty,
                span,
                cg.meta,
                module,
            )
        }

        TypedExpr::Range(start_expr, end_expr, _, _) => {
            crate::codegen::arrays::compile_range(builder, start_expr, end_expr, cg, module)
        }

        TypedExpr::CoerceToDyn(inner_expr, trait_name, _) => {
            crate::codegen::calls::compile_coerce_to_dyn(builder, inner_expr, trait_name, cg, module)
        }
        TypedExpr::DynCall(receiver_expr, method_name, args, ret_ty, _) => {
            crate::codegen::calls::compile_dyn_call(builder, receiver_expr, method_name, args, ret_ty, cg, module)
        }
    }
}

/// Helper to coerce Cranelift SSA values to match target block parameter types.
pub(crate) fn coerce_val(
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
    } else if (val_ty == types::I32 || val_ty == types::I64) && target_ty == types::F32 {
        builder.ins().fcvt_from_sint(types::F32, val)
    } else if val_ty == types::I32 && target_ty == types::F64 {
        builder.ins().fcvt_from_sint(types::F64, val)
    } else if val_ty == types::I64 && target_ty == types::F64 {
        builder.ins().bitcast(types::F64, MemFlags::new(), val)
    } else if val_ty == types::F64 && target_ty == types::I64 {
        builder.ins().bitcast(types::I64, MemFlags::new(), val)
    } else if val_ty == types::F32 && target_ty == types::I64 {
        let bits32 = builder.ins().bitcast(types::I32, MemFlags::new(), val);
        builder.ins().uextend(types::I64, bits32)
    } else if val_ty == types::I64 && target_ty == types::F32 {
        let low32 = builder.ins().ireduce(types::I32, val);
        builder.ins().bitcast(types::F32, MemFlags::new(), low32)
    } else if val_ty == types::F32 && target_ty == types::F64 {
        builder.ins().fpromote(types::F64, val)
    } else if val_ty == types::F64 && target_ty == types::F32 {
        builder.ins().fdemote(types::F32, val)
    } else {
        val
    }
}

/// Coerce an SSA `Value` using its semantic source `Type` so integer-to-float
/// conversions emit `fcvt_from_sint`, while erased `i64` float slots keep `bitcast`.
pub(crate) fn coerce_typed_val(
    builder: &mut cranelift_frontend::FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    src_ty: &Type,
    target_ty: cranelift_codegen::ir::Type,
) -> cranelift_codegen::ir::Value {
    let val_ty = builder.func.dfg.value_type(val);
    if val_ty == target_ty {
        return val;
    }
    if matches!(src_ty, Type::Int | Type::I32)
        && (target_ty == types::F64 || target_ty == types::F32)
    {
        return builder.ins().fcvt_from_sint(target_ty, val);
    }
    coerce_val(builder, val, target_ty)
}
