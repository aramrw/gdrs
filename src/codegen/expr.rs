//! codegen/expr.rs
//! Translates TypedAST expressions into Cranelift IR instructions.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

static STR_COUNTER: AtomicUsize = AtomicUsize::new(0);

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::assign::{compile_assign, compile_let};
use crate::codegen::branching::{compile_if, compile_if_else, compile_match};
use crate::codegen::loops::compile_while;
use crate::codegen::objects::compile_enum_construct;
use crate::codegen::refs::{compile_deref, compile_deref_assign, compile_ref};
use crate::sanal::StructLayout;

/// True for any floating-point Type variant.
#[inline]
pub(crate) fn is_float_ty(ty: &Type) -> bool {
    matches!(ty, Type::Float | Type::F32)
}

#[inline]
pub(crate) fn is_float_val(builder: &FunctionBuilder, val: Value) -> bool {
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
        Type::Obj(s) => {
            // Normalize the type name to Rust-style before matching
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
        _ => types::I64, // pointers / heap handles
    }
}

/// Widen two operand Values so they share the same Cranelift type before
/// emitting a binary instruction. Follows Rust promotion rules:
///   i32 + i64  → both i64
///   f32 + f64  → both f64
///   int + float → both float (using the wider float)
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

        // Float literal — emits F64 for precision
        TypedExpr::Float(f, _) => builder.ins().f64const(*f),

        // Addition -> Cranelift iadd / fadd instruction
        TypedExpr::Add(lhs, rhs, ty, _) => crate::codegen::binops::compile_add(
            builder,
            lhs,
            rhs,
            ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Subtraction -> Cranelift isub / fsub instruction
        TypedExpr::Sub(lhs, rhs, ty, _) => crate::codegen::binops::compile_sub(
            builder,
            lhs,
            rhs,
            ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Multiplication -> Cranelift imul / fmul instruction
        TypedExpr::Mul(lhs, rhs, ty, _) => crate::codegen::binops::compile_mul(
            builder,
            lhs,
            rhs,
            ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Division -> Cranelift sdiv / fdiv instruction
        TypedExpr::Div(lhs, rhs, ty, _) => crate::codegen::binops::compile_div(
            builder,
            lhs,
            rhs,
            ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Pipe(lhs, rhs, _, _) => crate::codegen::binops::compile_pipe(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Ampersand(lhs, rhs, _, _) => crate::codegen::binops::compile_ampersand(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Cast(inner_expr, _target_ty, _) => {
            compile_expr(builder, inner_expr, vars, var_counter, module, struct_layouts)
        }

        TypedExpr::Caret(lhs, rhs, _, _) => crate::codegen::binops::compile_caret(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Shr(lhs, rhs, _, _) => crate::codegen::binops::compile_shr(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Shl(lhs, rhs, _, _) => crate::codegen::binops::compile_shl(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Modulo -> Cranelift srem / float modulo instruction
        TypedExpr::Mod(lhs, rhs, ty, _) => crate::codegen::binops::compile_mod(
            builder,
            lhs,
            rhs,
            ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Unary Negation
        TypedExpr::Neg(val, ty, _) => crate::codegen::binops::compile_neg(
            builder,
            val,
            ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Logical NOT
        TypedExpr::Not(val, _) => crate::codegen::binops::compile_not(
            builder,
            val,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Greater Than Or Equal (>=)
        TypedExpr::GreaterEqual(lhs, rhs, _) => crate::codegen::binops::compile_gte(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Less Than Or Equal (<=)
        TypedExpr::LessEqual(lhs, rhs, _) => crate::codegen::binops::compile_lte(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Not Equal (!=)
        TypedExpr::NotEqual(lhs, rhs, _) => crate::codegen::binops::compile_neq(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Logical AND
        TypedExpr::And(lhs, rhs, _) => crate::codegen::binops::compile_and(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Logical OR
        TypedExpr::Or(lhs, rhs, _) => crate::codegen::binops::compile_or(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Return statement
        TypedExpr::Return(opt_expr, _) => {
            if let Some(e) = opt_expr {
                let ret_val = compile_expr(builder, e, vars, var_counter, module, struct_layouts);
                let ret_coerced = if !builder.func.signature.returns.is_empty() {
                    let target_ty = builder.func.signature.returns[0].value_type;
                    coerce_val(builder, ret_val, target_ty)
                } else {
                    ret_val
                };
                builder.ins().return_(&[ret_coerced]);
                ret_val
            } else {
                let zero = builder.ins().iconst(types::I64, 0);
                builder.ins().return_(&[]);
                zero
            }
        }

        // Greater Than Comparison (>)
        TypedExpr::GreaterThan(lhs, rhs, _) => crate::codegen::binops::compile_gt(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Less Than Comparison (<)
        TypedExpr::LessThan(lhs, rhs, _) => crate::codegen::binops::compile_lt(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Equal(lhs, rhs, _) => crate::codegen::binops::compile_eq(
            builder,
            lhs,
            rhs,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        // Variable Declaration -> Create variable and assign value
        TypedExpr::Let(name, _is_mutable, value, ty, _) => compile_let(
            builder,
            value,
            ty,
            vars,
            var_counter,
            module,
            struct_layouts,
            name,
        ),

        // Variable Reassignment -> Update Cranelift variable value
        TypedExpr::Assign(name, value, _) => compile_assign(
            builder,
            value,
            vars,
            var_counter,
            module,
            struct_layouts,
            name,
        ),
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
        TypedExpr::If(cond, body, _) => compile_if(
            builder,
            vars,
            var_counter,
            module,
            struct_layouts,
            cond,
            body,
        ),

        // If-Else Expression / Statement
        TypedExpr::IfElse(cond, then_b, else_b, ty, _) => compile_if_else(
            builder,
            vars,
            var_counter,
            ty,
            module,
            struct_layouts,
            cond,
            then_b,
            else_b,
        ),

        TypedExpr::Match(target, arms, ty, _) => compile_match(
            builder,
            target,
            arms,
            vars,
            var_counter,
            ty,
            module,
            struct_layouts,
        ),

        TypedExpr::While(cond, body, _) => compile_while(
            builder,
            cond,
            body,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

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
        TypedExpr::Call(name, args, ret_ty, span) => crate::codegen::calls::compile_call(
            builder,
            name,
            args,
            ret_ty,
            span,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Bool(b, _) => builder.ins().iconst(types::I8, if *b { 1 } else { 0 }),

        TypedExpr::ObjInit(struct_name, fields, _ty, _) => {
            crate::codegen::objects::compile_obj_init(
                builder,
                struct_name,
                fields,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
        }

        TypedExpr::FieldAccess(target, field_name, field_ty, _) => {
            crate::codegen::objects::compile_field_access(
                builder,
                target,
                field_name,
                field_ty,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
        }

        TypedExpr::FieldAssign(target, field_name, val, _) => {
            crate::codegen::objects::compile_field_assign(
                builder,
                target,
                field_name,
                val,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
        }

        TypedExpr::ArrayInit(elems, arr_ty, _) => crate::codegen::arrays::compile_array_init(
            builder,
            elems,
            arr_ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::IndexAccess(target, idx, elem_ty, _) => {
            crate::codegen::arrays::compile_index_access(
                builder,
                target,
                idx,
                elem_ty,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
        }

        TypedExpr::IndexAssign(target, idx, val, _) => {
            crate::codegen::arrays::compile_index_assign(
                builder,
                target,
                idx,
                val,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
        }

        TypedExpr::EnumConstruct(_enum_name, _variant_name, disc, payload_exprs, _ty, _) => {
            compile_enum_construct(
                builder,
                _enum_name,
                _variant_name,
                disc,
                payload_exprs,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
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

        TypedExpr::Ref(inner_expr, _is_mut, _ref_ty, _) => compile_ref(
            builder,
            inner_expr,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Deref(inner_expr, _ty, _) => compile_deref(
            builder,
            inner_expr,
            _ty,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::DerefAssign(ptr_expr, val_expr, _) => compile_deref_assign(
            builder,
            ptr_expr,
            val_expr,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::Closure(closure_name, params, body, ret_ty, span) => {
            crate::codegen::closures::compile_closure(
                builder,
                closure_name,
                params,
                body,
                ret_ty,
                span,
                module,
                struct_layouts,
            )
        }

        TypedExpr::Range(start_expr, end_expr, _, _) => crate::codegen::arrays::compile_range(
            builder,
            start_expr,
            end_expr,
            vars,
            var_counter,
            module,
            struct_layouts,
        ),

        TypedExpr::CoerceToDyn(inner_expr, _trait_name, _) => {
            crate::codegen::calls::compile_coerce_to_dyn(
                builder,
                inner_expr,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
        }

        TypedExpr::DynCall(receiver_expr, method_name, args, ret_ty, _) => {
            crate::codegen::calls::compile_dyn_call(
                builder,
                receiver_expr,
                method_name,
                args,
                ret_ty,
                vars,
                var_counter,
                module,
                struct_layouts,
            )
        }
    }
}

/// Helper to coerce Cranelift SSA values to match target block parameter types
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
        builder.ins().fcvt_from_sint(types::F64, val)
    } else if val_ty == types::F64 && target_ty == types::I64 {
        builder.ins().fcvt_to_sint(types::I64, val)
    } else if val_ty == types::F32 && target_ty == types::F64 {
        builder.ins().fpromote(types::F64, val)
    } else if val_ty == types::F64 && target_ty == types::F32 {
        builder.ins().fdemote(types::F32, val)
    } else {
        val
    }
}
