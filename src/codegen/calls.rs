//! codegen/calls.rs
//! Codegen for function calls, dynamic trait calls, and coercion to dyn trait objects.

use std::collections::HashMap;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, types, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::{Span, Type, TypedExpr};
use crate::codegen::expr::{coerce_val, compile_expr, cranelift_type_of};
use crate::sanal::StructLayout;

pub fn compile_call<M: Module>(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[TypedExpr],
    ret_ty: &Type,
    span: &Span,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
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
                (types::F32, types::I32) => builder.ins().fcvt_to_sint(types::I32, compiled_arg),
                (types::F64, types::I32) => builder.ins().fcvt_to_sint(types::I32, compiled_arg),
                (types::F32, types::I64) => builder.ins().fcvt_to_sint(types::I64, compiled_arg),
                (types::F64, types::I64) => builder.ins().fcvt_to_sint(types::I64, compiled_arg),
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

    let target_symbol_name = if name == "rc_new"
        || name == "arc_new"
        || name == "rc_clone"
        || name == "arc_clone"
    {
        format!("intrinsic_{}", name)
    } else {
        name.to_string()
    };

    if module.get_name(&target_symbol_name).is_none() {
        if let Some(var) = vars.get(name) {
            let func_ptr = builder.use_var(*var);
            let sig_ref = builder.import_signature(sig.clone());
            let call_inst = builder
                .ins()
                .call_indirect(sig_ref, func_ptr, &compiled_args);
            if *ret_ty != Type::Unit {
                return builder.inst_results(call_inst)[0];
            } else {
                return builder.ins().iconst(types::I64, 0);
            }
        }
    }

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
                    let coerced = coerce_val(builder, arg_val, expected_ty);
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
            let sym_str_expr = TypedExpr::String(target_symbol_name, span.clone());
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

pub fn compile_coerce_to_dyn<M: Module>(
    builder: &mut FunctionBuilder,
    inner_expr: &TypedExpr,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
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

pub fn compile_dyn_call<M: Module>(
    builder: &mut FunctionBuilder,
    receiver_expr: &TypedExpr,
    method_name: &str,
    args: &[TypedExpr],
    ret_ty: &Type,
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
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

    let type_name = match receiver_expr {
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
