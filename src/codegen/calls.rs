//! codegen/calls.rs
//! Codegen for function calls, `std::mem::drop`, `rc`/`arc`, and `dyn Trait` dispatch via vtables.

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{Linkage, Module};

use crate::ast::{Span, Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{emit_drop_for_value, emit_heap_drop_fn_ptr, has_drop_glue};
use crate::codegen::expr::{coerce_typed_val, coerce_val, compile_expr};
use crate::codegen::layout::{
    abi_signature_for_fn, alloc_stack_slot, emit_memcpy_bytes, load_multireg_chunks, repr_kind,
    store_multireg_chunks, PassMode, ReprKind,
};
use crate::codegen::vtables::{get_or_build_vtable, lookup_vtable_method_index};

fn emit_malloc<M: Module>(builder: &mut FunctionBuilder, module: &mut M, bytes: i64) -> Value {
    let mut malloc_sig = module.make_signature();
    malloc_sig.params.push(AbiParam::new(types::I64));
    malloc_sig.returns.push(AbiParam::new(types::I64));
    let malloc_id = module
        .declare_function("malloc", Linkage::Import, &malloc_sig)
        .unwrap();
    let local_malloc = module.declare_func_in_func(malloc_id, builder.func);
    let size_val = builder.ins().iconst(types::I64, bytes.max(1));
    let call_inst = builder.ins().call(local_malloc, &[size_val]);
    builder.inst_results(call_inst)[0]
}

pub fn compile_call<M: Module>(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[TypedExpr],
    ret_ty: &Type,
    span: &Span,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    // Handle `std::mem::drop(x)` directly by running drop glue on the moved argument
    if name == "std_mem_drop" {
        if let Some(arg) = args.first() {
            let val = compile_expr(builder, arg, cg, module);
            cg.cancel_temp(val);
            let arg_ty = arg.ty();
            if let TypedExpr::Ident(v_name, _, _) = arg {
                cg.mark_moved(builder, v_name);
            }
            emit_drop_for_value(
                builder,
                val,
                &arg_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
                module,
            );
        }
        return builder.ins().iconst(types::I64, 0);
    }

    // Handle `rc.new(val)` and `arc.new(val)` with heap boxing for stack aggregates + destructor
    if (name == "rc_new" || name == "arc_new") && args.len() == 1 {
        let val = compile_expr(builder, &args[0], cg, module);
        cg.cancel_temp(val);
        let inner_ty = args[0].ty();
        if let TypedExpr::Ident(v_name, _, _) = &args[0] {
            if !inner_ty.is_copy() {
                cg.mark_moved(builder, v_name);
            }
        }
        let payload_val = match repr_kind(&inner_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            ReprKind::Aggregate { size, .. } => {
                let heap_ptr = emit_malloc(builder, module, size as i64);
                emit_memcpy_bytes(builder, module, heap_ptr, val, size);
                heap_ptr
            }
            ReprKind::Scalar(_) | ReprKind::Zst => coerce_val(builder, val, types::I64),
        };
        let dtor_ptr = emit_heap_drop_fn_ptr(
            builder,
            &inner_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        );

        let sym = format!("intrinsic_{}", name);
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module.declare_function(&sym, Linkage::Import, &sig).unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let call_inst = builder.ins().call(local_callee, &[payload_val, dtor_ptr]);
        return builder.inst_results(call_inst)[0];
    }

    let target_symbol_name = if name == "rc_clone" || name == "arc_clone" {
        format!("intrinsic_{}", name)
    } else {
        name.to_string()
    };

    let existing_func_id = module.get_name(&target_symbol_name).and_then(|id| match id {
        cranelift_module::FuncOrDataId::Func(fid) => Some(fid),
        _ => None,
    });

    let call_conv = module.isa().default_call_conv();
    let expected_param_tys: Vec<Type> = cg
        .meta
        .fn_param_types
        .get(&target_symbol_name)
        .cloned()
        .unwrap_or_else(|| args.iter().map(|a| a.ty()).collect());
    let expected_ret_ty = cg
        .meta
        .fn_return_types
        .get(&target_symbol_name)
        .copied()
        .unwrap_or(*ret_ty);

    let (mut sig, fn_abi) = abi_signature_for_fn(
        call_conv,
        &expected_param_tys,
        &expected_ret_ty,
        target_symbol_name.ends_with("_drop"),
        &cg.meta.struct_layouts,
        cg.meta.enum_layouts,
    );
    let is_track_caller = cg.meta.track_caller_fns.contains(&target_symbol_name);
    if is_track_caller {
        use cranelift_codegen::ir::AbiParam;
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
    }

    let move_flags = cg.meta.fn_move_params.get(&target_symbol_name).cloned();

    let mut compiled_args = Vec::new();
    let sret_addr_opt = if let PassMode::Indirect { size, align } = fn_abi.ret_mode {
        let (_, addr) = alloc_stack_slot(builder, size, align);
        compiled_args.push(addr);
        Some(addr)
    } else {
        None
    };

    for (i, arg) in args.iter().enumerate() {
        let target_param_ty = expected_param_tys.get(i).copied().unwrap_or_else(|| arg.ty());
        let compiled_arg = if let Type::Array(_, arr_len) = arg.ty() {
            let raw_arr_ptr = compile_expr(builder, arg, cg, module);
            if matches!(target_param_ty, Type::Slice(_)) {
                crate::codegen::arrays::alloc_stack_slice_header(builder, raw_arr_ptr, arr_len)
            } else if matches!(target_param_ty, Type::Vec(_))
                || matches!(target_param_ty, Type::Obj(n) if n.contains("Vec"))
            {
                cg.cancel_temp(raw_arr_ptr);
                if let TypedExpr::Ident(v_name, _, _) = arg {
                    cg.mark_moved(builder, v_name);
                }
                let elem_ty = match arg.ty() {
                    Type::Array(et, _) => *et,
                    _ => Type::Int,
                };
                crate::codegen::arrays::alloc_stack_vec_header_from_array(
                    builder,
                    raw_arr_ptr,
                    &elem_ty,
                    arr_len,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                )
            } else {
                raw_arr_ptr
            }
        } else {
            compile_expr(builder, arg, cg, module)
        };

        let is_intrinsic_move = i == 0
            && matches!(
                target_symbol_name.as_str(),
                "rc_new" | "arc_new" | "intrinsic_rc_new" | "intrinsic_arc_new" | "std_mem_drop"
            );
        let is_indirect_move = existing_func_id.is_none()
            && cg.vars.contains_key(name)
            && !arg.ty().is_copy()
            && !matches!(arg.ty(), Type::Ref(_) | Type::MutRef(_));
        let moves_arg = move_flags
            .as_ref()
            .and_then(|flags| flags.get(i).copied())
            .unwrap_or(false)
            || is_intrinsic_move
            || is_indirect_move;
        if moves_arg {
            cg.cancel_temp(compiled_arg);
            if let TypedExpr::Ident(v_name, _, _) = arg {
                cg.mark_moved(builder, v_name);
            }
        }

        let pmode = fn_abi
            .param_modes
            .get(i)
            .cloned()
            .unwrap_or(PassMode::Direct(types::I64));
        match pmode {
            PassMode::Ignore => {}
            PassMode::Direct(target_cl_ty) => {
                let coerced = if target_param_ty == Type::Str
                    && matches!(
                        arg.ty(),
                        Type::String | Type::Obj("String") | Type::Obj("std_string_String")
                    ) {
                    builder.ins().load(types::I64, MemFlags::new(), compiled_arg, 0)
                } else {
                    coerce_typed_val(builder, compiled_arg, &arg.ty(), target_cl_ty)
                };
                compiled_args.push(coerced);
            }
            PassMode::MultiReg { size, chunks, .. } => {
                let loaded = load_multireg_chunks(builder, module, compiled_arg, size, &chunks);
                compiled_args.extend(loaded);
            }
            PassMode::Indirect { size, align } => {
                let (_, arg_addr) = alloc_stack_slot(builder, size, align);
                emit_memcpy_bytes(builder, module, arg_addr, compiled_arg, size);
                compiled_args.push(arg_addr);
            }
        }
    }

    if is_track_caller {
        if let Some((cf, cl, cc)) = cg.current_caller_loc {
            compiled_args.push(cf);
            compiled_args.push(cl);
            compiled_args.push(cc);
        } else {
            let (file, line, col) = cg.meta.source_map.get_location(span);
            let f_ptr = crate::codegen::expr::compile_string_constant(builder, &file, module);
            let l_val = builder.ins().iconst(types::I64, line as i64);
            let c_val = builder.ins().iconst(types::I64, col as i64);
            compiled_args.push(f_ptr);
            compiled_args.push(l_val);
            compiled_args.push(c_val);
        }
    }

    let call_inst = if existing_func_id.is_none() {
        if let Some(&var) = cg.vars.get(name) {
            let func_ptr = builder.use_var(var);
            let sig_ref = builder.import_signature(sig);
            builder.ins().call_indirect(sig_ref, func_ptr, &compiled_args)
        } else {
            let callee = module
                .declare_function(&target_symbol_name, Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            builder.ins().call(local_callee, &compiled_args)
        }
    } else {
        let callee = existing_func_id.unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        builder.ins().call(local_callee, &compiled_args)
    };

    unpack_call_result(builder, module, call_inst, &fn_abi.ret_mode, sret_addr_opt)
}

fn unpack_call_result<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    call_inst: cranelift_codegen::ir::Inst,
    ret_mode: &PassMode,
    sret_addr_opt: Option<Value>,
) -> Value {
    match ret_mode {
        PassMode::Ignore => builder.ins().iconst(types::I64, 0),
        PassMode::Direct(_) => builder.inst_results(call_inst)[0],
        PassMode::MultiReg { size, align, .. } => {
            let results = builder.inst_results(call_inst).to_vec();
            let (_, ret_addr) = alloc_stack_slot(builder, *size, *align);
            store_multireg_chunks(builder, module, ret_addr, *size, &results);
            ret_addr
        }
        PassMode::Indirect { .. } => sret_addr_opt.expect("sret address missing"),
    }
}

pub fn compile_coerce_to_dyn<M: Module>(
    builder: &mut FunctionBuilder,
    inner_expr: &TypedExpr,
    trait_name: &str,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let concrete_ty = inner_expr.ty();
    let data_val = compile_expr(builder, inner_expr, cg, module);
    cg.cancel_temp(data_val);
    if let TypedExpr::Ident(v_name, _, _) = inner_expr {
        if !concrete_ty.is_copy() {
            cg.mark_moved(builder, v_name);
        }
    }

    let boxed_data = match repr_kind(&concrete_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
        ReprKind::Aggregate { size, .. } => {
            let heap_ptr = emit_malloc(builder, module, size as i64);
            emit_memcpy_bytes(builder, module, heap_ptr, data_val, size);
            heap_ptr
        }
        ReprKind::Scalar(_) | ReprKind::Zst => coerce_val(builder, data_val, types::I64),
    };

    let fat_ptr = emit_malloc(builder, module, 24);
    builder.ins().store(MemFlags::new(), boxed_data, fat_ptr, 0);

    let vtable_ptr = get_or_build_vtable(builder, &concrete_ty, trait_name, cg.meta, module);
    builder.ins().store(MemFlags::new(), vtable_ptr, fat_ptr, 8);

    let dtor_ptr = if has_drop_glue(
        &concrete_ty,
        &cg.meta.known_drop_fns,
        &cg.meta.struct_layouts,
        cg.meta.enum_layouts,
    ) || matches!(concrete_ty, Type::Obj(_) | Type::Enum(_))
    {
        emit_heap_drop_fn_ptr(
            builder,
            &concrete_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        )
    } else {
        builder.ins().iconst(types::I64, 0)
    };
    builder.ins().store(MemFlags::new(), dtor_ptr, fat_ptr, 16);

    fat_ptr
}

pub fn compile_dyn_call<M: Module>(
    builder: &mut FunctionBuilder,
    receiver_expr: &TypedExpr,
    method_name: &str,
    args: &[TypedExpr],
    ret_ty: &Type,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let fat_ptr = compile_expr(builder, receiver_expr, cg, module);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), fat_ptr, 0);
    let vtable_ptr = builder.ins().load(types::I64, MemFlags::new(), fat_ptr, 8);

    let trait_name = receiver_expr.ty().name_or_default();
    let method_idx = lookup_vtable_method_index(cg.meta, trait_name, method_name).unwrap_or(0);
    let fn_ptr = builder.ins().load(
        types::I64,
        MemFlags::new(),
        vtable_ptr,
        (method_idx * 8) as i32,
    );

    let mut param_tys = vec![Type::Ptr(crate::ast::intern_type(Type::Void))];
    param_tys.extend(args.iter().map(|a| a.ty()));
    let (sig, fn_abi) = abi_signature_for_fn(
        module.isa().default_call_conv(),
        &param_tys,
        ret_ty,
        false,
        &cg.meta.struct_layouts,
        cg.meta.enum_layouts,
    );

    let mut compiled_args = Vec::new();
    let sret_addr_opt = if let PassMode::Indirect { size, align } = fn_abi.ret_mode {
        let (_, addr) = alloc_stack_slot(builder, size, align);
        compiled_args.push(addr);
        Some(addr)
    } else {
        None
    };
    compiled_args.push(data_ptr);

    for (arg, pmode) in args.iter().zip(fn_abi.param_modes.iter().skip(1)) {
        let val = compile_expr(builder, arg, cg, module);
        if !arg.ty().is_copy() && !matches!(arg.ty(), Type::Ref(_) | Type::MutRef(_)) {
            cg.cancel_temp(val);
            if let TypedExpr::Ident(v_name, _, _) = arg {
                cg.mark_moved(builder, v_name);
            }
        }
        match pmode {
            PassMode::Ignore => {}
            PassMode::Direct(target_cl_ty) => {
                compiled_args.push(coerce_typed_val(builder, val, &arg.ty(), *target_cl_ty));
            }
            PassMode::MultiReg { size, chunks, .. } => {
                compiled_args.extend(load_multireg_chunks(builder, module, val, *size, chunks));
            }
            PassMode::Indirect { size, align } => {
                let (_, arg_addr) = alloc_stack_slot(builder, *size, *align);
                emit_memcpy_bytes(builder, module, arg_addr, val, *size);
                compiled_args.push(arg_addr);
            }
        }
    }

    let sig_ref = builder.import_signature(sig);
    let call_inst = builder.ins().call_indirect(sig_ref, fn_ptr, &compiled_args);
    unpack_call_result(builder, module, call_inst, &fn_abi.ret_mode, sret_addr_opt)
}
