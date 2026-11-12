//! codegen/vtables.rs
//! Emits static read-only vtables for `dyn Trait` dispatch using native function relocations.

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, Value};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, FuncId, FuncOrDataId, Linkage, Module};

use crate::ast::Type;
use crate::codegen::ctx::ProgramMeta;
use crate::codegen::layout::{
    abi_signature_for_fn, alloc_stack_slot, emit_memcpy_bytes, load_multireg_chunks, PassMode,
};

fn build_vtable_byval_thunk<M: Module>(
    fn_sym: &str,
    callee_id: FuncId,
    callee_sig: &cranelift_codegen::ir::Signature,
    param0_mode: &PassMode,
    has_sret: bool,
    module: &mut M,
) -> FuncId {
    let thunk_sym = format!("__vtable_thunk_{fn_sym}");
    if let Some(FuncOrDataId::Func(fid)) = module.get_name(&thunk_sym) {
        return fid;
    }

    // Thunk ABI matches `compile_dyn_call`: `[sret?], data_ptr: I64, ...rest_params`.
    let mut thunk_sig = module.make_signature();
    let p0_chunk_count = match param0_mode {
        PassMode::Ignore => 0,
        PassMode::Direct(_) | PassMode::Indirect { .. } => 1,
        PassMode::MultiReg { chunks, .. } => chunks.len(),
    };
    let sret_count = usize::from(has_sret);
    if has_sret {
        thunk_sig.params.push(AbiParam::new(types::I64));
    }
    thunk_sig.params.push(AbiParam::new(types::I64)); // data_ptr
    for p in callee_sig.params.iter().skip(sret_count + p0_chunk_count) {
        thunk_sig.params.push(*p);
    }
    thunk_sig.returns = callee_sig.returns.clone();

    let thunk_id = module
        .declare_function(&thunk_sym, Linkage::Export, &thunk_sig)
        .expect("Failed to declare vtable thunk");

    let mut ctx = module.make_context();
    ctx.func.signature = thunk_sig;
    let mut builder_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = builder.create_block();
        builder.switch_to_block(entry);
        builder.append_block_params_for_function_params(entry);
        let bparams = builder.block_params(entry).to_vec();

        let mut forward_args = Vec::new();
        let mut cursor = 0usize;
        if has_sret {
            forward_args.push(bparams[cursor]);
            cursor += 1;
        }
        let data_ptr = bparams[cursor];
        cursor += 1;

        match param0_mode {
            PassMode::Ignore => {}
            PassMode::Direct(_) => forward_args.push(data_ptr),
            PassMode::MultiReg { size, chunks, .. } => {
                let loaded = load_multireg_chunks(&mut builder, module, data_ptr, *size, chunks);
                forward_args.extend(loaded);
            }
            PassMode::Indirect { size, align } => {
                let (_, arg_addr) = alloc_stack_slot(&mut builder, *size, *align);
                emit_memcpy_bytes(&mut builder, module, arg_addr, data_ptr, *size);
                forward_args.push(arg_addr);
            }
        }
        forward_args.extend_from_slice(&bparams[cursor..]);

        let local_callee = module.declare_func_in_func(callee_id, builder.func);
        let call_inst = builder.ins().call(local_callee, &forward_args);
        let results = builder.inst_results(call_inst).to_vec();
        builder.ins().return_(&results);
        builder.seal_all_blocks();
        builder.finalize();
    }
    let _ = module.define_function(thunk_id, &mut ctx);
    module.clear_context(&mut ctx);
    thunk_id
}

pub fn get_or_build_vtable<M: Module>(
    builder: &mut FunctionBuilder,
    concrete_ty: &Type,
    trait_name: &str,
    meta: &mut ProgramMeta,
    module: &mut M,
) -> Value {
    let type_name = concrete_ty.name_or_default().to_string();
    let vtable_sym = format!("__vtable_{}_{}", type_name, trait_name.replace("::", "_"));

    let data_id = match module.get_name(&vtable_sym) {
        Some(FuncOrDataId::Data(id)) => id,
        _ => {
            let methods = meta
                .trait_methods
                .get(trait_name)
                .or_else(|| {
                    meta.trait_methods
                        .iter()
                        .find(|(k, _)| k.ends_with(&format!("_{trait_name}")))
                        .map(|(_, v)| v)
                })
                .cloned()
                .unwrap_or_default();

            let vtable_bytes = methods.len().max(1) * 8;
            let mut data_desc = DataDescription::new();
            // Zero-initialized regular data (not S_ZEROFILL / BSS) so Mach-O permits function relocations.
            data_desc.define(vec![0u8; vtable_bytes].into_boxed_slice());
            data_desc.set_align(8);

            let call_conv = module.isa().default_call_conv();
            for (idx, method_name) in methods.iter().enumerate() {
                let fn_sym = format!("{}_{}", type_name, method_name);
                let raw_func_id = match module.get_name(&fn_sym) {
                    Some(FuncOrDataId::Func(fid)) => fid,
                    _ => {
                        let mut sig = module.make_signature();
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));
                        module
                            .declare_function(&fn_sym, Linkage::Import, &sig)
                            .expect("Failed to declare trait method in vtable")
                    }
                };

                let entry_func_id = if let (Some(ptys), Some(rty)) = (
                    meta.fn_param_types.get(&fn_sym),
                    meta.fn_return_types.get(&fn_sym),
                ) {
                    let (callee_sig, fn_abi) = abi_signature_for_fn(
                        call_conv,
                        ptys,
                        rty,
                        false,
                        &meta.struct_layouts,
                        meta.enum_layouts,
                    );
                    match fn_abi.param_modes.first() {
                        Some(PassMode::Direct(_)) | None => raw_func_id,
                        Some(p0_mode) => build_vtable_byval_thunk(
                            &fn_sym,
                            raw_func_id,
                            &callee_sig,
                            p0_mode,
                            fn_abi.has_sret,
                            module,
                        ),
                    }
                } else {
                    raw_func_id
                };

                let func_ref = module.declare_func_in_data(entry_func_id, &mut data_desc);
                data_desc.write_function_addr((idx * 8) as u32, func_ref);
            }

            let id = module
                .declare_data(&vtable_sym, Linkage::Export, true, false)
                .expect("Failed to declare static vtable");
            module
                .define_data(id, &data_desc)
                .expect("Failed to define static vtable");
            id
        }
    };

    let local_data = module.declare_data_in_func(data_id, builder.func);
    builder.ins().symbol_value(types::I64, local_data)
}

pub fn lookup_vtable_method_index(meta: &ProgramMeta, trait_name: &str, method_name: &str) -> Option<usize> {
    let methods = meta.trait_methods.get(trait_name).or_else(|| {
        meta.trait_methods
            .iter()
            .find(|(k, _)| k.ends_with(&format!("_{trait_name}")))
            .map(|(_, v)| v)
    })?;
    methods.iter().position(|m| m == method_name)
}
