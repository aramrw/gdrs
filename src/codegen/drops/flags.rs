//! codegen/drops/flags.rs
//! Cranelift drop flags, conditional drops, and drop function pointers.

use std::collections::{HashMap, HashSet};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    types, AbiParam, InstBuilder, MemFlags, StackSlot, StackSlotData, StackSlotKind, Value,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{
    has_drop_glue, synthesis::emit_free_call, synthesis::resolve_or_synthesize_drop_fn,
    EnumLayoutMap,
};
use crate::codegen::layout::is_aggregate_type;
use crate::sanal::StructLayout;

pub fn allocate_drop_flag(builder: &mut FunctionBuilder) -> StackSlot {
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        1,
        0,
    ));
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().stack_store(one, slot, 0);
    slot
}

pub fn mark_drop_flag_moved(builder: &mut FunctionBuilder, slot: StackSlot) {
    let zero = builder.ins().iconst(types::I8, 0);
    builder.ins().stack_store(zero, slot, 0);
}

pub fn mark_drop_flag_active(builder: &mut FunctionBuilder, slot: StackSlot) {
    let one = builder.ins().iconst(types::I8, 1);
    builder.ins().stack_store(one, slot, 0);
}

pub fn emit_drop_for_value<M: Module>(
    builder: &mut FunctionBuilder,
    val: Value,
    ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) {
    let Some(callee) = resolve_or_synthesize_drop_fn(ty, known_drop_fns, struct_layouts, enum_layouts, module) else {
        return;
    };
    let local_callee = module.declare_func_in_func(callee, builder.func);
    builder.ins().call(local_callee, &[val]);
}

pub fn emit_drop_fn_ptr<M: Module>(
    builder: &mut FunctionBuilder,
    inner_ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Value {
    match resolve_or_synthesize_drop_fn(inner_ty, known_drop_fns, struct_layouts, enum_layouts, module) {
        Some(id) => {
            let local_callee = module.declare_func_in_func(id, builder.func);
            builder.ins().func_addr(types::I64, local_callee)
        }
        None => builder.ins().iconst(types::I64, 0),
    }
}

/// Emits a destructor function pointer for heap-boxed aggregates (`rc[T]`, `arc[T]`, `dyn Trait`),
/// running `in_place` drop (if any) and then `free(ptr)` on the heap box.
pub fn emit_heap_drop_fn_ptr<M: Module>(
    builder: &mut FunctionBuilder,
    inner_ty: &Type,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) -> Value {
    if !is_aggregate_type(inner_ty, struct_layouts, enum_layouts) {
        return emit_drop_fn_ptr(builder, inner_ty, known_drop_fns, struct_layouts, enum_layouts, module);
    }

    let in_place_id =
        resolve_or_synthesize_drop_fn(inner_ty, known_drop_fns, struct_layouts, enum_layouts, module);
    let Some(drop_id) = in_place_id else {
        let mut free_sig = module.make_signature();
        free_sig.params.push(AbiParam::new(types::I64));
        let free_id = module
            .declare_function("free", Linkage::Import, &free_sig)
            .unwrap();
        let local_free = module.declare_func_in_func(free_id, builder.func);
        return builder.ins().func_addr(types::I64, local_free);
    };

    let synth_name = format!("__gdrs_heap_drop_{}", crate::sanal::mono::type_suffix(inner_ty));
    let heap_fn_id = if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
        id
    } else {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function(&synth_name, Linkage::Export, &sig)
            .unwrap();
        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut fbuilder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let entry = fbuilder.create_block();
            fbuilder.switch_to_block(entry);
            fbuilder.append_block_params_for_function_params(entry);
            let ptr_val = fbuilder.block_params(entry)[0];

            let drop_body = fbuilder.create_block();
            let exit_blk = fbuilder.create_block();
            fbuilder.ins().brif(ptr_val, drop_body, &[], exit_blk, &[]);

            fbuilder.switch_to_block(drop_body);
            fbuilder.seal_block(drop_body);
            let local_drop = module.declare_func_in_func(drop_id, fbuilder.func);
            fbuilder.ins().call(local_drop, &[ptr_val]);
            emit_free_call(&mut fbuilder, ptr_val, module);
            fbuilder.ins().jump(exit_blk, &[]);

            fbuilder.switch_to_block(exit_blk);
            fbuilder.seal_block(exit_blk);
            fbuilder.ins().return_(&[]);
            fbuilder.seal_all_blocks();
            fbuilder.finalize();
        }
        let _ = module.define_function(fid, &mut ctx);
        module.clear_context(&mut ctx);
        fid
    };
    let local_callee = module.declare_func_in_func(heap_fn_id, builder.func);
    builder.ins().func_addr(types::I64, local_callee)
}

pub fn emit_conditional_drop<M: Module>(
    builder: &mut FunctionBuilder,
    var: Variable,
    ty: &Type,
    slot: StackSlot,
    known_drop_fns: &HashSet<String>,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    module: &mut M,
) {
    if !has_drop_glue(ty, known_drop_fns, struct_layouts, enum_layouts) || builder.is_unreachable() {
        return;
    }

    let flag = builder.ins().stack_load(types::I8, slot, 0);
    let drop_block = builder.create_block();
    let cont_block = builder.create_block();

    builder.ins().brif(flag, drop_block, &[], cont_block, &[]);

    builder.switch_to_block(drop_block);
    builder.seal_block(drop_block);

    // Mark as dropped (flag = 0) to prevent double drop
    mark_drop_flag_moved(builder, slot);

    // Emit the drop glue execution using the exact Variable captured at binding time
    let val = builder.use_var(var);
    emit_drop_for_value(builder, val, ty, known_drop_fns, struct_layouts, enum_layouts, module);

    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}
