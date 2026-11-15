//! codegen/intrinsics/macros.rs
//! Compiler intrinsic macro code generator (`compile_macro_call`).

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{Linkage, Module};

use crate::ast::{Span, Type, TypedExpr};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::expr::{coerce_val, compile_expr, compile_string_constant, cranelift_type_of};
use crate::codegen::layout::{is_aggregate_type, tuple_field_offsets};
use crate::sanal::macros::{parse_format_string, FormatChunk, FormatSpec};

fn format_type_name(ty: &Type) -> String {
    match ty {
        Type::Int => "i64".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I8 => "i8".to_string(),
        Type::U64 => "u64".to_string(),
        Type::U32 => "u32".to_string(),
        Type::U16 => "u16".to_string(),
        Type::U8 => "u8".to_string(),
        Type::Float => "f64".to_string(),
        Type::F32 => "f32".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str => "str".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "()".to_string(),
        Type::Void => "void".to_string(),
        Type::Obj(name) | Type::Enum(name) | Type::Generic(name) => name.to_string(),
        Type::DynTrait(name) => format!("dyn {name}"),
        Type::Array(inner, len) => format!("[{}; {len}]", format_type_name(inner)),
        Type::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(format_type_name).collect();
            if parts.len() == 1 {
                format!("({},)", parts[0])
            } else {
                format!("({})", parts.join(", "))
            }
        }
        Type::Slice(inner) => format!("[{}]", format_type_name(inner)),
        Type::Vec(inner) => format!("Vec<{}>", format_type_name(inner)),
        Type::Box(inner) => format!("Box<{}>", format_type_name(inner)),
        Type::Rc(inner) => format!("Rc<{}>", format_type_name(inner)),
        Type::Arc(inner) => format!("Arc<{}>", format_type_name(inner)),
        Type::FnPtr(params, ret) => {
            let p_str: Vec<String> = params.iter().map(format_type_name).collect();
            if **ret == Type::Unit {
                format!("fn({})", p_str.join(", "))
            } else {
                format!("fn({}) -> {}", p_str.join(", "), format_type_name(ret))
            }
        }
        Type::Ref(inner) => format!("&{}", format_type_name(inner)),
        Type::MutRef(inner) => format!("&mut {}", format_type_name(inner)),
        Type::Ptr(inner) => format!("*{}", format_type_name(inner)),
        Type::Infer(id) => format!("?{id}"),
        Type::Error => "{error}".to_string(),
    }
}

fn emit_log_part<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    type_tag: i64,
    value_bits: Value,
    suffix: i64,
) -> Value {
    let type_tag_val = builder.ins().iconst(types::I64, type_tag);
    let suffix_val = builder.ins().iconst(types::I64, suffix);

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));

    let callee = module
        .declare_function("intrinsic_log_part", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder
        .ins()
        .call(local_callee, &[type_tag_val, value_bits, suffix_val]);
    builder.inst_results(call_inst)[0]
}

fn emit_panic_cstr_and_trap<M: Module>(
    builder: &mut FunctionBuilder,
    msg_ptr: Value,
    span: &Span,
    cg: &CodegenCtx,
    module: &mut M,
) {
    let (file_ptr, line_val, col_val) = if let Some(loc) = cg.current_caller_loc {
        loc
    } else {
        let (file, line, col) = cg.meta.source_map.get_location(span);
        (
            compile_string_constant(builder, &file, module),
            builder.ins().iconst(types::I64, line as i64),
            builder.ins().iconst(types::I64, col as i64),
        )
    };

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("intrinsic_panic_loc", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    builder
        .ins()
        .call(local_callee, &[msg_ptr, file_ptr, line_val, col_val]);
    builder
        .ins()
        .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
}

fn emit_float_to_str<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    val: Value,
    is_f32: bool,
) -> Value {
    let val_f64 = coerce_val(builder, val, types::F64);
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        8,
        3,
    ));
    let slot_addr = builder.ins().stack_addr(types::I64, slot, 0);
    builder.ins().store(MemFlags::new(), val_f64, slot_addr, 0);
    let val_bits = builder.ins().load(types::I64, MemFlags::new(), slot_addr, 0);

    let fn_name = if is_f32 {
        "intrinsic_f32_to_str"
    } else {
        "intrinsic_float_to_str"
    };
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function(fn_name, Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(local_callee, &[val_bits]);
    builder.inst_results(call_inst)[0]
}

fn stage_format_parts(
    builder: &mut FunctionBuilder,
    parts: &[(Value, bool)],
) -> (Value, Value, Value) {
    let count = parts.len();
    let parts_size = (count.max(1) * 8) as u32;
    let owned_size = count.max(1) as u32;

    let parts_slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        parts_size,
        3,
    ));
    let owned_slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        owned_size,
        0,
    ));

    let parts_addr = builder.ins().stack_addr(types::I64, parts_slot, 0);
    let owned_addr = builder.ins().stack_addr(types::I64, owned_slot, 0);

    for (i, &(str_val, is_owned)) in parts.iter().enumerate() {
        builder
            .ins()
            .store(MemFlags::new(), str_val, parts_addr, (i * 8) as i32);
        let flag_val = builder
            .ins()
            .iconst(types::I8, if is_owned { 1 } else { 0 });
        builder
            .ins()
            .store(MemFlags::new(), flag_val, owned_addr, i as i32);
    }

    let count_val = builder.ins().iconst(types::I64, count as i64);
    (count_val, parts_addr, owned_addr)
}

fn emit_format_join_parts<M: Module>(
    builder: &mut FunctionBuilder,
    parts: &[(Value, bool)],
    module: &mut M,
) -> Value {
    let (count_val, parts_addr, owned_addr) = stage_format_parts(builder, parts);

    let mut sig_join = module.make_signature();
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.returns.push(AbiParam::new(types::I64));
    let callee_join = module
        .declare_function("intrinsic_format_join", Linkage::Import, &sig_join)
        .unwrap();
    let local_join = module.declare_func_in_func(callee_join, builder.func);

    let call_inst = builder
        .ins()
        .call(local_join, &[count_val, parts_addr, owned_addr]);
    builder.inst_results(call_inst)[0]
}

fn emit_format_join_parts_to_string<M: Module>(
    builder: &mut FunctionBuilder,
    parts: &[(Value, bool)],
    module: &mut M,
) -> Value {
    let (count_val, parts_addr, owned_addr) = stage_format_parts(builder, parts);
    let (_, out_addr) = crate::codegen::layout::alloc_stack_slot(builder, 24, 8);

    let mut sig_join = module.make_signature();
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.params.push(AbiParam::new(types::I64));
    let callee_join = module
        .declare_function("intrinsic_format_join_to_string", Linkage::Import, &sig_join)
        .unwrap();
    let local_join = module.declare_func_in_func(callee_join, builder.func);
    builder
        .ins()
        .call(local_join, &[count_val, parts_addr, owned_addr, out_addr]);
    out_addr
}

fn has_custom_display(type_name: &str, cg: &CodegenCtx, module: &impl Module) -> bool {
    let to_string_fn = format!("{type_name}_to_string");
    let fmt_fn = format!("{type_name}_fmt");
    cg.meta.fn_return_types.contains_key(&to_string_fn)
        || module.get_name(&to_string_fn).is_some()
        || cg.meta.fn_return_types.contains_key(&fmt_fn)
        || module.get_name(&fmt_fn).is_some()
}

/// Formats a tuple into an owned malloc'd C string in Debug format.
fn emit_tuple_to_debug_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    tuple_ptr: Value,
    elems: &[Type],
    alternate: bool,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    if elems.is_empty() {
        return (compile_string_constant(builder, "()", module), false, None);
    }
    let count = elems.len();
    let vals_slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        (count * 8) as u32,
        3,
    ));
    let vals_addr = builder.ins().stack_addr(types::I64, vals_slot, 0);

    let (_, _, offsets) =
        tuple_field_offsets(elems, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    let mut temp_drops = Vec::new();

    for (i, &e_ty) in elems.iter().enumerate() {
        let off = offsets.get(i).copied().unwrap_or((i * 8) as u32);
        let elem_val = if is_aggregate_type(&e_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            builder.ins().iadd_imm(tuple_ptr, off as i64)
        } else {
            let cl_ty = cranelift_type_of(&e_ty);
            builder.ins().load(cl_ty, MemFlags::new(), tuple_ptr, off as i32)
        };
        let (val_cstr, _is_owned, drop_opt) =
            emit_val_to_cstr(builder, elem_val, e_ty, FormatSpec::Debug { alternate }, cg, module);
        if let Some(d) = drop_opt {
            temp_drops.push(d);
        }
        builder.ins().store(MemFlags::new(), val_cstr, vals_addr, (i * 8) as i32);
    }

    let empty_var_name = compile_string_constant(builder, "", module);
    let count_val = builder.ins().iconst(types::I64, count as i64);
    let alt_val = builder.ins().iconst(types::I64, if alternate { 1 } else { 0 });

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64)); // name
    sig.params.push(AbiParam::new(types::I64)); // count
    sig.params.push(AbiParam::new(types::I64)); // vals
    sig.params.push(AbiParam::new(types::I64)); // alternate
    sig.returns.push(AbiParam::new(types::I64)); // char*
    let callee = module
        .declare_function("intrinsic_format_debug_tuple", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(
        local_callee,
        &[empty_var_name, count_val, vals_addr, alt_val],
    );
    let res_ptr = builder.inst_results(call_inst)[0];

    let mut free_arr_sig = module.make_signature();
    free_arr_sig.params.push(AbiParam::new(types::I64));
    free_arr_sig.params.push(AbiParam::new(types::I64));
    let free_arr_callee = module
        .declare_function("intrinsic_free_cstr_array", Linkage::Import, &free_arr_sig)
        .unwrap();
    let local_free_arr = module.declare_func_in_func(free_arr_callee, builder.func);
    builder.ins().call(local_free_arr, &[count_val, vals_addr]);

    for (tmp_val, tmp_ty) in temp_drops {
        crate::codegen::drops::emit_drop_for_value(
            builder,
            tmp_val,
            &tmp_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        );
    }

    (res_ptr, true, None)
}

fn emit_struct_to_debug_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    struct_name: &str,
    struct_ptr: Value,
    alternate: bool,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    let synth_name = format!(
        "__gdrs_debug_struct_{}_{}",
        struct_name,
        if alternate { "alt" } else { "std" }
    );
    let func_id = if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
        id
    } else {
        let mut fn_sig = module.make_signature();
        fn_sig.params.push(AbiParam::new(types::I64));
        fn_sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function(&synth_name, Linkage::Local, &fn_sig)
            .unwrap();
        let mut ctx = module.make_context();
        ctx.func.signature = fn_sig;
        let mut b_ctx = cranelift_frontend::FunctionBuilderContext::new();
        {
            let mut sub_builder = FunctionBuilder::new(&mut ctx.func, &mut b_ctx);
            let entry = sub_builder.create_block();
            sub_builder.switch_to_block(entry);
            sub_builder.append_block_params_for_function_params(entry);
            let sub_ptr = sub_builder.block_params(entry)[0];
            let (res_cstr, _, _) = emit_struct_to_debug_cstr_body(
                &mut sub_builder,
                struct_name,
                sub_ptr,
                alternate,
                cg,
                module,
            );
            sub_builder.ins().return_(&[res_cstr]);
            sub_builder.seal_all_blocks();
            sub_builder.finalize();
        }
        let _ = module.define_function(fid, &mut ctx);
        module.clear_context(&mut ctx);
        fid
    };
    let local_fn = module.declare_func_in_func(func_id, builder.func);
    let call_inst = builder.ins().call(local_fn, &[struct_ptr]);
    (builder.inst_results(call_inst)[0], true, None)
}

fn emit_struct_to_debug_cstr_body<M: Module>(
    builder: &mut FunctionBuilder,
    struct_name: &str,
    struct_ptr: Value,
    alternate: bool,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    let clean_name = struct_name.rsplit_once('_').map(|(_, s)| s).unwrap_or(struct_name);
    let name_val = compile_string_constant(builder, clean_name, module);
    let zero_count = builder.ins().iconst(types::I64, 0);
    let null_ptrs = builder.ins().iconst(types::I64, 0);
    let alt_val = builder.ins().iconst(types::I64, if alternate { 1 } else { 0 });

    let layout_opt = crate::codegen::layout::find_struct_layout(&cg.meta.struct_layouts, struct_name);
    let Some(layout) = layout_opt else {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module
            .declare_function("intrinsic_format_debug_struct", Linkage::Import, &sig)
            .unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let call_inst = builder.ins().call(
            local_callee,
            &[name_val, zero_count, null_ptrs, null_ptrs, alt_val],
        );
        return (builder.inst_results(call_inst)[0], true, None);
    };

    let mut fields: Vec<(&String, u32, Type)> = layout
        .field_offsets
        .iter()
        .map(|(name, &(off, ty))| (name, off, ty))
        .collect();
    fields.sort_by_key(|&(_, off, _)| off);

    let count = fields.len();
    if count == 0 {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module
            .declare_function("intrinsic_format_debug_struct", Linkage::Import, &sig)
            .unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let call_inst = builder.ins().call(
            local_callee,
            &[name_val, zero_count, null_ptrs, null_ptrs, alt_val],
        );
        return (builder.inst_results(call_inst)[0], true, None);
    }

    let names_slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        (count * 8) as u32,
        3,
    ));
    let vals_slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        (count * 8) as u32,
        3,
    ));
    let names_addr = builder.ins().stack_addr(types::I64, names_slot, 0);
    let vals_addr = builder.ins().stack_addr(types::I64, vals_slot, 0);

    let mut temp_drops = Vec::new();

    for (i, (fname, off, fty)) in fields.iter().enumerate() {
        let name_const = compile_string_constant(builder, fname, module);
        builder.ins().store(MemFlags::new(), name_const, names_addr, (i * 8) as i32);

        let field_val = if is_aggregate_type(fty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            builder.ins().iadd_imm(struct_ptr, *off as i64)
        } else {
            let cl_ty = cranelift_type_of(fty);
            builder.ins().load(cl_ty, MemFlags::new(), struct_ptr, *off as i32)
        };

        let (val_cstr, _is_owned, drop_opt) =
            emit_val_to_cstr(builder, field_val, *fty, FormatSpec::Debug { alternate }, cg, module);
        if let Some(d) = drop_opt {
            temp_drops.push(d);
        }
        builder.ins().store(MemFlags::new(), val_cstr, vals_addr, (i * 8) as i32);
    }

    let count_val = builder.ins().iconst(types::I64, count as i64);

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64)); // name
    sig.params.push(AbiParam::new(types::I64)); // count
    sig.params.push(AbiParam::new(types::I64)); // names
    sig.params.push(AbiParam::new(types::I64)); // vals
    sig.params.push(AbiParam::new(types::I64)); // alternate
    sig.returns.push(AbiParam::new(types::I64)); // char*
    let callee = module
        .declare_function("intrinsic_format_debug_struct", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(
        local_callee,
        &[name_val, count_val, names_addr, vals_addr, alt_val],
    );
    let res_ptr = builder.inst_results(call_inst)[0];

    let mut free_arr_sig = module.make_signature();
    free_arr_sig.params.push(AbiParam::new(types::I64));
    free_arr_sig.params.push(AbiParam::new(types::I64));
    let free_arr_callee = module
        .declare_function("intrinsic_free_cstr_array", Linkage::Import, &free_arr_sig)
        .unwrap();
    let local_free_arr = module.declare_func_in_func(free_arr_callee, builder.func);
    builder.ins().call(local_free_arr, &[count_val, vals_addr]);

    for (tmp_val, tmp_ty) in temp_drops {
        crate::codegen::drops::emit_drop_for_value(
            builder,
            tmp_val,
            &tmp_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        );
    }

    (res_ptr, true, None)
}

fn emit_enum_to_debug_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    enum_name: &str,
    enum_ptr: Value,
    alternate: bool,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    let synth_name = format!(
        "__gdrs_debug_enum_{}_{}",
        enum_name,
        if alternate { "alt" } else { "std" }
    );
    let func_id = if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&synth_name) {
        id
    } else {
        let mut fn_sig = module.make_signature();
        fn_sig.params.push(AbiParam::new(types::I64));
        fn_sig.returns.push(AbiParam::new(types::I64));
        let fid = module
            .declare_function(&synth_name, Linkage::Local, &fn_sig)
            .unwrap();
        let mut ctx = module.make_context();
        ctx.func.signature = fn_sig;
        let mut b_ctx = cranelift_frontend::FunctionBuilderContext::new();
        {
            let mut sub_builder = FunctionBuilder::new(&mut ctx.func, &mut b_ctx);
            let entry = sub_builder.create_block();
            sub_builder.switch_to_block(entry);
            sub_builder.append_block_params_for_function_params(entry);
            let sub_ptr = sub_builder.block_params(entry)[0];
            let (res_cstr, _, _) = emit_enum_to_debug_cstr_body(
                &mut sub_builder,
                enum_name,
                sub_ptr,
                alternate,
                cg,
                module,
            );
            sub_builder.ins().return_(&[res_cstr]);
            sub_builder.seal_all_blocks();
            sub_builder.finalize();
        }
        let _ = module.define_function(fid, &mut ctx);
        module.clear_context(&mut ctx);
        fid
    };
    let local_fn = module.declare_func_in_func(func_id, builder.func);
    let call_inst = builder.ins().call(local_fn, &[enum_ptr]);
    (builder.inst_results(call_inst)[0], true, None)
}

fn emit_enum_to_debug_cstr_body<M: Module>(
    builder: &mut FunctionBuilder,
    enum_name: &str,
    enum_ptr: Value,
    alternate: bool,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    let variants_opt = crate::codegen::drops::find_enum_layout(enum_name, cg.meta.enum_layouts);
    let clean_enum = enum_name.rsplit_once('_').map(|(_, s)| s).unwrap_or(enum_name);
    let alt_val = builder.ins().iconst(types::I64, if alternate { 1 } else { 0 });

    let Some(variants) = variants_opt else {
        let fallback_val = compile_string_constant(builder, clean_enum, module);
        let zero_count = builder.ins().iconst(types::I64, 0);
        let null_vals = builder.ins().iconst(types::I64, 0);
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module
            .declare_function("intrinsic_format_debug_tuple", Linkage::Import, &sig)
            .unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let call_inst = builder.ins().call(
            local_callee,
            &[fallback_val, zero_count, null_vals, alt_val],
        );
        return (builder.inst_results(call_inst)[0], true, None);
    };

    let tag = builder.ins().load(types::I64, MemFlags::new(), enum_ptr, 0);

    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    let first_block = builder.create_block();
    builder.ins().jump(first_block, &[]);

    let mut next_block = first_block;

    for (var_name, var_tag, payload_tys) in variants {
        let curr_block = next_block;
        next_block = builder.create_block();

        builder.switch_to_block(curr_block);
        builder.seal_block(curr_block);

        let is_match = builder.ins().icmp_imm(IntCC::Equal, tag, *var_tag);
        let arm_block = builder.create_block();
        builder.ins().brif(is_match, arm_block, &[], next_block, &[]);

        builder.switch_to_block(arm_block);
        builder.seal_block(arm_block);

        let payload_count = payload_tys.len();
        let clean_var = var_name.rsplit_once("::").map(|(_, s)| s).unwrap_or(var_name);
        let var_name_val = compile_string_constant(builder, clean_var, module);

        if payload_count == 0 {
            let zero_count = builder.ins().iconst(types::I64, 0);
            let null_vals = builder.ins().iconst(types::I64, 0);
            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64)); // name
            sig.params.push(AbiParam::new(types::I64)); // count
            sig.params.push(AbiParam::new(types::I64)); // vals
            sig.params.push(AbiParam::new(types::I64)); // alternate
            sig.returns.push(AbiParam::new(types::I64)); // char*
            let callee = module
                .declare_function("intrinsic_format_debug_tuple", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(
                local_callee,
                &[var_name_val, zero_count, null_vals, alt_val],
            );
            let res_ptr = builder.inst_results(call_inst)[0];
            builder.ins().jump(merge_block, &[res_ptr]);
        } else {
            let vals_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                (payload_count * 8) as u32,
                3,
            ));
            let vals_addr = builder.ins().stack_addr(types::I64, vals_slot, 0);

            let (_, _, offsets) = crate::codegen::layout::enum_variant_offsets(
                payload_tys,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
            );

            let mut temp_drops = Vec::new();

            for (i, p_ty) in payload_tys.iter().enumerate() {
                let off = offsets.get(i).copied().unwrap_or(((i + 1) * 8) as u32);
                let p_val = if is_aggregate_type(p_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                    builder.ins().iadd_imm(enum_ptr, off as i64)
                } else {
                    let cl_ty = cranelift_type_of(p_ty);
                    builder.ins().load(cl_ty, MemFlags::new(), enum_ptr, off as i32)
                };

                let (val_cstr, _is_owned, drop_opt) =
                    emit_val_to_cstr(builder, p_val, *p_ty, FormatSpec::Debug { alternate }, cg, module);
                if let Some(d) = drop_opt {
                    temp_drops.push(d);
                }
                builder.ins().store(MemFlags::new(), val_cstr, vals_addr, (i * 8) as i32);
            }

            let count_val = builder.ins().iconst(types::I64, payload_count as i64);

            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64)); // name
            sig.params.push(AbiParam::new(types::I64)); // count
            sig.params.push(AbiParam::new(types::I64)); // vals
            sig.params.push(AbiParam::new(types::I64)); // alternate
            sig.returns.push(AbiParam::new(types::I64)); // char*
            let callee = module
                .declare_function("intrinsic_format_debug_tuple", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(
                local_callee,
                &[var_name_val, count_val, vals_addr, alt_val],
            );
            let res_ptr = builder.inst_results(call_inst)[0];

            let mut free_arr_sig = module.make_signature();
            free_arr_sig.params.push(AbiParam::new(types::I64));
            free_arr_sig.params.push(AbiParam::new(types::I64));
            let free_arr_callee = module
                .declare_function("intrinsic_free_cstr_array", Linkage::Import, &free_arr_sig)
                .unwrap();
            let local_free_arr = module.declare_func_in_func(free_arr_callee, builder.func);
            builder.ins().call(local_free_arr, &[count_val, vals_addr]);

            for (tmp_val, tmp_ty) in temp_drops {
                crate::codegen::drops::emit_drop_for_value(
                    builder,
                    tmp_val,
                    &tmp_ty,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
            }

            builder.ins().jump(merge_block, &[res_ptr]);
        }
    }

    builder.switch_to_block(next_block);
    builder.seal_block(next_block);
    let fallback_val = compile_string_constant(builder, "<unknown enum variant>", module);
    let zero_count = builder.ins().iconst(types::I64, 0);
    let null_vals = builder.ins().iconst(types::I64, 0);
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("intrinsic_format_debug_tuple", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(
        local_callee,
        &[fallback_val, zero_count, null_vals, alt_val],
    );
    let fallback_res = builder.inst_results(call_inst)[0];
    builder.ins().jump(merge_block, &[fallback_res]);

    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    let res = builder.block_params(merge_block)[0];

    (res, true, None)
}

fn emit_list_to_debug_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    list_val: Value,
    elem_ty: Type,
    is_array: Option<usize>,
    alternate: bool,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    if let Some(arr_len) = is_array {
        if arr_len == 0 {
            return (compile_string_constant(builder, "[]", module), false, None);
        }
        let vals_slot = builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (arr_len * 8) as u32,
            3,
        ));
        let vals_addr = builder.ins().stack_addr(types::I64, vals_slot, 0);

        let elem_size = crate::codegen::layout::array_stride(&elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
        let mut temp_drops = Vec::new();

        for i in 0..arr_len {
            let off = (i as u32) * elem_size;
            let elem_val = if is_aggregate_type(&elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                builder.ins().iadd_imm(list_val, off as i64)
            } else {
                let cl_ty = cranelift_type_of(&elem_ty);
                builder.ins().load(cl_ty, MemFlags::new(), list_val, off as i32)
            };

            let (val_cstr, _is_owned, drop_opt) =
                emit_val_to_cstr(builder, elem_val, elem_ty, FormatSpec::Debug { alternate }, cg, module);
            if let Some(d) = drop_opt {
                temp_drops.push(d);
            }
            builder.ins().store(MemFlags::new(), val_cstr, vals_addr, (i * 8) as i32);
        }

        let count_val = builder.ins().iconst(types::I64, arr_len as i64);
        let alt_val = builder.ins().iconst(types::I64, if alternate { 1 } else { 0 });

        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // count
        sig.params.push(AbiParam::new(types::I64)); // vals
        sig.params.push(AbiParam::new(types::I64)); // alternate
        sig.returns.push(AbiParam::new(types::I64)); // char*
        let callee = module
            .declare_function("intrinsic_format_debug_list", Linkage::Import, &sig)
            .unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let call_inst = builder.ins().call(local_callee, &[count_val, vals_addr, alt_val]);
        let res_ptr = builder.inst_results(call_inst)[0];

        let mut free_arr_sig = module.make_signature();
        free_arr_sig.params.push(AbiParam::new(types::I64));
        free_arr_sig.params.push(AbiParam::new(types::I64));
        let free_arr_callee = module
            .declare_function("intrinsic_free_cstr_array", Linkage::Import, &free_arr_sig)
            .unwrap();
        let local_free_arr = module.declare_func_in_func(free_arr_callee, builder.func);
        builder.ins().call(local_free_arr, &[count_val, vals_addr]);

        for (tmp_val, tmp_ty) in temp_drops {
            crate::codegen::drops::emit_drop_for_value(
                builder,
                tmp_val,
                &tmp_ty,
                &cg.meta.known_drop_fns,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
                module,
            );
        }

        (res_ptr, true, None)
    } else {
        // Dynamic Vec or Slice
        let buf_ptr = builder.ins().load(types::I64, MemFlags::new(), list_val, 0);
        let len_val = builder.ins().load(types::I64, MemFlags::new(), list_val, 8);

        let is_empty = builder.ins().icmp_imm(IntCC::Equal, len_val, 0);
        let empty_str = compile_string_constant(builder, "[]", module);

        let non_empty_blk = builder.create_block();
        let merge_blk = builder.create_block();
        builder.append_block_param(merge_blk, types::I64);

        builder.ins().brif(is_empty, merge_blk, &[empty_str], non_empty_blk, &[]);

        builder.switch_to_block(non_empty_blk);
        builder.seal_block(non_empty_blk);

        let vals_bytes = builder.ins().imul_imm(len_val, 8);
        let mut malloc_sig = module.make_signature();
        malloc_sig.params.push(AbiParam::new(types::I64));
        malloc_sig.returns.push(AbiParam::new(types::I64));
        let malloc_callee = module.declare_function("malloc", Linkage::Import, &malloc_sig).unwrap();
        let local_malloc = module.declare_func_in_func(malloc_callee, builder.func);
        let call = builder.ins().call(local_malloc, &[vals_bytes]);
        let vals_addr = builder.inst_results(call)[0];

        let elem_size = crate::codegen::layout::array_stride(&elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);

        let loop_header = builder.create_block();
        let loop_body = builder.create_block();
        let loop_exit = builder.create_block();

        builder.append_block_param(loop_header, types::I64);
        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().jump(loop_header, &[zero]);

        builder.switch_to_block(loop_header);
        let i_val = builder.block_params(loop_header)[0];
        let cond = builder.ins().icmp(IntCC::SignedLessThan, i_val, len_val);
        builder.ins().brif(cond, loop_body, &[], loop_exit, &[]);

        builder.switch_to_block(loop_body);
        builder.seal_block(loop_body);

        let elem_off = builder.ins().imul_imm(i_val, elem_size as i64);
        let elem_addr = builder.ins().iadd(buf_ptr, elem_off);

        let elem_val = if is_aggregate_type(&elem_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            elem_addr
        } else {
            let cl_ty = cranelift_type_of(&elem_ty);
            builder.ins().load(cl_ty, MemFlags::new(), elem_addr, 0)
        };

        let (val_cstr, _, _) =
            emit_val_to_cstr(builder, elem_val, elem_ty, FormatSpec::Debug { alternate }, cg, module);

        let slot_off = builder.ins().imul_imm(i_val, 8);
        let slot_addr = builder.ins().iadd(vals_addr, slot_off);
        builder.ins().store(MemFlags::new(), val_cstr, slot_addr, 0);

        let next_i = builder.ins().iadd_imm(i_val, 1);
        builder.ins().jump(loop_header, &[next_i]);

        builder.seal_block(loop_header);

        builder.switch_to_block(loop_exit);
        builder.seal_block(loop_exit);

        let alt_val = builder.ins().iconst(types::I64, if alternate { 1 } else { 0 });

        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // count
        sig.params.push(AbiParam::new(types::I64)); // vals
        sig.params.push(AbiParam::new(types::I64)); // alternate
        sig.returns.push(AbiParam::new(types::I64)); // char*
        let callee = module
            .declare_function("intrinsic_format_debug_list_and_free", Linkage::Import, &sig)
            .unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let call_inst = builder.ins().call(local_callee, &[len_val, vals_addr, alt_val]);
        let res_ptr = builder.inst_results(call_inst)[0];

        builder.ins().jump(merge_blk, &[res_ptr]);

        builder.switch_to_block(merge_blk);
        builder.seal_block(merge_blk);
        let res = builder.block_params(merge_blk)[0];

        (res, true, None)
    }
}

/// Converts a value of `raw_ty` to `(cstr_ptr, is_malloc_owned, optional_temp_string_drop)`.
fn emit_val_to_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    val: Value,
    raw_ty: Type,
    spec: FormatSpec,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    let (val, ty) = match raw_ty {
        Type::Ref(inner) | Type::MutRef(inner) => {
            if matches!(
                *inner,
                Type::String
                    | Type::Obj(_)
                    | Type::Enum(_)
                    | Type::Tuple(_)
                    | Type::Array(_, _)
                    | Type::Vec(_)
                    | Type::Slice(_)
            ) {
                (val, *inner)
            } else if inner.is_numeric() || *inner == Type::Bool {
                let cl_ty = cranelift_type_of(inner);
                let loaded = builder.ins().load(cl_ty, MemFlags::new(), val, 0);
                (loaded, *inner)
            } else {
                (val, *inner)
            }
        }
        other => (val, other),
    };

    match spec {
        FormatSpec::Display => {
            match ty {
                Type::Str => (val, false, None),
                Type::String | Type::Obj("String") | Type::Obj("std_string_String") => {
                    let str_ptr = builder.ins().load(types::I64, MemFlags::new(), val, 0);
                    let is_null = builder.ins().icmp_imm(IntCC::Equal, str_ptr, 0);
                    let empty_str = compile_string_constant(builder, "", module);
                    (builder.ins().select(is_null, empty_str, str_ptr), false, None)
                }
                _ if ty.is_unsigned_integer() => {
                    let val_i64 = coerce_val(builder, val, types::I64);
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_uint_to_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val_i64]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::Int | Type::I32 | Type::I16 | Type::I8 => {
                    let val_i64 = coerce_val(builder, val, types::I64);
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_int_to_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val_i64]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::F32 => (emit_float_to_str(builder, module, val, true), true, None),
                Type::Float => (emit_float_to_str(builder, module, val, false), true, None),
                _ if builder.func.dfg.value_type(val) == types::F32 => {
                    (emit_float_to_str(builder, module, val, true), true, None)
                }
                _ if builder.func.dfg.value_type(val) == types::F64 => {
                    (emit_float_to_str(builder, module, val, false), true, None)
                }
                Type::Bool => {
                    let val_i8 = coerce_val(builder, val, types::I8);
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I8));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_bool_to_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val_i8]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::Obj(tn) if matches!(tn, "f32" | "F32") => {
                    (emit_float_to_str(builder, module, val, true), true, None)
                }
                Type::Obj(tn) if matches!(tn, "f64" | "Float" | "F64") => {
                    (emit_float_to_str(builder, module, val, false), true, None)
                }
                Type::Obj(tn) | Type::Enum(tn) => {
                    if has_custom_display(tn, cg, module) {
                        let (cstr_ptr, drop_opt) =
                            compile_custom_display_to_cstr(builder, tn, val, cg, module);
                        (cstr_ptr, false, drop_opt)
                    } else {
                        let fallback = compile_string_constant(builder, &format!("<{tn}>"), module);
                        (fallback, false, None)
                    }
                }
                Type::Box(inner) => {
                    let elem_val = if is_aggregate_type(inner, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                        val
                    } else {
                        let cl_ty = cranelift_type_of(inner);
                        builder.ins().load(cl_ty, MemFlags::new(), val, 0)
                    };
                    emit_val_to_cstr(builder, elem_val, *inner, spec, cg, module)
                }
                Type::Rc(inner) | Type::Arc(inner) => {
                    let elem_val = if is_aggregate_type(inner, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                        builder.ins().load(types::I64, MemFlags::new(), val, 8)
                    } else {
                        let cl_ty = cranelift_type_of(inner);
                        builder.ins().load(cl_ty, MemFlags::new(), val, 8)
                    };
                    emit_val_to_cstr(builder, elem_val, *inner, spec, cg, module)
                }
                Type::Tuple(elems) => emit_tuple_to_cstr(builder, val, elems, cg, module),
                _ => (
                    compile_string_constant(builder, &format!("<{}>", format_type_name(&ty)), module),
                    false,
                    None,
                ),
            }
        }
        FormatSpec::Debug { alternate } => {
            match ty {
                Type::Str => {
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_debug_escape_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::String | Type::Obj("String") | Type::Obj("std_string_String") => {
                    let str_ptr = builder.ins().load(types::I64, MemFlags::new(), val, 0);
                    let is_null = builder.ins().icmp_imm(IntCC::Equal, str_ptr, 0);
                    let empty_str = compile_string_constant(builder, "", module);
                    let safe_ptr = builder.ins().select(is_null, empty_str, str_ptr);

                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_debug_escape_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[safe_ptr]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::Ptr(_) | Type::FnPtr(_, _) => {
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_ptr_to_debug_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::Unit => {
                    (compile_string_constant(builder, "()", module), false, None)
                }
                _ if ty.is_unsigned_integer() => {
                    let val_i64 = coerce_val(builder, val, types::I64);
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_uint_to_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val_i64]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::Int | Type::I32 | Type::I16 | Type::I8 => {
                    let val_i64 = coerce_val(builder, val, types::I64);
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_int_to_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val_i64]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::F32 => (emit_float_to_str(builder, module, val, true), true, None),
                Type::Float => (emit_float_to_str(builder, module, val, false), true, None),
                _ if builder.func.dfg.value_type(val) == types::F32 => {
                    (emit_float_to_str(builder, module, val, true), true, None)
                }
                _ if builder.func.dfg.value_type(val) == types::F64 => {
                    (emit_float_to_str(builder, module, val, false), true, None)
                }
                Type::Bool => {
                    let val_i8 = coerce_val(builder, val, types::I8);
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I8));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function("intrinsic_bool_to_str", Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val_i8]);
                    (builder.inst_results(call_inst)[0], true, None)
                }
                Type::Tuple(elems) => emit_tuple_to_debug_cstr(builder, val, elems, alternate, cg, module),
                Type::Array(inner, len) => {
                    emit_list_to_debug_cstr(builder, val, *inner, Some(len), alternate, cg, module)
                }
                Type::Slice(inner) | Type::Vec(inner) => {
                    emit_list_to_debug_cstr(builder, val, *inner, None, alternate, cg, module)
                }
                Type::Box(inner) => {
                    let elem_val = if is_aggregate_type(inner, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                        val
                    } else {
                        let cl_ty = cranelift_type_of(inner);
                        builder.ins().load(cl_ty, MemFlags::new(), val, 0)
                    };
                    emit_val_to_cstr(builder, elem_val, *inner, spec, cg, module)
                }
                Type::Rc(inner) | Type::Arc(inner) => {
                    let elem_val = if is_aggregate_type(inner, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                        builder.ins().load(types::I64, MemFlags::new(), val, 8)
                    } else {
                        let cl_ty = cranelift_type_of(inner);
                        builder.ins().load(cl_ty, MemFlags::new(), val, 8)
                    };
                    emit_val_to_cstr(builder, elem_val, *inner, spec, cg, module)
                }
                Type::Obj(tn) | Type::Enum(tn) => {
                    if crate::codegen::drops::find_enum_layout(tn, cg.meta.enum_layouts).is_some() {
                        emit_enum_to_debug_cstr(builder, tn, val, alternate, cg, module)
                    } else if crate::codegen::layout::find_struct_layout(&cg.meta.struct_layouts, tn).is_some() {
                        emit_struct_to_debug_cstr(builder, tn, val, alternate, cg, module)
                    } else {
                        let clean = tn.rsplit_once('_').map(|(_, s)| s).unwrap_or(tn);
                        (compile_string_constant(builder, clean, module), false, None)
                    }
                }
                _ => (
                    compile_string_constant(builder, &format!("<{}>", format_type_name(&ty)), module),
                    false,
                    None,
                ),
            }
        }
    }
}

/// Formats a tuple `(e0, e1, ...)` into an owned malloc'd C string `"(v0, v1, ...)"`.
fn emit_tuple_to_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    tuple_ptr: Value,
    elems: &[Type],
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    if elems.is_empty() {
        return (compile_string_constant(builder, "()", module), false, None);
    }

    let (_, _, offsets) =
        tuple_field_offsets(elems, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    let mut parts: Vec<(Value, bool)> = Vec::new();
    let mut temp_drops: Vec<(Value, Type)> = Vec::new();

    parts.push((compile_string_constant(builder, "(", module), false));
    for (i, &e_ty) in elems.iter().enumerate() {
        if i > 0 {
            parts.push((compile_string_constant(builder, ", ", module), false));
        }
        let off = offsets.get(i).copied().unwrap_or((i * 8) as u32);
        let elem_val = if is_aggregate_type(&e_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
            builder.ins().iadd_imm(tuple_ptr, off as i64)
        } else {
            let cl_ty = cranelift_type_of(&e_ty);
            builder
                .ins()
                .load(cl_ty, MemFlags::new(), tuple_ptr, off as i32)
        };
        let (cstr_ptr, is_owned, drop_opt) = emit_val_to_cstr(builder, elem_val, e_ty, FormatSpec::Display, cg, module);
        if let Some(d) = drop_opt {
            temp_drops.push(d);
        }
        parts.push((cstr_ptr, is_owned));
    }
    let close_lit = if elems.len() == 1 { ",)" } else { ")" };
    parts.push((compile_string_constant(builder, close_lit, module), false));

    let joined = emit_format_join_parts(builder, &parts, module);
    for (tmp_val, tmp_ty) in temp_drops {
        crate::codegen::drops::emit_drop_for_value(
            builder,
            tmp_val,
            &tmp_ty,
            &cg.meta.known_drop_fns,
            &cg.meta.struct_layouts,
            cg.meta.enum_layouts,
            module,
        );
    }
    (joined, true, None)
}

/// Evaluates `args` where `args[0]` is a format string literal and collects parts + temp drops.
fn collect_format_parts<M: Module>(
    builder: &mut FunctionBuilder,
    args: &[TypedExpr],
    cg: &mut CodegenCtx,
    module: &mut M,
) -> (Vec<(Value, bool)>, Vec<(Value, Type)>) {
    let mut parts: Vec<(Value, bool)> = Vec::new();
    let mut temp_string_drops: Vec<(Value, Type)> = Vec::new();

    if let Some(TypedExpr::String(raw_fmt, fmt_span)) = args.first() {
        let chunks = parse_format_string(raw_fmt, true, fmt_span).unwrap_or_default();
        for chunk in chunks {
            match chunk {
                FormatChunk::Literal(lit) => {
                    let ptr = compile_string_constant(builder, &lit, module);
                    parts.push((ptr, false));
                }
                FormatChunk::Hole { arg_idx, spec } => {
                    if let Some(arg) = args.get(1 + arg_idx) {
                        let val = compile_expr(builder, arg, cg, module);
                        let (cstr_ptr, is_owned, drop_opt) =
                            emit_val_to_cstr(builder, val, arg.ty(), spec, cg, module);
                        if let Some(d) = drop_opt {
                            temp_string_drops.push(d);
                        }
                        parts.push((cstr_ptr, is_owned));
                    }
                }
            }
        }
    }

    (parts, temp_string_drops)
}

/// Evaluates `args` where `args[0]` is a format string literal and returns `(cstr_ptr, temp_drops)`.
fn emit_format_interpolated<M: Module>(
    builder: &mut FunctionBuilder,
    args: &[TypedExpr],
    cg: &mut CodegenCtx,
    module: &mut M,
) -> (Value, Vec<(Value, Type)>) {
    let (parts, temp_string_drops) = collect_format_parts(builder, args, cg, module);
    let joined = emit_format_join_parts(builder, &parts, module);
    (joined, temp_string_drops)
}

/// Evaluates `args` and returns `(String stack slot ptr, temp_drops)`.
fn emit_format_interpolated_to_string<M: Module>(
    builder: &mut FunctionBuilder,
    args: &[TypedExpr],
    cg: &mut CodegenCtx,
    module: &mut M,
) -> (Value, Vec<(Value, Type)>) {
    let (parts, temp_string_drops) = collect_format_parts(builder, args, cg, module);
    let joined_str = emit_format_join_parts_to_string(builder, &parts, module);
    (joined_str, temp_string_drops)
}

fn compile_print_macro<M: Module>(
    builder: &mut FunctionBuilder,
    args: &[TypedExpr],
    trailing_newline: bool,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    if args.is_empty() {
        let zero = builder.ins().iconst(types::I64, 0);
        return if trailing_newline {
            emit_log_part(builder, module, 5, zero, 2)
        } else {
            zero
        };
    }

    let Some(TypedExpr::String(raw_fmt, fmt_span)) = args.first() else {
        let zero = builder.ins().iconst(types::I64, 0);
        return zero;
    };

    let chunks = parse_format_string(raw_fmt, true, fmt_span).unwrap_or_default();
    if chunks.is_empty() {
        let zero = builder.ins().iconst(types::I64, 0);
        return if trailing_newline {
            emit_log_part(builder, module, 5, zero, 2)
        } else {
            zero
        };
    }

    let mut last_val = builder.ins().iconst(types::I64, 0);
    for (idx, chunk) in chunks.iter().enumerate() {
        let is_last = idx + 1 == chunks.len();
        let suffix = if is_last && trailing_newline { 2 } else { 0 };

        match chunk {
            FormatChunk::Literal(lit) => {
                let ptr = compile_string_constant(builder, lit, module);
                last_val = emit_log_part(builder, module, 2, ptr, suffix);
            }
            FormatChunk::Hole { arg_idx, spec } => {
                let Some(arg) = args.get(1 + arg_idx) else {
                    continue;
                };
                let effective_ty = match arg.ty() {
                    Type::Ref(inner) | Type::MutRef(inner) => *inner,
                    other => other,
                };
                let mut temp_string_drop: Option<(Value, Type)> = None;
                let mut temp_cstr_free: Option<Value> = None;
                let (raw_val, type_tag) = if *spec != FormatSpec::Display
                    || matches!(effective_ty, Type::Box(_) | Type::Rc(_) | Type::Arc(_))
                {
                    let target_val = compile_expr(builder, arg, cg, module);
                    let (cstr_ptr, is_owned, drop_opt) =
                        emit_val_to_cstr(builder, target_val, arg.ty(), *spec, cg, module);
                    temp_string_drop = drop_opt;
                    if is_owned {
                        temp_cstr_free = Some(cstr_ptr);
                    }
                    (cstr_ptr, 2)
                } else {
                    match effective_ty {
                        _ if effective_ty.is_unsigned_integer() => (compile_expr(builder, arg, cg, module), 6),
                        Type::Int | Type::I32 | Type::I16 | Type::I8 => (compile_expr(builder, arg, cg, module), 0),
                        Type::Bool => (compile_expr(builder, arg, cg, module), 1),
                        Type::Str => (compile_expr(builder, arg, cg, module), 2),
                        Type::String | Type::Obj("String") | Type::Obj("std_string_String") => {
                            let string_obj_val = compile_expr(builder, arg, cg, module);
                            let str_ptr =
                                builder
                                    .ins()
                                    .load(types::I64, MemFlags::new(), string_obj_val, 0);
                            let is_null = builder.ins().icmp_imm(IntCC::Equal, str_ptr, 0);
                            let empty_str = compile_string_constant(builder, "", module);
                            (builder.ins().select(is_null, empty_str, str_ptr), 2)
                        }
                        Type::Float => (compile_expr(builder, arg, cg, module), 3),
                        Type::F32 => (compile_expr(builder, arg, cg, module), 4),
                        Type::Obj(tn) | Type::Enum(tn) => {
                            let target_val = compile_expr(builder, arg, cg, module);
                            if has_custom_display(tn, cg, module) {
                                let (str_ptr, drop_opt) =
                                    compile_custom_display_to_cstr(builder, tn, target_val, cg, module);
                                temp_string_drop = drop_opt;
                                (str_ptr, 2)
                            } else {
                                (
                                    compile_string_constant(builder, &format!("<{tn}>"), module),
                                    2,
                                )
                            }
                        }
                        Type::Tuple(elems) => {
                            let tuple_ptr = compile_expr(builder, arg, cg, module);
                            let (cstr_ptr, is_owned, drop_opt) =
                                emit_tuple_to_cstr(builder, tuple_ptr, elems, cg, module);
                            temp_string_drop = drop_opt;
                            if is_owned {
                                temp_cstr_free = Some(cstr_ptr);
                            }
                            (cstr_ptr, 2)
                        }
                        _ => (compile_expr(builder, arg, cg, module), 0),
                    }
                };

                let value_bits = {
                    let raw_ty = builder.func.dfg.value_type(raw_val);
                    if raw_ty == types::F64 {
                        builder.ins().bitcast(types::I64, MemFlags::new(), raw_val)
                    } else if raw_ty == types::F32 {
                        let promoted = builder.ins().fpromote(types::F64, raw_val);
                        builder.ins().bitcast(types::I64, MemFlags::new(), promoted)
                    } else if raw_ty == types::I32 || raw_ty == types::I16 || raw_ty == types::I8 {
                        if effective_ty.is_unsigned_integer() {
                            builder.ins().uextend(types::I64, raw_val)
                        } else {
                            builder.ins().sextend(types::I64, raw_val)
                        }
                    } else {
                        raw_val
                    }
                };

                last_val = emit_log_part(builder, module, type_tag, value_bits, suffix);
                if let Some(cstr_ptr) = temp_cstr_free {
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    let callee = module.declare_function("free", Linkage::Import, &sig).unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    builder.ins().call(local_callee, &[cstr_ptr]);
                }
                if let Some((tmp_val, tmp_ty)) = temp_string_drop {
                    crate::codegen::drops::emit_drop_for_value(
                        builder,
                        tmp_val,
                        &tmp_ty,
                        &cg.meta.known_drop_fns,
                        &cg.meta.struct_layouts,
                        cg.meta.enum_layouts,
                        module,
                    );
                }
            }
        }
    }

    last_val
}

/// Calls `{type_name}_to_string` or `{type_name}_fmt` on `target_val`, returning
/// `(cstr_ptr, optional_owned_temp_string_to_drop)`.
fn compile_custom_display_to_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    type_name: &str,
    target_val: Value,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, Option<(Value, Type)>) {
    let to_string_fn = format!("{type_name}_to_string");
    let fmt_fn = format!("{type_name}_fmt");
    let func_name = if cg.meta.fn_return_types.contains_key(&to_string_fn)
        || module.get_name(&to_string_fn).is_some()
    {
        to_string_fn
    } else {
        fmt_fn
    };
    let ret_ty = cg
        .meta
        .fn_return_types
        .get(&func_name)
        .copied()
        .unwrap_or(Type::Obj(crate::ast::intern_str("std_string_String")));
    let param_tys = cg
        .meta
        .fn_param_types
        .get(&func_name)
        .cloned()
        .unwrap_or_else(|| vec![Type::Obj(crate::ast::intern_str(type_name))]);

    let (sig, fn_abi) = crate::codegen::layout::abi_signature_for_fn(
        module.isa().default_call_conv(),
        &param_tys,
        &ret_ty,
        false,
        &cg.meta.struct_layouts,
        cg.meta.enum_layouts,
    );

    let callee = match module.get_name(&func_name) {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        _ => module
            .declare_function(&func_name, Linkage::Import, &sig)
            .unwrap(),
    };

    let mut call_args = Vec::new();
    let sret_addr_opt = if let crate::codegen::layout::PassMode::Indirect { size, align } =
        fn_abi.ret_mode
    {
        let (_, addr) = crate::codegen::layout::alloc_stack_slot(builder, size, align);
        call_args.push(addr);
        Some(addr)
    } else {
        None
    };

    if let Some(pmode) = fn_abi.param_modes.first() {
        match pmode {
            crate::codegen::layout::PassMode::Ignore => {}
            crate::codegen::layout::PassMode::Direct(cl_ty) => {
                call_args.push(coerce_val(builder, target_val, *cl_ty));
            }
            crate::codegen::layout::PassMode::MultiReg { size, chunks, .. } => {
                let loaded = crate::codegen::layout::load_multireg_chunks(
                    builder, module, target_val, *size, chunks,
                );
                call_args.extend(loaded);
            }
            crate::codegen::layout::PassMode::Indirect { size, align } => {
                let (_, arg_addr) =
                    crate::codegen::layout::alloc_stack_slot(builder, *size, *align);
                crate::codegen::layout::emit_memcpy_bytes(
                    builder, module, arg_addr, target_val, *size,
                );
                call_args.push(arg_addr);
            }
        }
    }

    let local_callee = module.declare_func_in_func(callee, builder.func);
    let call_inst = builder.ins().call(local_callee, &call_args);
    let res_val = match fn_abi.ret_mode {
        crate::codegen::layout::PassMode::Ignore => builder.ins().iconst(types::I64, 0),
        crate::codegen::layout::PassMode::Direct(_) => builder.inst_results(call_inst)[0],
        crate::codegen::layout::PassMode::MultiReg { size, align, .. } => {
            let results = builder.inst_results(call_inst).to_vec();
            let (_, ret_addr) = crate::codegen::layout::alloc_stack_slot(builder, size, align);
            crate::codegen::layout::store_multireg_chunks(builder, module, ret_addr, size, &results);
            ret_addr
        }
        crate::codegen::layout::PassMode::Indirect { .. } => {
            sret_addr_opt.expect("sret addr missing in display")
        }
    };

    if ret_ty == Type::Str {
        (res_val, None)
    } else {
        let cstr_ptr = builder.ins().load(types::I64, MemFlags::new(), res_val, 0);
        let drop_ty = match ret_ty {
            Type::String | Type::Obj("String") | Type::Obj("std_string_String") => ret_ty,
            _ => Type::Obj(crate::ast::intern_str("std_string_String")),
        };
        (cstr_ptr, Some((res_val, drop_ty)))
    }
}

/// Central dispatcher for all compiler macro intrinsics (`macro_name!(...)`)
pub fn compile_macro_call<M: Module>(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[TypedExpr],
    ret_ty: &Type,
    span: &Span,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let clean_name = name.trim_end_matches('!');
    match clean_name {
        "format" => {
            let (joined_str, temp_drops) =
                emit_format_interpolated_to_string(builder, args, cg, module);
            for (tmp_val, tmp_ty) in temp_drops {
                crate::codegen::drops::emit_drop_for_value(
                    builder,
                    tmp_val,
                    &tmp_ty,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
            }
            joined_str
        }
        "panic" => {
            let msg_ptr = if args.is_empty() {
                compile_string_constant(builder, "explicit panic", module)
            } else {
                let (ptr, _) = emit_format_interpolated(builder, args, cg, module);
                ptr
            };
            emit_panic_cstr_and_trap(builder, msg_ptr, span, cg, module);

            let dead_block = builder.create_block();
            builder.switch_to_block(dead_block);
            builder.seal_block(dead_block);

            let dummy = builder.ins().iconst(types::I64, 0);
            builder
                .ins()
                .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
            dummy
        }
        "assert" => {
            if let Some(cond_expr) = args.first() {
                let cond_val = compile_expr(builder, cond_expr, cg, module);
                let pass_blk = builder.create_block();
                let fail_blk = builder.create_block();
                builder.ins().brif(cond_val, pass_blk, &[], fail_blk, &[]);

                builder.switch_to_block(fail_blk);
                builder.seal_block(fail_blk);
                let msg_ptr = if args.len() > 1 {
                    let (ptr, _) = emit_format_interpolated(builder, &args[1..], cg, module);
                    ptr
                } else {
                    let snippet = cg.meta.source_map.get_snippet(&cond_expr.span());
                    let msg = format!("assertion failed: {snippet}");
                    compile_string_constant(builder, &msg, module)
                };
                emit_panic_cstr_and_trap(builder, msg_ptr, span, cg, module);

                builder.switch_to_block(pass_blk);
                builder.seal_block(pass_blk);
            }
            builder.ins().iconst(types::I64, 0)
        }
        "assert_eq" | "assert_ne" => {
            if args.len() >= 2 {
                let is_ne = clean_name == "assert_ne";
                let left_expr = &args[0];
                let right_expr = &args[1];

                // Evaluate both operands exactly once into SSA values
                let left_val = compile_expr(builder, left_expr, cg, module);
                let right_val = compile_expr(builder, right_expr, cg, module);

                let pass_cond = crate::codegen::binops::compile_equality_cmp_vals(
                    builder,
                    left_val,
                    left_expr.ty(),
                    right_val,
                    right_expr.ty(),
                    is_ne,
                    cg,
                    module,
                );

                let pass_blk = builder.create_block();
                let fail_blk = builder.create_block();
                builder.ins().brif(pass_cond, pass_blk, &[], fail_blk, &[]);

                builder.switch_to_block(fail_blk);
                builder.seal_block(fail_blk);
                let msg_ptr = if args.len() > 2 {
                    let (ptr, _) = emit_format_interpolated(builder, &args[2..], cg, module);
                    ptr
                } else {
                    let op_str = if is_ne { "!=" } else { "==" };
                    let header = compile_string_constant(
                        builder,
                        &format!("assertion `left {op_str} right` failed\n  left: "),
                        module,
                    );
                    let mid = compile_string_constant(builder, "\n right: ", module);
                    let (l_cstr, l_owned, _) =
                        emit_val_to_cstr(builder, left_val, left_expr.ty(), FormatSpec::Debug { alternate: false }, cg, module);
                    let (r_cstr, r_owned, _) =
                        emit_val_to_cstr(builder, right_val, right_expr.ty(), FormatSpec::Debug { alternate: false }, cg, module);

                    emit_format_join_parts(
                        builder,
                        &[
                            (header, false),
                            (l_cstr, l_owned),
                            (mid, false),
                            (r_cstr, r_owned),
                        ],
                        module,
                    )
                };
                emit_panic_cstr_and_trap(builder, msg_ptr, span, cg, module);

                builder.switch_to_block(pass_blk);
                builder.seal_block(pass_blk);
            }
            builder.ins().iconst(types::I64, 0)
        }
        "thread" | "spawn" => {
            if args.is_empty() {
                return builder.ins().iconst(types::I64, 0);
            }
            let raw_func_ptr = compile_expr(builder, &args[0], cg, module);
            let mut func_ptr = coerce_val(builder, raw_func_ptr, types::I64);
            let has_arg = args.len() > 1;
            let opt_arg = if has_arg {
                if let TypedExpr::Ident(v_name, v_ty, _) = &args[1] {
                    if !v_ty.is_copy() {
                        cg.mark_moved(builder, v_name);
                    }
                }
                let val = compile_expr(builder, &args[1], cg, module);
                cg.cancel_temp(val);
                let arg_ty = args[1].ty();
                let arg_repr = crate::codegen::layout::repr_kind(
                    &arg_ty,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                );
                Some((val, arg_ty, arg_repr))
            } else {
                None
            };

            let default_params = opt_arg
                .as_ref()
                .map(|(_, t, _)| vec![*t])
                .unwrap_or_default();
            let (param_tys, ret_ty) = match &args[0] {
                TypedExpr::Closure(_, params, _, ret, _) => {
                    (params.iter().map(|(_, t)| *t).collect::<Vec<_>>(), *ret)
                }
                TypedExpr::Ident(fn_name, _, _) => (
                    cg.meta
                        .fn_param_types
                        .get(fn_name)
                        .cloned()
                        .unwrap_or(default_params),
                    cg.meta
                        .fn_return_types
                        .get(fn_name)
                        .copied()
                        .unwrap_or(Type::Unit),
                ),
                _ => (default_params, Type::Unit),
            };
            let ret_mode = crate::codegen::layout::pass_mode_for_type(
                &ret_ty,
                false,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
            );
            let arg_needs_tramp = opt_arg.as_ref().is_some_and(|(_, _, r)| {
                matches!(
                    r,
                    crate::codegen::layout::ReprKind::Aggregate { .. }
                        | crate::codegen::layout::ReprKind::Zst
                )
            });
            let needs_trampoline = arg_needs_tramp
                || matches!(ret_mode, crate::codegen::layout::PassMode::Indirect { .. });

            if needs_trampoline {
                static TRAMPOLINE_COUNTER: std::sync::atomic::AtomicUsize =
                    std::sync::atomic::AtomicUsize::new(0);
                let id = TRAMPOLINE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let (arg_offset, pkt_size) = match opt_arg.as_ref().map(|(_, _, r)| r) {
                    Some(crate::codegen::layout::ReprKind::Aggregate { size, align }) => {
                        let off = crate::codegen::layout::align_up(8, (*align).max(8));
                        (off, off + size)
                    }
                    Some(_) => (8u32, 16u32),
                    None => (8u32, 8u32),
                };

                let mut malloc_sig = module.make_signature();
                malloc_sig.params.push(AbiParam::new(types::I64));
                malloc_sig.returns.push(AbiParam::new(types::I64));
                let malloc_id = module
                    .declare_function("malloc", Linkage::Import, &malloc_sig)
                    .unwrap();
                let local_malloc = module.declare_func_in_func(malloc_id, builder.func);
                let pkt_sz_val = builder.ins().iconst(types::I64, pkt_size as i64);
                let malloc_call = builder.ins().call(local_malloc, &[pkt_sz_val]);
                let pkt_ptr = builder.inst_results(malloc_call)[0];

                let oom_blk = builder.create_block();
                let alloc_ok_blk = builder.create_block();
                let done_blk = builder.create_block();
                builder.append_block_param(done_blk, types::I64);
                let is_null = builder.ins().icmp_imm(IntCC::Equal, pkt_ptr, 0);
                builder.ins().brif(is_null, oom_blk, &[], alloc_ok_blk, &[]);

                builder.switch_to_block(oom_blk);
                builder.seal_block(oom_blk);
                if let Some((val, arg_ty, _)) = &opt_arg {
                    if crate::codegen::drops::has_drop_glue(
                        arg_ty,
                        &cg.meta.known_drop_fns,
                        &cg.meta.struct_layouts,
                        cg.meta.enum_layouts,
                    ) {
                        crate::codegen::drops::flags::emit_drop_for_value(
                            builder,
                            *val,
                            arg_ty,
                            &cg.meta.known_drop_fns,
                            &cg.meta.struct_layouts,
                            cg.meta.enum_layouts,
                            module,
                        );
                    }
                }
                let neg_one = builder.ins().iconst(types::I64, -1);
                builder.ins().jump(done_blk, &[neg_one.into()]);

                builder.switch_to_block(alloc_ok_blk);
                builder.seal_block(alloc_ok_blk);
                builder.ins().store(MemFlags::new(), func_ptr, pkt_ptr, 0);
                if let Some((val, _, arg_repr)) = &opt_arg {
                    match arg_repr {
                        crate::codegen::layout::ReprKind::Aggregate { size, .. } => {
                            let dst = builder.ins().iadd_imm(pkt_ptr, arg_offset as i64);
                            crate::codegen::layout::emit_memcpy_bytes(
                                builder, module, dst, *val, *size,
                            );
                        }
                        crate::codegen::layout::ReprKind::Scalar(_) => {
                            let coerced = coerce_val(builder, *val, types::I64);
                            builder.ins().store(
                                MemFlags::new(),
                                coerced,
                                pkt_ptr,
                                arg_offset as i32,
                            );
                        }
                        crate::codegen::layout::ReprKind::Zst => {}
                    }
                }

                // Synthesize thread entry trampoline: unpacks heap packet to child stack/regs and frees it.
                let mut tramp_sig = module.make_signature();
                tramp_sig.params.push(AbiParam::new(types::I64));
                tramp_sig.returns.push(AbiParam::new(types::I64));
                let tramp_name = format!("__gdrs_thread_trampoline_{id}");
                let tramp_id = module
                    .declare_function(&tramp_name, Linkage::Local, &tramp_sig)
                    .unwrap();

                let mut tctx = module.make_context();
                tctx.func.signature = tramp_sig;
                let mut tb_ctx = cranelift_frontend::FunctionBuilderContext::new();
                {
                    let mut tbuilder = FunctionBuilder::new(&mut tctx.func, &mut tb_ctx);
                    let entry = tbuilder.create_block();
                    tbuilder.switch_to_block(entry);
                    tbuilder.append_block_params_for_function_params(entry);
                    let pkt = tbuilder.block_params(entry)[0];

                    let real_fn = tbuilder.ins().load(types::I64, MemFlags::new(), pkt, 0);
                    let call_conv = module.isa().default_call_conv();
                    let (target_sig, fn_abi) = crate::codegen::layout::abi_signature_for_fn(
                        call_conv,
                        &param_tys,
                        &ret_ty,
                        false,
                        &cg.meta.struct_layouts,
                        cg.meta.enum_layouts,
                    );

                    let mut call_args = Vec::new();
                    let mut sret_addr_opt = None;
                    if let crate::codegen::layout::PassMode::Indirect { size, align } =
                        fn_abi.ret_mode
                    {
                        let (_, sret_addr) =
                            crate::codegen::layout::alloc_stack_slot(&mut tbuilder, size, align);
                        call_args.push(sret_addr);
                        sret_addr_opt = Some(sret_addr);
                    }
                    if has_arg {
                        if let Some(pmode) = fn_abi.param_modes.first() {
                            match pmode {
                                crate::codegen::layout::PassMode::Ignore => {}
                                crate::codegen::layout::PassMode::Direct(cl_ty) => {
                                    let raw = tbuilder.ins().load(
                                        types::I64,
                                        MemFlags::new(),
                                        pkt,
                                        arg_offset as i32,
                                    );
                                    call_args.push(coerce_val(&mut tbuilder, raw, *cl_ty));
                                }
                                crate::codegen::layout::PassMode::MultiReg { size, chunks, .. } => {
                                    let src = tbuilder.ins().iadd_imm(pkt, arg_offset as i64);
                                    let loaded = crate::codegen::layout::load_multireg_chunks(
                                        &mut tbuilder,
                                        module,
                                        src,
                                        *size,
                                        chunks,
                                    );
                                    call_args.extend(loaded);
                                }
                                crate::codegen::layout::PassMode::Indirect { size, align } => {
                                    let (_, stack_arg) = crate::codegen::layout::alloc_stack_slot(
                                        &mut tbuilder,
                                        *size,
                                        *align,
                                    );
                                    let src = tbuilder.ins().iadd_imm(pkt, arg_offset as i64);
                                    crate::codegen::layout::emit_memcpy_bytes(
                                        &mut tbuilder,
                                        module,
                                        stack_arg,
                                        src,
                                        *size,
                                    );
                                    call_args.push(stack_arg);
                                }
                            }
                        }
                    }

                    crate::codegen::drops::synthesis::emit_free_call(&mut tbuilder, pkt, module);

                    let sig_ref = tbuilder.import_signature(target_sig);
                    let target_call = tbuilder.ins().call_indirect(sig_ref, real_fn, &call_args);

                    if crate::codegen::drops::has_drop_glue(
                        &ret_ty,
                        &cg.meta.known_drop_fns,
                        &cg.meta.struct_layouts,
                        cg.meta.enum_layouts,
                    ) {
                        if let Some(sret_addr) = sret_addr_opt {
                            crate::codegen::drops::flags::emit_drop_for_value(
                                &mut tbuilder,
                                sret_addr,
                                &ret_ty,
                                &cg.meta.known_drop_fns,
                                &cg.meta.struct_layouts,
                                cg.meta.enum_layouts,
                                module,
                            );
                        } else if matches!(
                            fn_abi.ret_mode,
                            crate::codegen::layout::PassMode::Direct(_)
                        ) {
                            let ret_val = tbuilder.inst_results(target_call)[0];
                            crate::codegen::drops::flags::emit_drop_for_value(
                                &mut tbuilder,
                                ret_val,
                                &ret_ty,
                                &cg.meta.known_drop_fns,
                                &cg.meta.struct_layouts,
                                cg.meta.enum_layouts,
                                module,
                            );
                        }
                    }

                    let zero = tbuilder.ins().iconst(types::I64, 0);
                    tbuilder.ins().return_(&[zero]);
                    tbuilder.seal_all_blocks();
                    tbuilder.finalize();
                }
                module
                    .define_function(tramp_id, &mut tctx)
                    .expect("failed to define thread trampoline");
                module.clear_context(&mut tctx);

                let local_tramp = module.declare_func_in_func(tramp_id, builder.func);
                func_ptr = builder.ins().func_addr(types::I64, local_tramp);

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                let callee = module
                    .declare_function("intrinsic_spawn_thread", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                let call_inst = builder.ins().call(local_callee, &[func_ptr, pkt_ptr]);
                let res = builder.inst_results(call_inst)[0];

                // Drop moved payload and free the heap packet if pthread_create failed (res < 0).
                let fail_blk = builder.create_block();
                let is_err = builder.ins().icmp_imm(IntCC::SignedLessThan, res, 0);
                builder.ins().brif(is_err, fail_blk, &[], done_blk, &[res.into()]);

                builder.switch_to_block(fail_blk);
                builder.seal_block(fail_blk);
                if let Some((val, arg_ty, arg_repr)) = &opt_arg {
                    if crate::codegen::drops::has_drop_glue(
                        arg_ty,
                        &cg.meta.known_drop_fns,
                        &cg.meta.struct_layouts,
                        cg.meta.enum_layouts,
                    ) {
                        let drop_arg = match arg_repr {
                            crate::codegen::layout::ReprKind::Aggregate { .. } => {
                                builder.ins().iadd_imm(pkt_ptr, arg_offset as i64)
                            }
                            _ => *val,
                        };
                        crate::codegen::drops::flags::emit_drop_for_value(
                            builder,
                            drop_arg,
                            arg_ty,
                            &cg.meta.known_drop_fns,
                            &cg.meta.struct_layouts,
                            cg.meta.enum_layouts,
                            module,
                        );
                    }
                }
                crate::codegen::drops::synthesis::emit_free_call(builder, pkt_ptr, module);
                builder.ins().jump(done_blk, &[res.into()]);

                builder.switch_to_block(done_blk);
                builder.seal_block(done_blk);
                return builder.block_params(done_blk)[0];
            }

            let arg_val = opt_arg
                .as_ref()
                .map(|(v, _, _)| coerce_val(builder, *v, types::I64))
                .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));

            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));

            let callee = module
                .declare_function("intrinsic_spawn_thread", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[func_ptr, arg_val]);
            let res = builder.inst_results(call_inst)[0];

            if let Some((val, arg_ty, _)) = &opt_arg {
                if crate::codegen::drops::has_drop_glue(
                    arg_ty,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                ) {
                    let fail_blk = builder.create_block();
                    let ok_blk = builder.create_block();
                    let is_err = builder.ins().icmp_imm(IntCC::SignedLessThan, res, 0);
                    builder.ins().brif(is_err, fail_blk, &[], ok_blk, &[]);
                    builder.switch_to_block(fail_blk);
                    builder.seal_block(fail_blk);
                    crate::codegen::drops::flags::emit_drop_for_value(
                        builder,
                        *val,
                        arg_ty,
                        &cg.meta.known_drop_fns,
                        &cg.meta.struct_layouts,
                        cg.meta.enum_layouts,
                        module,
                    );
                    builder.ins().jump(ok_blk, &[]);
                    builder.switch_to_block(ok_blk);
                    builder.seal_block(ok_blk);
                }
            }
            res
        }
        "log" | "println" => compile_print_macro(builder, args, true, cg, module),
        "print" => compile_print_macro(builder, args, false, cg, module),
        "typeof" => {
            let type_name = args
                .first()
                .map(|a| format_type_name(&a.ty()))
                .unwrap_or_else(|| "()".to_string());
            compile_string_constant(builder, &type_name, module)
        }
        "file" => {
            let (file, _, _) = cg.meta.source_map.get_location(span);
            compile_string_constant(builder, &file, module)
        }
        "line" => {
            let (_, line, _) = cg.meta.source_map.get_location(span);
            builder.ins().iconst(types::I64, line as i64)
        }
        "column" => {
            let (_, _, col) = cg.meta.source_map.get_location(span);
            builder.ins().iconst(types::I64, col as i64)
        }
        "stringify" => {
            let snippet = args
                .first()
                .map(|a| cg.meta.source_map.get_snippet(&a.span()))
                .unwrap_or_default();
            compile_string_constant(builder, &snippet, module)
        }
        "vec" => {
            let vec_ty = if matches!(ret_ty, Type::Vec(_)) {
                *ret_ty
            } else {
                let elem_ty = args.first().map(|a| a.ty()).unwrap_or(Type::Int);
                Type::Vec(crate::ast::intern_type(elem_ty))
            };
            crate::codegen::arrays::compile_array_init(builder, args, &vec_ty, cg, module)
        }
        "dbg" => {
            if args.is_empty() {
                return builder.ins().iconst(types::I64, 0);
            }
            let arg = &args[0];
            let val = compile_expr(builder, arg, cg, module);
            let (file, line, col) = cg.meta.source_map.get_location(span);
            let loc_str = format!("{}:{}:{}", file, line, col);
            let snippet = cg.meta.source_map.get_snippet(&arg.span());
            let loc_val = compile_string_constant(builder, &loc_str, module);
            let snippet_val = compile_string_constant(builder, &snippet, module);
            let (val_str, is_owned, drop_opt) =
                emit_val_to_cstr(builder, val, arg.ty(), FormatSpec::Debug { alternate: true }, cg, module);

            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            let callee = module
                .declare_function("intrinsic_eprint_dbg", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            builder.ins().call(local_callee, &[loc_val, snippet_val, val_str]);

            if is_owned {
                let mut free_sig = module.make_signature();
                free_sig.params.push(AbiParam::new(types::I64));
                let free_callee = module.declare_function("free", Linkage::Import, &free_sig).unwrap();
                let local_free = module.declare_func_in_func(free_callee, builder.func);
                builder.ins().call(local_free, &[val_str]);
            }
            if let Some((tmp_val, tmp_ty)) = drop_opt {
                crate::codegen::drops::emit_drop_for_value(
                    builder,
                    tmp_val,
                    &tmp_ty,
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
            }

            val
        }
        _ => panic!("Unknown intrinsic macro: '{name}!'"),
    }
}
