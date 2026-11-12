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
use crate::sanal::macros::{parse_format_string, FormatChunk};

fn format_type_name(ty: &Type) -> String {
    match ty {
        Type::Int => "i64".to_string(),
        Type::I32 => "i32".to_string(),
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
        Type::Rc(inner) => format!("rc<{}>", format_type_name(inner)),
        Type::Arc(inner) => format!("arc<{}>", format_type_name(inner)),
        Type::Ref(inner) => format!("&{}", format_type_name(inner)),
        Type::MutRef(inner) => format!("&mut {}", format_type_name(inner)),
        Type::Ptr(inner) => format!("*{}", format_type_name(inner)),
        Type::Infer(id) => format!("?{id}"),
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
    module: &mut M,
) {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    let callee = module
        .declare_function("intrinsic_panic", Linkage::Import, &sig)
        .unwrap();
    let local_callee = module.declare_func_in_func(callee, builder.func);
    builder.ins().call(local_callee, &[msg_ptr]);
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

fn emit_format_join_parts<M: Module>(
    builder: &mut FunctionBuilder,
    parts: &[(Value, bool)],
    module: &mut M,
) -> Value {
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

    let mut sig_join = module.make_signature();
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.params.push(AbiParam::new(types::I64));
    sig_join.returns.push(AbiParam::new(types::I64));
    let callee_join = module
        .declare_function("intrinsic_format_join", Linkage::Import, &sig_join)
        .unwrap();
    let local_join = module.declare_func_in_func(callee_join, builder.func);

    let count_val = builder.ins().iconst(types::I64, count as i64);
    let call_inst = builder
        .ins()
        .call(local_join, &[count_val, parts_addr, owned_addr]);
    builder.inst_results(call_inst)[0]
}

fn has_custom_display(type_name: &str, cg: &CodegenCtx, module: &impl Module) -> bool {
    let to_string_fn = format!("{type_name}_to_string");
    let fmt_fn = format!("{type_name}_fmt");
    cg.meta.fn_return_types.contains_key(&to_string_fn)
        || module.get_name(&to_string_fn).is_some()
        || cg.meta.fn_return_types.contains_key(&fmt_fn)
        || module.get_name(&fmt_fn).is_some()
}

/// Converts a value of `raw_ty` to `(cstr_ptr, is_malloc_owned, optional_temp_string_drop)`.
fn emit_val_to_cstr<M: Module>(
    builder: &mut FunctionBuilder,
    val: Value,
    raw_ty: Type,
    cg: &CodegenCtx,
    module: &mut M,
) -> (Value, bool, Option<(Value, Type)>) {
    let ty = match raw_ty {
        Type::Ref(inner) | Type::MutRef(inner)
            if matches!(
                *inner,
                Type::String | Type::Obj(_) | Type::Enum(_) | Type::Tuple(_)
            ) =>
        {
            *inner
        }
        other => other,
    };

    match ty {
        Type::Str => (val, false, None),
        Type::String | Type::Obj("String") | Type::Obj("std_string_String") => {
            let str_ptr = builder.ins().load(types::I64, MemFlags::new(), val, 0);
            let is_null = builder.ins().icmp_imm(IntCC::Equal, str_ptr, 0);
            let empty_str = compile_string_constant(builder, "", module);
            (builder.ins().select(is_null, empty_str, str_ptr), false, None)
        }
        Type::Int | Type::I32 => {
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
        Type::Tuple(elems) => emit_tuple_to_cstr(builder, val, elems, cg, module),
        _ => (
            compile_string_constant(builder, &format!("<{}>", format_type_name(&ty)), module),
            false,
            None,
        ),
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
        let (cstr_ptr, is_owned, drop_opt) = emit_val_to_cstr(builder, elem_val, e_ty, cg, module);
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

/// Evaluates `args` where `args[0]` is a format string literal and returns `(cstr_ptr, temp_drops)`.
fn emit_format_interpolated<M: Module>(
    builder: &mut FunctionBuilder,
    args: &[TypedExpr],
    cg: &mut CodegenCtx,
    module: &mut M,
) -> (Value, Vec<(Value, Type)>) {
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
                FormatChunk::Hole(idx) => {
                    if let Some(arg) = args.get(1 + idx) {
                        let val = compile_expr(builder, arg, cg, module);
                        let (cstr_ptr, is_owned, drop_opt) =
                            emit_val_to_cstr(builder, val, arg.ty(), cg, module);
                        if let Some(d) = drop_opt {
                            temp_string_drops.push(d);
                        }
                        parts.push((cstr_ptr, is_owned));
                    }
                }
            }
        }
    }

    let joined = emit_format_join_parts(builder, &parts, module);
    (joined, temp_string_drops)
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
            FormatChunk::Hole(arg_idx) => {
                let Some(arg) = args.get(1 + arg_idx) else {
                    continue;
                };
                let effective_ty = match arg.ty() {
                    Type::Ref(inner) | Type::MutRef(inner) => *inner,
                    other => other,
                };
                let mut temp_string_drop: Option<(Value, Type)> = None;
                let mut temp_cstr_free: Option<Value> = None;
                let (raw_val, type_tag) = match effective_ty {
                    Type::Int | Type::I32 => (compile_expr(builder, arg, cg, module), 0),
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
                };

                let value_bits = {
                    let raw_ty = builder.func.dfg.value_type(raw_val);
                    if raw_ty == types::F64 {
                        builder.ins().bitcast(types::I64, MemFlags::new(), raw_val)
                    } else if raw_ty == types::F32 {
                        let promoted = builder.ins().fpromote(types::F64, raw_val);
                        builder.ins().bitcast(types::I64, MemFlags::new(), promoted)
                    } else if raw_ty == types::I32 || raw_ty == types::I8 {
                        builder.ins().sextend(types::I64, raw_val)
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
            let (joined, temp_drops) = emit_format_interpolated(builder, args, cg, module);
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
            joined
        }
        "panic" => {
            let msg_ptr = if args.is_empty() {
                compile_string_constant(builder, "explicit panic", module)
            } else {
                let (ptr, _) = emit_format_interpolated(builder, args, cg, module);
                ptr
            };
            emit_panic_cstr_and_trap(builder, msg_ptr, module);

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
                    let (file, line, col) = cg.meta.source_map.get_location(span);
                    let snippet = cg.meta.source_map.get_snippet(&cond_expr.span());
                    let msg = format!("assertion failed: {snippet} at {file}:{line}:{col}");
                    compile_string_constant(builder, &msg, module)
                };
                emit_panic_cstr_and_trap(builder, msg_ptr, module);

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
                    let (file, line, col) = cg.meta.source_map.get_location(span);
                    let op_str = if is_ne { "!=" } else { "==" };
                    let header = compile_string_constant(
                        builder,
                        &format!("assertion `left {op_str} right` failed at {file}:{line}:{col}\n  left: "),
                        module,
                    );
                    let mid = compile_string_constant(builder, "\n right: ", module);
                    let (l_cstr, l_owned, _) =
                        emit_val_to_cstr(builder, left_val, left_expr.ty(), cg, module);
                    let (r_cstr, r_owned, _) =
                        emit_val_to_cstr(builder, right_val, right_expr.ty(), cg, module);

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
                emit_panic_cstr_and_trap(builder, msg_ptr, module);

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
            let func_ptr = coerce_val(builder, raw_func_ptr, types::I64);
            let raw_arg_val = if args.len() > 1 {
                if let TypedExpr::Ident(v_name, v_ty, _) = &args[1] {
                    if !v_ty.is_copy() {
                        cg.mark_moved(builder, v_name);
                    }
                }
                let val = compile_expr(builder, &args[1], cg, module);
                cg.cancel_temp(val);
                val
            } else {
                builder.ins().iconst(types::I64, 0)
            };
            let arg_val = coerce_val(builder, raw_arg_val, types::I64);

            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));

            let callee = module
                .declare_function("intrinsic_spawn_thread", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[func_ptr, arg_val]);
            builder.inst_results(call_inst)[0]
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
        _ => panic!("Unknown intrinsic macro: '{name}!'"),
    }
}
