//! codegen/intrinsics/macros.rs
//! Compiler intrinsic macro code generator (`compile_macro_call`).

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::expr::{coerce_val, compile_expr};
use crate::sanal::StructLayout;

static STR_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn compile_string_constant<M: Module>(
    builder: &mut FunctionBuilder,
    s: &str,
    _var_counter: &mut usize,
    module: &mut M,
) -> Value {
    use cranelift_module::DataDescription;
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

/// Central dispatcher for all compiler macro intrinsics (`macro_name!(...)`)
pub fn compile_macro_call<M: Module>(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[TypedExpr],
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut M,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    let clean_name = name.trim_end_matches('!');
    match clean_name {
        "format" => {
            let mut compiled_args = Vec::new();
            for arg in args {
                let val = compile_expr(builder, arg, vars, var_counter, module, struct_layouts);
                let ty = arg.ty();
                let str_val = match ty {
                    Type::Str => val,
                    Type::String => {
                        builder.ins().load(types::I64, MemFlags::new(), val, 0)
                    }
                    Type::Obj(target_name) if target_name == "String" || target_name == "std_string_String" => {
                        builder.ins().load(types::I64, MemFlags::new(), val, 0)
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
                        builder.inst_results(call_inst)[0]
                    }
                    Type::Float | Type::F32 => {
                        let val_f64 = coerce_val(builder, val, types::F64);
                        let slot = builder.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            8,
                            3,
                        ));
                        let slot_addr = builder.ins().stack_addr(types::I64, slot, 0);
                        builder.ins().store(MemFlags::new(), val_f64, slot_addr, 0);
                        let val_bits = builder.ins().load(types::I64, MemFlags::new(), slot_addr, 0);

                        let mut sig = module.make_signature();
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));
                        let callee = module
                            .declare_function("intrinsic_float_to_str", Linkage::Import, &sig)
                            .unwrap();
                        let local_callee = module.declare_func_in_func(callee, builder.func);
                        let call_inst = builder.ins().call(local_callee, &[val_bits]);
                        builder.inst_results(call_inst)[0]
                    }
                    _ if builder.func.dfg.value_type(val) == types::F64 => {
                        let val_f64 = coerce_val(builder, val, types::F64);
                        let slot = builder.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            8,
                            3,
                        ));
                        let slot_addr = builder.ins().stack_addr(types::I64, slot, 0);
                        builder.ins().store(MemFlags::new(), val_f64, slot_addr, 0);
                        let val_bits = builder.ins().load(types::I64, MemFlags::new(), slot_addr, 0);

                        let mut sig = module.make_signature();
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));
                        let callee = module
                            .declare_function("intrinsic_float_to_str", Linkage::Import, &sig)
                            .unwrap();
                        let local_callee = module.declare_func_in_func(callee, builder.func);
                        let call_inst = builder.ins().call(local_callee, &[val_bits]);
                        builder.inst_results(call_inst)[0]
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
                        builder.inst_results(call_inst)[0]
                    }
                    Type::Obj(target_name) if matches!(&target_name[..], "f64" | "Float" | "F64" | "f32" | "F32") => {
                        let val_f64 = coerce_val(builder, val, types::F64);
                        let slot = builder.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            8,
                            3,
                        ));
                        let slot_addr = builder.ins().stack_addr(types::I64, slot, 0);
                        builder.ins().store(MemFlags::new(), val_f64, slot_addr, 0);
                        let val_bits = builder.ins().load(types::I64, MemFlags::new(), slot_addr, 0);

                        let mut sig = module.make_signature();
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));
                        let callee = module
                            .declare_function("intrinsic_float_to_str", Linkage::Import, &sig)
                            .unwrap();
                        let local_callee = module.declare_func_in_func(callee, builder.func);
                        let call_inst = builder.ins().call(local_callee, &[val_bits]);
                        builder.inst_results(call_inst)[0]
                    }
                    Type::Obj(target_name) | Type::Enum(target_name) => {
                        let method_mangled = format!("{target_name}_to_string");
                        let mut sig = module.make_signature();
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));
                        let callee = module
                            .declare_function(&method_mangled, Linkage::Import, &sig)
                            .unwrap();
                        let local_callee = module.declare_func_in_func(callee, builder.func);
                        let call_inst = builder.ins().call(local_callee, &[val]);
                        let str_obj_ptr = builder.inst_results(call_inst)[0];
                        builder.ins().load(types::I64, MemFlags::new(), str_obj_ptr, 0)
                    }
                    _ => {
                        eprintln!("[DEBUG format!] matched DEFAULT _ ! arg.ty()={:?}, val={}", arg.ty(), val);
                        val
                    }
                };
                compiled_args.push(str_val);
            }

            let mut sig_malloc = module.make_signature();
            sig_malloc.params.push(AbiParam::new(types::I64));
            sig_malloc.returns.push(AbiParam::new(types::I64));
            let callee_malloc = module
                .declare_function("malloc", Linkage::Import, &sig_malloc)
                .unwrap();
            let local_malloc = module.declare_func_in_func(callee_malloc, builder.func);

            let buf_size = builder.ins().iconst(types::I64, 4096);
            let buf_call = builder.ins().call(local_malloc, &[buf_size]);
            let buf_ptr = builder.inst_results(buf_call)[0];
            let zero = builder.ins().iconst(types::I8, 0);
            builder.ins().store(MemFlags::new(), zero, buf_ptr, 0);

            let mut sig_strcat = module.make_signature();
            sig_strcat.params.push(AbiParam::new(types::I64));
            sig_strcat.params.push(AbiParam::new(types::I64));
            sig_strcat.returns.push(AbiParam::new(types::I64));
            let callee_strcat = module
                .declare_function("strcat", Linkage::Import, &sig_strcat)
                .unwrap();
            let local_strcat = module.declare_func_in_func(callee_strcat, builder.func);

            for str_val in compiled_args {
                builder.ins().call(local_strcat, &[buf_ptr, str_val]);
            }
            buf_ptr
        }
        "panic" => {
            let msg_ptr = if !args.is_empty() {
                compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts)
            } else {
                builder.ins().iconst(types::I64, 0)
            };
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

            let dead_block = builder.create_block();
            builder.switch_to_block(dead_block);
            builder.seal_block(dead_block);

            let dummy = builder.ins().iconst(types::I64, 0);
            builder
                .ins()
                .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
            dummy
        }
        "args" => {
            let mut sig = module.make_signature();
            sig.returns.push(AbiParam::new(types::I64));
            let callee = module
                .declare_function("intrinsic_args_str", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[]);
            builder.inst_results(call_inst)[0]
        }
        "arg_count" | "args_count" => {
            let mut sig = module.make_signature();
            sig.returns.push(AbiParam::new(types::I64));
            let callee = module
                .declare_function("intrinsic_arg_count", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[]);
            builder.inst_results(call_inst)[0]
        }
        "arg_at" | "args_at" => {
            if args.is_empty() {
                return builder.ins().iconst(types::I64, 0);
            }
            let raw_idx_val =
                compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
            let idx_val = crate::codegen::expr::coerce_val(builder, raw_idx_val, types::I64);
            let mut sig = module.make_signature();
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            let callee = module
                .declare_function("intrinsic_arg_at", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[idx_val]);
            builder.inst_results(call_inst)[0]
        }
        "thread" | "spawn" => {
            if args.is_empty() {
                return builder.ins().iconst(types::I64, 0);
            }
            let raw_func_ptr =
                compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
            let func_ptr = crate::codegen::expr::coerce_val(builder, raw_func_ptr, types::I64);
            let raw_arg_val = if args.len() > 1 {
                compile_expr(builder, &args[1], vars, var_counter, module, struct_layouts)
            } else {
                builder.ins().iconst(types::I64, 0)
            };
            let arg_val = crate::codegen::expr::coerce_val(builder, raw_arg_val, types::I64);

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
        "log" | "println" => {
            let mut last_val = builder.ins().iconst(types::I64, 0);
            for arg in args {
                let effective_ty = match arg.ty() {
                    Type::Ref(inner) | Type::MutRef(inner) => *inner,
                    other => other,
                };
                let (raw_val, type_tag) = match effective_ty {
                    Type::Int | Type::I32 => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        0,
                    ),
                    Type::Bool => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        1,
                    ),
                    Type::Str => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        2,
                    ),
                    Type::String => {
                        let string_obj_val =
                            compile_expr(builder, arg, vars, var_counter, module, struct_layouts);
                        let str_ptr =
                            builder.ins().load(types::I64, MemFlags::new(), string_obj_val, 0);
                        (str_ptr, 2)
                    }
                    Type::Float | Type::F32 => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        3,
                    ),
                    Type::Obj(tn) | Type::Enum(tn) => {
                        let to_string_fn = format!("{tn}_to_string");
                        let fmt_fn = format!("{tn}_fmt");
                        let func_name = if module.get_name(&to_string_fn).is_some() {
                            to_string_fn
                        } else {
                            fmt_fn
                        };

                        let method_call = TypedExpr::Call(
                            func_name,
                            vec![arg.clone()],
                            Type::Str,
                            arg.span(),
                        );
                        let string_obj_val = compile_expr(
                            builder,
                            &method_call,
                            vars,
                            var_counter,
                            module,
                            struct_layouts,
                        );
                        let str_ptr = builder.ins().load(types::I64, MemFlags::new(), string_obj_val, 0);
                        (str_ptr, 2)
                    }
                    _ => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        0,
                    ),
                };

                let type_tag_val = builder.ins().iconst(types::I64, type_tag);

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
                        raw_val // already I64 pointer or integer
                    }
                };

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64)); // type_tag
                sig.params.push(AbiParam::new(types::I64)); // value_bits
                sig.returns.push(AbiParam::new(types::I64));

                let callee = module
                    .declare_function("intrinsic_log", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                let call_inst = builder.ins().call(local_callee, &[type_tag_val, value_bits]);
                last_val = builder.inst_results(call_inst)[0];
            }
            last_val
        }
        "typeof" => {
            let mut last_val = builder.ins().iconst(types::I64, 0);
            for arg in args {
                let type_name = match arg.ty() {
                    Type::Int | Type::I32 => "Int",
                    Type::Float | Type::F32 => "Float",
                    Type::Bool => "Bool",
                    Type::Str => "Str",
                    Type::String => "String",
                    Type::Unit => "Unit",
                    Type::Obj(name) => name,
                    Type::Enum(name) => name,
                    Type::Array(_, _) => "Array",
                    Type::Slice(_) => "Slice",
                    Type::Vec(_) => "Vec",
                    Type::Generic(name) => name,
                    Type::DynTrait(name) => name,
                    Type::Rc(_) => "Rc",
                    Type::Arc(_) => "Arc",
                    Type::Ref(_) => "Ref",
                    Type::MutRef(_) => "MutRef",
                    Type::Void => "Void",
                    Type::Ptr(_) => "Ptr",
                };

                let ptr_val = compile_string_constant(builder, type_name, var_counter, module);
                let type_tag_val = builder.ins().iconst(types::I64, 2);

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));

                let callee = module
                    .declare_function("intrinsic_log", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                let call_inst = builder.ins().call(local_callee, &[type_tag_val, ptr_val]);
                last_val = builder.inst_results(call_inst)[0];
            }
            last_val
        }
        "push_str" => {
            if args.len() == 2 {
                let raw_target_ptr =
                    compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
                let target_ptr =
                    crate::codegen::expr::coerce_val(builder, raw_target_ptr, types::I64);
                let raw_append_ptr =
                    compile_expr(builder, &args[1], vars, var_counter, module, struct_layouts);
                let append_ptr =
                    crate::codegen::expr::coerce_val(builder, raw_append_ptr, types::I64);

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64)); // header_ptr
                sig.params.push(AbiParam::new(types::I64)); // append_str_ptr

                let callee = module
                    .declare_function("intrinsic_push_str", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                builder.ins().call(local_callee, &[target_ptr, append_ptr]);
            }
            builder.ins().iconst(types::I64, 0)
        }
        "push" => {
            if args.len() == 2 {
                let raw_target_ptr =
                    compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
                let target_ptr =
                    crate::codegen::expr::coerce_val(builder, raw_target_ptr, types::I64);
                let raw_elem_val =
                    compile_expr(builder, &args[1], vars, var_counter, module, struct_layouts);
                let elem_val =
                    crate::codegen::expr::coerce_val(builder, raw_elem_val, types::I64);

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64)); // header_ptr
                sig.params.push(AbiParam::new(types::I64)); // elem_val

                let callee = module
                    .declare_function("intrinsic_vec_push", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                builder.ins().call(local_callee, &[target_ptr, elem_val]);
            }
            builder.ins().iconst(types::I64, 0)
        }
        "pop" => {
            if args.len() == 1 {
                let raw_target_ptr =
                    compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
                let target_ptr =
                    crate::codegen::expr::coerce_val(builder, raw_target_ptr, types::I64);

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64)); // header_ptr
                sig.returns.push(AbiParam::new(types::I64));

                let callee = module
                    .declare_function("intrinsic_vec_pop", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                let call_inst = builder.ins().call(local_callee, &[target_ptr]);
                builder.inst_results(call_inst)[0]
            } else {
                builder.ins().iconst(types::I64, 0)
            }
        }
        "len" => {
            if args.len() == 1 {
                if let Type::Array(_, len) = args[0].ty() {
                    builder.ins().iconst(types::I64, len as i64)
                } else {
                    let raw_target_ptr =
                        compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
                    let target_ptr =
                        crate::codegen::expr::coerce_val(builder, raw_target_ptr, types::I64);
                    builder.ins().load(types::I64, MemFlags::new(), target_ptr, 8)
                }
            } else {
                builder.ins().iconst(types::I64, 0)
            }
        }
        "vec" => {
            let mut sig = module.make_signature();
            sig.returns.push(AbiParam::new(types::I64));
            let callee = module
                .declare_function("intrinsic_vec_new", Linkage::Import, &sig)
                .unwrap();
            let local_callee = module.declare_func_in_func(callee, builder.func);
            let call_inst = builder.ins().call(local_callee, &[]);
            let vec_ptr = builder.inst_results(call_inst)[0];

            for arg in args {
                let raw_elem_val =
                    compile_expr(builder, arg, vars, var_counter, module, struct_layouts);
                let elem_val =
                    crate::codegen::expr::coerce_val(builder, raw_elem_val, types::I64);
                let mut sig_push = module.make_signature();
                sig_push.params.push(AbiParam::new(types::I64));
                sig_push.params.push(AbiParam::new(types::I64));
                let callee_push = module
                    .declare_function("intrinsic_vec_push", Linkage::Import, &sig_push)
                    .unwrap();
                let local_push = module.declare_func_in_func(callee_push, builder.func);
                builder.ins().call(local_push, &[vec_ptr, elem_val]);
            }

            vec_ptr
        }
        _ => panic!("Unknown intrinsic macro: '{name}!'"),
    }
}
