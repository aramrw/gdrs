//! codegen/intrinsics.rs
//! Central dispatcher for compiler intrinsic macro calls (`name!(args...)`).

use std::collections::HashMap;

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::expr::compile_expr;
use crate::sanal::StructLayout;

/// Type Tag ABI:
/// 0 = Int (i64)
/// 1 = Bool (1 = true, 0 = false)
/// 2 = String (*const c_char pointer)
pub extern "C" fn intrinsic_log(type_tag: u64, value_bits: u64) -> i64 {
    match type_tag {
        0 => println!("{}", value_bits as i64),
        1 => println!("{}", value_bits != 0),
        2 => {
            let ptr = value_bits as *const std::os::raw::c_char;
            if ptr.is_null() {
                println!("<null>");
            } else {
                let c_str = unsafe { std::ffi::CStr::from_ptr(ptr) };
                println!("{}", c_str.to_string_lossy());
            }
        }
        3 => println!("{}", f64::from_bits(value_bits)),
        _ => println!("<unknown type 0x{:x}: 0x{:x}>", type_tag, value_bits),
    }
    0
}

unsafe extern "C" {
    fn malloc(size: usize) -> *mut std::ffi::c_void;
    fn realloc(ptr: *mut std::ffi::c_void, size: usize) -> *mut std::ffi::c_void;
    fn free(ptr: *mut std::ffi::c_void);
}

pub extern "C" fn intrinsic_rc_new(val_bits: u64) -> *mut u64 {
    unsafe {
        let ptr = malloc(16) as *mut u64;
        if !ptr.is_null() {
            *ptr = 1;
            *ptr.add(1) = val_bits;
        }
        ptr
    }
}

pub extern "C" fn intrinsic_arc_new(val_bits: u64) -> *mut u64 {
    unsafe {
        let ptr = malloc(16) as *mut u64;
        if !ptr.is_null() {
            *ptr = 1;
            *ptr.add(1) = val_bits;
        }
        ptr
    }
}

pub extern "C" fn intrinsic_rc_clone(ptr: *mut u64) -> *mut u64 {
    if !ptr.is_null() {
        unsafe {
            *ptr += 1;
        }
    }
    ptr
}

pub extern "C" fn intrinsic_arc_clone(ptr: *mut u64) -> *mut u64 {
    if !ptr.is_null() {
        let atomic_ref = unsafe { &*(ptr as *const std::sync::atomic::AtomicU64) };
        atomic_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }
    ptr
}

pub extern "C" fn intrinsic_rc_drop(ptr: *mut u64) {
    if !ptr.is_null() {
        unsafe {
            *ptr -= 1;
            if *ptr == 0 {
                free(ptr as *mut _);
            }
        }
    }
}

pub extern "C" fn intrinsic_arc_drop(ptr: *mut u64) {
    if !ptr.is_null() {
        let atomic_ref = unsafe { &*(ptr as *const std::sync::atomic::AtomicU64) };
        if atomic_ref.fetch_sub(1, std::sync::atomic::Ordering::SeqCst) == 1 {
            unsafe {
                free(ptr as *mut _);
            }
        }
    }
}

pub extern "C" fn intrinsic_push_str(header_ptr: *mut u64, append_str_ptr: *const std::os::raw::c_char) {
    if header_ptr.is_null() || append_str_ptr.is_null() {
        return;
    }
    unsafe {
        let ptr_slot = header_ptr as *mut *mut u8;
        let len_slot = header_ptr.add(1);
        let cap_slot = header_ptr.add(2);

        let append_len = std::ffi::CStr::from_ptr(append_str_ptr).to_bytes().len();
        let cur_len = if *len_slot > 0 { *len_slot as usize } else if !(*ptr_slot).is_null() { std::ffi::CStr::from_ptr(*ptr_slot as *const _).to_bytes().len() } else { 0 };
        let cur_cap = *cap_slot as usize;

        let needed_cap = cur_len + append_len + 1;
        if cur_cap == 0 {
            let new_cap = if needed_cap < 16 { 16 } else { needed_cap.next_power_of_two() };
            let new_ptr = malloc(new_cap) as *mut u8;
            if !(*ptr_slot).is_null() && cur_len > 0 {
                std::ptr::copy_nonoverlapping(*ptr_slot, new_ptr, cur_len);
            }
            std::ptr::copy_nonoverlapping(append_str_ptr as *const u8, new_ptr.add(cur_len), append_len);
            *new_ptr.add(cur_len + append_len) = 0;
            *ptr_slot = new_ptr;
            *len_slot = (cur_len + append_len) as u64;
            *cap_slot = new_cap as u64;
        } else if needed_cap > cur_cap {
            let new_cap = needed_cap.next_power_of_two();
            let new_ptr = realloc(*ptr_slot as *mut std::ffi::c_void, new_cap) as *mut u8;
            std::ptr::copy_nonoverlapping(append_str_ptr as *const u8, new_ptr.add(cur_len), append_len);
            *new_ptr.add(cur_len + append_len) = 0;
            *ptr_slot = new_ptr;
            *len_slot = (cur_len + append_len) as u64;
            *cap_slot = new_cap as u64;
        } else {
            std::ptr::copy_nonoverlapping(append_str_ptr as *const u8, (*ptr_slot).add(cur_len), append_len);
            *(*ptr_slot).add(cur_len + append_len) = 0;
            *len_slot = (cur_len + append_len) as u64;
        }
    }
}

pub extern "C" fn intrinsic_vec_push(header_ptr: *mut u64, elem_val: u64) {
    if header_ptr.is_null() {
        return;
    }
    unsafe {
        let ptr_slot = header_ptr as *mut *mut u64;
        let len_slot = header_ptr.add(1);
        let cap_slot = header_ptr.add(2);

        let cur_len = *len_slot as usize;
        let cur_cap = *cap_slot as usize;

        let needed_cap = cur_len + 1;
        if cur_cap == 0 {
            let new_cap = if needed_cap < 8 { 8 } else { needed_cap.next_power_of_two() };
            let new_ptr = malloc(new_cap * 8) as *mut u64;
            if !(*ptr_slot).is_null() && cur_len > 0 {
                std::ptr::copy_nonoverlapping(*ptr_slot, new_ptr, cur_len);
            }
            *new_ptr.add(cur_len) = elem_val;
            *ptr_slot = new_ptr;
            *len_slot = (cur_len + 1) as u64;
            *cap_slot = new_cap as u64;
        } else if needed_cap > cur_cap {
            let new_cap = needed_cap.next_power_of_two();
            let new_ptr = realloc(*ptr_slot as *mut std::ffi::c_void, new_cap * 8) as *mut u64;
            *new_ptr.add(cur_len) = elem_val;
            *ptr_slot = new_ptr;
            *len_slot = (cur_len + 1) as u64;
            *cap_slot = new_cap as u64;
        } else {
            *(*ptr_slot).add(cur_len) = elem_val;
            *len_slot = (cur_len + 1) as u64;
        }
    }
}

pub extern "C" fn intrinsic_vec_pop(header_ptr: *mut u64) -> u64 {
    if header_ptr.is_null() {
        return 0;
    }
    unsafe {
        let ptr_slot = header_ptr as *mut *mut u64;
        let len_slot = header_ptr.add(1);
        let cur_len = *len_slot as usize;

        if cur_len == 0 || (*ptr_slot).is_null() {
            return 0;
        }
        let val = *(*ptr_slot).add(cur_len - 1);
        *len_slot = (cur_len - 1) as u64;
        val
    }
}

use std::sync::atomic::{AtomicUsize, Ordering};
static STR_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn compile_string_constant(
    builder: &mut FunctionBuilder,
    s: &str,
    _var_counter: &mut usize,
    module: &mut JITModule,
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
pub fn compile_macro_call(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[TypedExpr],
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut JITModule,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    match name {
        "log" | "println" => {
            let mut last_val = builder.ins().iconst(types::I64, 0);
            for arg in args {
                let type_tag = match arg.ty() {
                    Type::Int | Type::I32 => 0,
                    Type::Bool => 1,
                    Type::Str | Type::String => 2,
                    Type::Float | Type::F32 => 3,
                    Type::Unit | Type::Obj(_) | Type::Enum(_) | Type::Array(_, _) | Type::Slice(_) | Type::Vec(_) | Type::Generic(_) | Type::DynTrait(_) | Type::Rc(_) | Type::Arc(_) => 0,
                };

                let type_tag_val = builder.ins().iconst(types::I64, type_tag);
                let raw_val = compile_expr(builder, arg, vars, var_counter, module, struct_layouts);

                let value_bits = if arg.ty() == Type::Float {
                    builder.ins().bitcast(types::I64, MemFlags::new(), raw_val)
                } else if (arg.ty() == Type::Str || arg.ty() == Type::String) && !matches!(arg, TypedExpr::String(..)) {
                    builder.ins().load(types::I64, MemFlags::new(), raw_val, 0)
                } else {
                    raw_val
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
                let target_ptr = compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
                let append_ptr = compile_expr(builder, &args[1], vars, var_counter, module, struct_layouts);

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
                let target_ptr = compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
                let elem_val = compile_expr(builder, &args[1], vars, var_counter, module, struct_layouts);

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
                let target_ptr = compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);

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
                let target_ptr = compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
                builder.ins().load(types::I64, MemFlags::new(), target_ptr, 8)
            } else {
                builder.ins().iconst(types::I64, 0)
            }
        }
        _ => panic!("Unknown intrinsic macro: '{name}!'"),
    }
}

