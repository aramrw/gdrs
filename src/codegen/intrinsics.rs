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

use std::sync::Mutex;

static JIT_ARGS: Mutex<Vec<String>> = Mutex::new(Vec::new());

pub fn set_jit_args(args: Vec<String>) {
    let mut guard = JIT_ARGS.lock().unwrap();
    *guard = args;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn gdrs_resolve_symbol(name_ptr: *const std::os::raw::c_char) -> *mut std::ffi::c_void {
    if name_ptr.is_null() {
        eprintln!("[RUNTIME ERROR] Attempted to resolve NULL symbol name");
        std::process::exit(1);
    }
    let c_str = unsafe { std::ffi::CStr::from_ptr(name_ptr) };
    let name = c_str.to_string_lossy();

    let p = unsafe { libc::dlsym(libc::RTLD_DEFAULT, name_ptr) };
    if !p.is_null() {
        return p;
    }

    let mangled = format!("_{}", name);
    if let Ok(c_mangled) = std::ffi::CString::new(mangled) {
        let p_mangled = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_mangled.as_ptr()) };
        if !p_mangled.is_null() {
            return p_mangled;
        }
    }

    eprintln!("[RUNTIME ERROR] Unable to resolve symbol: '{}'", name);
    std::process::exit(1);
}

pub extern "C" fn intrinsic_panic(msg_ptr: *const std::os::raw::c_char) -> ! {
    let msg = if msg_ptr.is_null() {
        "explicit panic"
    } else {
        unsafe { std::ffi::CStr::from_ptr(msg_ptr).to_str().unwrap_or("explicit panic") }
    };
    eprintln!("thread 'main' panicked at '{msg}'");
    std::process::exit(101);
}

pub extern "C" fn intrinsic_arg_count() -> i64 {
    let guard = JIT_ARGS.lock().unwrap();
    guard.len() as i64
}

pub extern "C" fn intrinsic_execvp(path_ptr: *const std::os::raw::c_char) -> i32 {
    if path_ptr.is_null() {
        unsafe { libc::_exit(-1) };
    }
    let argv: [*const std::os::raw::c_char; 2] = [path_ptr, std::ptr::null()];
    unsafe {
        libc::execvp(path_ptr, argv.as_ptr());
        libc::_exit(-1);
    }
}

pub extern "C" fn intrinsic_waitpid(pid: i32) -> i32 {
    let mut status: i32 = 0;
    let res = unsafe { libc::waitpid(pid, &mut status as *mut i32, 0) };
    if res < 0 {
        return -1;
    }
    if libc::WIFEXITED(status) {
        let code = libc::WEXITSTATUS(status);
        if code == 255 { -1 } else { code }
    } else {
        -1
    }
}

pub extern "C" fn intrinsic_arg_at(idx: i64) -> *const std::os::raw::c_char {
    let guard = JIT_ARGS.lock().unwrap();
    if idx < 0 || (idx as usize) >= guard.len() {
        return std::ptr::null();
    }
    let s = &guard[idx as usize];
    let c_str = std::ffi::CString::new(s.as_str()).unwrap();
    c_str.into_raw() as *const std::os::raw::c_char
}

pub extern "C" fn intrinsic_args_str() -> i64 {
    let guard = JIT_ARGS.lock().unwrap();
    let joined = guard.join(" ");
    drop(guard);
    let mut bytes = joined.into_bytes();
    bytes.push(0);
    let ptr = bytes.as_ptr() as i64;
    std::mem::forget(bytes);
    ptr
}

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

pub extern "C" fn intrinsic_spawn_thread(func_ptr: u64, arg: u64) {
    if func_ptr == 0 {
        return;
    }
    std::thread::spawn(move || unsafe {
        let f: extern "C" fn(u64) -> u64 = std::mem::transmute(func_ptr as *const ());
        f(arg);
    });
}

pub extern "C" fn intrinsic_iter_for_each(range_ptr: *mut u64, func_ptr: u64) {
    if range_ptr.is_null() || func_ptr == 0 {
        return;
    }
    unsafe {
        let start = *range_ptr;
        let end = *range_ptr.add(1);
        let f: extern "C" fn(u64) -> u64 = std::mem::transmute(func_ptr as *const ());
        for i in start..end {
            f(i);
        }
    }
}

pub extern "C" fn intrinsic_iter_map(range_ptr: *mut u64, closure_ptr: u64) -> *mut u64 {
    if range_ptr.is_null() {
        return std::ptr::null_mut();
    }
    unsafe {
        let ptr = malloc(24) as *mut u64;
        *ptr = *range_ptr;
        *ptr.add(1) = *range_ptr.add(1);
        *ptr.add(2) = closure_ptr;
        ptr
    }
}

pub extern "C" fn intrinsic_map_for_each(map_iter_ptr: *mut u64, consumer_func_ptr: u64) {
    if map_iter_ptr.is_null() {
        return;
    }
    unsafe {
        let start = *map_iter_ptr;
        let end = *map_iter_ptr.add(1);
        let map_fn_ptr = *map_iter_ptr.add(2);
        if map_fn_ptr == 0 {
            return;
        }
        let map_fn: extern "C" fn(u64) -> u64 = std::mem::transmute(map_fn_ptr as *const ());

        if consumer_func_ptr != 0 {
            let consumer_fn: extern "C" fn(u64) -> u64 = std::mem::transmute(consumer_func_ptr as *const ());
            for i in start..end {
                let mapped_val = map_fn(i);
                consumer_fn(mapped_val);
            }
        } else {
            for i in start..end {
                map_fn(i);
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
                let str_val = if ty == Type::Str || matches!(ty, Type::Obj(n) if n == "String") {
                    val
                } else {
                    let target_name = match ty {
                        Type::Obj(n) | Type::Enum(n) => n,
                        _ => "",
                    };
                    let method_mangled = format!("{target_name}_to_string");
                    let mut sig = module.make_signature();
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let callee = module
                        .declare_function(&method_mangled, Linkage::Import, &sig)
                        .unwrap();
                    let local_callee = module.declare_func_in_func(callee, builder.func);
                    let call_inst = builder.ins().call(local_callee, &[val]);
                    builder.inst_results(call_inst)[0]
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
            let idx_val = compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
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
            let func_ptr = compile_expr(builder, &args[0], vars, var_counter, module, struct_layouts);
            let arg_val = if args.len() > 1 {
                compile_expr(builder, &args[1], vars, var_counter, module, struct_layouts)
            } else {
                builder.ins().iconst(types::I64, 0)
            };

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
                let (raw_val, type_tag) = match arg.ty() {
                    Type::Int | Type::I32 => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        0,
                    ),
                    Type::Bool => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        1,
                    ),
                    Type::Str | Type::String => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        2,
                    ),
                    Type::Float | Type::F32 => (
                        compile_expr(builder, arg, vars, var_counter, module, struct_layouts),
                        3,
                    ),
                    Type::Obj(tn) | Type::Enum(tn) => {
                        let to_string_fn = format!("{tn}_to_string");
                        if module.get_name(&to_string_fn).is_some() {
                            let method_call = TypedExpr::Call(
                                to_string_fn,
                                vec![arg.clone()],
                                Type::Str,
                                arg.span(),
                            );
                            (
                                compile_expr(
                                    builder,
                                    &method_call,
                                    vars,
                                    var_counter,
                                    module,
                                    struct_layouts,
                                ),
                                2,
                            )
                        } else {
                            (
                                compile_expr(
                                    builder,
                                    arg,
                                    vars,
                                    var_counter,
                                    module,
                                    struct_layouts,
                                ),
                                0,
                            )
                        }
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

