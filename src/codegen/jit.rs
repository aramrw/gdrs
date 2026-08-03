//! codegen/jit.rs
//! Initializes the Cranelift JITModule with host machine target ISA settings.

use cranelift_codegen::settings::Configurable;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::default_libcall_names;
use cranelift_native::builder as native_builder;

use crate::codegen::intrinsics::{
    gdrs_resolve_symbol, intrinsic_arc_clone, intrinsic_arc_drop, intrinsic_arc_new, intrinsic_arg_at,
    intrinsic_arg_count, intrinsic_args_str, intrinsic_bool_to_str, intrinsic_execvp, intrinsic_float_to_str,
    intrinsic_int_to_str, intrinsic_log, intrinsic_panic, intrinsic_push_str,
    intrinsic_rc_clone, intrinsic_rc_drop, intrinsic_rc_new, intrinsic_spawn_thread,
    intrinsic_vec_new, intrinsic_vec_pop, intrinsic_vec_push, intrinsic_waitpid,
};

/// Creates a new Cranelift JITModule configured for the host CPU architecture.
pub fn create_jit_module() -> JITModule {
    let flag_builder = cranelift_codegen::settings::builder();
    let isa_builder = native_builder().expect("Host machine target architecture not supported by Cranelift");
    let isa = isa_builder
        .finish(cranelift_codegen::settings::Flags::new(flag_builder))
        .expect("Failed to build target ISA");

    let mut builder = JITBuilder::with_isa(isa, default_libcall_names());
    builder.symbol("gdrs_resolve_symbol", gdrs_resolve_symbol as *const u8);
    builder.symbol("intrinsic_log", intrinsic_log as *const u8);
    builder.symbol("intrinsic_int_to_str", intrinsic_int_to_str as *const u8);
    builder.symbol("intrinsic_float_to_str", intrinsic_float_to_str as *const u8);
    builder.symbol("intrinsic_bool_to_str", intrinsic_bool_to_str as *const u8);
    builder.symbol("intrinsic_panic", intrinsic_panic as *const u8);
    builder.symbol("intrinsic_push_str", intrinsic_push_str as *const u8);
    builder.symbol("intrinsic_vec_push", intrinsic_vec_push as *const u8);
    builder.symbol("intrinsic_vec_pop", intrinsic_vec_pop as *const u8);
    builder.symbol("intrinsic_vec_new", intrinsic_vec_new as *const u8);
    builder.symbol("intrinsic_rc_new", intrinsic_rc_new as *const u8);
    builder.symbol("intrinsic_arc_new", intrinsic_arc_new as *const u8);
    builder.symbol("intrinsic_rc_clone", intrinsic_rc_clone as *const u8);
    builder.symbol("intrinsic_arc_clone", intrinsic_arc_clone as *const u8);
    builder.symbol("intrinsic_rc_drop", intrinsic_rc_drop as *const u8);
    builder.symbol("intrinsic_arc_drop", intrinsic_arc_drop as *const u8);
    builder.symbol("intrinsic_spawn_thread", intrinsic_spawn_thread as *const u8);
    builder.symbol("intrinsic_arg_count", intrinsic_arg_count as *const u8);
    builder.symbol("intrinsic_arg_at", intrinsic_arg_at as *const u8);
    builder.symbol("intrinsic_args_str", intrinsic_args_str as *const u8);
    builder.symbol("intrinsic_execvp", intrinsic_execvp as *const u8);
    builder.symbol("intrinsic_waitpid", intrinsic_waitpid as *const u8);
    builder.symbol("malloc", crate::codegen::intrinsics::gdrs_malloc as *const u8);
    builder.symbol("free", crate::codegen::intrinsics::gdrs_free as *const u8);
    builder.symbol("realloc", crate::codegen::intrinsics::gdrs_realloc as *const u8);
    builder.symbol("memcpy", crate::codegen::intrinsics::gdrs_memcpy as *const u8);
    builder.symbol("memset", crate::codegen::intrinsics::gdrs_memset as *const u8);
    builder.symbol("strlen", libc::strlen as *const u8);
    builder.symbol("strdup", libc::strdup as *const u8);
    builder.symbol("strcmp", libc::strcmp as *const u8);
    builder.symbol("strncmp", libc::strncmp as *const u8);
    builder.symbol("strcpy", libc::strcpy as *const u8);

    builder.symbol("std_libc_malloc", crate::codegen::intrinsics::gdrs_malloc as *const u8);
    builder.symbol("std_libc_free", crate::codegen::intrinsics::gdrs_free as *const u8);
    builder.symbol("std_libc_realloc", crate::codegen::intrinsics::gdrs_realloc as *const u8);
    builder.symbol("std_libc_memcpy", crate::codegen::intrinsics::gdrs_memcpy as *const u8);
    builder.symbol("std_libc_memset", crate::codegen::intrinsics::gdrs_memset as *const u8);
    builder.symbol("std_libc_strlen", libc::strlen as *const u8);
    builder.symbol("std_libc_strdup", libc::strdup as *const u8);
    builder.symbol("std_libc_strcmp", libc::strcmp as *const u8);
    builder.symbol("std_libc_strncmp", libc::strncmp as *const u8);
    builder.symbol("std_libc_strcpy", libc::strcpy as *const u8);

    let math_syms: &[(&str, *const u8)] = &[
        ("exp", crate::codegen::intrinsics::gdrs_exp as *const u8),
        ("sqrt", crate::codegen::intrinsics::gdrs_sqrt as *const u8),
        ("sin", crate::codegen::intrinsics::gdrs_sin as *const u8),
        ("cos", crate::codegen::intrinsics::gdrs_cos as *const u8),
        ("tan", crate::codegen::intrinsics::gdrs_tan as *const u8),
        ("pow", crate::codegen::intrinsics::gdrs_pow as *const u8),
        ("fabs", crate::codegen::intrinsics::gdrs_fabs as *const u8),
        ("std_math_exp", crate::codegen::intrinsics::gdrs_exp as *const u8),
        ("std_math_sqrt", crate::codegen::intrinsics::gdrs_sqrt as *const u8),
        ("std_math_sin", crate::codegen::intrinsics::gdrs_sin as *const u8),
        ("std_math_cos", crate::codegen::intrinsics::gdrs_cos as *const u8),
        ("std_math_tan", crate::codegen::intrinsics::gdrs_tan as *const u8),
        ("std_math_pow", crate::codegen::intrinsics::gdrs_pow as *const u8),
        ("std_math_fabs", crate::codegen::intrinsics::gdrs_fabs as *const u8),
        ("c_exp", crate::codegen::intrinsics::gdrs_exp as *const u8),
        ("c_sqrt", crate::codegen::intrinsics::gdrs_sqrt as *const u8),
        ("c_sin", crate::codegen::intrinsics::gdrs_sin as *const u8),
        ("c_cos", crate::codegen::intrinsics::gdrs_cos as *const u8),
        ("c_tan", crate::codegen::intrinsics::gdrs_tan as *const u8),
        ("c_pow", crate::codegen::intrinsics::gdrs_pow as *const u8),
        ("c_fabs", crate::codegen::intrinsics::gdrs_fabs as *const u8),
        ("std_math_c_exp", crate::codegen::intrinsics::gdrs_exp as *const u8),
        ("std_math_c_sqrt", crate::codegen::intrinsics::gdrs_sqrt as *const u8),
        ("std_math_c_sin", crate::codegen::intrinsics::gdrs_sin as *const u8),
        ("std_math_c_cos", crate::codegen::intrinsics::gdrs_cos as *const u8),
        ("std_math_c_tan", crate::codegen::intrinsics::gdrs_tan as *const u8),
        ("std_math_c_pow", crate::codegen::intrinsics::gdrs_pow as *const u8),
        ("std_math_c_fabs", crate::codegen::intrinsics::gdrs_fabs as *const u8),
    ];
    for (name, ptr) in math_syms {
        builder.symbol(*name, *ptr);
    }

    builder.symbol_lookup_fn(Box::new(|name| {
        let clean_name = name
            .strip_prefix("std_math_c_")
            .or_else(|| name.strip_prefix("std_math_"))
            .or_else(|| name.strip_prefix("std_libc_c_"))
            .or_else(|| name.strip_prefix("std_libc_"))
            .unwrap_or(name);
        match clean_name {
            "malloc" => return Some(crate::codegen::intrinsics::gdrs_malloc as *const u8),
            "free" => return Some(crate::codegen::intrinsics::gdrs_free as *const u8),
            "realloc" => return Some(crate::codegen::intrinsics::gdrs_realloc as *const u8),
            "memcpy" => return Some(crate::codegen::intrinsics::gdrs_memcpy as *const u8),
            "memset" => return Some(crate::codegen::intrinsics::gdrs_memset as *const u8),
            _ => {}
        }
        let c_str = std::ffi::CString::new(clean_name).ok()?;
        let mut ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_str.as_ptr()) };
        if ptr.is_null() {
            let mangled = format!("_{}", clean_name);
            if let Ok(c_mangled) = std::ffi::CString::new(mangled) {
                ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_mangled.as_ptr()) };
            }
        }
        if ptr.is_null() {
            for dylib_path in &["/opt/homebrew/lib/libraylib.dylib", "libraylib.dylib", "/usr/local/lib/libraylib.dylib"] {
                if let Ok(c_path) = std::ffi::CString::new(*dylib_path) {
                    unsafe {
                        libc::dlopen(c_path.as_ptr(), 9);
                    }
                    ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_str.as_ptr()) };
                    if !ptr.is_null() {
                        break;
                    }
                }
            }
        }
        if ptr.is_null() {
            None
        } else {
            Some(ptr as *const u8)
        }
    }));

    JITModule::new(builder)
}
