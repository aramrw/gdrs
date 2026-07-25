//! codegen/jit.rs
//! Initializes the Cranelift JITModule with host machine target ISA settings.

use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::default_libcall_names;
use cranelift_native::builder as native_builder;

use crate::codegen::intrinsics::{intrinsic_log, intrinsic_push_str, intrinsic_vec_pop, intrinsic_vec_push};

/// Creates a new Cranelift JITModule configured for the host CPU architecture.
pub fn create_jit_module() -> JITModule {
    let flag_builder = cranelift_codegen::settings::builder();
    let isa_builder = native_builder().expect("Host machine target architecture not supported by Cranelift");
    let isa = isa_builder
        .finish(cranelift_codegen::settings::Flags::new(flag_builder))
        .expect("Failed to build target ISA");

    let mut builder = JITBuilder::with_isa(isa, default_libcall_names());
    builder.symbol("intrinsic_log", intrinsic_log as *const u8);
    builder.symbol("intrinsic_push_str", intrinsic_push_str as *const u8);
    builder.symbol("intrinsic_vec_push", intrinsic_vec_push as *const u8);
    builder.symbol("intrinsic_vec_pop", intrinsic_vec_pop as *const u8);

    builder.symbol_lookup_fn(Box::new(|name| {
        let c_str = std::ffi::CString::new(name).ok()?;
        let ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_str.as_ptr()) };
        let res = if ptr.is_null() {
            let mangled = format!("_{}", name);
            if let Ok(c_mangled) = std::ffi::CString::new(mangled) {
                let p2 = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_mangled.as_ptr()) };
                if !p2.is_null() {
                    Some(p2 as *const u8)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            Some(ptr as *const u8)
        };
        eprintln!("[JIT LOOKUP] {} -> {:?}", name, res);
        res
    }));

    JITModule::new(builder)
}
