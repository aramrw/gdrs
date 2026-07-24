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
    JITModule::new(builder)
}
