//! codegen/intrinsics/mod.rs
//! Compiler intrinsics module containing FFI declarations, iterator callbacks, and macro codegen.

pub mod ffi;
pub mod iterators;
pub mod macros;

pub use ffi::*;
pub use iterators::*;
pub use macros::*;
