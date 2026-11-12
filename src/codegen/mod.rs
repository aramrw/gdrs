//! codegen/mod.rs
//! Main entry point for Cranelift AOT native code generation.

pub mod arrays;
pub mod assign;
pub mod binops;
pub mod branching;
pub mod calls;
pub mod closures;
pub mod ctx;
pub mod drops;
pub mod expr;
pub mod func;
pub mod intrinsics;
pub mod layout;
pub mod loops;
pub mod object;
pub mod objects;
pub mod refs;
pub mod vtables;
