//! sanal/control_flow/mod.rs
//! Type checking for control flow: block, unsafe, match, try, while, if, if-else, return.

pub mod blocks;
pub mod branching;
pub mod lifetimes;
pub mod loops;
pub mod patterns;
pub mod try_op;

pub use blocks::{type_check_block, type_check_return, type_check_unsafe};
pub use branching::{type_check_if, type_check_if_else};
pub use lifetimes::{check_block_escape_lifetime, check_return_ref_lifetime};
pub use loops::{type_check_break, type_check_continue, type_check_while};
pub use patterns::type_check_match;
pub use try_op::type_check_try;
