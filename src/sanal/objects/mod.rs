//! sanal/objects/mod.rs
//! Type checking for structs, field access/assignment, enum construction, arrays, and indexing.

pub mod construction;
pub mod fields;
pub mod indexing;

pub use construction::{type_check_enum_construct, type_check_obj_init};
pub(crate) use construction::lookup_struct_layout_for_type;
pub use fields::{type_check_field_access, type_check_field_assign};
pub use indexing::{
    type_check_array_init, type_check_index_access, type_check_index_assign, type_check_tuple_init,
};
