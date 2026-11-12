//! codegen/layout.rs
//! Canonical C-ABI value layout, classification, calling convention (`PassMode`/`FnAbi`),
//! and stack/memory copy helpers shared across all codegen modules.

use std::collections::{HashMap, HashSet};

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, StackSlot, StackSlotData, StackSlotKind, Value};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{Linkage, Module};

use crate::ast::{normalize_type_name, Type};
use crate::codegen::drops::{find_enum_layout, is_npo_enum, EnumLayoutMap};
use crate::sanal::StructLayout;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReprKind {
    Zst,
    Scalar(cranelift_codegen::ir::Type),
    Aggregate { size: u32, align: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PassMode {
    Ignore,
    Direct(cranelift_codegen::ir::Type),
    /// Small aggregate (1..=16 bytes) passed/returned in 1 or 2 `I64` registers.
    MultiReg {
        size: u32,
        align: u32,
        chunks: Vec<cranelift_codegen::ir::Type>,
    },
    /// Large aggregate (>16 bytes) or `_drop` receiver passed via stack pointer (`I64`).
    Indirect { size: u32, align: u32 },
}

#[derive(Debug, Clone)]
pub struct FnAbi {
    pub has_sret: bool,
    pub ret_mode: PassMode,
    pub param_modes: Vec<PassMode>,
}

#[inline]
pub fn align_up(offset: u32, align: u32) -> u32 {
    let a = align.max(1);
    (offset + a - 1) & !(a - 1)
}

pub fn find_struct_layout<'a>(
    struct_layouts: &'a HashMap<String, StructLayout>,
    struct_name: &str,
) -> Option<&'a StructLayout> {
    struct_layouts.get(struct_name).or_else(|| {
        struct_layouts
            .iter()
            .find(|(k, _)| {
                **k == struct_name
                    || struct_name.starts_with(k.as_str())
                    || k.ends_with(&format!("_{struct_name}"))
            })
            .map(|(_, v)| v)
    })
}

/// Recomputes C-ABI aligned offsets and sizes for all structs in `layouts` in a fixed-point pass
/// so nested structs receive exact field offsets regardless of declaration order.
pub fn normalize_struct_layouts(
    raw_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> HashMap<String, StructLayout> {
    let mut current = raw_layouts.clone();
    // Run bounded fixed-point passes for arbitrarily nested structs.
    for _ in 0..8 {
        let mut changed = false;
        let snapshot = current.clone();
        for (name, layout) in current.iter_mut() {
            let mut ordered: Vec<(String, u32, Type)> = layout
                .field_offsets
                .iter()
                .map(|(fname, (off, fty))| (fname.clone(), *off, *fty))
                .collect();
            // Sort by previous offset; ties break by name for determinism.
            ordered.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(&b.0)));

            let mut offset = 0u32;
            let mut max_align = 1u32;
            let mut new_fields = HashMap::with_capacity(ordered.len());
            for (fname, _, fty) in ordered {
                let (f_size, f_align) = size_and_align_inner(
                    &fty,
                    &snapshot,
                    enum_layouts,
                    &mut HashSet::from([name.clone()]),
                );
                let fa = f_align.max(1);
                offset = align_up(offset, fa);
                new_fields.insert(fname, (offset, fty));
                offset += f_size;
                max_align = max_align.max(fa);
            }
            let total = if offset == 0 { 0 } else { align_up(offset, max_align) };
            if layout.total_size != total || layout.field_offsets != new_fields {
                layout.total_size = total;
                layout.field_offsets = new_fields;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    current
}

fn scalar_cl_ty(ty: &Type) -> Option<cranelift_codegen::ir::Type> {
    match ty {
        Type::I32 => Some(types::I32),
        Type::Int => Some(types::I64),
        Type::F32 => Some(types::F32),
        Type::Float => Some(types::F64),
        Type::Bool => Some(types::I8),
        Type::Str
        | Type::Ptr(_)
        | Type::Ref(_)
        | Type::MutRef(_)
        | Type::Rc(_)
        | Type::Arc(_)
        | Type::DynTrait(_)
        | Type::Generic(_)
        | Type::Infer(_) => Some(types::I64),
        Type::Enum(name) if is_npo_enum(name) => Some(types::I64),
        Type::Obj(s) => {
            let norm = normalize_type_name(s);
            match norm.as_str() {
                "f64" | "float" => Some(types::F64),
                "f32" => Some(types::F32),
                _ => None,
            }
        }
        _ => None,
    }
}

pub fn size_and_align(
    ty: &Type,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> (u32, u32) {
    let mut visited = HashSet::new();
    size_and_align_inner(ty, struct_layouts, enum_layouts, &mut visited)
}

fn size_and_align_inner(
    ty: &Type,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    visited: &mut HashSet<String>,
) -> (u32, u32) {
    match ty {
        Type::Unit | Type::Void => (0, 1),
        Type::Bool => (1, 1),
        Type::I32 | Type::F32 => (4, 4),
        Type::Int
        | Type::Float
        | Type::Str
        | Type::Ptr(_)
        | Type::Ref(_)
        | Type::MutRef(_)
        | Type::Rc(_)
        | Type::Arc(_)
        | Type::DynTrait(_)
        | Type::Generic(_)
        | Type::Infer(_) => (8, 8),
        Type::Vec(_) | Type::String => (24, 8),
        Type::Slice(_) => (16, 8),
        Type::Array(elem, len) => {
            let (es, ea) = size_and_align_inner(elem, struct_layouts, enum_layouts, visited);
            let stride = align_up(es, ea);
            (stride * (*len as u32), ea.max(1))
        }
        Type::Tuple(elems) => {
            let (sz, al, _) =
                tuple_field_offsets_inner(elems, struct_layouts, enum_layouts, visited);
            (sz, al)
        }
        Type::Enum(name) => {
            if is_npo_enum(name) {
                (8, 8)
            } else {
                enum_size_and_align_inner(name, struct_layouts, enum_layouts, visited)
            }
        }
        Type::Obj(name) => {
            let norm = normalize_type_name(name);
            if matches!(norm.as_str(), "f64" | "float") {
                return (8, 8);
            }
            if norm == "f32" {
                return (4, 4);
            }
            if *name == "Vec" || *name == "std_vec_Vec" || name.starts_with("std_vec_Vec_") {
                return (24, 8);
            }
            if *name == "String" || *name == "std_string_String" {
                return (24, 8);
            }
            if !visited.insert((*name).to_string()) {
                return (8, 8);
            }
            let res = if let Some(layout) = find_struct_layout(struct_layouts, name) {
                if layout.field_offsets.is_empty() {
                    (0, 1)
                } else {
                    let mut ordered: Vec<(u32, Type)> =
                        layout.field_offsets.values().copied().collect();
                    ordered.sort_by_key(|(off, _)| *off);
                    let mut max_align = 1u32;
                    let mut max_end = 0u32;
                    for (off, fty) in ordered {
                        let (fs, fa) =
                            size_and_align_inner(&fty, struct_layouts, enum_layouts, visited);
                        max_align = max_align.max(fa);
                        max_end = max_end.max(off + fs);
                    }
                    let computed = align_up(max_end, max_align);
                    (computed.max(layout.total_size), max_align)
                }
            } else {
                (8, 8)
            };
            visited.remove(*name);
            res
        }
    }
}

pub fn array_stride(
    elem_ty: &Type,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> u32 {
    let (s, a) = size_and_align(elem_ty, struct_layouts, enum_layouts);
    align_up(s, a)
}

/// Computes `(total_size, align, field_byte_offsets)` for a tuple `(T0, T1, ...)` using C-ABI alignment.
pub fn tuple_field_offsets(
    elem_tys: &[Type],
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> (u32, u32, Vec<u32>) {
    let mut visited = HashSet::new();
    tuple_field_offsets_inner(elem_tys, struct_layouts, enum_layouts, &mut visited)
}

fn tuple_field_offsets_inner(
    elem_tys: &[Type],
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    visited: &mut HashSet<String>,
) -> (u32, u32, Vec<u32>) {
    let mut offset = 0u32;
    let mut max_align = 1u32;
    let mut offsets = Vec::with_capacity(elem_tys.len());
    for ety in elem_tys {
        let (fs, fa) = size_and_align_inner(ety, struct_layouts, enum_layouts, visited);
        let fa = fa.max(1);
        offset = align_up(offset, fa);
        offsets.push(offset);
        offset += fs;
        max_align = max_align.max(fa);
    }
    let total = if offset == 0 {
        0
    } else {
        align_up(offset, max_align)
    };
    (total, max_align, offsets)
}

/// Computes `(variant_total_size, variant_align, field_byte_offsets)` for one enum variant,
/// placing the `i64` discriminant at offset 0 and payload fields starting at offset 8+.
pub fn enum_variant_offsets(
    payload_tys: &[Type],
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> (u32, u32, Vec<u32>) {
    let mut visited = HashSet::new();
    enum_variant_offsets_inner(payload_tys, struct_layouts, enum_layouts, &mut visited)
}

fn enum_variant_offsets_inner(
    payload_tys: &[Type],
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    visited: &mut HashSet<String>,
) -> (u32, u32, Vec<u32>) {
    let mut offset = 8u32;
    let mut max_align = 8u32;
    let mut field_offsets = Vec::with_capacity(payload_tys.len());
    for pty in payload_tys {
        let (fs, fa) = size_and_align_inner(pty, struct_layouts, enum_layouts, visited);
        let fa = fa.max(1);
        offset = align_up(offset, fa);
        field_offsets.push(offset);
        offset += fs;
        max_align = max_align.max(fa);
    }
    let total = align_up(offset, max_align);
    (total, max_align, field_offsets)
}

fn enum_size_and_align_inner(
    name: &str,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
    visited: &mut HashSet<String>,
) -> (u32, u32) {
    if !visited.insert(format!("enum:{name}")) {
        return (8, 8);
    }
    let res = if let Some(variants) = find_enum_layout(name, enum_layouts) {
        let mut max_size = 8u32;
        let mut max_align = 8u32;
        for (_, _, p_tys) in variants {
            let (vsize, valign, _) =
                enum_variant_offsets_inner(p_tys, struct_layouts, enum_layouts, visited);
            max_size = max_size.max(vsize);
            max_align = max_align.max(valign);
        }
        (align_up(max_size, max_align), max_align)
    } else {
        (16, 8)
    };
    visited.remove(&format!("enum:{name}"));
    res
}

pub fn repr_kind(
    ty: &Type,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> ReprKind {
    if let Some(cl_ty) = scalar_cl_ty(ty) {
        return ReprKind::Scalar(cl_ty);
    }
    let (size, align) = size_and_align(ty, struct_layouts, enum_layouts);
    if size == 0 {
        ReprKind::Zst
    } else {
        ReprKind::Aggregate { size, align }
    }
}

#[inline]
pub fn is_aggregate_type(
    ty: &Type,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> bool {
    matches!(
        repr_kind(ty, struct_layouts, enum_layouts),
        ReprKind::Aggregate { .. }
    )
}

/// Scalar Cranelift IR type used when moving or storing a scalar (`I64` dummy for ZST/Aggregate).
pub fn scalar_ir_type(ty: &Type) -> cranelift_codegen::ir::Type {
    scalar_cl_ty(ty).unwrap_or(types::I64)
}

pub fn pass_mode_for_type(
    ty: &Type,
    force_indirect: bool,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> PassMode {
    match repr_kind(ty, struct_layouts, enum_layouts) {
        ReprKind::Zst => PassMode::Ignore,
        ReprKind::Scalar(cl_ty) => PassMode::Direct(cl_ty),
        ReprKind::Aggregate { size, align } => {
            if force_indirect || size > 16 {
                PassMode::Indirect { size, align }
            } else {
                let chunk_count = if size <= 8 { 1 } else { 2 };
                PassMode::MultiReg {
                    size,
                    align,
                    chunks: vec![types::I64; chunk_count],
                }
            }
        }
    }
}

pub fn abi_signature_for_fn(
    call_conv: CallConv,
    param_types: &[Type],
    ret_type: &Type,
    is_drop_fn: bool,
    struct_layouts: &HashMap<String, StructLayout>,
    enum_layouts: &EnumLayoutMap,
) -> (cranelift_codegen::ir::Signature, FnAbi) {
    let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
    let ret_mode = pass_mode_for_type(ret_type, false, struct_layouts, enum_layouts);
    let has_sret = matches!(ret_mode, PassMode::Indirect { .. });
    if has_sret {
        sig.params.push(AbiParam::new(types::I64));
    } else {
        match &ret_mode {
            PassMode::Ignore => {}
            PassMode::Direct(cl_ty) => sig.returns.push(AbiParam::new(*cl_ty)),
            PassMode::MultiReg { chunks, .. } => {
                for cl_ty in chunks {
                    sig.returns.push(AbiParam::new(*cl_ty));
                }
            }
            PassMode::Indirect { .. } => unreachable!(),
        }
    }

    let mut param_modes = Vec::with_capacity(param_types.len());
    for (i, pty) in param_types.iter().enumerate() {
        // `Drop::drop(mut self)` receives `&mut self` pointer so in-place drop sees all mutations.
        let force_ind = is_drop_fn && i == 0;
        let mode = pass_mode_for_type(pty, force_ind, struct_layouts, enum_layouts);
        match &mode {
            PassMode::Ignore => {}
            PassMode::Direct(cl_ty) => sig.params.push(AbiParam::new(*cl_ty)),
            PassMode::MultiReg { chunks, .. } => {
                for cl_ty in chunks {
                    sig.params.push(AbiParam::new(*cl_ty));
                }
            }
            PassMode::Indirect { .. } => sig.params.push(AbiParam::new(types::I64)),
        }
        param_modes.push(mode);
    }

    (
        sig,
        FnAbi {
            has_sret,
            ret_mode,
            param_modes,
        },
    )
}

/// Allocates a stack slot for an aggregate of `(size, align)` and returns `(slot, stack_addr)`.
pub fn alloc_stack_slot(
    builder: &mut FunctionBuilder,
    size: u32,
    align: u32,
) -> (StackSlot, Value) {
    let alloc_size = size.max(1);
    let align_shift = align.max(1).trailing_zeros() as u8;
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        alloc_size,
        align_shift,
    ));
    let addr = builder.ins().stack_addr(types::I64, slot, 0);
    (slot, addr)
}

/// Copies `size` bytes from `src_ptr` to `dst_ptr`.
pub fn emit_memcpy_bytes<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    dst_ptr: Value,
    src_ptr: Value,
    size: u32,
) {
    if size == 0 {
        return;
    }
    if size <= 64 {
        let mut off = 0u32;
        while off + 8 <= size {
            let v = builder
                .ins()
                .load(types::I64, MemFlags::new(), src_ptr, off as i32);
            builder.ins().store(MemFlags::new(), v, dst_ptr, off as i32);
            off += 8;
        }
        while off + 4 <= size {
            let v = builder
                .ins()
                .load(types::I32, MemFlags::new(), src_ptr, off as i32);
            builder.ins().store(MemFlags::new(), v, dst_ptr, off as i32);
            off += 4;
        }
        while off < size {
            let v = builder
                .ins()
                .load(types::I8, MemFlags::new(), src_ptr, off as i32);
            builder.ins().store(MemFlags::new(), v, dst_ptr, off as i32);
            off += 1;
        }
    } else {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module
            .declare_function("memcpy", Linkage::Import, &sig)
            .unwrap();
        let local_callee = module.declare_func_in_func(callee, builder.func);
        let len_val = builder.ins().iconst(types::I64, size as i64);
        builder.ins().call(local_callee, &[dst_ptr, src_ptr, len_val]);
    }
}

/// Loads `chunks.len()` `I64` registers from an aggregate stored at `src_ptr`,
/// copying through a padded scratch stack slot if `size % 8 != 0` to avoid out-of-bounds reads.
pub fn load_multireg_chunks<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    src_ptr: Value,
    size: u32,
    chunks: &[cranelift_codegen::ir::Type],
) -> Vec<Value> {
    let read_base = if size % 8 == 0 && size >= (chunks.len() as u32) * 8 {
        src_ptr
    } else {
        let buf_bytes = (chunks.len() as u32) * 8;
        let (_, scratch_addr) = alloc_stack_slot(builder, buf_bytes, 8);
        let zero = builder.ins().iconst(types::I64, 0);
        for i in 0..chunks.len() {
            builder
                .ins()
                .store(MemFlags::new(), zero, scratch_addr, (i * 8) as i32);
        }
        emit_memcpy_bytes(builder, module, scratch_addr, src_ptr, size);
        scratch_addr
    };
    chunks
        .iter()
        .enumerate()
        .map(|(i, cl_ty)| {
            builder
                .ins()
                .load(*cl_ty, MemFlags::new(), read_base, (i * 8) as i32)
        })
        .collect()
}

/// Stores `values` (`I64` register chunks) into an aggregate at `dst_ptr`,
/// avoiding out-of-bounds writes when `size % 8 != 0`.
pub fn store_multireg_chunks<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    dst_ptr: Value,
    size: u32,
    values: &[Value],
) {
    if size % 8 == 0 && size >= (values.len() as u32) * 8 {
        for (i, val) in values.iter().enumerate() {
            builder
                .ins()
                .store(MemFlags::new(), *val, dst_ptr, (i * 8) as i32);
        }
    } else {
        let buf_bytes = (values.len() as u32).max(1) * 8;
        let (_, scratch_addr) = alloc_stack_slot(builder, buf_bytes, 8);
        for (i, val) in values.iter().enumerate() {
            builder
                .ins()
                .store(MemFlags::new(), *val, scratch_addr, (i * 8) as i32);
        }
        emit_memcpy_bytes(builder, module, dst_ptr, scratch_addr, size);
    }
}
