//! codegen/ctx.rs
//! Shared per-function codegen state: SSA variables, lexical scopes, RAII drop flags, loop targets, and vtables.

use std::collections::{HashMap, HashSet};
use cranelift_codegen::ir::{types, Block, InstBuilder, StackSlot, StackSlotData, StackSlotKind, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;

use crate::ast::{Type, TypedProgram};
use crate::codegen::drops::{
    allocate_drop_flag, emit_conditional_drop, emit_drop_for_value, has_drop_glue,
    mark_drop_flag_moved,
};
use crate::codegen::expr::{coerce_val, cranelift_type_of};
use crate::sanal::StructLayout;

pub struct ProgramMeta<'a> {
    pub struct_layouts: HashMap<String, StructLayout>,
    pub enum_layouts: &'a HashMap<String, Vec<(String, i64, Vec<Type>)>>,
    pub fn_move_params: HashMap<String, Vec<bool>>,
    pub non_consuming_self_fns: HashSet<String>,
    pub fn_param_types: HashMap<String, Vec<Type>>,
    pub fn_return_types: HashMap<String, Type>,
    pub known_drop_fns: HashSet<String>,
    pub trait_methods: HashMap<String, Vec<String>>,
    pub source_map: &'a crate::loader::SourceMap,
}

impl<'a> ProgramMeta<'a> {
    pub fn from_program(
        program: &'a TypedProgram,
        raw_struct_layouts: &'a HashMap<String, StructLayout>,
        source_map: &'a crate::loader::SourceMap,
    ) -> Self {
        let struct_layouts =
            crate::codegen::layout::normalize_struct_layouts(raw_struct_layouts, &program.enum_layouts);
        let mut fn_move_params = HashMap::new();
        let mut non_consuming_self_fns = HashSet::new();
        let mut fn_param_types = HashMap::new();
        let mut fn_return_types = HashMap::new();
        let mut known_drop_fns = HashSet::new();

        for func in &program.functions {
            if func.name.ends_with("_drop") {
                known_drop_fns.insert(func.name.clone());
            }
        }

        let mut non_drop_trait_methods = HashSet::new();
        for imp in &program.impls {
            if let Some(ref tr_name) = imp.trait_name {
                if tr_name != "Drop" && !tr_name.ends_with("Drop") {
                    for m in &imp.methods {
                        non_drop_trait_methods.insert(format!("{}_{}", imp.target_type, m.name));
                    }
                }
            }
        }

        for func in &program.functions {
            fn_param_types.insert(
                func.name.clone(),
                func.params.iter().map(|p| p.ty).collect(),
            );
            fn_return_types.insert(func.name.clone(), func.return_type);

            let is_non_drop_trait_copy_method = func.return_type != Type::Unit
                && func.return_type.is_copy()
                && (non_drop_trait_methods.contains(&func.name)
                    || non_drop_trait_methods
                        .iter()
                        .any(|m| func.name.ends_with(&format!("_{m}"))));

            let is_non_consuming_self = func.name.ends_with("_drop")
                || func.name.ends_with("_fmt")
                || (func.name.ends_with("_to_string") && !func.name.ends_with("read_to_string"))
                || is_non_drop_trait_copy_method;

            if is_non_consuming_self {
                non_consuming_self_fns.insert(func.name.clone());
            }

            let moves: Vec<bool> = func
                .params
                .iter()
                .map(|p| {
                    if p.name == "self" {
                        !is_non_consuming_self
                            && !matches!(p.ty, Type::Ref(_) | Type::MutRef(_))
                            && !p.ty.is_copy()
                    } else {
                        !p.ty.is_copy() && !matches!(p.ty, Type::Ref(_) | Type::MutRef(_))
                    }
                })
                .collect();
            fn_move_params.insert(func.name.clone(), moves);
        }

        let mut trait_methods = HashMap::new();
        for t in &program.traits {
            let names: Vec<String> = t.methods.iter().map(|m| m.name.clone()).collect();
            trait_methods.insert(t.name.clone(), names);
        }

        Self {
            struct_layouts,
            enum_layouts: &program.enum_layouts,
            fn_move_params,
            non_consuming_self_fns,
            fn_param_types,
            fn_return_types,
            known_drop_fns,
            trait_methods,
            source_map,
        }
    }
}

type SavedBinding = (
    String,
    Option<Variable>,
    Option<StackSlot>,
    Option<(StackSlot, cranelift_codegen::ir::Type)>,
    Option<Type>,
);

#[derive(Default)]
pub struct ScopeFrame {
    pub drops: Vec<(Variable, Type, StackSlot)>,
    pub saved_bindings: Vec<SavedBinding>,
}

pub struct CodegenCtx<'a, 'b> {
    pub meta: &'a mut ProgramMeta<'b>,
    pub func_name: String,
    pub ret_type: Type,
    pub sret_ptr: Option<Value>,
    pub ret_slot: Option<StackSlot>,
    pub vars: HashMap<String, Variable>,
    pub var_types: HashMap<String, Type>,
    pub var_counter: usize,
    pub scopes: Vec<ScopeFrame>,
    pub drop_flags: HashMap<String, StackSlot>,
    pub loop_stack: Vec<(Block, Block, usize, usize)>,
    /// Variables whose address is taken via `&` / `&mut` inside this function.
    pub addr_taken: HashSet<String>,
    /// Stack slots backing addressable scalar variables so `&mut x` mutates `x` in place.
    pub var_slots: HashMap<String, (StackSlot, cranelift_codegen::ir::Type)>,
    /// Statement-scoped unconsumed rvalue temporaries dropped in LIFO order at statement exit.
    pub temp_scopes: Vec<Vec<(Value, Type)>>,
}

impl<'a, 'b> CodegenCtx<'a, 'b> {
    pub fn new(meta: &'a mut ProgramMeta<'b>) -> Self {
        Self {
            meta,
            func_name: String::new(),
            ret_type: Type::Unit,
            sret_ptr: None,
            ret_slot: None,
            vars: HashMap::new(),
            var_types: HashMap::new(),
            var_counter: 0,
            scopes: vec![ScopeFrame::default()],
            drop_flags: HashMap::new(),
            loop_stack: Vec::new(),
            addr_taken: HashSet::new(),
            var_slots: HashMap::new(),
            temp_scopes: Vec::new(),
        }
    }

    pub fn is_addressable_scalar(ty: &Type) -> bool {
        matches!(
            ty,
            Type::Int | Type::I32 | Type::Float | Type::F32 | Type::Bool | Type::Str | Type::Ptr(_)
        )
    }

    /// Binds `name` to `var` in the current lexical scope, saving any shadowed outer binding
    /// so it is restored when the scope exits and cannot be clobbered by inner drops or mutations.
    pub fn bind_var(&mut self, name: &str, var: Variable, ty: Type) {
        let prev_var = self.vars.insert(name.to_string(), var);
        let prev_flag = self.drop_flags.remove(name);
        let prev_slot = self.var_slots.remove(name);
        let prev_ty = self.var_types.insert(name.to_string(), ty);
        if let Some(top) = self.scopes.last_mut() {
            top.saved_bindings
                .push((name.to_string(), prev_var, prev_flag, prev_slot, prev_ty));
        }
    }

    fn restore_scope_bindings(&mut self, frame: ScopeFrame) {
        for (name, prev_var, prev_flag, prev_slot, prev_ty) in frame.saved_bindings.into_iter().rev() {
            if let Some(v) = prev_var {
                self.vars.insert(name.clone(), v);
            } else {
                self.vars.remove(&name);
            }
            if let Some(f) = prev_flag {
                self.drop_flags.insert(name.clone(), f);
            } else {
                self.drop_flags.remove(&name);
            }
            if let Some(s) = prev_slot {
                self.var_slots.insert(name.clone(), s);
            } else {
                self.var_slots.remove(&name);
            }
            if let Some(t) = prev_ty {
                self.var_types.insert(name, t);
            } else {
                self.var_types.remove(&name);
            }
        }
    }

    pub fn track_addr_taken_slot(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &str,
        ty: &Type,
        cl_ty: cranelift_codegen::ir::Type,
        val: Value,
    ) {
        if self.addr_taken.contains(name) && Self::is_addressable_scalar(ty) {
            let slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                8,
                0,
            ));
            builder.ins().stack_store(val, slot, 0);
            self.var_slots.insert(name.to_string(), (slot, cl_ty));
        }
    }

    #[inline]
    pub fn push_scope(&mut self) {
        self.scopes.push(ScopeFrame::default());
    }

    pub fn pop_scope_without_drop(&mut self) {
        if let Some(frame) = self.scopes.pop() {
            self.restore_scope_bindings(frame);
        }
    }

    pub fn track_var_if_droppable(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &str,
        ty: &Type,
        active: bool,
    ) {
        if !has_drop_glue(ty, &self.meta.known_drop_fns, &self.meta.struct_layouts, self.meta.enum_layouts) {
            return;
        }
        let Some(&var) = self.vars.get(name) else {
            return;
        };
        let slot = allocate_drop_flag(builder);
        if !active {
            mark_drop_flag_moved(builder, slot);
        }
        if let Some(top) = self.scopes.last_mut() {
            top.drops.push((var, *ty, slot));
        }
        self.drop_flags.insert(name.to_string(), slot);
    }

    pub fn mark_moved(&self, builder: &mut FunctionBuilder, name: &str) {
        if let Some(&slot) = self.drop_flags.get(name) {
            mark_drop_flag_moved(builder, slot);
        }
    }

    pub fn pop_scope_and_drop<M: Module>(&mut self, builder: &mut FunctionBuilder, module: &mut M) {
        let Some(frame) = self.scopes.pop() else {
            return;
        };
        if !builder.is_unreachable() {
            for &(var, ty, slot) in frame.drops.iter().rev() {
                emit_conditional_drop(
                    builder,
                    var,
                    &ty,
                    slot,
                    &self.meta.known_drop_fns,
                    &self.meta.struct_layouts,
                    self.meta.enum_layouts,
                    module,
                );
            }
        }
        self.restore_scope_bindings(frame);
    }

    pub fn emit_drops_down_to_depth<M: Module>(
        &self,
        builder: &mut FunctionBuilder,
        module: &mut M,
        target_depth: usize,
    ) {
        if builder.is_unreachable() {
            return;
        }
        for scope in self.scopes[target_depth..].iter().rev() {
            for &(var, ty, slot) in scope.drops.iter().rev() {
                emit_conditional_drop(
                    builder,
                    var,
                    &ty,
                    slot,
                    &self.meta.known_drop_fns,
                    &self.meta.struct_layouts,
                    self.meta.enum_layouts,
                    module,
                );
            }
        }
    }

    #[inline]
    pub fn push_temp_scope(&mut self) {
        self.temp_scopes.push(Vec::new());
    }

    #[inline]
    pub fn pop_temp_scope_without_drop(&mut self) {
        self.temp_scopes.pop();
    }

    /// Registers an owned droppable temporary `Value` in the active statement temp scope.
    pub fn register_temp(&mut self, val: Value, ty: &Type) {
        if let Some(top) = self.temp_scopes.last_mut() {
            if has_drop_glue(
                ty,
                &self.meta.known_drop_fns,
                &self.meta.struct_layouts,
                self.meta.enum_layouts,
            ) {
                top.push((val, *ty));
            }
        }
    }

    /// Removes `val` from active temp tracking because ownership transferred to a binding, field, or move call.
    pub fn cancel_temp(&mut self, val: Value) {
        for scope in self.temp_scopes.iter_mut().rev() {
            if let Some(pos) = scope.iter().rposition(|(v, _)| *v == val) {
                scope.remove(pos);
                return;
            }
        }
    }

    pub fn pop_temp_scope_and_drop<M: Module>(&mut self, builder: &mut FunctionBuilder, module: &mut M) {
        let Some(frame) = self.temp_scopes.pop() else {
            return;
        };
        if builder.is_unreachable() {
            return;
        }
        for (val, ty) in frame.into_iter().rev() {
            let coerced = coerce_val(builder, val, cranelift_type_of(&ty));
            emit_drop_for_value(
                builder,
                coerced,
                &ty,
                &self.meta.known_drop_fns,
                &self.meta.struct_layouts,
                self.meta.enum_layouts,
                module,
            );
        }
    }

    pub fn emit_temp_drops_down_to_depth<M: Module>(
        &self,
        builder: &mut FunctionBuilder,
        module: &mut M,
        target_depth: usize,
    ) {
        if builder.is_unreachable() || target_depth >= self.temp_scopes.len() {
            return;
        }
        for scope in self.temp_scopes[target_depth..].iter().rev() {
            for &(val, ty) in scope.iter().rev() {
                let coerced = coerce_val(builder, val, cranelift_type_of(&ty));
                emit_drop_for_value(
                    builder,
                    coerced,
                    &ty,
                    &self.meta.known_drop_fns,
                    &self.meta.struct_layouts,
                    self.meta.enum_layouts,
                    module,
                );
            }
        }
    }
}
