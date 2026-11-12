//! sanal.rs
//! Semantic analysis & Type Checking pass converting untyped AST into Typed AST.

pub mod binops;
pub mod calls;
pub mod compat;
pub mod control_flow;
pub mod infer;
pub mod macros;
pub mod mono;
pub mod objects;
pub mod refs;
pub mod types;
pub mod vars;

use crate::{
    ast::{intern_str, FuncDecl, Param, Program, Span, Type, TypedExpr, TypedFuncDecl, TypedProgram},
    sanal::mono::{extract_generic_params_enum, extract_generic_params_struct, Monomorphizer},
    sanal::types::{type_check_expr, TypeCtx},
};
use std::cell::RefCell;
use std::collections::HashMap;

// A custom struct to hold the error message, label, error code, optional help message, AND where it happened
#[derive(Debug)]
pub struct SemanticError {
    pub code: &'static str,
    pub message: String,
    pub label: String,
    pub secondary_label: Option<(Span, String)>,
    pub help: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StructLayout {
    pub name: String,
    pub total_size: u32,
    pub field_offsets: HashMap<String, (u32, Type)>,
}

#[derive(Debug, Clone, Copy)]
pub struct VarInfo {
    pub is_mutable: bool,
    pub ty: Type,
    pub is_moved: bool,
    pub from_caller: bool,
}

/// A scope stack (symbol table) to manage nested lexical scopes, variable types, and mutability flags.
#[derive(Debug)]
pub struct ScopeStack {
    scopes: Vec<HashMap<String, VarInfo>>,
    /// Active local borrows per lexical scope: `(holder_var, borrowed_target_var, is_mut)`.
    borrows: Vec<Vec<(String, String, bool)>>,
}

impl Default for ScopeStack {
    fn default() -> Self {
        Self::new()
    }
}

impl ScopeStack {
    pub fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            borrows: vec![Vec::new()],
        }
    }

    /// Pushes a new child lexical scope.
    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.borrows.push(Vec::new());
    }

    /// Pops the innermost lexical scope upon exiting a block/function.
    pub fn pop_scope(&mut self) {
        self.scopes.pop();
        self.borrows.pop();
    }

    /// Declares a variable in the innermost (current) scope.
    pub fn declare(&mut self, name: String, is_mutable: bool, ty: Type) {
        self.declare_with_caller(name, is_mutable, ty, false);
    }

    /// Declares a variable with an explicit flag indicating whether a reference originates from a caller parameter.
    pub fn declare_with_caller(&mut self, name: String, is_mutable: bool, ty: Type, from_caller: bool) {
        if let Some(current_scope) = self.scopes.last_mut() {
            current_scope.insert(
                name,
                VarInfo {
                    is_mutable,
                    ty,
                    is_moved: false,
                    from_caller,
                },
            );
        }
    }

    /// Returns true if `name` is declared in the innermost lexical scope.
    pub fn current_scope_contains(&self, name: &str) -> bool {
        self.scopes.last().is_some_and(|s| s.contains_key(name))
    }

    pub fn mark_moved(&mut self, name: &str) {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(info) = scope.get_mut(name) {
                if !info.ty.is_copy() {
                    info.is_moved = true;
                }
                return;
            }
        }
    }

    pub fn mark_active(&mut self, name: &str) {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(info) = scope.get_mut(name) {
                info.is_moved = false;
                return;
            }
        }
    }

    /// Looks up variable info from innermost scope up to parent scopes.
    pub fn lookup(&self, name: &str) -> Option<&VarInfo> {
        for scope in self.scopes.iter().rev() {
            if let Some(info) = scope.get(name) {
                return Some(info);
            }
        }
        None
    }

    /// Looks up mutable variable info from innermost scope up to parent scopes.
    pub fn lookup_mut(&mut self, name: &str) -> Option<&mut VarInfo> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(info) = scope.get_mut(name) {
                return Some(info);
            }
        }
        None
    }

    /// Records an active local borrow (`holder` borrowing `target`) in the current scope.
    pub fn add_borrow(&mut self, holder: String, target: String, is_mut: bool) {
        if let Some(current) = self.borrows.last_mut() {
            current.push((holder, target, is_mut));
        }
    }

    /// Removes any active local borrow entries owned by `holder` (e.g., on reference reassignment).
    pub fn remove_borrow(&mut self, holder: &str) {
        for scope_borrows in &mut self.borrows {
            scope_borrows.retain(|(h, _, _)| h != holder);
        }
    }

    /// Returns the most recent target variable borrowed by `holder`, if any.
    pub fn borrow_target(&self, holder: &str) -> Option<String> {
        for scope_borrows in self.borrows.iter().rev() {
            for (h, target, _) in scope_borrows.iter().rev() {
                if h == holder {
                    return Some(target.clone());
                }
            }
        }
        None
    }

    /// Returns `Some((is_mut, holder_name))` if `target` currently has any active local borrow.
    /// Prefers returning a mutable borrow if one exists.
    pub fn active_borrow(&self, target: &str) -> Option<(bool, String)> {
        let mut imm_holder: Option<String> = None;
        for scope_borrows in &self.borrows {
            for (holder, t, is_mut) in scope_borrows {
                if t == target {
                    if *is_mut {
                        return Some((true, holder.clone()));
                    }
                    if imm_holder.is_none() {
                        imm_holder = Some(holder.clone());
                    }
                }
            }
        }
        imm_holder.map(|h| (false, h))
    }

    /// Snapshots move flags across all active scopes for flow-sensitive branching.
    pub fn snapshot_moves(&self) -> Vec<HashMap<String, bool>> {
        self.scopes
            .iter()
            .map(|s| s.iter().map(|(k, v)| (k.clone(), v.is_moved)).collect())
            .collect()
    }

    /// Restores previously snapshotted move flags across scopes.
    pub fn restore_moves(&mut self, snap: &[HashMap<String, bool>]) {
        for (scope, saved) in self.scopes.iter_mut().zip(snap.iter()) {
            for (k, &was_moved) in saved {
                if let Some(info) = scope.get_mut(k) {
                    info.is_moved = was_moved;
                }
            }
        }
    }

    /// Applies any moves recorded in `branch` onto the current scopes.
    pub fn merge_moves(&mut self, branch: &[HashMap<String, bool>]) {
        for (scope, br) in self.scopes.iter_mut().zip(branch.iter()) {
            for (k, &moved_in_branch) in br {
                if moved_in_branch {
                    if let Some(info) = scope.get_mut(k) {
                        info.is_moved = true;
                    }
                }
            }
        }
    }
}

pub fn check_semantics(
    program: &Program,
) -> Result<(TypedProgram, HashMap<String, StructLayout>), Vec<SemanticError>> {
    let mut errors = Vec::new();
    let mut typed_functions = Vec::new();

    let mut mono = Monomorphizer::default();
    mono.impl_templates = program.impls.clone();
    let mono_cell = std::cell::RefCell::new(mono);

    let mut struct_map = HashMap::new();
    fn type_contains_ref(ty: &Type) -> bool {
        match ty {
            Type::Ref(_) | Type::MutRef(_) => true,
            Type::Ptr(t) | Type::Slice(t) | Type::Vec(t) | Type::Rc(t) | Type::Arc(t) => {
                type_contains_ref(t)
            }
            Type::Array(t, _) => type_contains_ref(t),
            Type::Tuple(tys) => tys.iter().any(type_contains_ref),
            _ => false,
        }
    }

    for s in &program.structs {
        for field in &s.fields {
            if type_contains_ref(&field.ty) {
                errors.push(SemanticError {
                    code: "E0106",
                    message: format!(
                        "Struct field `{}.{}` cannot store a reference (`&T` / `&mut T`)",
                        s.name, field.name
                    ),
                    label: "References cannot be stored in structs".to_string(),
                    secondary_label: None,
                    help: Some("Store an owned value, `rc<T>`, or `arc<T>` instead".to_string()),
                    span: field.span.clone(),
                });
            }
        }
        let has_generic_fields_or_bounds = s.where_clause.is_some()
            || s.fields
                .iter()
                .any(|f| compat::type_contains_generic(&f.ty));
        let is_generic = !extract_generic_params_struct(s, &mono_cell).is_empty();
        if is_generic {
            mono_cell.borrow_mut().struct_templates.insert(s.name.clone(), s.clone());
        }
        if !has_generic_fields_or_bounds {
            let mut total_size = 0u32;
            let mut field_offsets = HashMap::new();
            for field in &s.fields {
                field_offsets.insert(field.name.clone(), (total_size, field.ty));
                total_size += 8;
            }
            struct_map.insert(
                s.name.clone(),
                StructLayout {
                    name: s.name.clone(),
                    total_size,
                    field_offsets,
                },
            );
        }
    }

    let enum_names: std::collections::HashSet<String> =
        program.enums.iter().map(|e| e.name.clone()).collect();
    let mut enum_map = HashMap::new();
    for e in &program.enums {
        for variant in &e.variants {
            if variant.payload_types.iter().any(type_contains_ref) {
                errors.push(SemanticError {
                    code: "E0106",
                    message: format!(
                        "Enum variant `{}::{}` cannot store a reference (`&T` / `&mut T`)",
                        e.name, variant.name
                    ),
                    label: "References cannot be stored in enums".to_string(),
                    secondary_label: None,
                    help: Some("Store an owned value, `rc<T>`, or `arc<T>` instead".to_string()),
                    span: variant.span.clone(),
                });
            }
        }
        let is_generic = !extract_generic_params_enum(e).is_empty();
        if is_generic {
            mono_cell.borrow_mut().enum_templates.insert(e.name.clone(), e.clone());
        } else {
            let mut variant_map = HashMap::new();
            for (i, variant) in e.variants.iter().enumerate() {
                variant_map.insert(
                    variant.name.clone(),
                    (i as i64, variant.payload_types.clone()),
                );
            }
            enum_map.insert(e.name.clone(), (intern_str(&e.name), variant_map));
        }
    }

    let mut all_functions = Vec::new();

    fn resolve_self_type(param_ty: Type, target_ty: Type) -> Type {
        match param_ty {
            Type::Unit => target_ty,
            Type::Ref(inner) if *inner == Type::Unit => Type::Ref(crate::ast::intern_type(target_ty)),
            Type::MutRef(inner) if *inner == Type::Unit => Type::MutRef(crate::ast::intern_type(target_ty)),
            _ => param_ty,
        }
    }

    fn type_contains_generic_decl(ty: &Type) -> bool {
        match ty {
            Type::Generic(_) => true,
            Type::Ptr(t) | Type::Ref(t) | Type::MutRef(t) | Type::Slice(t) | Type::Vec(t) | Type::Rc(t) | Type::Arc(t) => {
                type_contains_generic_decl(t)
            }
            Type::Array(t, _) => type_contains_generic_decl(t),
            Type::Tuple(tys) => tys.iter().any(type_contains_generic_decl),
            _ => false,
        }
    }

    for impl_block in &program.impls {
        let target_is_generic_type = {
            let mono = mono_cell.borrow();
            let is_generic_struct = mono.struct_templates.get(&impl_block.target_type).map(|s| {
                s.where_clause.is_some() || s.fields.iter().any(|f| type_contains_generic_decl(&f.ty))
            }).unwrap_or(false);
            let is_generic_enum = mono.enum_templates.contains_key(&impl_block.target_type);
            is_generic_struct || is_generic_enum
        };
        if target_is_generic_type {
            continue;
        }
        let target_ty = resolve_type(Type::Obj(intern_str(&impl_block.target_type)), &enum_names, 0..1, &mut errors);
        for method in &impl_block.methods {
            let is_generic = method.params.iter().any(|p| matches!(p.ty, Type::Generic(_)))
                || matches!(method.return_type, Type::Generic(_));
            if is_generic {
                continue;
            }
            let mangled_name = format!("{}_{}", impl_block.target_type, method.name);
            let mut params = Vec::new();
            for p in &method.params {
                if p.name == "self" {
                    params.push(Param {
                        name: "self".to_string(),
                        is_mutable: p.is_mutable,
                        ty: resolve_self_type(p.ty, target_ty),
                        span: p.span.clone(),
                    });
                } else {
                    params.push(p.clone());
                }
            }
            all_functions.push(FuncDecl {
                name: mangled_name,
                params,
                return_type: method.return_type,
                where_clause: method.where_clause.clone(),
                body: method.body.clone(),
            });
        }
    }

    all_functions.extend(program.functions.clone());

    // Populate default trait implementations for structs
    for t in &program.traits {
        for method in &t.methods {
            if !method.body.is_empty() {
                for s in &program.structs {
                    let mangled_name = format!("{}_{}", s.name, method.name);
                    let target_ty = Type::Obj(intern_str(&s.name));
                    if !all_functions.iter().any(|f| f.name == mangled_name) {
                        let mut params = Vec::new();
                        for p in &method.params {
                            if p.name == "self" {
                                params.push(Param {
                                    name: "self".to_string(),
                                    is_mutable: p.is_mutable,
                                    ty: resolve_self_type(p.ty, target_ty),
                                    span: p.span.clone(),
                                });
                            } else {
                                params.push(p.clone());
                            }
                        }
                        all_functions.push(FuncDecl {
                            name: mangled_name,
                            params,
                            return_type: method.return_type,
                            where_clause: method.where_clause.clone(),
                            body: method.body.clone(),
                        });
                    }
                }
            }
        }
    }

    for func in &mut all_functions {
        let f_span = func
            .params
            .first()
            .map(|p| p.span.clone())
            .or_else(|| func.body.first().map(|e| e.span()))
            .unwrap_or(0..1);
        func.return_type = resolve_type(func.return_type, &enum_names, f_span.clone(), &mut errors);
        if type_contains_ref(&func.return_type) {
            errors.push(SemanticError {
                code: "E0106",
                message: format!(
                    "Function `{}` cannot return a reference (`&T` / `&mut T`)",
                    func.name
                ),
                label: "References cannot escape a function".to_string(),
                secondary_label: None,
                help: Some("Return an owned value, `rc<T>`, or `arc<T>` instead".to_string()),
                span: f_span,
            });
        }
        for param in &mut func.params {
            param.ty = resolve_type(param.ty, &enum_names, param.span.clone(), &mut errors);
        }
    }

    let mut fn_map = HashMap::new();
    for func in &all_functions {
        fn_map.insert(func.name.clone(), func.clone());
        mono_cell.borrow_mut().fn_templates.insert(func.name.clone(), func.clone());
    }

    let mut extern_fn_names = std::collections::HashSet::new();
    let mut extern_map = HashMap::new();
    let mut extern_signatures = HashMap::new();
    let mut extern_c_names = HashMap::new();
    for ext in &program.externs {
        for ef in &ext.functions {
            let res_ret = resolve_type(ef.return_type, &enum_names, 0..1, &mut errors);
            let res_params: Vec<Type> = ef
                .params
                .iter()
                .map(|p| resolve_type(p.ty, &enum_names, p.span.clone(), &mut errors))
                .collect();

            extern_fn_names.insert(ef.name.clone());
            extern_map.insert(ef.name.clone(), res_ret);
            extern_signatures.insert(ef.name.clone(), (res_params.clone(), res_ret));
            extern_c_names.insert(ef.name.clone(), ef.c_name.clone());

            let mangled = format!("std_libc_{}", ef.name);
            extern_fn_names.insert(mangled.clone());
            extern_map.entry(mangled.clone()).or_insert(res_ret);
            extern_signatures
                .entry(mangled.clone())
                .or_insert_with(|| (res_params.clone(), res_ret));
            extern_c_names
                .entry(mangled)
                .or_insert_with(|| ef.c_name.clone());

            let mangled_math = format!("std_math_{}", ef.name);
            extern_fn_names.insert(mangled_math.clone());
            extern_map.entry(mangled_math.clone()).or_insert(res_ret);
            extern_signatures
                .entry(mangled_math.clone())
                .or_insert_with(|| (res_params, res_ret));
            extern_c_names
                .entry(mangled_math)
                .or_insert_with(|| ef.c_name.clone());
        }
    }

    let mut trait_methods: HashMap<String, Vec<(String, Vec<Type>, Type)>> = HashMap::new();
    for t in &program.traits {
        let mut entries = Vec::new();
        for method in &t.methods {
            let p_types = method.params.iter().map(|p| p.ty).collect();
            let ret_ty = resolve_type(method.return_type, &enum_names, 0..1, &mut errors);
            entries.push((method.name.clone(), p_types, ret_ty));
        }
        trait_methods.insert(t.name.clone(), entries);
    }

    let mut trait_impls: std::collections::HashSet<(String, String)> =
        std::collections::HashSet::new();
    for impl_block in &program.impls {
        let Some(ref tr_name) = impl_block.trait_name else {
            continue;
        };
        trait_impls.insert((impl_block.target_type.clone(), tr_name.clone()));

        let tr_decl = program.traits.iter().find(|t| {
            t.name == *tr_name
                || t.name.ends_with(&format!("_{tr_name}"))
                || tr_name.ends_with(&format!("_{}", t.name))
        });
        if let Some(t_decl) = tr_decl {
            let target_ty = resolve_type(
                Type::Obj(intern_str(&impl_block.target_type)),
                &enum_names,
                impl_block.span.clone(),
                &mut errors,
            );
            for req_m in &t_decl.methods {
                let imp_m = impl_block.methods.iter().find(|m| m.name == req_m.name);
                match imp_m {
                    None if req_m.body.is_empty() => {
                        errors.push(SemanticError {
                            code: "E0046",
                            message: format!(
                                "Not all trait items implemented: missing method `{}` in `impl {} for {}`",
                                req_m.name, tr_name, impl_block.target_type
                            ),
                            label: format!("Missing `{}`", req_m.name),
                            secondary_label: None,
                            help: Some(format!("Implement `fn {}(...)` inside `impl {tr_name} for {}`", req_m.name, impl_block.target_type)),
                            span: impl_block.span.clone(),
                        });
                    }
                    Some(imp) => {
                        if imp.params.len() != req_m.params.len() {
                            errors.push(SemanticError {
                                code: "E0050",
                                message: format!(
                                    "Method `{}` in `impl {} for {}` has {} parameter(s), but trait `{}` requires {}",
                                    imp.name,
                                    tr_name,
                                    impl_block.target_type,
                                    imp.params.len(),
                                    tr_name,
                                    req_m.params.len()
                                ),
                                label: format!("Expected {} parameter(s)", req_m.params.len()),
                                secondary_label: None,
                                help: None,
                                span: imp.params.first().map(|p| p.span.clone()).unwrap_or_else(|| impl_block.span.clone()),
                            });
                        } else {
                            for (rp, ip) in req_m.params.iter().zip(imp.params.iter()) {
                                if rp.name == "self" {
                                    continue;
                                }
                                let rp_ty = if rp.ty == Type::Unit { target_ty } else { resolve_type(rp.ty, &enum_names, impl_block.span.clone(), &mut errors) };
                                let ip_ty = resolve_type(ip.ty, &enum_names, ip.span.clone(), &mut errors);
                                if !compat::is_type_compatible(&rp_ty, &ip_ty) {
                                    errors.push(SemanticError {
                                        code: "E0053",
                                        message: format!(
                                            "Method `{}` parameter `{}` has incompatible type: trait expects `{:?}`, found `{:?}`",
                                            imp.name, ip.name, rp_ty, ip_ty
                                        ),
                                        label: format!("Expected `{:?}`", rp_ty),
                                        secondary_label: None,
                                        help: None,
                                        span: ip.span.clone(),
                                    });
                                }
                            }
                        }
                        let req_ret = if req_m.return_type == Type::Unit && req_m.name != "drop" {
                            Type::Unit
                        } else {
                            resolve_type(req_m.return_type, &enum_names, impl_block.span.clone(), &mut errors)
                        };
                        let imp_ret = resolve_type(imp.return_type, &enum_names, impl_block.span.clone(), &mut errors);
                        let ret_ok = (req_m.return_type == Type::Unit && imp_ret == target_ty)
                            || compat::is_type_compatible(&req_ret, &imp_ret);
                        if !ret_ok {
                            errors.push(SemanticError {
                                code: "E0053",
                                message: format!(
                                    "Method `{}` in `impl {} for {}` has incompatible return type: expected `{:?}`, found `{:?}`",
                                    imp.name, tr_name, impl_block.target_type, req_ret, imp_ret
                                ),
                                label: format!("Expected return `{:?}`", req_ret),
                                secondary_label: None,
                                help: None,
                                span: imp.params.first().map(|p| p.span.clone()).unwrap_or_else(|| impl_block.span.clone()),
                            });
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    {
        let mut m = mono_cell.borrow_mut();
        m.trait_methods = trait_methods.clone();
        m.trait_impls = trait_impls.clone();
    }

    let struct_map_cell = RefCell::new(struct_map);
    let enum_map_cell = RefCell::new(enum_map);
    let fn_map_cell = RefCell::new(fn_map);
    let worklist_cell = RefCell::new(all_functions);

    let dummy_infer_cell = RefCell::new(infer::InferCtx::new());
    let type_ctx = TypeCtx {
        fn_map: &fn_map_cell,
        struct_map: &struct_map_cell,
        enum_map: &enum_map_cell,
        extern_fn_names: &extern_fn_names,
        extern_map: &extern_map,
        extern_signatures: &extern_signatures,
        extern_c_names: &extern_c_names,
        trait_methods: &trait_methods,
        trait_impls: &trait_impls,
        is_unsafe: false,
        loop_depth: 0,
        current_return_type: None,
        current_expected_type: None,
        mono: &mono_cell,
        worklist: &worklist_cell,
        infer: &dummy_infer_cell,
    };

    let mut processed_fn_names = std::collections::HashSet::new();
    let mut i = 0;
    while i < worklist_cell.borrow().len() {
        let func = worklist_cell.borrow()[i].clone();
        i += 1;

        let has_generic = func.params.iter().any(|p| compat::type_contains_generic(&p.ty))
            || compat::type_contains_generic(&func.return_type)
            || func.name.contains("_t_")
            || func.name.ends_with("_t");

        if has_generic {
            continue;
        }

        if processed_fn_names.contains(&func.name) {
            continue;
        }
        processed_fn_names.insert(func.name.clone());

        let mut scope_stack = ScopeStack::new();
        let mut typed_body = Vec::new();
        let fn_infer_cell = RefCell::new(infer::InferCtx::new());

        let resolved_return_type = func.return_type;
        let mut resolved_params = Vec::new();
        let mut fn_ctx = type_ctx.clone();
        fn_ctx.current_return_type = Some(resolved_return_type);
        fn_ctx.infer = &fn_infer_cell;

        for param in &func.params {
            let res_ty = param.ty;
            let from_caller = matches!(res_ty, Type::Ref(_) | Type::MutRef(_));
            scope_stack.declare_with_caller(param.name.clone(), param.is_mutable, res_ty, from_caller);
            resolved_params.push(Param {
                name: param.name.clone(),
                is_mutable: param.is_mutable,
                ty: res_ty,
                span: param.span.clone(),
            });
        }

        let body_len = func.body.len();
        for (idx, expr) in func.body.iter().enumerate() {
            let mut stmt_ctx = fn_ctx.clone();
            if idx + 1 == body_len && resolved_return_type != Type::Unit {
                stmt_ctx.current_expected_type = Some(resolved_return_type);
            }
            if let Some(typed_expr) =
                type_check_expr(&mut scope_stack, &mut errors, &stmt_ctx, expr)
            {
                typed_body.push(typed_expr);
            }
        }

        if resolved_return_type != Type::Unit && !compat::definitely_returns(&typed_body) {
            if let Some(last) = typed_body.last() {
                if !matches!(last, TypedExpr::Let(..) | TypedExpr::LetTuple(..)) && !compat::is_diverging_expr(last) {
                    let _ = fn_infer_cell.borrow_mut().unify(resolved_return_type, last.ty());
                }
            }
        }

        infer::finalize_function_body(
            &mut typed_body,
            &mut fn_infer_cell.borrow_mut(),
            &fn_ctx,
            &mut errors,
        );

        if resolved_return_type != Type::Unit && !compat::definitely_returns(&typed_body) {
            if let Some(last) = typed_body.last() {
                compat::consume_tail_expr(&mut scope_stack, &mut errors, &fn_ctx, last);
                if matches!(resolved_return_type, Type::Ref(_) | Type::MutRef(_)) {
                    control_flow::check_return_ref_lifetime(&scope_stack, last, &mut errors);
                }
            }
            let tail_ok = match typed_body.last() {
                Some(TypedExpr::Let(..) | TypedExpr::LetTuple(..)) | None => false,
                Some(last) => {
                    compat::is_diverging_expr(last)
                        || compat::is_type_compatible(&resolved_return_type, &last.ty())
                }
            };
            if !tail_ok {
                let err_span = typed_body
                    .last()
                    .map(|e| e.span())
                    .or_else(|| func.body.last().map(|e| e.span()))
                    .unwrap_or(0..1);
                let found_desc = match typed_body.last() {
                    Some(TypedExpr::Let(..) | TypedExpr::LetTuple(..)) => "statement (`let`)".to_string(),
                    Some(e) => format!("{:?}", e.ty()),
                    None => "()".to_string(),
                };
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Function `{}` must return `{:?}`, found `{found_desc}`",
                        func.name, resolved_return_type
                    ),
                    label: format!("Expected return type `{:?}`", resolved_return_type),
                    secondary_label: None,
                    help: Some(format!(
                        "Return a value of type `{:?}` on all control-flow paths",
                        resolved_return_type
                    )),
                    span: err_span,
                });
            }
        }

        typed_functions.push(TypedFuncDecl {
            name: func.name.clone(),
            params: resolved_params,
            return_type: resolved_return_type,
            where_clause: func.where_clause.clone(),
            body: typed_body,
        });
    }

    let final_struct_map = struct_map_cell.into_inner();
    let final_enum_map = enum_map_cell.into_inner();
    let mut enum_layouts = HashMap::new();
    for (enum_name, (_, variants)) in final_enum_map {
        let mut sorted: Vec<(String, i64, Vec<Type>)> = variants
            .into_iter()
            .map(|(v_name, (tag, p_tys))| (v_name, tag, p_tys))
            .collect();
        sorted.sort_by_key(|(_, tag, _)| *tag);
        enum_layouts.insert(enum_name, sorted);
    }

    errors.extend(mono_cell.into_inner().bound_violations);

    if errors.is_empty() {
        typed_functions.sort_by_key(|f| if f.name == "main" { 1 } else { 0 });
        Ok((
            TypedProgram {
                traits: program.traits.clone(),
                trait_aliases: program.trait_aliases.clone(),
                externs: program.externs.clone(),
                structs: program.structs.clone(),
                enums: program.enums.clone(),
                impls: program.impls.clone(),
                functions: typed_functions,
                enum_layouts,
            },
            final_struct_map,
        ))
    } else {
        Err(errors)
    }
}

fn resolve_type(
    ty: Type,
    enum_names: &std::collections::HashSet<String>,
    span: Span,
    errors: &mut Vec<SemanticError>,
) -> Type {
    match ty {
        Type::Obj("Result_bare") | Type::Obj("std_core_Result_bare") => {
            errors.push(SemanticError {
                code: "E0107",
                message: "Type `Result` requires generic parameter(s), e.g. `Result<T>` or `Result<T, E>`".to_string(),
                label: "Missing generic parameter for `Result`".to_string(),
                secondary_label: None,
                help: Some("Specify generic types: `Result<T>` or `Result<T, E>`".to_string()),
                span,
            });
            Type::Enum(intern_str("std_core_Result"))
        }
        Type::Obj("Option_bare") | Type::Obj("std_core_Option_bare") => {
            errors.push(SemanticError {
                code: "E0107",
                message: "Type `Option` requires a generic parameter, e.g. `Option<T>`".to_string(),
                label: "Missing generic parameter for `Option`".to_string(),
                secondary_label: None,
                help: Some("Specify generic type: `Option<T>`".to_string()),
                span,
            });
            Type::Enum(intern_str("std_core_Option"))
        }
        Type::Obj("Option") | Type::Obj("Opt") => Type::Enum(intern_str("std_core_Option")),
        Type::Obj("Result") | Type::Obj("Res") => Type::Enum(intern_str("std_core_Result")),
        Type::Obj(name) if name == "Vec" || name == "std_vec_Vec" => {
            Type::Vec(crate::ast::intern_type(Type::Int))
        }
        Type::Obj(name) if name.contains("Option") || name.contains("Result") || enum_names.contains(name) => {
            Type::Enum(intern_str(name))
        }
        Type::Array(elem_ty, len) => Type::Array(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
            len,
        ),
        Type::Tuple(elems) => {
            let resolved: Vec<Type> = elems
                .iter()
                .map(|t| resolve_type(*t, enum_names, span.clone(), errors))
                .collect();
            Type::Tuple(crate::ast::intern_tuple(&resolved))
        }
        Type::Slice(elem_ty) => Type::Slice(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Vec(elem_ty) => Type::Vec(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Ptr(elem_ty) => Type::Ptr(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Ref(elem_ty) => Type::Ref(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::MutRef(elem_ty) => Type::MutRef(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Rc(elem_ty) => Type::Rc(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        Type::Arc(elem_ty) => Type::Arc(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
        ),
        other => other,
    }
}
