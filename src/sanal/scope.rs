//! sanal/scope.rs
//! Lexical symbol table, scope management, variable info, and active borrow tracking.

use crate::ast::Type;
use std::collections::HashMap;

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

    /// Returns the zero-based scope stack index where `name` is declared (innermost match).
    pub fn scope_depth(&self, name: &str) -> Option<usize> {
        self.scopes.iter().rposition(|scope| scope.contains_key(name))
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
