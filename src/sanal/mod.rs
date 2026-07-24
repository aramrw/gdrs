//! sanal.rs
//! Semantic analysis & Type Checking pass converting untyped AST into Typed AST.

pub mod types;

use crate::{
    ast::{intern_str, Expr, FuncDecl, Program, Span, StructDecl, Type, TypedExpr, TypedFuncDecl, TypedProgram},
    sanal::types::type_check_expr,
};
use std::collections::HashMap;

// A custom struct to hold the error message, label, optional help message, AND where it happened
#[derive(Debug)]
pub struct SemanticError {
    pub message: String,
    pub label: String,
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
}

/// A scope stack (symbol table) to manage nested lexical scopes, variable types, and mutability flags.
#[derive(Debug, Default)]
pub struct ScopeStack {
    scopes: Vec<HashMap<String, VarInfo>>,
}

impl ScopeStack {
    pub fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
        }
    }

    /// Pushes a new child lexical scope.
    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Pops the innermost lexical scope upon exiting a block/function.
    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// Declares a variable in the innermost (current) scope.
    pub fn declare(&mut self, name: String, is_mutable: bool, ty: Type) {
        if let Some(current_scope) = self.scopes.last_mut() {
            current_scope.insert(name, VarInfo { is_mutable, ty });
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

    /// Checks if a variable is declared in the current scope or any parent scope.
    pub fn contains(&self, name: &str) -> bool {
        self.lookup(name).is_some()
    }
}

pub fn check_semantics(program: &Program) -> Result<TypedProgram, Vec<SemanticError>> {
    let mut errors = Vec::new();
    let mut typed_functions = Vec::new();

    let mut fn_map = HashMap::new();
    for func in &program.functions {
        fn_map.insert(func.name.clone(), func);
    }

    let mut struct_map = HashMap::new();
    for s in &program.structs {
        let mut total_size = 0u32;
        let mut field_offsets = HashMap::new();

        for field in &s.fields {
            field_offsets.insert(field.name.clone(), (total_size, field.ty));
            total_size += 8; // Each primitive or pointer field occupies 8 bytes (i64 stack aligned)
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

    for func in &program.functions {
        let mut scope_stack = ScopeStack::new();
        let mut typed_body = Vec::new();

        for param in &func.params {
            scope_stack.declare(param.name.clone(), false, param.ty);
        }

        for expr in &func.body {
            if let Some(typed_expr) = type_check_expr(&mut scope_stack, &mut errors, &fn_map, &struct_map, expr) {
                typed_body.push(typed_expr);
            }
        }

        typed_functions.push(TypedFuncDecl {
            name: func.name.clone(),
            params: func.params.clone(),
            return_type: func.return_type,
            body: typed_body,
        });
    }

    if errors.is_empty() {
        Ok(TypedProgram {
            structs: program.structs.clone(),
            functions: typed_functions,
        })
    } else {
        Err(errors)
    }
}

