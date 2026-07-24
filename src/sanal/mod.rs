//! sanal.rs
//! Semantic analysis & Type Checking pass converting untyped AST into Typed AST.

use crate::ast::{Expr, FuncDecl, Program, Span, Type, TypedExpr, TypedFuncDecl, TypedProgram};
use std::collections::HashMap;

// A custom struct to hold the error message, label, optional help message, AND where it happened
#[derive(Debug)]
pub struct SemanticError {
    pub message: String,
    pub label: String,
    pub help: Option<String>,
    pub span: Span,
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

    for func in &program.functions {
        let mut scope_stack = ScopeStack::new();
        let mut typed_body = Vec::new();

        for param in &func.params {
            scope_stack.declare(param.name.clone(), false, param.ty);
        }

        for expr in &func.body {
            if let Some(typed_expr) = type_check_expr(&mut scope_stack, &mut errors, &fn_map, expr) {
                typed_body.push(typed_expr);
            }
        }

        typed_functions.push(TypedFuncDecl {
            name: func.name.clone(),
            params: func.params.clone(),
            body: typed_body,
        });
    }

    if errors.is_empty() {
        Ok(TypedProgram {
            functions: typed_functions,
        })
    } else {
        Err(errors)
    }
}

// Type checks an untyped Expr and produces a TypedExpr
fn type_check_expr(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    fn_map: &HashMap<String, &FuncDecl>,
    expr: &Expr,
) -> Option<TypedExpr> {
    match expr {
        Expr::Int(n, span) => Some(TypedExpr::Int(*n, span.clone())),
        Expr::Bool(b, span) => Some(TypedExpr::Bool(*b, span.clone())),
        Expr::String(s, span) => Some(TypedExpr::String(s.clone(), span.clone())),

        Expr::Ident(name, span) => {
            if let Some(info) = scopes.lookup(name) {
                Some(TypedExpr::Ident(name.clone(), info.ty, span.clone()))
            } else {
                errors.push(SemanticError {
                    message: format!("Undefined variable '{name}'"),
                    label: "Variable does not exist in this scope".to_string(),
                    help: None,
                    span: span.clone(),
                });
                None
            }
        }

        Expr::Let(name, is_mutable, value, span) => {
            let typed_val = type_check_expr(scopes, errors, fn_map, value)?;
            let ty = typed_val.ty();
            scopes.declare(name.clone(), *is_mutable, ty);
            Some(TypedExpr::Let(
                name.clone(),
                *is_mutable,
                Box::new(typed_val),
                ty,
                span.clone(),
            ))
        }

        Expr::Assign(name, value, span) => {
            match scopes.lookup(name) {
                Some(info) => {
                    let err = format!("Cannot reassign immutable variable '{name}'");
                    if !info.is_mutable {
                        errors.push(SemanticError {
                            message: err.clone(),
                            label: err,
                            help: Some(format!(
                                "Consider declaring this variable as mutable: 'let mut {name}'"
                            )),
                            span: span.clone(),
                        });
                    }
                    let typed_val = type_check_expr(scopes, errors, fn_map, value)?;
                    Some(TypedExpr::Assign(name.clone(), Box::new(typed_val), span.clone()))
                }
                None => {
                    errors.push(SemanticError {
                        message: format!("Cannot assign to undefined variable '{name}'"),
                        label: format!("Variable '{name}' does not exist in this scope"),
                        help: None,
                        span: span.clone(),
                    });
                    let typed_val = type_check_expr(scopes, errors, fn_map, value)?;
                    errors.retain(|err| !(err.message == format!("Undefined variable '{name}'")));
                    Some(TypedExpr::Assign(name.clone(), Box::new(typed_val), span.clone()))
                }
            }
        }

        Expr::Add(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, rhs)?;
            Some(TypedExpr::Add(Box::new(t_lhs), Box::new(t_rhs), span.clone()))
        }

        Expr::Sub(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, rhs)?;
            Some(TypedExpr::Sub(Box::new(t_lhs), Box::new(t_rhs), span.clone()))
        }

        Expr::GreaterThan(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, rhs)?;
            Some(TypedExpr::GreaterThan(Box::new(t_lhs), Box::new(t_rhs), span.clone()))
        }

        Expr::LessThan(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, rhs)?;
            Some(TypedExpr::LessThan(Box::new(t_lhs), Box::new(t_rhs), span.clone()))
        }

        Expr::Equal(lhs, rhs, span) => {
            let t_lhs = type_check_expr(scopes, errors, fn_map, lhs)?;
            let t_rhs = type_check_expr(scopes, errors, fn_map, rhs)?;
            Some(TypedExpr::Equal(Box::new(t_lhs), Box::new(t_rhs), span.clone()))
        }

        Expr::Block(stmts, span) => {
            scopes.push_scope();
            let mut typed_stmts = Vec::new();
            for stmt in stmts {
                if let Some(t_stmt) = type_check_expr(scopes, errors, fn_map, stmt) {
                    typed_stmts.push(t_stmt);
                }
            }
            scopes.pop_scope();
            let block_ty = typed_stmts.last().map(|s| s.ty()).unwrap_or(Type::Unit);
            Some(TypedExpr::Block(typed_stmts, block_ty, span.clone()))
        }

        Expr::While(cond, body, span) => {
            let t_cond = type_check_expr(scopes, errors, fn_map, cond)?;
            let t_body = type_check_expr(scopes, errors, fn_map, body)?;
            Some(TypedExpr::While(Box::new(t_cond), Box::new(t_body), span.clone()))
        }

        Expr::If(cond, body, span) => {
            let t_cond = type_check_expr(scopes, errors, fn_map, cond)?;
            let t_body = type_check_expr(scopes, errors, fn_map, body)?;
            Some(TypedExpr::If(Box::new(t_cond), Box::new(t_body), span.clone()))
        }

        Expr::MacroCall(name, args, span) => {
            let mut typed_args = Vec::new();
            for arg in args {
                if let Some(t_arg) = type_check_expr(scopes, errors, fn_map, arg) {
                    typed_args.push(t_arg);
                }
            }
            Some(TypedExpr::MacroCall(name.clone(), typed_args, span.clone()))
        }

        Expr::Call(name, args, span) => {
            let mut typed_args = Vec::new();
            for arg in args {
                if let Some(t_arg) = type_check_expr(scopes, errors, fn_map, arg) {
                    typed_args.push(t_arg);
                }
            }
            if let Some(target_func) = fn_map.get(name) {
                if target_func.params.len() != typed_args.len() {
                    errors.push(SemanticError {
                        message: format!(
                            "Function '{name}' expects {} arguments, found {}",
                            target_func.params.len(),
                            typed_args.len()
                        ),
                        label: format!("Expected {} args", target_func.params.len()),
                        help: None,
                        span: span.clone(),
                    });
                }
            } else {
                errors.push(SemanticError {
                    message: format!("Undefined function '{name}'"),
                    label: "Function does not exist".to_string(),
                    help: None,
                    span: span.clone(),
                });
            }
            Some(TypedExpr::Call(name.clone(), typed_args, Type::Int, span.clone()))
        }
    }
}
