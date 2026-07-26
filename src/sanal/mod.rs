//! sanal.rs
//! Semantic analysis & Type Checking pass converting untyped AST into Typed AST.

pub mod binops;
pub mod calls;
pub mod control_flow;
pub mod objects;
pub mod refs;
pub mod types;
pub mod vars;

use crate::{
    ast::{intern_str, FuncDecl, Param, Program, Span, Type, TypedFuncDecl, TypedProgram},
    sanal::types::{type_check_expr, TypeCtx},
};
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

    /// Looks up mutable variable info from innermost scope up to parent scopes.
    pub fn lookup_mut(&mut self, name: &str) -> Option<&mut VarInfo> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(info) = scope.get_mut(name) {
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

pub fn check_semantics(program: &Program) -> Result<(TypedProgram, HashMap<String, StructLayout>), Vec<SemanticError>> {
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

    let mut enum_names: std::collections::HashSet<String> =
        program.enums.iter().map(|e| e.name.clone()).collect();
    let mut enum_map = HashMap::new();
    for e in &program.enums {
        let mut variant_map = HashMap::new();
        for (i, variant) in e.variants.iter().enumerate() {
            variant_map.insert(
                variant.name.clone(),
                (i as i64, variant.payload_types.clone()),
            );
        }
        enum_map.insert(e.name.clone(), (intern_str(&e.name), variant_map));
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

    for impl_block in &program.impls {
        let target_ty = resolve_type(Type::Obj(intern_str(&impl_block.target_type)), &enum_names, 0..1, &mut errors);
        for method in &impl_block.methods {
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
        let f_span = func.params.first().map(|p| p.span.clone()).unwrap_or(0..1);
        func.return_type = resolve_type(func.return_type, &enum_names, f_span, &mut errors);
        for param in &mut func.params {
            param.ty = resolve_type(param.ty, &enum_names, param.span.clone(), &mut errors);
        }
    }

    let mut fn_map = HashMap::new();
    for func in &all_functions {
        fn_map.insert(func.name.clone(), func);
    }

    let mut extern_fn_names = std::collections::HashSet::new();
    let mut extern_map = HashMap::new();
    let mut extern_signatures = HashMap::new();
    for ext in &program.externs {
        for ef in &ext.functions {
            extern_fn_names.insert(ef.name.clone());
            let res_ret = resolve_type(ef.return_type, &enum_names, 0..1, &mut errors);
            let res_params: Vec<Type> = ef.params.iter().map(|p| resolve_type(p.ty, &enum_names, p.span.clone(), &mut errors)).collect();
            extern_map.insert(ef.name.clone(), res_ret);
            extern_signatures.insert(ef.name.clone(), (res_params, res_ret));
        }
    }

    let type_ctx = TypeCtx {
        fn_map: &fn_map,
        struct_map: &struct_map,
        enum_map: &enum_map,
        extern_fn_names: &extern_fn_names,
        extern_map: &extern_map,
        extern_signatures: &extern_signatures,
        is_unsafe: false,
    };

    for func in &all_functions {
        let mut scope_stack = ScopeStack::new();
        let mut typed_body = Vec::new();

        let resolved_return_type = func.return_type;
        let mut resolved_params = Vec::new();

        for param in &func.params {
            let res_ty = param.ty;
            scope_stack.declare(param.name.clone(), param.is_mutable, res_ty);
            resolved_params.push(Param {
                name: param.name.clone(),
                is_mutable: param.is_mutable,
                ty: res_ty,
                span: param.span.clone(),
            });
        }

        for expr in &func.body {
            if let Some(typed_expr) =
                type_check_expr(&mut scope_stack, &mut errors, &type_ctx, expr)
            {
                typed_body.push(typed_expr);
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
            },
            struct_map,
        ))
    } else {
        Err(errors)
    }
}

fn resolve_type(ty: Type, enum_names: &std::collections::HashSet<String>, span: Span, errors: &mut Vec<SemanticError>) -> Type {
    match ty {
        Type::Obj("Result_bare") => {
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
        Type::Obj("Option_bare") => {
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
        Type::Obj("Option") => Type::Enum(intern_str("std_core_Option")),
        Type::Obj("Result") => Type::Enum(intern_str("std_core_Result")),
        Type::Obj(name) if enum_names.contains(name) => Type::Enum(intern_str(name)),
        Type::Array(elem_ty, len) => Type::Array(
            crate::ast::intern_type(resolve_type(*elem_ty, enum_names, span, errors)),
            len,
        ),
        other => other,
    }
}
