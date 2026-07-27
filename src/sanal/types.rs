//! sanal/types.rs
//! Main entry point for expression type-checking. Delegating match arms to domain modules.

use crate::{
    ast::{Expr, FuncDecl, Span, Type, TypedExpr},
    sanal::{
        binops, calls, control_flow, mono::Monomorphizer, objects, refs, vars, ScopeStack,
        SemanticError, StructLayout,
    },
};
use std::cell::RefCell;
use std::collections::HashMap;

fn parse_suffix_to_type(s: &str) -> Option<Type> {
    match s {
        "i64" | "int" => Some(Type::Int),
        "i32" => Some(Type::I32),
        "f64" | "float" => Some(Type::Float),
        "f32" => Some(Type::F32),
        "bool" => Some(Type::Bool),
        "str" | "string" => Some(Type::Str),
        "unit" => Some(Type::Unit),
        _ => None,
    }
}

#[derive(Clone)]
pub struct TypeCtx<'a> {
    pub fn_map: &'a RefCell<HashMap<String, FuncDecl>>,
    pub struct_map: &'a RefCell<HashMap<String, StructLayout>>,
    pub enum_map: &'a RefCell<HashMap<String, (&'static str, HashMap<String, (i64, Vec<Type>)>)>>,
    pub extern_fn_names: &'a std::collections::HashSet<String>,
    pub extern_map: &'a HashMap<String, Type>,
    pub extern_signatures: &'a HashMap<String, (Vec<Type>, Type)>,
    pub is_unsafe: bool,
    pub mono: &'a RefCell<Monomorphizer>,
    pub worklist: &'a RefCell<Vec<FuncDecl>>,
}

impl<'a> TypeCtx<'a> {
    pub fn get_struct(&self, name: &str) -> Option<StructLayout> {
        let res = self.struct_map.borrow().get(name).cloned().or_else(|| {
            self.struct_map
                .borrow()
                .iter()
                .find(|(k, _)| **k == name || k.starts_with(&format!("{name}_")) || k.ends_with(&format!("_{name}")))
                .map(|(_, v)| v.clone())
        });
        if let Some(s) = res {
            return Some(s);
        }

        if let Some((base_name, suffix)) = name.rsplit_once('_') {
            let type_args: Vec<Type> = suffix.split('_').filter_map(parse_suffix_to_type).collect();
            if !type_args.is_empty() {
                if let Some(mangled) = crate::sanal::mono::monomorphize_struct(
                    self.mono,
                    base_name,
                    &type_args,
                    self.struct_map,
                    self.enum_map,
                    self.fn_map,
                    self.worklist,
                ) {
                    return self.struct_map.borrow().get(&mangled).cloned();
                }
            }
        }
        None
    }

    pub fn contains_struct(&self, name: &str) -> bool {
        self.get_struct(name).is_some()
    }

    pub fn get_enum(&self, name: &str) -> Option<(&'static str, HashMap<String, (i64, Vec<Type>)>)> {
        if let Some(res) = self.enum_map.borrow().get(name).cloned().or_else(|| {
            self.enum_map
                .borrow()
                .iter()
                .find(|(k, _)| **k == name || k.ends_with(&format!("_{name}")))
                .map(|(_, v)| v.clone())
        }) {
            return Some(res);
        }

        if name.starts_with("std_core_Option") || name.starts_with("std_core_Result") {
            let base_name = if name.starts_with("std_core_Option") {
                "std_core_Option"
            } else {
                "std_core_Result"
            };
            let rest = if name.len() > base_name.len() {
                &name[base_name.len() + 1..]
            } else {
                "i64"
            };
            let type_args: Vec<Type> = rest.split('_').filter_map(parse_suffix_to_type).collect();
            let final_args = if type_args.is_empty() {
                vec![Type::Int]
            } else {
                type_args
            };
            if let Some(mangled) = crate::sanal::mono::monomorphize_enum(
                self.mono,
                base_name,
                &final_args,
                self.enum_map,
                self.fn_map,
                self.worklist,
            ) {
                return self.enum_map.borrow().get(&mangled).cloned();
            }
        }
        None
    }

    pub fn contains_enum(&self, name: &str) -> bool {
        self.get_enum(name).is_some()
    }

    pub fn get_fn(&self, name: &str) -> Option<FuncDecl> {
        self.fn_map.borrow().get(name).cloned().or_else(|| {
            self.fn_map
                .borrow()
                .iter()
                .find(|(k, _)| **k == name || k.ends_with(&format!("_{name}")))
                .map(|(_, v)| v.clone())
        })
    }

    pub fn contains_fn(&self, name: &str) -> bool {
        self.get_fn(name).is_some()
    }
}

/// Type checks an untyped Expr and produces a TypedExpr
pub fn type_check_expr<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    expr: &Expr,
) -> Option<TypedExpr> {
    match expr {
        Expr::Int(n, span) => Some(TypedExpr::Int(*n, span.clone())),
        Expr::Float(f, span) => Some(TypedExpr::Float(*f, span.clone())),
        Expr::Bool(b, span) => Some(TypedExpr::Bool(*b, span.clone())),
        Expr::String(s, span) => Some(TypedExpr::String(s.clone(), span.clone())),
        Expr::Range(start, end, span) => {
            let t_start = type_check_expr(scopes, errors, type_ctx, start)?;
            let t_end = type_check_expr(scopes, errors, type_ctx, end)?;
            Some(TypedExpr::Range(
                Box::new(t_start),
                Box::new(t_end),
                Type::Obj(crate::ast::intern_str("Range")),
                span.clone(),
            ))
        }

        // Variable & Let bindings
        Expr::Ident(name, span) => vars::type_check_ident(scopes, errors, type_ctx, name, span),
        Expr::Let(name, explicit_ty, is_mutable, value, span) => {
            vars::type_check_let(scopes, errors, type_ctx, name, explicit_ty.as_ref(), *is_mutable, value, span)
        }
        Expr::Assign(name, value, span) => {
            vars::type_check_assign(scopes, errors, type_ctx, name, value, span)
        }

        // Arithmetic & Bitwise
        Expr::Add(lhs, rhs, span) => binops::type_check_add(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Sub(lhs, rhs, span) => binops::type_check_sub(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Mul(lhs, rhs, span) => binops::type_check_mul(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Div(lhs, rhs, span) => binops::type_check_div(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Mod(lhs, rhs, span) => binops::type_check_mod(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Pipe(lhs, rhs, span) => binops::type_check_pipe(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Ampersand(lhs, rhs, span) => binops::type_check_ampersand(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Caret(lhs, rhs, span) => binops::type_check_caret(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Shl(lhs, rhs, span) => binops::type_check_shl(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Shr(lhs, rhs, span) => binops::type_check_shr(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Neg(val, span) => binops::type_check_neg(scopes, errors, type_ctx, val, span),
        Expr::Not(val, span) => binops::type_check_not(scopes, errors, type_ctx, val, span),

        // Relational & Logical
        Expr::GreaterThan(lhs, rhs, span) => binops::type_check_greater_than(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::LessThan(lhs, rhs, span) => binops::type_check_less_than(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::GreaterEqual(lhs, rhs, span) => binops::type_check_greater_equal(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::LessEqual(lhs, rhs, span) => binops::type_check_less_equal(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Equal(lhs, rhs, span) => binops::type_check_equal(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::NotEqual(lhs, rhs, span) => binops::type_check_not_equal(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::And(lhs, rhs, span) => binops::type_check_and(scopes, errors, type_ctx, lhs, rhs, span),
        Expr::Or(lhs, rhs, span) => binops::type_check_or(scopes, errors, type_ctx, lhs, rhs, span),

        // Control Flow
        Expr::Block(stmts, span) => control_flow::type_check_block(scopes, errors, type_ctx, stmts, span),
        Expr::Unsafe(stmts, span) => control_flow::type_check_unsafe(scopes, errors, type_ctx, stmts, span),
        Expr::Match(target_expr, arms, span) => control_flow::type_check_match(scopes, errors, type_ctx, target_expr, arms, span),
        Expr::Try(inner_expr, span) => control_flow::type_check_try(scopes, errors, type_ctx, inner_expr, span),
        Expr::While(cond, body, span) => control_flow::type_check_while(scopes, errors, type_ctx, cond, body, span),
        Expr::If(cond, body, span) => control_flow::type_check_if(scopes, errors, type_ctx, cond, body, span),
        Expr::IfElse(cond, then_b, else_b, span) => control_flow::type_check_if_else(scopes, errors, type_ctx, cond, then_b, else_b, span),
        Expr::Return(opt_expr, span) => control_flow::type_check_return(scopes, errors, type_ctx, opt_expr.as_deref(), span),

        // Functions & Invocation
        Expr::Call(raw_name, args, span) => calls::type_check_call(scopes, errors, type_ctx, raw_name, args, span),
        Expr::MacroCall(name, args, span) => calls::type_check_macro_call(scopes, errors, type_ctx, name, args, span),
        Expr::Closure(params, body, span) => calls::type_check_closure(scopes, errors, type_ctx, params, body, span),

        // Structs, Enums, Arrays, Indexing
        Expr::ArrayInit(elems, span) => objects::type_check_array_init(scopes, errors, type_ctx, elems, span),
        Expr::IndexAccess(target, idx, span) => objects::type_check_index_access(scopes, errors, type_ctx, target, idx, span),
        Expr::IndexAssign(target, idx, val, span) => objects::type_check_index_assign(scopes, errors, type_ctx, target, idx, val, span),
        Expr::ObjInit(raw_name, fields, span) => objects::type_check_obj_init(scopes, errors, type_ctx, raw_name, fields, span),
        Expr::FieldAccess(target, field_name, span) => objects::type_check_field_access(scopes, errors, type_ctx, target, field_name, span),
        Expr::FieldAssign(target, field_name, val, span) => objects::type_check_field_assign(scopes, errors, type_ctx, target, field_name, val, span),
        Expr::EnumConstruct(enum_name, variant_name, args, span) => objects::type_check_enum_construct(scopes, errors, type_ctx, enum_name, variant_name, args, span),

        // References & Dereferences
        Expr::Ref(inner, is_mut, span) => refs::type_check_ref(scopes, errors, type_ctx, inner, *is_mut, span),
        Expr::Deref(inner, span) => refs::type_check_deref(scopes, errors, type_ctx, inner, span),
        Expr::DerefAssign(ptr, val, span) => refs::type_check_deref_assign(scopes, errors, type_ctx, ptr, val, span),
    }
}

// Forward re-exports for helper functions
pub use binops::{check_binary_op, is_float, is_int};
pub use objects::is_obj_field_type_compatible;
