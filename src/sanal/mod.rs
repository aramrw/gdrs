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
pub mod resolve;
pub mod scope;
pub mod types;
pub mod vars;

pub use scope::{ScopeStack, VarInfo};
use resolve::{resolve_type, substitute_self_type};

pub(crate) fn type_contains_ref(ty: &Type) -> bool {
    match ty {
        Type::Ref(_) | Type::MutRef(_) => true,
        Type::Ptr(t)
        | Type::Slice(t)
        | Type::Vec(t)
        | Type::Box(t)
        | Type::Rc(t)
        | Type::Arc(t) => type_contains_ref(t),
        Type::FnPtr(params, ret) => {
            params.iter().any(type_contains_ref) || type_contains_ref(ret)
        }
        Type::Array(t, _) => type_contains_ref(t),
        Type::Tuple(tys) => tys.iter().any(type_contains_ref),
        _ => false,
    }
}

use crate::{
    ast::{
        intern_str, is_visible, Expr, FuncDecl, Param, Program, Span, StaticInitVal, Type,
        TypedExpr, TypedFuncDecl, TypedProgram, TypedStaticDecl, Visibility,
    },
    sanal::mono::{extract_generic_params_enum, extract_generic_params_struct, Monomorphizer},
    sanal::types::{type_check_expr, TypeCtx},
};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
enum ConstVal {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
}

type ConstMapEntry = (Type, TypedExpr, Visibility, Vec<String>);

fn extract_const_val(expr: &TypedExpr) -> Option<ConstVal> {
    match expr {
        TypedExpr::Int(v, _) => Some(ConstVal::Int(*v)),
        TypedExpr::Float(f, _) => Some(ConstVal::Float(*f)),
        TypedExpr::Bool(b, _) => Some(ConstVal::Bool(*b)),
        TypedExpr::String(s, _) => Some(ConstVal::Str(s.clone())),
        TypedExpr::CastI32(inner, _)
        | TypedExpr::CastF32(inner, _)
        | TypedExpr::Cast(inner, _, _) => extract_const_val(inner),
        _ => None,
    }
}

fn eval_const_expr(
    expr: &Expr,
    const_map: &HashMap<String, ConstMapEntry>,
    enum_names: &HashSet<String>,
    decl_mod: &[String],
    errors: &mut Vec<SemanticError>,
) -> Option<ConstVal> {
    match expr {
        Expr::Int(v, _) => Some(ConstVal::Int(*v)),
        Expr::Float(f, _) => Some(ConstVal::Float(*f)),
        Expr::Bool(b, _) => Some(ConstVal::Bool(*b)),
        Expr::String(s, _) => Some(ConstVal::Str(s.clone())),
        Expr::Ident(name, span) => {
            let normalized = name.replace("::", "_");
            let local_key = if !decl_mod.is_empty() {
                Some(format!("{}_{}", decl_mod.join("_"), name))
            } else {
                None
            };
            let found = local_key
                .as_ref()
                .and_then(|k| const_map.get(k))
                .or_else(|| const_map.get(name))
                .or_else(|| const_map.get(&normalized));
            let Some((_, val_expr, vis, target_mod)) = found else {
                errors.push(SemanticError {
                    code: "E0425",
                    message: format!("Undefined constant `{name}` in constant expression"),
                    label: "Constant not found".to_string(),
                    secondary_label: None,
                    help: None,
                    span: span.clone(),
                });
                return None;
            };
            if !is_visible(*vis, target_mod, decl_mod) {
                errors.push(SemanticError {
                    code: "E0603",
                    message: format!("Constant `{name}` is private"),
                    label: "Private constant".to_string(),
                    secondary_label: None,
                    help: Some(format!("Mark `{name}` with `pub const` in its defining module")),
                    span: span.clone(),
                });
                return None;
            }
            extract_const_val(val_expr)
        }
        Expr::Neg(inner, span) => {
            match eval_const_expr(inner, const_map, enum_names, decl_mod, errors)? {
                ConstVal::Int(v) => Some(ConstVal::Int(v.wrapping_neg())),
                ConstVal::Float(f) => Some(ConstVal::Float(-f)),
                other => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!("Cannot negate constant `{other:?}`"),
                        label: "Invalid negation in constant".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                    None
                }
            }
        }
        Expr::Not(inner, span) => {
            match eval_const_expr(inner, const_map, enum_names, decl_mod, errors)? {
                ConstVal::Bool(b) => Some(ConstVal::Bool(!b)),
                other => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!("Cannot apply `!` to constant `{other:?}`"),
                        label: "Expected bool in constant".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                    None
                }
            }
        }
        Expr::Cast(inner, target_ty, span) => {
            let val = eval_const_expr(inner, const_map, enum_names, decl_mod, errors)?;
            let ty = resolve_type(*target_ty, enum_names, span.clone(), errors);
            match (val, ty) {
                (ConstVal::Int(v), Type::Float | Type::F32) => Some(ConstVal::Float(v as f64)),
                (
                    ConstVal::Int(v),
                    Type::Int | Type::I32 | Type::I16 | Type::I8 | Type::U64 | Type::U32 | Type::U16 | Type::U8,
                ) => Some(ConstVal::Int(v)),
                (ConstVal::Int(v), Type::Bool) => Some(ConstVal::Bool(v != 0)),
                (ConstVal::Float(f), Type::Float | Type::F32) => Some(ConstVal::Float(f)),
                (
                    ConstVal::Float(f),
                    Type::Int | Type::I32 | Type::I16 | Type::I8 | Type::U64 | Type::U32 | Type::U16 | Type::U8,
                ) => Some(ConstVal::Int(f as i64)),
                (
                    ConstVal::Bool(b),
                    Type::Int | Type::I32 | Type::I16 | Type::I8 | Type::U64 | Type::U32 | Type::U16 | Type::U8,
                ) => Some(ConstVal::Int(if b { 1 } else { 0 })),
                (ConstVal::Bool(b), Type::Bool) => Some(ConstVal::Bool(b)),
                (ConstVal::Int(v), Type::Ptr(_)) => Some(ConstVal::Int(v)),
                (v, t) => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!("Unsupported constant cast `{v:?}` as `{t:?}`"),
                        label: "Invalid constant cast".to_string(),
                        secondary_label: None,
                        help: None,
                        span: span.clone(),
                    });
                    None
                }
            }
        }
        Expr::Add(l, r, s)
        | Expr::Sub(l, r, s)
        | Expr::Mul(l, r, s)
        | Expr::Div(l, r, s)
        | Expr::Mod(l, r, s)
        | Expr::Shl(l, r, s)
        | Expr::Shr(l, r, s)
        | Expr::Ampersand(l, r, s)
        | Expr::Pipe(l, r, s)
        | Expr::Caret(l, r, s)
        | Expr::Equal(l, r, s)
        | Expr::NotEqual(l, r, s)
        | Expr::LessThan(l, r, s)
        | Expr::LessEqual(l, r, s)
        | Expr::GreaterThan(l, r, s)
        | Expr::GreaterEqual(l, r, s)
        | Expr::And(l, r, s)
        | Expr::Or(l, r, s) => {
            let lv = eval_const_expr(l, const_map, enum_names, decl_mod, errors)?;
            let rv = eval_const_expr(r, const_map, enum_names, decl_mod, errors)?;
            match (expr, lv, rv) {
                (Expr::Add(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a.wrapping_add(b))),
                (Expr::Sub(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a.wrapping_sub(b))),
                (Expr::Mul(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a.wrapping_mul(b))),
                (Expr::Div(..), ConstVal::Int(a), ConstVal::Int(b)) => {
                    if b == 0 {
                        errors.push(SemanticError {
                            code: "E0080",
                            message: "Attempted to divide by zero in constant expression".to_string(),
                            label: "Division by zero".to_string(),
                            secondary_label: None,
                            help: None,
                            span: s.clone(),
                        });
                        None
                    } else {
                        Some(ConstVal::Int(a.wrapping_div(b)))
                    }
                }
                (Expr::Mod(..), ConstVal::Int(a), ConstVal::Int(b)) => {
                    if b == 0 {
                        errors.push(SemanticError {
                            code: "E0080",
                            message: "Attempted remainder by zero in constant expression".to_string(),
                            label: "Modulo by zero".to_string(),
                            secondary_label: None,
                            help: None,
                            span: s.clone(),
                        });
                        None
                    } else {
                        Some(ConstVal::Int(a.wrapping_rem(b)))
                    }
                }
                (Expr::Shl(..), ConstVal::Int(a), ConstVal::Int(b)) => {
                    Some(ConstVal::Int(a.wrapping_shl(b as u32)))
                }
                (Expr::Shr(..), ConstVal::Int(a), ConstVal::Int(b)) => {
                    Some(ConstVal::Int(a.wrapping_shr(b as u32)))
                }
                (Expr::Ampersand(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a & b)),
                (Expr::Pipe(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a | b)),
                (Expr::Caret(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a ^ b)),
                (Expr::Add(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a + b)),
                (Expr::Sub(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a - b)),
                (Expr::Mul(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a * b)),
                (Expr::Div(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a / b)),
                (Expr::Mod(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a % b)),
                (Expr::Equal(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a == b)),
                (Expr::NotEqual(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a != b)),
                (Expr::LessThan(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a < b)),
                (Expr::LessEqual(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a <= b)),
                (Expr::GreaterThan(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a > b)),
                (Expr::GreaterEqual(..), ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a >= b)),
                (Expr::Equal(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a == b)),
                (Expr::NotEqual(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a != b)),
                (Expr::LessThan(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a < b)),
                (Expr::LessEqual(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a <= b)),
                (Expr::GreaterThan(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a > b)),
                (Expr::GreaterEqual(..), ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a >= b)),
                (Expr::And(..), ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a && b)),
                (Expr::Or(..), ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a || b)),
                (Expr::Equal(..), ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a == b)),
                (Expr::NotEqual(..), ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a != b)),
                (_, l_other, r_other) => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!("Incompatible operand types `{l_other:?}` and `{r_other:?}` in constant expression"),
                        label: "Invalid constant binary operation".to_string(),
                        secondary_label: None,
                        help: None,
                        span: s.clone(),
                    });
                    None
                }
            }
        }
        _ => {
            errors.push(SemanticError {
                code: "E0015",
                message: "Expression in top-level `const` is not a compile-time constant".to_string(),
                label: "Expected constant expression".to_string(),
                secondary_label: None,
                help: None,
                span: expr.span(),
            });
            None
        }
    }
}

fn const_val_to_typed_expr(
    val: ConstVal,
    expected_ty: Type,
    span: Span,
    errors: &mut Vec<SemanticError>,
) -> Option<TypedExpr> {
    match (val, expected_ty) {
        (ConstVal::Int(n), Type::Int) => Some(TypedExpr::Int(n, span)),
        (ConstVal::Int(n), Type::I32) => {
            Some(TypedExpr::CastI32(Box::new(TypedExpr::Int(n, span.clone())), span))
        }
        (
            ConstVal::Int(n),
            Type::I8 | Type::I16 | Type::U8 | Type::U16 | Type::U32 | Type::U64,
        ) => Some(TypedExpr::Cast(
            Box::new(TypedExpr::Int(n, span.clone())),
            expected_ty,
            span,
        )),
        (ConstVal::Float(f), Type::Float) => Some(TypedExpr::Float(f, span)),
        (ConstVal::Float(f), Type::F32) => Some(TypedExpr::CastF32(
            Box::new(TypedExpr::Float(f as f32 as f64, span.clone())),
            span,
        )),
        (ConstVal::Bool(b), Type::Bool) => Some(TypedExpr::Bool(b, span)),
        (ConstVal::Str(s), Type::Str) => Some(TypedExpr::String(s, span)),
        (other, ty) => {
            errors.push(SemanticError {
                code: "E0308",
                message: format!("Mismatched `const` type: expected `{ty:?}`, found `{other:?}`"),
                label: format!("Expected `{ty:?}`"),
                secondary_label: None,
                help: None,
                span,
            });
            None
        }
    }
}

fn type_contains_drop_for_static(
    ty: Type,
    struct_map: &HashMap<String, StructLayout>,
    drop_impls: &HashSet<String>,
    visited: &mut HashSet<String>,
) -> bool {
    match ty {
        Type::String | Type::Vec(_) | Type::Box(_) | Type::Rc(_) | Type::Arc(_) | Type::DynTrait(_) => true,
        Type::Array(inner, _) => type_contains_drop_for_static(*inner, struct_map, drop_impls, visited),
        Type::Tuple(elems) => elems
            .iter()
            .any(|e| type_contains_drop_for_static(*e, struct_map, drop_impls, visited)),
        Type::Obj(name) => {
            if drop_impls.contains(name) || !visited.insert(name.to_string()) {
                return drop_impls.contains(name);
            }
            if let Some(layout) = struct_map.get(name) {
                layout
                    .field_offsets
                    .values()
                    .any(|(_, fty)| type_contains_drop_for_static(*fty, struct_map, drop_impls, visited))
            } else {
                false
            }
        }
        Type::Enum(_) => false,
        _ => false,
    }
}

fn eval_static_init_expr(
    expr: &Expr,
    expected_ty: Type,
    const_map: &HashMap<String, ConstMapEntry>,
    struct_map: &HashMap<String, StructLayout>,
    enum_names: &HashSet<String>,
    decl_mod: &[String],
    errors: &mut Vec<SemanticError>,
) -> Option<StaticInitVal> {
    let span = expr.span();
    match (expr, expected_ty) {
        (Expr::ArrayInit(elems, _), Type::Array(elem_ty, expected_len)) => {
            if elems.len() != expected_len {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched array length in `static`: expected {expected_len}, found {}",
                        elems.len()
                    ),
                    label: format!("Expected {expected_len} elements"),
                    secondary_label: None,
                    help: None,
                    span,
                });
                return None;
            }
            let mut vals = Vec::with_capacity(elems.len());
            for e in elems {
                vals.push(eval_static_init_expr(
                    e,
                    *elem_ty,
                    const_map,
                    struct_map,
                    enum_names,
                    decl_mod,
                    errors,
                )?);
            }
            Some(StaticInitVal::Array(vals))
        }
        (Expr::TupleInit(elems, _), Type::Tuple(elem_tys)) => {
            if elems.len() != elem_tys.len() {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched tuple length in `static`: expected {}, found {}",
                        elem_tys.len(),
                        elems.len()
                    ),
                    label: "Tuple arity mismatch".to_string(),
                    secondary_label: None,
                    help: None,
                    span,
                });
                return None;
            }
            let mut vals = Vec::with_capacity(elems.len());
            for (e, ty) in elems.iter().zip(elem_tys.iter()) {
                vals.push(eval_static_init_expr(
                    e,
                    *ty,
                    const_map,
                    struct_map,
                    enum_names,
                    decl_mod,
                    errors,
                )?);
            }
            Some(StaticInitVal::Tuple(vals))
        }
        (Expr::ObjInit(raw_name, field_inits, _), Type::Obj(expected_struct_name)) => {
            let norm = raw_name.replace("::", "_");
            let local_key = if !decl_mod.is_empty() {
                format!("{}_{}", decl_mod.join("_"), norm)
            } else {
                norm.clone()
            };
            let layout = struct_map
                .get(&local_key)
                .or_else(|| struct_map.get(&norm))
                .or_else(|| struct_map.get(expected_struct_name))
                .filter(|l| l.name == expected_struct_name);
            let Some(layout) = layout else {
                errors.push(SemanticError {
                    code: "E0308",
                    message: format!(
                        "Mismatched `static` struct initializer: expected `{expected_struct_name}`, found `{raw_name}`"
                    ),
                    label: format!("Expected `{expected_struct_name}`"),
                    secondary_label: None,
                    help: None,
                    span,
                });
                return None;
            };
            let mut seen = HashSet::new();
            let mut typed_fields = Vec::with_capacity(field_inits.len());
            for (fname, fexpr) in field_inits {
                if !seen.insert(fname.clone()) {
                    errors.push(SemanticError {
                        code: "E0062",
                        message: format!("Field `{fname}` specified more than once in `static` initializer"),
                        label: "Duplicate field".to_string(),
                        secondary_label: None,
                        help: None,
                        span: fexpr.span(),
                    });
                    return None;
                }
                let Some((_, fty)) = layout.field_offsets.get(fname) else {
                    errors.push(SemanticError {
                        code: "E0560",
                        message: format!("Unknown field `{fname}` on struct `{}`", layout.name),
                        label: "Unknown field".to_string(),
                        secondary_label: None,
                        help: None,
                        span: fexpr.span(),
                    });
                    return None;
                };
                if let Some(f_vis) = layout.field_vis.get(fname) {
                    if !is_visible(*f_vis, &layout.module_path, decl_mod) {
                        errors.push(SemanticError {
                            code: "E0616",
                            message: format!("Field `{fname}` of struct `{}` is private", layout.name),
                            label: "Private field".to_string(),
                            secondary_label: None,
                            help: None,
                            span: fexpr.span(),
                        });
                        return None;
                    }
                }
                let fval = eval_static_init_expr(
                    fexpr,
                    *fty,
                    const_map,
                    struct_map,
                    enum_names,
                    decl_mod,
                    errors,
                )?;
                typed_fields.push((fname.clone(), fval));
            }
            for req_field in layout.field_offsets.keys() {
                if !seen.contains(req_field) {
                    errors.push(SemanticError {
                        code: "E0063",
                        message: format!("Missing field `{req_field}` in initializer of `{}`", layout.name),
                        label: "Missing field".to_string(),
                        secondary_label: None,
                        help: None,
                        span,
                    });
                    return None;
                }
            }
            Some(StaticInitVal::Struct(layout.name.clone(), typed_fields))
        }
        (other_expr, other_ty) => {
            let c_val = eval_const_expr(other_expr, const_map, enum_names, decl_mod, errors)?;
            match (c_val, other_ty) {
                (
                    ConstVal::Int(n),
                    Type::Int
                    | Type::I32
                    | Type::I16
                    | Type::I8
                    | Type::U64
                    | Type::U32
                    | Type::U16
                    | Type::U8
                    | Type::Ptr(_),
                ) => Some(StaticInitVal::Int(n)),
                (ConstVal::Float(f), Type::Float | Type::F32) => Some(StaticInitVal::Float(f)),
                (ConstVal::Bool(b), Type::Bool) => Some(StaticInitVal::Bool(b)),
                (ConstVal::Str(s), Type::Str) => Some(StaticInitVal::Str(s)),
                (found, expected) => {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "Mismatched `static` type: expected `{expected:?}`, found `{found:?}`"
                        ),
                        label: format!("Expected `{expected:?}`"),
                        secondary_label: None,
                        help: None,
                        span,
                    });
                    None
                }
            }
        }
    }
}

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
    pub vis: crate::ast::Visibility,
    pub module_path: Vec<String>,
    pub field_vis: HashMap<String, crate::ast::Visibility>,
    pub repr_align: u32,
    pub repr_packed: Option<u32>,
}

/// Parses `#[repr(...)]` attributes on a struct and returns `(repr_align, repr_packed)`.
pub fn parse_struct_repr(
    attrs: &[crate::ast::Attribute],
    errors: &mut Vec<SemanticError>,
) -> (u32, Option<u32>) {
    let mut repr_align = 1u32;
    let mut has_align = false;
    let mut repr_packed: Option<u32> = None;
    let mut last_repr_span: Option<crate::ast::Span> = None;

    let parse_pow2_align = |raw_val: &str, kind: &str, span: &crate::ast::Span, errors: &mut Vec<SemanticError>| -> Option<u32> {
        let trimmed = raw_val.trim();
        let valid = trimmed.parse::<u64>().ok().filter(|&n| n >= 1 && n.is_power_of_two() && n <= (1u64 << 29));
        match valid {
            Some(n) => Some(n as u32),
            None => {
                errors.push(SemanticError {
                    code: "E0589",
                    message: format!(
                        "Invalid alignment `{}` in `#[repr({kind}(...))]`: must be a non-zero power of two (up to `2^29`)",
                        trimmed
                    ),
                    label: "Expected a power-of-two byte alignment >= 1".to_string(),
                    secondary_label: None,
                    help: Some(format!("Use a power of two such as `{kind}(1)`, `{kind}(2)`, `{kind}(4)`, or `{kind}(8)`")),
                    span: span.clone(),
                });
                None
            }
        }
    };

    for attr in attrs {
        if attr.name != "repr" {
            continue;
        }
        last_repr_span = Some(attr.span.clone());
        if attr.args.is_empty() {
            errors.push(SemanticError {
                code: "E0552",
                message: "Malformed `#[repr]` attribute: expected representation specifier".to_string(),
                label: "Empty `#[repr]` attribute".to_string(),
                secondary_label: None,
                help: Some("Use `#[repr(C)]`, `#[repr(packed)]`, `#[repr(packed(N))]`, or `#[repr(align(N))]`".to_string()),
                span: attr.span.clone(),
            });
            continue;
        }
        for raw_arg in &attr.args {
            let arg = raw_arg.trim();
            if arg == "C" {
                // C field declaration order is already the layout default.
            } else if arg == "packed" {
                if let Some(prev) = repr_packed {
                    if prev != 1 {
                        errors.push(SemanticError {
                            code: "E0634",
                            message: format!(
                                "Type has conflicting packed representation hints (`packed` vs `packed({prev})`)"
                            ),
                            label: "Conflicting `packed` hint".to_string(),
                            secondary_label: None,
                            help: Some("Keep a single `packed` or `packed(N)` alignment specifier".to_string()),
                            span: attr.span.clone(),
                        });
                    }
                }
                repr_packed = Some(1);
            } else if let Some(inner) = arg.strip_prefix("packed(").and_then(|s| s.strip_suffix(')')) {
                if let Some(n) = parse_pow2_align(inner, "packed", &attr.span, errors) {
                    if let Some(prev) = repr_packed {
                        if prev != n {
                            errors.push(SemanticError {
                                code: "E0634",
                                message: format!(
                                    "Type has conflicting packed representation hints (`packed({prev})` vs `packed({n})`)"
                                ),
                                label: "Conflicting `packed` hint".to_string(),
                                secondary_label: None,
                                help: Some("Keep a single `packed` or `packed(N)` alignment specifier".to_string()),
                                span: attr.span.clone(),
                            });
                        }
                    }
                    repr_packed = Some(n);
                }
            } else if let Some(inner) = arg.strip_prefix("align(").and_then(|s| s.strip_suffix(')')) {
                if let Some(n) = parse_pow2_align(inner, "align", &attr.span, errors) {
                    repr_align = repr_align.max(n);
                    has_align = true;
                }
            } else {
                errors.push(SemanticError {
                    code: "E0552",
                    message: format!("Unrecognized representation specifier `{arg}` in `#[repr(...)]`"),
                    label: "Unsupported `#[repr]` specifier".to_string(),
                    secondary_label: None,
                    help: Some("Supported struct `#[repr]` specifiers are `C`, `packed`, `packed(N)`, and `align(N)`".to_string()),
                    span: attr.span.clone(),
                });
            }
        }
    }

    if repr_packed.is_some() && has_align {
        errors.push(SemanticError {
            code: "E0587",
            message: "Type cannot have both `#[repr(packed)]` and `#[repr(align(...))]`".to_string(),
            label: "Conflicting `packed` and `align` attributes".to_string(),
            secondary_label: None,
            help: Some("Use `packed` / `packed(N)` to cap field alignment or `align(N)` to raise type alignment, not both".to_string()),
            span: last_repr_span.unwrap_or(0..0),
        });
    }

    (repr_align, repr_packed)
}

pub fn check_semantics(
    program: &Program,
) -> Result<(TypedProgram, HashMap<String, StructLayout>), Vec<SemanticError>> {
    let mut errors = Vec::new();
    let mut typed_functions = Vec::new();

    let mut mono = Monomorphizer::default();
    mono.impl_templates = program.impls.clone();
    let mono_cell = std::cell::RefCell::new(mono);

    let enum_names: std::collections::HashSet<String> =
        program.enums.iter().map(|e| e.name.clone()).collect();
    let mut struct_map = HashMap::new();

    for s in &program.structs {
        let (repr_align, repr_packed) = parse_struct_repr(&s.attributes, &mut errors);
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
            let mut field_vis = HashMap::new();
            for field in &s.fields {
                let resolved_field_ty = resolve_type(field.ty, &enum_names, field.span.clone(), &mut errors);
                field_offsets.insert(field.name.clone(), (total_size, resolved_field_ty));
                field_vis.insert(field.name.clone(), field.vis);
                total_size += 8;
            }
            struct_map.insert(
                s.name.clone(),
                StructLayout {
                    name: s.name.clone(),
                    total_size,
                    field_offsets,
                    vis: s.vis,
                    module_path: s.module_path.clone(),
                    field_vis,
                    repr_align,
                    repr_packed,
                },
            );
        }
    }

    let mut enum_map = HashMap::new();
    let mut enum_vis_map = HashMap::new();
    for e in &program.enums {
        if let Some(repr_attr) = e.attributes.iter().find(|a| a.name == "repr") {
            errors.push(SemanticError {
                code: "E0517",
                message: format!(
                    "Attribute `#[repr(...)]` is not supported on enum `{}`",
                    e.name
                ),
                label: "`#[repr(...)]` is only supported on `struct` definitions".to_string(),
                secondary_label: None,
                help: Some("Remove `#[repr(...)]` from this enum or wrap the C representation inside a `struct`".to_string()),
                span: repr_attr.span.clone(),
            });
        }
        let has_derive_error = e
            .attributes
            .iter()
            .any(|a| a.name == "derive" && a.args.iter().any(|arg| arg == "Error"));
        if has_derive_error {
            for v in &e.variants {
                if let Some(err_attr) = v.attributes.iter().find(|a| a.name == "error" || a.name == "err") {
                    if let Some(tmpl) = err_attr.args.first() {
                        let chars: Vec<char> = tmpl.chars().collect();
                        let mut ci = 0;
                        while ci < chars.len() {
                            if chars[ci] == '{' {
                                if let Some(close_rel) = chars[ci + 1..].iter().position(|&c| c == '}') {
                                    let inner: String = chars[ci + 1..ci + 1 + close_rel].iter().collect();
                                    if !inner.is_empty() && inner.chars().all(|c| c.is_ascii_digit()) {
                                        if let Ok(idx) = inner.parse::<usize>() {
                                            if idx >= v.payload_types.len() {
                                                let help_msg = if v.payload_types.is_empty() {
                                                    format!("Variant `{}` has no payload fields", v.name)
                                                } else if v.payload_types.len() == 1 {
                                                    format!("Valid field index for `{}` is `0`", v.name)
                                                } else {
                                                    format!(
                                                        "Valid field indices for `{}` are `0..={}`",
                                                        v.name,
                                                        v.payload_types.len() - 1
                                                    )
                                                };
                                                errors.push(SemanticError {
                                                    code: "E0001",
                                                    message: format!(
                                                        "Format placeholder `{{{idx}}}` is out of bounds for `{}::{}` (has {} field(s))",
                                                        e.name,
                                                        v.name,
                                                        v.payload_types.len()
                                                    ),
                                                    label: format!("Index `{idx}` is out of bounds"),
                                                    secondary_label: None,
                                                    help: Some(help_msg),
                                                    span: err_attr.span.clone(),
                                                });
                                            }
                                            ci += close_rel + 2;
                                            continue;
                                        }
                                    }
                                }
                            }
                            ci += 1;
                        }
                    }
                }
            }
        }
        enum_vis_map.insert(e.name.clone(), (e.vis, e.module_path.clone()));
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
                let resolved_payloads: Vec<Type> = variant
                    .payload_types
                    .iter()
                    .map(|pt| resolve_type(*pt, &enum_names, variant.span.clone(), &mut errors))
                    .collect();
                variant_map.insert(
                    variant.name.clone(),
                    (i as i64, resolved_payloads),
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
            Type::Ptr(t)
            | Type::Ref(t)
            | Type::MutRef(t)
            | Type::Slice(t)
            | Type::Vec(t)
            | Type::Box(t)
            | Type::Rc(t)
            | Type::Arc(t) => type_contains_generic_decl(t),
            Type::FnPtr(params, ret) => {
                params.iter().any(type_contains_generic_decl) || type_contains_generic_decl(ret)
            }
            Type::Array(t, _) => type_contains_generic_decl(t),
            Type::Tuple(tys) => tys.iter().any(type_contains_generic_decl),
            _ => false,
        }
    }

    fn resolve_impl_target_type(
        target_type: &str,
        enum_names: &std::collections::HashSet<String>,
        span: crate::ast::Span,
        errors: &mut Vec<SemanticError>,
    ) -> Type {
        if let Some(base) = target_type.strip_prefix("&mut ") {
            let inner = resolve_type(Type::Obj(intern_str(base)), enum_names, span, errors);
            Type::MutRef(crate::ast::intern_type(inner))
        } else if let Some(base) = target_type.strip_prefix('&') {
            let inner = resolve_type(Type::Obj(intern_str(base)), enum_names, span, errors);
            Type::Ref(crate::ast::intern_type(inner))
        } else {
            resolve_type(Type::Obj(intern_str(target_type)), enum_names, span, errors)
        }
    }

    for impl_block in &program.impls {
        let base_target_name = impl_block
            .target_type
            .strip_prefix("&mut ")
            .or_else(|| impl_block.target_type.strip_prefix('&'))
            .unwrap_or(&impl_block.target_type);
        let target_is_generic_type = {
            let mono = mono_cell.borrow();
            let is_generic_struct = mono.struct_templates.get(base_target_name).map(|s| {
                s.where_clause.is_some() || s.fields.iter().any(|f| type_contains_generic_decl(&f.ty))
            }).unwrap_or(false);
            let is_generic_enum = mono.enum_templates.contains_key(base_target_name);
            is_generic_struct || is_generic_enum
        };
        if target_is_generic_type {
            continue;
        }
        let target_ty = resolve_impl_target_type(&impl_block.target_type, &enum_names, 0..1, &mut errors);
        let method_prefix = crate::ast::impl_method_prefix(&impl_block.target_type);
        for method in &impl_block.methods {
            let mangled_name = format!("{}_{}", method_prefix, method.name);
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
                    let mut cp = p.clone();
                    cp.ty = substitute_self_type(cp.ty, target_ty);
                    params.push(cp);
                }
            }
            all_functions.push(FuncDecl {
                name: mangled_name,
                params,
                return_type: substitute_self_type(method.return_type, target_ty),
                where_clause: method.where_clause.clone(),
                body: method.body.clone(),
                is_track_caller: method.is_track_caller,
                vis: method.vis,
                module_path: method.module_path.clone(),
                is_trait_impl: impl_block.trait_name.is_some(),
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
                            is_track_caller: method.is_track_caller,
                            vis: crate::ast::Visibility::Pub,
                            module_path: s.module_path.clone(),
                            is_trait_impl: true,
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
        let is_index_or_deref_ref_method = (func.name.ends_with("_index")
            || func.name.ends_with("_index_mut")
            || func.name.ends_with("_deref")
            || func.name.ends_with("_deref_mut"))
            && func
                .params
                .first()
                .is_some_and(|p| p.name == "self" && matches!(p.ty, Type::Ref(_) | Type::MutRef(_)));
        if type_contains_ref(&func.return_type) && !is_index_or_deref_ref_method {
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
    let mut extern_vis_map = HashMap::new();
    for ext in &program.externs {
        for ef in &ext.functions {
            extern_vis_map.insert(ef.name.clone(), (ef.vis, ef.module_path.clone()));
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

    let mut const_map: HashMap<String, ConstMapEntry> = HashMap::new();
    for c in &program.consts {
        let resolved_ty = resolve_type(c.ty, &enum_names, c.span.clone(), &mut errors);
        if let Some(c_val) = eval_const_expr(&c.value, &const_map, &enum_names, &c.module_path, &mut errors) {
            if let Some(typed_val) = const_val_to_typed_expr(c_val, resolved_ty, c.span.clone(), &mut errors) {
                const_map.insert(c.name.clone(), (resolved_ty, typed_val, c.vis, c.module_path.clone()));
            }
        }
    }

    let drop_impls: HashSet<String> = program
        .impls
        .iter()
        .filter(|i| {
            i.trait_name
                .as_deref()
                .is_some_and(|t| t == "Drop" || t.ends_with("_Drop"))
        })
        .map(|i| i.target_type.clone())
        .collect();

    let mut static_map: HashMap<String, (Type, bool, crate::ast::Visibility, Vec<String>)> =
        HashMap::new();
    let mut typed_statics: Vec<TypedStaticDecl> = Vec::new();
    for st in &program.statics {
        let resolved_ty = resolve_type(st.ty, &enum_names, st.span.clone(), &mut errors);
        if type_contains_ref(&resolved_ty) {
            errors.push(SemanticError {
                code: "E0106",
                message: format!("Static item `{}` cannot store a reference (`&T` / `&mut T`)", st.name),
                label: "References cannot be stored in static items".to_string(),
                secondary_label: None,
                help: None,
                span: st.span.clone(),
            });
            continue;
        }
        if type_contains_drop_for_static(resolved_ty, &struct_map, &drop_impls, &mut HashSet::new()) {
            errors.push(SemanticError {
                code: "E0493",
                message: format!(
                    "Static item `{}` cannot have type `{resolved_ty:?}` with heap ownership or `Drop`",
                    st.name
                ),
                label: "Type with destructor not allowed in static initializer".to_string(),
                secondary_label: None,
                help: Some("Use a scalar, fixed array, tuple, raw pointer, or non-Drop POD struct".to_string()),
                span: st.span.clone(),
            });
            continue;
        }
        if let Some(init_val) = eval_static_init_expr(
            &st.value,
            resolved_ty,
            &const_map,
            &struct_map,
            &enum_names,
            &st.module_path,
            &mut errors,
        ) {
            static_map.insert(
                st.name.clone(),
                (resolved_ty, st.is_mut, st.vis, st.module_path.clone()),
            );
            typed_statics.push(TypedStaticDecl {
                name: st.name.clone(),
                ty: resolved_ty,
                is_mut: st.is_mut,
                init: init_val,
                vis: st.vis,
                module_path: st.module_path.clone(),
            });
        }
    }

    for u in &program.uses {
        let target = &u.resolved_target;
        if target.is_empty() {
            continue;
        }
        let mut vis_info: Option<(crate::ast::Visibility, Vec<String>)> = None;
        if let Some(s) = struct_map.get(target) {
            vis_info = Some((s.vis, s.module_path.clone()));
        } else if let Some(s) = mono_cell.borrow().struct_templates.get(target) {
            vis_info = Some((s.vis, s.module_path.clone()));
        } else if let Some(e) = enum_vis_map.get(target) {
            vis_info = Some(e.clone());
        } else if let Some(f) = fn_map.get(target) {
            vis_info = Some((f.vis, f.module_path.clone()));
        } else if let Some(ext) = extern_vis_map.get(target) {
            vis_info = Some(ext.clone());
        } else if let Some(t) = program.traits.iter().find(|t| t.name == *target) {
            vis_info = Some((t.vis, t.module_path.clone()));
        } else if let Some(ta) = program.trait_aliases.iter().find(|ta| ta.name == *target) {
            vis_info = Some((ta.vis, ta.module_path.clone()));
        } else if let Some((_, _, vis, m_path)) = const_map.get(target) {
            vis_info = Some((*vis, m_path.clone()));
        } else if let Some((_, _, vis, m_path)) = static_map.get(target) {
            vis_info = Some((*vis, m_path.clone()));
        }

        if let Some((vis, decl_mod)) = vis_info {
            if !crate::ast::is_visible(vis, &decl_mod, &u.module_path) {
                let sym = u.path.last().map(|s| s.as_str()).unwrap_or(target);
                errors.push(SemanticError {
                    code: "E0603",
                    message: format!("Item `{sym}` in `{}` is private", u.path.join("::")),
                    label: "Private item imported here".to_string(),
                    secondary_label: None,
                    help: Some(format!("Mark `{sym}` with `pub` in its defining module")),
                    span: u.span.clone(),
                });
            }
        }
    }

    let mut trait_methods: HashMap<String, Vec<(String, Vec<Type>, Type)>> = HashMap::new();
    for t in &program.traits {
        let mut entries = Vec::new();
        for method in &t.methods {
            let p_types = method
                .params
                .iter()
                .map(|p| resolve_type(p.ty, &enum_names, 0..1, &mut errors))
                .collect();
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
            let target_ty = resolve_impl_target_type(
                &impl_block.target_type,
                &enum_names,
                impl_block.span.clone(),
                &mut errors,
            );
            for req_m in &t_decl.methods {
                let imp_m = impl_block.methods.iter().find(|m| m.name == req_m.name);
                match imp_m {
                    None if req_m.body.is_empty()
                        && !(impl_block.methods.is_empty()
                            && (tr_name == "Debug" || tr_name.ends_with("_Debug"))) =>
                    {
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

                                let rp_ty = if rp.ty == Type::Unit {
                                    target_ty
                                } else {
                                    let resolved = resolve_type(rp.ty, &enum_names, impl_block.span.clone(), &mut errors);
                                    substitute_self_type(resolved, target_ty)
                                };
                                let ip_ty = substitute_self_type(
                                    resolve_type(ip.ty, &enum_names, ip.span.clone(), &mut errors),
                                    target_ty,
                                );
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
                            substitute_self_type(
                                resolve_type(req_m.return_type, &enum_names, impl_block.span.clone(), &mut errors),
                                target_ty,
                            )
                        };
                        let imp_ret = substitute_self_type(
                            resolve_type(imp.return_type, &enum_names, impl_block.span.clone(), &mut errors),
                            target_ty,
                        );
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
        const_map: &const_map,
        static_map: &static_map,
        current_module: Vec::new(),
        enum_vis: &enum_vis_map,
        extern_vis: &extern_vis_map,
        is_unsafe: false,
        loop_depth: 0,
        current_loop_breaks: None,
        current_return_type: None,
        current_expected_type: None,
        mono: &mono_cell,
        worklist: &worklist_cell,
        infer: &dummy_infer_cell,
    };

    let ensure_layout_types_monomorphized = |ctx: &TypeCtx<'_>| {
        let field_tys: Vec<Type> = ctx
            .struct_map
            .borrow()
            .values()
            .flat_map(|s| s.field_offsets.values().map(|(_, t)| *t))
            .collect();
        for ty in field_tys {
            infer::ensure_concrete_monomorphized(ty, ctx);
        }
        let payload_tys: Vec<Type> = ctx
            .enum_map
            .borrow()
            .values()
            .flat_map(|(_, variants)| variants.values().flat_map(|(_, pts)| pts.iter().copied()))
            .collect();
        for ty in payload_tys {
            infer::ensure_concrete_monomorphized(ty, ctx);
        }
    };
    ensure_layout_types_monomorphized(&type_ctx);

    let mut processed_fn_names = std::collections::HashSet::new();
    let mut extern_import_fns = std::collections::HashSet::new();
    let mut i = 0;
    while i < worklist_cell.borrow().len() {
        let func = worklist_cell.borrow()[i].clone();
        i += 1;

        let has_generic = func.params.iter().any(|p| compat::type_contains_generic(&p.ty))
            || compat::type_contains_generic(&func.return_type);

        if has_generic {
            continue;
        }

        if processed_fn_names.contains(&func.name) {
            continue;
        }
        processed_fn_names.insert(func.name.clone());

        let is_from_extern_crate = func
            .module_path
            .first()
            .is_some_and(|c| program.extern_crate_names.contains(c))
            && crate::sanal::mono::lookup_mangled(&func.name).is_none();
        if is_from_extern_crate {
            extern_import_fns.insert(func.name.clone());
            typed_functions.push(TypedFuncDecl {
                name: func.name.clone(),
                params: func.params.clone(),
                return_type: func.return_type,
                where_clause: func.where_clause.clone(),
                body: Vec::new(),
                is_track_caller: func.is_track_caller,
                is_std: false,
            });
            continue;
        }

        let mut scope_stack = ScopeStack::new();
        let mut typed_body = Vec::new();
        let fn_infer_cell = RefCell::new(infer::InferCtx::new());

        let resolved_return_type = func.return_type;
        let mut resolved_params = Vec::new();
        let mut fn_ctx = type_ctx.clone();
        fn_ctx.current_module = func.module_path.clone();
        fn_ctx.current_return_type = Some(resolved_return_type);
        fn_ctx.infer = &fn_infer_cell;

        let fn_non_consuming_self = calls::validation::is_non_consuming_self_method(
            &func.name,
            &func.params,
            resolved_return_type,
            &trait_methods,
            &trait_impls,
        );
        for param in &func.params {
            let res_ty = param.ty;
            let from_caller = control_flow::lifetimes::type_may_borrow(&res_ty);
            if param.name == "self" && !from_caller && fn_non_consuming_self {
                scope_stack.declare_borrowed_self(param.name.clone(), param.is_mutable, res_ty);
            } else {
                scope_stack.declare_with_caller(param.name.clone(), param.is_mutable, res_ty, from_caller);
            }
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
                if !matches!(last, TypedExpr::Let(..) | TypedExpr::LetTuple(..) | TypedExpr::LetStruct(..)) && !compat::is_diverging_expr(last) {
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
                calls::closures::check_return_closure_escape(last, &fn_ctx, &mut errors);
                if control_flow::lifetimes::type_may_borrow(&resolved_return_type) {
                    control_flow::check_return_ref_lifetime(&scope_stack, last, &mut errors);
                }
            }
            let tail_ok = match typed_body.last() {
                Some(TypedExpr::Let(..) | TypedExpr::LetTuple(..) | TypedExpr::LetStruct(..)) | None => false,
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
                    Some(TypedExpr::Let(..) | TypedExpr::LetTuple(..) | TypedExpr::LetStruct(..)) => "statement (`let`)".to_string(),
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
            is_track_caller: func.is_track_caller,
            is_std: func.module_path.first().map(|s| s.as_str()) == Some("std"),
        });
    }

    ensure_layout_types_monomorphized(&type_ctx);

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
                statics: typed_statics,
                structs: program.structs.clone(),
                enums: program.enums.clone(),
                impls: program.impls.clone(),
                functions: typed_functions,
                enum_layouts,
                extern_crate_names: program.extern_crate_names.clone(),
                extern_import_fns,
            },
            final_struct_map,
        ))
    } else {
        Err(errors)
    }
}

