//! sanal/macros.rs
//! Single source of truth for compiler-intrinsic macros and format string validation.

use crate::ast::{unescape_string_literal, Span, Type, TypedExpr};
use crate::sanal::compat::{is_type_compatible, mark_expr_moved_if_ident};
use crate::sanal::mono::type_satisfies_bound;
use crate::sanal::types::TypeCtx;
use crate::sanal::SemanticError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroKind {
    Assert,
    AssertEq,
    AssertNe,
    Panic,
    Format,
    Print { newline: bool },
    TypeOf,
    Thread,
    Vec,
    File,
    Line,
    Column,
    Stringify,
}

pub struct MacroDefinition {
    pub name: &'static str,
    pub kind: MacroKind,
    pub min_args: usize,
    pub max_args: Option<usize>,
    pub returns: Type,
}

pub static MACRO_REGISTRY: &[MacroDefinition] = &[
    MacroDefinition {
        name: "assert",
        kind: MacroKind::Assert,
        min_args: 1,
        max_args: None,
        returns: Type::Unit,
    },
    MacroDefinition {
        name: "assert_eq",
        kind: MacroKind::AssertEq,
        min_args: 2,
        max_args: None,
        returns: Type::Unit,
    },
    MacroDefinition {
        name: "assert_ne",
        kind: MacroKind::AssertNe,
        min_args: 2,
        max_args: None,
        returns: Type::Unit,
    },
    MacroDefinition {
        name: "panic",
        kind: MacroKind::Panic,
        min_args: 0,
        max_args: None,
        returns: Type::Unit,
    },
    MacroDefinition {
        name: "format",
        kind: MacroKind::Format,
        min_args: 1,
        max_args: None,
        returns: Type::Str,
    },
    MacroDefinition {
        name: "log",
        kind: MacroKind::Print { newline: true },
        min_args: 1,
        max_args: None,
        returns: Type::Unit,
    },
    MacroDefinition {
        name: "println",
        kind: MacroKind::Print { newline: true },
        min_args: 0,
        max_args: None,
        returns: Type::Unit,
    },
    MacroDefinition {
        name: "print",
        kind: MacroKind::Print { newline: false },
        min_args: 1,
        max_args: None,
        returns: Type::Unit,
    },
    MacroDefinition {
        name: "typeof",
        kind: MacroKind::TypeOf,
        min_args: 1,
        max_args: Some(1),
        returns: Type::Str,
    },
    MacroDefinition {
        name: "file",
        kind: MacroKind::File,
        min_args: 0,
        max_args: Some(0),
        returns: Type::Str,
    },
    MacroDefinition {
        name: "line",
        kind: MacroKind::Line,
        min_args: 0,
        max_args: Some(0),
        returns: Type::Int,
    },
    MacroDefinition {
        name: "column",
        kind: MacroKind::Column,
        min_args: 0,
        max_args: Some(0),
        returns: Type::Int,
    },
    MacroDefinition {
        name: "stringify",
        kind: MacroKind::Stringify,
        min_args: 1,
        max_args: Some(1),
        returns: Type::Str,
    },
    MacroDefinition {
        name: "thread",
        kind: MacroKind::Thread,
        min_args: 2,
        max_args: Some(2),
        returns: Type::Int,
    },
    MacroDefinition {
        name: "spawn",
        kind: MacroKind::Thread,
        min_args: 2,
        max_args: Some(2),
        returns: Type::Int,
    },
    MacroDefinition {
        name: "vec",
        kind: MacroKind::Vec,
        min_args: 0,
        max_args: None,
        returns: Type::Unit, // Refined dynamically per element type
    },
];

pub fn lookup_macro(name: &str) -> Option<&'static MacroDefinition> {
    let clean = name.trim_end_matches('!');
    MACRO_REGISTRY.iter().find(|m| m.name == clean)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormatChunk {
    Literal(String),
    Hole(usize),
}

/// Parses an unescaped or raw string literal into `FormatChunk`s.
pub fn parse_format_string(raw_or_unescaped: &str, is_raw: bool, span: &Span) -> Result<Vec<FormatChunk>, SemanticError> {
    let fmt = if is_raw {
        unescape_string_literal(raw_or_unescaped)
    } else {
        raw_or_unescaped.to_string()
    };

    let mut chunks = Vec::new();
    let mut current_lit = String::new();
    let mut hole_idx = 0usize;
    let chars: Vec<char> = fmt.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        match chars[i] {
            '{' => {
                if i + 1 < chars.len() && chars[i + 1] == '{' {
                    current_lit.push('{');
                    i += 2;
                } else if i + 1 < chars.len() && chars[i + 1] == '}' {
                    if !current_lit.is_empty() {
                        chunks.push(FormatChunk::Literal(std::mem::take(&mut current_lit)));
                    }
                    chunks.push(FormatChunk::Hole(hole_idx));
                    hole_idx += 1;
                    i += 2;
                } else if i + 3 < chars.len()
                    && chars[i + 1] == ':'
                    && chars[i + 2] == '?'
                    && chars[i + 3] == '}'
                {
                    return Err(SemanticError {
                        code: "E0277",
                        message: "The trait `Debug` is not yet supported in format strings; use `{}` (`Display`) instead".to_string(),
                        label: "Debug format specifier `{:?}` is unsupported".to_string(),
                        secondary_label: None,
                        help: Some("Replace `{:?}` with `{}` and ensure the type implements `Display`".to_string()),
                        span: span.clone(),
                    });
                } else {
                    return Err(SemanticError {
                        code: "E0001",
                        message: "Invalid or unmatched `{` in format string".to_string(),
                        label: "Invalid format placeholder".to_string(),
                        secondary_label: None,
                        help: Some("Use `{}` for placeholders or `{{` for a literal `{`".to_string()),
                        span: span.clone(),
                    });
                }
            }
            '}' => {
                if i + 1 < chars.len() && chars[i + 1] == '}' {
                    current_lit.push('}');
                    i += 2;
                } else {
                    return Err(SemanticError {
                        code: "E0001",
                        message: "Unmatched `}` in format string".to_string(),
                        label: "Unmatched closing brace".to_string(),
                        secondary_label: None,
                        help: Some("Use `}}` for a literal `}`".to_string()),
                        span: span.clone(),
                    });
                }
            }
            ch => {
                current_lit.push(ch);
                i += 1;
            }
        }
    }

    if !current_lit.is_empty() {
        chunks.push(FormatChunk::Literal(current_lit));
    }

    Ok(chunks)
}

/// Checks if `ty` can be formatted with `{}` (`Display` or built-in primitive).
pub fn is_displayable_type(ty: Type, type_ctx: &TypeCtx<'_>) -> bool {
    let mut infer = type_ctx.infer.borrow_mut();
    let resolved = infer.resolve(ty);
    drop(infer);

    let inner = match resolved {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };

    if inner.is_numeric() {
        return true;
    }

    match inner {
        Type::Error
        | Type::Bool
        | Type::Str
        | Type::String
        | Type::Infer(_) => true,
        Type::Obj("String")
        | Type::Obj("std_string_String")
        | Type::Obj("f32")
        | Type::Obj("F32")
        | Type::Obj("f64")
        | Type::Obj("Float")
        | Type::Obj("F64") => true,
        Type::Obj(tn) | Type::Enum(tn) => {
            let fn_map = type_ctx.fn_map.borrow();
            type_satisfies_bound(
                inner,
                "Display",
                type_ctx.trait_methods,
                type_ctx.trait_impls,
                &fn_map,
            ) || fn_map.contains_key(&format!("{tn}_fmt"))
                || fn_map.contains_key(&format!("{tn}_to_string"))
        }
        Type::Tuple(elems) => elems.iter().all(|e| is_displayable_type(*e, type_ctx)),
        _ => false,
    }
}

fn validate_format_args(
    args: &[TypedExpr],
    type_ctx: &TypeCtx<'_>,
    errors: &mut Vec<SemanticError>,
) {
    let Some(first) = args.first() else {
        return;
    };
    let TypedExpr::String(raw_fmt, fmt_span) = first else {
        errors.push(SemanticError {
            code: "E0308",
            message: "format argument must be a string literal".to_string(),
            label: "Expected a string literal here".to_string(),
            secondary_label: None,
            help: Some("Use a string literal such as `\"value: {}\"` as the format string".to_string()),
            span: first.span(),
        });
        return;
    };

    let chunks = match parse_format_string(raw_fmt, true, fmt_span) {
        Ok(c) => c,
        Err(err) => {
            errors.push(err);
            return;
        }
    };

    let hole_count = chunks
        .iter()
        .filter(|c| matches!(c, FormatChunk::Hole(_)))
        .count();
    let supplied_count = args.len() - 1;

    if hole_count != supplied_count {
        errors.push(SemanticError {
            code: "E0061",
            message: format!(
                "Invalid format string: expected {hole_count} positional argument(s), found {supplied_count}"
            ),
            label: format!("Expected {hole_count} argument(s), found {supplied_count}"),
            secondary_label: None,
            help: None,
            span: fmt_span.clone(),
        });
    }

    for arg in &args[1..] {
        let arg_ty = arg.ty();
        if !is_displayable_type(arg_ty, type_ctx) {
            errors.push(SemanticError {
                code: "E0277",
                message: format!("The trait `Display` is not implemented for `{arg_ty:?}`"),
                label: format!("`{arg_ty:?}` cannot be formatted with `{{}}`"),
                secondary_label: None,
                help: Some("Implement `Display` for this type or convert it to a string".to_string()),
                span: arg.span(),
            });
        }
    }
}

pub fn validate_and_finalize_macro(
    scopes: &mut crate::sanal::ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'_>,
    raw_name: &str,
    typed_args: Vec<TypedExpr>,
    span: &Span,
) -> TypedExpr {
    let Some(def) = lookup_macro(raw_name) else {
        errors.push(SemanticError {
            code: "E0425",
            message: format!("Unknown intrinsic macro `{raw_name}`"),
            label: "Undefined macro".to_string(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
        return TypedExpr::MacroCall(raw_name.to_string(), typed_args, Type::Unit, span.clone());
    };

    // Arity validation
    if typed_args.len() < def.min_args {
        errors.push(SemanticError {
            code: "E0061",
            message: format!(
                "`{}!` expects at least {} argument(s), found {}",
                def.name,
                def.min_args,
                typed_args.len()
            ),
            label: "Too few arguments".to_string(),
            secondary_label: None,
            help: None,
            span: span.clone(),
        });
    } else if let Some(max) = def.max_args {
        if typed_args.len() > max {
            errors.push(SemanticError {
                code: "E0061",
                message: format!(
                    "`{}!` expects at most {max} argument(s), found {}",
                    def.name,
                    typed_args.len()
                ),
                label: "Too many arguments".to_string(),
                secondary_label: None,
                help: None,
                span: span.clone(),
            });
        }
    }

    match def.kind {
        MacroKind::Vec => {
            if let Some(first) = typed_args.first() {
                let elem_ty = first.ty();
                for (i, arg) in typed_args.iter().enumerate().skip(1) {
                    let unify_res = type_ctx.infer.borrow_mut().unify(elem_ty, arg.ty());
                    if unify_res.is_err() && !is_type_compatible(&elem_ty, &arg.ty()) {
                        let resolved_expected = type_ctx.infer.borrow_mut().resolve(elem_ty);
                        let resolved_found = type_ctx.infer.borrow_mut().resolve(arg.ty());
                        errors.push(SemanticError {
                            code: "E0308",
                            message: format!(
                                "`vec!` elements must all have the same type. Expected `{:?}`, element {} has type `{:?}`",
                                resolved_expected,
                                i + 1,
                                resolved_found
                            ),
                            label: format!("Expected `{:?}`", resolved_expected),
                            secondary_label: None,
                            help: Some("Vectors are homogeneous and cannot hold mixed types".into()),
                            span: arg.span(),
                        });
                    }
                }
            }
            for arg in &typed_args {
                mark_expr_moved_if_ident(scopes, errors, arg);
            }
        }
        MacroKind::Thread => {
            for arg in &typed_args {
                mark_expr_moved_if_ident(scopes, errors, arg);
            }
        }
        MacroKind::Assert => {
            if let Some(cond) = typed_args.first() {
                if !is_type_compatible(&Type::Bool, &cond.ty()) {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "`assert!` condition must be `bool`, found `{:?}`",
                            cond.ty()
                        ),
                        label: "Expected `bool`".to_string(),
                        secondary_label: None,
                        help: None,
                        span: cond.span(),
                    });
                }
            }
            if typed_args.len() > 1 {
                validate_format_args(&typed_args[1..], type_ctx, errors);
            }
        }
        MacroKind::AssertEq | MacroKind::AssertNe => {
            if typed_args.len() >= 2 {
                let is_str = |t: &Type| {
                    matches!(
                        t,
                        Type::Str
                            | Type::String
                            | Type::Obj("String")
                            | Type::Obj("std_string_String")
                    )
                };
                let t0 = typed_args[0].ty();
                let t1 = typed_args[1].ty();
                if !(is_str(&t0) && is_str(&t1))
                    && !is_type_compatible(&t0, &t1)
                    && !is_type_compatible(&t1, &t0)
                {
                    errors.push(SemanticError {
                        code: "E0308",
                        message: format!(
                            "`{}!` arguments have incompatible types: `{:?}` and `{:?}`",
                            def.name, t0, t1
                        ),
                        label: format!("Mismatched types in `{}!`", def.name),
                        secondary_label: None,
                        help: None,
                        span: typed_args[1].span(),
                    });
                }
            }
            if typed_args.len() > 2 {
                validate_format_args(&typed_args[2..], type_ctx, errors);
            }
        }
        MacroKind::Format | MacroKind::Print { .. } | MacroKind::Panic => {
            if !typed_args.is_empty() {
                validate_format_args(&typed_args, type_ctx, errors);
            }
        }
        MacroKind::TypeOf
        | MacroKind::File
        | MacroKind::Line
        | MacroKind::Column
        | MacroKind::Stringify => {}
    }

    let ret_ty = match def.kind {
        MacroKind::Vec => {
            let expected_elem = type_ctx.current_expected_type.and_then(|exp| {
                let resolved = type_ctx.infer.borrow_mut().probe(exp);
                match resolved {
                    Type::Vec(elem) | Type::Slice(elem) | Type::Array(elem, _) => Some(*elem),
                    _ => None,
                }
            });
            let elem_ty = if let Some(first) = typed_args.first() {
                let resolved_first = type_ctx.infer.borrow_mut().resolve(first.ty());
                if let Some(exp_elem) = expected_elem {
                    if is_type_compatible(&exp_elem, &resolved_first) {
                        exp_elem
                    } else {
                        resolved_first
                    }
                } else {
                    resolved_first
                }
            } else if let Some(exp_elem) = expected_elem {
                exp_elem
            } else {
                type_ctx
                    .infer
                    .borrow_mut()
                    .fresh(span.clone(), "element type of `vec!`")
            };
            Type::Vec(crate::ast::intern_type(elem_ty))
        }
        _ => def.returns,
    };

    TypedExpr::MacroCall(raw_name.to_string(), typed_args, ret_ty, span.clone())
}
