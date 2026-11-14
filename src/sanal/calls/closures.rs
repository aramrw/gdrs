//! sanal/calls/closures.rs
//! Closure capture analysis (RFC 2229 disjoint field captures, `move` closures),
//! `Fn`/`FnMut`/`FnOnce` classification, and unboxed `__Closure_N` struct lowering.

use std::{
    collections::HashSet,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{
    ast::{
        intern_str, intern_tuple, intern_type, AssignOp, Expr, FuncDecl, Param, Span, Type,
        TypedExpr, Visibility,
    },
    sanal::{
        compat::{check_not_borrowed_on_move, extract_root_var, mark_expr_moved_if_ident},
        objects::construction::lookup_struct_layout_for_type,
        types::{type_check_expr, TypeCtx},
        ScopeStack, SemanticError, StructLayout,
    },
};

static CLOSURE_ENV_COUNTER: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum CaptureNeed {
    Read = 0,
    Mutate = 1,
    Consume = 2,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaptureMode {
    ByRef,
    ByMutRef,
    ByValue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

#[derive(Debug, Clone)]
struct RawCaptureUse {
    root: String,
    fields: Vec<String>,
    need: CaptureNeed,
    span: Span,
}

#[derive(Debug, Clone)]
struct FinalCapture {
    root: String,
    fields: Vec<String>,
    mode: CaptureMode,
    consumes_in_body: bool,
    proj_ty: Type,
    field_ty: Type,
    cap_field_name: String,
    unpacked_var: Option<String>,
    span: Span,
}

fn parse_closure_params<'a>(
    raw_params: &[String],
    fallback_param_tys: &[Type],
    type_ctx: &TypeCtx<'a>,
    span: &Span,
) -> Vec<(String, Type)> {
    raw_params
        .iter()
        .enumerate()
        .map(|(i, raw)| {
            if let Some((n, t_str)) = raw.split_once(':') {
                let parsed = parse_type_annotation_str(t_str.trim(), type_ctx);
                (n.trim().to_string(), parsed)
            } else {
                let ty = fallback_param_tys.get(i).copied().unwrap_or_else(|| {
                    type_ctx
                        .infer
                        .borrow_mut()
                        .fresh(span.clone(), format!("closure parameter `{raw}`"))
                });
                (raw.clone(), ty)
            }
        })
        .collect()
}

fn parse_type_annotation_str(s: &str, type_ctx: &TypeCtx<'_>) -> Type {
    let clean = s.trim();
    match clean {
        "i64" => Type::Int,
        "i32" => Type::I32,
        "i16" => Type::I16,
        "i8" => Type::I8,
        "u64" => Type::U64,
        "u32" => Type::U32,
        "u16" => Type::U16,
        "u8" => Type::U8,
        "f64" => Type::Float,
        "f32" => Type::F32,
        "bool" => Type::Bool,
        "str" => Type::Str,
        "String" => Type::String,
        "()" => Type::Unit,
        _ => {
            if let Some(inner) = clean.strip_prefix("&mut ") {
                return Type::MutRef(intern_type(parse_type_annotation_str(inner, type_ctx)));
            }
            if let Some(inner) = clean.strip_prefix('&') {
                return Type::Ref(intern_type(parse_type_annotation_str(inner, type_ctx)));
            }
            if let Some(inner) = clean.strip_prefix('*') {
                return Type::Ptr(intern_type(parse_type_annotation_str(inner, type_ctx)));
            }
            let norm = clean.replace("::", "_");
            type_ctx.resolve_type_annotation(Type::Obj(intern_str(&norm)))
        }
    }
}

fn is_local_name(locals: &[HashSet<String>], name: &str) -> bool {
    locals.iter().rev().any(|s| s.contains(name))
}

fn extract_raw_projection(expr: &Expr) -> Option<(String, Vec<String>)> {
    match expr {
        Expr::Ident(name, _) => Some((name.clone(), Vec::new())),
        Expr::FieldAccess(inner, field, _) => {
            let (root, mut fields) = extract_raw_projection(inner)?;
            fields.push(field.clone());
            Some((root, fields))
        }
        Expr::Deref(inner, _) => extract_raw_projection(inner),
        _ => None,
    }
}

fn bind_tuple_pattern_locals(pat: &crate::ast::TuplePattern, scope: &mut HashSet<String>) {
    match pat {
        crate::ast::TuplePattern::Ident { name, .. } => {
            if name != "_" {
                scope.insert(name.clone());
            }
        }
        crate::ast::TuplePattern::Tuple(subs, _) => {
            for s in subs {
                bind_tuple_pattern_locals(s, scope);
            }
        }
    }
}

fn resolve_projection_type(root_ty: Type, fields: &[String], type_ctx: &TypeCtx<'_>) -> Type {
    let mut cur = type_ctx.infer.borrow_mut().resolve(root_ty);
    for field in fields {
        while let Type::Ref(inner)
        | Type::MutRef(inner)
        | Type::Box(inner)
        | Type::Rc(inner)
        | Type::Arc(inner) = cur
        {
            cur = *inner;
        }
        if let Type::Tuple(elems) = cur {
            if let Ok(idx) = field.parse::<usize>() {
                if let Some(&fty) = elems.get(idx) {
                    cur = fty;
                    continue;
                }
            }
        }
        if let Some((_, layout)) = lookup_struct_layout_for_type(type_ctx, cur) {
            if let Some((_, fty)) = layout.field_offsets.get(field) {
                cur = type_ctx.infer.borrow_mut().resolve(*fty);
                continue;
            }
        }
        return cur;
    }
    cur
}

fn collect_raw_capture_uses(
    expr: &Expr,
    ctx_need: CaptureNeed,
    locals: &mut Vec<HashSet<String>>,
    scopes: &ScopeStack,
    type_ctx: &TypeCtx<'_>,
    out: &mut Vec<RawCaptureUse>,
) {
    match expr {
        Expr::Ident(name, span) => {
            if !is_local_name(locals, name) && scopes.lookup(name).is_some() {
                out.push(RawCaptureUse {
                    root: name.clone(),
                    fields: Vec::new(),
                    need: ctx_need,
                    span: span.clone(),
                });
            }
        }
        Expr::FieldAccess(inner, _, span) => {
            if let Some((root, fields)) = extract_raw_projection(expr) {
                if !is_local_name(locals, &root) && scopes.lookup(&root).is_some() {
                    out.push(RawCaptureUse {
                        root,
                        fields,
                        need: ctx_need,
                        span: span.clone(),
                    });
                    return;
                }
            }
            collect_raw_capture_uses(inner, CaptureNeed::Read, locals, scopes, type_ctx, out);
        }
        Expr::Let(name, _, _, val, _) => {
            collect_raw_capture_uses(val, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            if let Some(cur) = locals.last_mut() {
                cur.insert(name.clone());
            }
        }
        Expr::LetTuple(pat, _, val, _) => {
            collect_raw_capture_uses(val, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            if let Some(cur) = locals.last_mut() {
                bind_tuple_pattern_locals(pat, cur);
            }
        }
        Expr::Block(stmts, _) | Expr::Unsafe(stmts, _) => {
            locals.push(HashSet::new());
            for (i, s) in stmts.iter().enumerate() {
                let n = if i + 1 == stmts.len() {
                    ctx_need
                } else {
                    CaptureNeed::Consume
                };
                collect_raw_capture_uses(s, n, locals, scopes, type_ctx, out);
            }
            locals.pop();
        }
        Expr::While(cond, body, _) | Expr::If(cond, body, _) => {
            collect_raw_capture_uses(cond, CaptureNeed::Read, locals, scopes, type_ctx, out);
            locals.push(HashSet::new());
            collect_raw_capture_uses(body, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            locals.pop();
        }
        Expr::IfElse(cond, then_b, else_b, _) => {
            collect_raw_capture_uses(cond, CaptureNeed::Read, locals, scopes, type_ctx, out);
            locals.push(HashSet::new());
            collect_raw_capture_uses(then_b, ctx_need, locals, scopes, type_ctx, out);
            locals.pop();
            locals.push(HashSet::new());
            collect_raw_capture_uses(else_b, ctx_need, locals, scopes, type_ctx, out);
            locals.pop();
        }
        Expr::Match(target, arms, _) => {
            collect_raw_capture_uses(target, CaptureNeed::Read, locals, scopes, type_ctx, out);
            for arm in arms {
                locals.push(arm.bindings.iter().cloned().collect());
                for (i, s) in arm.body.iter().enumerate() {
                    let n = if i + 1 == arm.body.len() {
                        ctx_need
                    } else {
                        CaptureNeed::Consume
                    };
                    collect_raw_capture_uses(s, n, locals, scopes, type_ctx, out);
                }
                locals.pop();
            }
        }
        Expr::Assign(name, rhs, span) => {
            if !is_local_name(locals, name) && scopes.lookup(name).is_some() {
                out.push(RawCaptureUse {
                    root: name.clone(),
                    fields: Vec::new(),
                    need: CaptureNeed::Mutate,
                    span: span.clone(),
                });
            }
            collect_raw_capture_uses(rhs, CaptureNeed::Consume, locals, scopes, type_ctx, out);
        }
        Expr::CompoundAssign(_, lhs, rhs, span) => {
            if let Some((root, fields)) = extract_raw_projection(lhs) {
                if !is_local_name(locals, &root) && scopes.lookup(&root).is_some() {
                    out.push(RawCaptureUse {
                        root,
                        fields,
                        need: CaptureNeed::Mutate,
                        span: span.clone(),
                    });
                } else {
                    collect_raw_capture_uses(lhs, CaptureNeed::Mutate, locals, scopes, type_ctx, out);
                }
            } else {
                collect_raw_capture_uses(lhs, CaptureNeed::Mutate, locals, scopes, type_ctx, out);
            }
            collect_raw_capture_uses(rhs, CaptureNeed::Consume, locals, scopes, type_ctx, out);
        }
        Expr::FieldAssign(target, field, rhs, span) => {
            if let Some((root, mut fields)) = extract_raw_projection(target) {
                fields.push(field.clone());
                if !is_local_name(locals, &root) && scopes.lookup(&root).is_some() {
                    out.push(RawCaptureUse {
                        root,
                        fields,
                        need: CaptureNeed::Mutate,
                        span: span.clone(),
                    });
                } else {
                    collect_raw_capture_uses(target, CaptureNeed::Mutate, locals, scopes, type_ctx, out);
                }
            } else {
                collect_raw_capture_uses(target, CaptureNeed::Mutate, locals, scopes, type_ctx, out);
            }
            collect_raw_capture_uses(rhs, CaptureNeed::Consume, locals, scopes, type_ctx, out);
        }
        Expr::IndexAssign(target, idx, rhs, _) => {
            collect_raw_capture_uses(target, CaptureNeed::Mutate, locals, scopes, type_ctx, out);
            collect_raw_capture_uses(idx, CaptureNeed::Read, locals, scopes, type_ctx, out);
            collect_raw_capture_uses(rhs, CaptureNeed::Consume, locals, scopes, type_ctx, out);
        }
        Expr::Ref(inner, is_mut, _) => {
            let need = if *is_mut {
                CaptureNeed::Mutate
            } else {
                CaptureNeed::Read
            };
            collect_raw_capture_uses(inner, need, locals, scopes, type_ctx, out);
        }
        Expr::Deref(inner, _) => {
            collect_raw_capture_uses(inner, CaptureNeed::Read, locals, scopes, type_ctx, out);
        }
        Expr::DerefAssign(ptr, val, _) => {
            collect_raw_capture_uses(ptr, CaptureNeed::Mutate, locals, scopes, type_ctx, out);
            collect_raw_capture_uses(val, CaptureNeed::Consume, locals, scopes, type_ctx, out);
        }
        Expr::Call(raw_name, args, span) => {
            let is_method = raw_name.starts_with('.');
            let clean_name = raw_name.strip_prefix('.').unwrap_or(raw_name);
            if !is_method && !is_local_name(locals, clean_name) {
                if let Some(var_info) = scopes.lookup(clean_name) {
                    let var_ty = type_ctx.infer.borrow_mut().resolve(var_info.ty);
                    let need = closure_call_need(var_ty, type_ctx);
                    out.push(RawCaptureUse {
                        root: clean_name.to_string(),
                        fields: Vec::new(),
                        need,
                        span: span.clone(),
                    });
                }
            }
            if is_method && !args.is_empty() {
                let recv_need = method_receiver_need(&args[0], clean_name, scopes, type_ctx);
                collect_raw_capture_uses(&args[0], recv_need, locals, scopes, type_ctx, out);
                for a in &args[1..] {
                    collect_raw_capture_uses(a, CaptureNeed::Consume, locals, scopes, type_ctx, out);
                }
            } else {
                let fn_params = type_ctx.get_fn(clean_name).map(|f| f.params);
                for (i, a) in args.iter().enumerate() {
                    let arg_need = fn_params
                        .as_ref()
                        .and_then(|ps| ps.get(i))
                        .map(|p| match p.ty {
                            Type::Ref(_) => CaptureNeed::Read,
                            Type::MutRef(_) => CaptureNeed::Mutate,
                            _ => CaptureNeed::Consume,
                        })
                        .unwrap_or(CaptureNeed::Consume);
                    collect_raw_capture_uses(a, arg_need, locals, scopes, type_ctx, out);
                }
            }
        }
        Expr::MacroCall(_, args, _) => {
            for a in args {
                collect_raw_capture_uses(a, CaptureNeed::Read, locals, scopes, type_ctx, out);
            }
        }
        Expr::Closure(_, inner_params, inner_body, _) => {
            let mut inner_scope = HashSet::new();
            for p in inner_params {
                let p_name = p.split_once(':').map(|(n, _)| n.trim()).unwrap_or(p.as_str());
                inner_scope.insert(p_name.to_string());
            }
            locals.push(inner_scope);
            collect_raw_capture_uses(inner_body, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            locals.pop();
        }
        Expr::Add(l, r, _)
        | Expr::Sub(l, r, _)
        | Expr::Mul(l, r, _)
        | Expr::Div(l, r, _)
        | Expr::Mod(l, r, _)
        | Expr::GreaterThan(l, r, _)
        | Expr::LessThan(l, r, _)
        | Expr::GreaterEqual(l, r, _)
        | Expr::LessEqual(l, r, _)
        | Expr::Equal(l, r, _)
        | Expr::NotEqual(l, r, _)
        | Expr::And(l, r, _)
        | Expr::Or(l, r, _)
        | Expr::Pipe(l, r, _)
        | Expr::Ampersand(l, r, _)
        | Expr::Caret(l, r, _)
        | Expr::Shl(l, r, _)
        | Expr::Shr(l, r, _)
        | Expr::IndexAccess(l, r, _)
        | Expr::Range(l, r, _) => {
            collect_raw_capture_uses(l, CaptureNeed::Read, locals, scopes, type_ctx, out);
            collect_raw_capture_uses(r, CaptureNeed::Read, locals, scopes, type_ctx, out);
        }
        Expr::Neg(inner, _)
        | Expr::Not(inner, _)
        | Expr::Try(inner, _)
        | Expr::Cast(inner, _, _) => {
            collect_raw_capture_uses(inner, ctx_need, locals, scopes, type_ctx, out);
        }
        Expr::Return(opt_e, _) => {
            if let Some(e) = opt_e {
                collect_raw_capture_uses(e, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            }
        }
        Expr::ArrayInit(elems, _) | Expr::TupleInit(elems, _) => {
            for e in elems {
                collect_raw_capture_uses(e, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            }
        }
        Expr::ObjInit(_, _, _) | Expr::EnumConstruct(_, _, _, _) => {
            unreachable_fields_walk(expr, locals, scopes, type_ctx, out);
        }
        Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::String(..) | Expr::Break(..) | Expr::Continue(..) => {}
    }
}

fn unreachable_fields_walk(
    expr: &Expr,
    locals: &mut Vec<HashSet<String>>,
    scopes: &ScopeStack,
    type_ctx: &TypeCtx<'_>,
    out: &mut Vec<RawCaptureUse>,
) {
    match expr {
        Expr::ObjInit(_, fields, _) => {
            for (_, v) in fields {
                collect_raw_capture_uses(v, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            }
        }
        Expr::EnumConstruct(_, _, args, _) => {
            for a in args {
                collect_raw_capture_uses(a, CaptureNeed::Consume, locals, scopes, type_ctx, out);
            }
        }
        _ => {}
    }
}

fn closure_call_need(var_ty: Type, type_ctx: &TypeCtx<'_>) -> CaptureNeed {
    if let Type::Obj(name) = var_ty {
        if name.starts_with("__Closure_") {
            if type_ctx.get_fn(&format!("{name}_call_ref")).is_some() {
                return CaptureNeed::Read;
            }
            if type_ctx.get_fn(&format!("{name}_call_mut")).is_some() {
                return CaptureNeed::Mutate;
            }
            return CaptureNeed::Consume;
        }
    }
    CaptureNeed::Read
}

fn method_receiver_need(
    recv: &Expr,
    method: &str,
    scopes: &ScopeStack,
    type_ctx: &TypeCtx<'_>,
) -> CaptureNeed {
    if let Some((root, fields)) = extract_raw_projection(recv) {
        if let Some(info) = scopes.lookup(&root) {
            let proj_ty = resolve_projection_type(info.ty, &fields, type_ctx);
            let mut base_ty = type_ctx.infer.borrow_mut().resolve(proj_ty);
            while let Type::Ref(inner) | Type::MutRef(inner) | Type::Box(inner) = base_ty {
                base_ty = *inner;
            }
            let struct_name = match base_ty {
                Type::Obj(s) => Some(s.to_string()),
                Type::Vec(_) => Some("std_vec_Vec".to_string()),
                Type::String => Some("std_string_String".to_string()),
                _ => None,
            };
            if let Some(sname) = struct_name {
                let fn_decl = type_ctx.get_fn(&format!("{sname}_{method}")).or_else(|| {
                    let base = crate::sanal::mono::lookup_mangled(&sname)
                        .map(|(b, _)| b)
                        .unwrap_or(sname);
                    let mono = type_ctx.mono.borrow();
                    crate::sanal::mono::find_impl_method(&mono, &base, method)
                });
                if let Some(decl) = fn_decl {
                    if let Some(p0) = decl.params.first() {
                        return match p0.ty {
                            Type::Ref(_) => CaptureNeed::Read,
                            Type::MutRef(_) => CaptureNeed::Mutate,
                            Type::Unit if p0.name == "self" => {
                                if matches!(method, "len" | "is_empty" | "capacity" | "as_str" | "as_ptr" | "iter" | "into_iter" | "clone" | "fmt") {
                                    CaptureNeed::Read
                                } else {
                                    CaptureNeed::Consume
                                }
                            }
                            _ => CaptureNeed::Consume,
                        };
                    }
                }
            }
        }
    }
    if matches!(
        method,
        "len" | "is_empty" | "capacity" | "as_str" | "as_ptr" | "iter" | "clone" | "fmt"
    ) {
        CaptureNeed::Read
    } else if matches!(method, "push" | "pop" | "clear" | "next" | "remove" | "insert" | "sort" | "as_mut_ptr") {
        CaptureNeed::Mutate
    } else {
        CaptureNeed::Consume
    }
}

fn is_prefix(prefix: &[String], full: &[String]) -> bool {
    prefix.len() <= full.len() && full[..prefix.len()] == *prefix
}

fn coalesce_captures(
    raw_uses: Vec<RawCaptureUse>,
    is_move: bool,
    scopes: &ScopeStack,
    type_ctx: &TypeCtx<'_>,
) -> Vec<FinalCapture> {
    let mut coalesced: Vec<(RawCaptureUse, bool)> = Vec::new();
    for mut u in raw_uses {
        let Some(info) = scopes.lookup(&u.root) else {
            continue;
        };
        let proj_ty = resolve_projection_type(info.ty, &u.fields, type_ctx);
        // Never partially move a non-Copy field out of a parent struct; coalesce to whole root.
        let moving_non_copy_field = !u.fields.is_empty()
            && !proj_ty.is_copy()
            && (is_move || u.need == CaptureNeed::Consume);
        if moving_non_copy_field {
            u.fields.clear();
        }
        let mut u_mut = u.need == CaptureNeed::Mutate;

        if let Some((existing, existing_mut)) = coalesced
            .iter_mut()
            .find(|(e, _)| e.root == u.root && is_prefix(&e.fields, &u.fields))
        {
            if u.need > existing.need {
                existing.need = u.need;
            }
            *existing_mut |= u_mut;
            continue;
        }
        let mut max_need = u.need;
        coalesced.retain(|(e, e_mut)| {
            if e.root == u.root && is_prefix(&u.fields, &e.fields) {
                if e.need > max_need {
                    max_need = e.need;
                }
                u_mut |= *e_mut;
                false
            } else {
                true
            }
        });
        u.need = max_need;
        coalesced.push((u, u_mut));
    }

    coalesced
        .into_iter()
        .enumerate()
        .map(|(idx, (u, was_mutated))| {
            let root_ty = scopes.lookup(&u.root).map(|i| i.ty).unwrap_or(Type::Int);
            let proj_ty = resolve_projection_type(root_ty, &u.fields, type_ctx);
            let consumes_in_body = u.need == CaptureNeed::Consume && !proj_ty.is_copy();
            let mode = if is_move || consumes_in_body {
                CaptureMode::ByValue
            } else if was_mutated {
                CaptureMode::ByMutRef
            } else {
                CaptureMode::ByRef
            };
            let field_ty = match mode {
                CaptureMode::ByValue => proj_ty,
                CaptureMode::ByMutRef => match proj_ty {
                    Type::MutRef(inner) => Type::MutRef(inner),
                    other => Type::MutRef(intern_type(other)),
                },
                CaptureMode::ByRef => match proj_ty {
                    Type::Ref(inner) => Type::Ref(inner),
                    other => Type::Ref(intern_type(other)),
                },
            };
            FinalCapture {
                root: u.root,
                fields: u.fields,
                mode,
                consumes_in_body,
                proj_ty,
                field_ty,
                cap_field_name: format!("__cap_{idx}"),
                unpacked_var: None,
                span: u.span,
            }
        })
        .collect()
}

fn find_capture_for_projection<'a>(
    captures: &'a [FinalCapture],
    root: &str,
    fields: &[String],
) -> Option<(usize, &'a FinalCapture, Vec<String>)> {
    captures.iter().enumerate().find_map(|(i, c)| {
        if c.root == root && is_prefix(&c.fields, fields) {
            Some((i, c, fields[c.fields.len()..].to_vec()))
        } else {
            None
        }
    })
}

fn self_cap_expr(cap: &FinalCapture, span: &Span) -> Expr {
    if let Some(ref unpacked) = cap.unpacked_var {
        return Expr::Ident(unpacked.clone(), span.clone());
    }
    Expr::FieldAccess(
        Box::new(Expr::Ident("self".to_string(), span.clone())),
        cap.cap_field_name.clone(),
        span.clone(),
    )
}

fn cap_access_with_tail(
    cap: &FinalCapture,
    tail: &[String],
    need_deref_leaf: bool,
    span: &Span,
) -> Expr {
    let base = self_cap_expr(cap, span);
    if tail.is_empty() {
        if need_deref_leaf && matches!(cap.mode, CaptureMode::ByRef | CaptureMode::ByMutRef) && !matches!(cap.proj_ty, Type::Ref(_) | Type::MutRef(_)) {
            Expr::Deref(Box::new(base), span.clone())
        } else {
            base
        }
    } else {
        let mut cur = base;
        for f in tail {
            cur = Expr::FieldAccess(Box::new(cur), f.clone(), span.clone());
        }
        cur
    }
}

fn rewrite_closure_body(
    expr: &Expr,
    captures: &[FinalCapture],
    locals: &mut Vec<HashSet<String>>,
) -> Expr {
    match expr {
        Expr::Ident(name, span) => {
            if !is_local_name(locals, name) {
                if let Some((_, cap, _)) = find_capture_for_projection(captures, name, &[]) {
                    return cap_access_with_tail(cap, &[], true, span);
                }
            }
            expr.clone()
        }
        Expr::FieldAccess(inner, field, span) => {
            if let Some((root, fields)) = extract_raw_projection(expr) {
                if !is_local_name(locals, &root) {
                    if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                        return cap_access_with_tail(cap, &tail, true, span);
                    }
                }
            }
            Expr::FieldAccess(
                Box::new(rewrite_closure_body(inner, captures, locals)),
                field.clone(),
                span.clone(),
            )
        }
        Expr::Assign(name, rhs, span) => {
            let new_rhs = rewrite_closure_body(rhs, captures, locals);
            if !is_local_name(locals, name) {
                if let Some((_, cap, _)) = find_capture_for_projection(captures, name, &[]) {
                    let target = self_cap_expr(cap, span);
                    return match cap.mode {
                        CaptureMode::ByValue => {
                            if let Some(ref unpacked) = cap.unpacked_var {
                                Expr::Assign(unpacked.clone(), Box::new(new_rhs), span.clone())
                            } else {
                                Expr::FieldAssign(
                                    Box::new(Expr::Ident("self".to_string(), span.clone())),
                                    cap.cap_field_name.clone(),
                                    Box::new(new_rhs),
                                    span.clone(),
                                )
                            }
                        }
                        CaptureMode::ByMutRef | CaptureMode::ByRef => {
                            Expr::DerefAssign(Box::new(target), Box::new(new_rhs), span.clone())
                        }
                    };
                }
            }
            Expr::Assign(name.clone(), Box::new(new_rhs), span.clone())
        }
        Expr::CompoundAssign(op, lhs, rhs, span) => {
            let new_rhs = rewrite_closure_body(rhs, captures, locals);
            if let Some((root, fields)) = extract_raw_projection(lhs) {
                if !is_local_name(locals, &root) {
                    if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                        let rewritten_lhs = if tail.is_empty() && matches!(cap.mode, CaptureMode::ByMutRef) && !matches!(cap.proj_ty, Type::MutRef(_)) {
                            Expr::Deref(Box::new(self_cap_expr(cap, span)), span.clone())
                        } else {
                            cap_access_with_tail(cap, &tail, false, span)
                        };
                        return Expr::CompoundAssign(*op, Box::new(rewritten_lhs), Box::new(new_rhs), span.clone());
                    }
                }
            }
            Expr::CompoundAssign(
                *op,
                Box::new(rewrite_closure_body(lhs, captures, locals)),
                Box::new(new_rhs),
                span.clone(),
            )
        }
        Expr::FieldAssign(target, field, rhs, span) => {
            let new_rhs = rewrite_closure_body(rhs, captures, locals);
            if let Some((root, mut fields)) = extract_raw_projection(target) {
                fields.push(field.clone());
                if !is_local_name(locals, &root) {
                    if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                        if tail.is_empty() {
                            return match cap.mode {
                                CaptureMode::ByValue => {
                                    if let Some(ref unpacked) = cap.unpacked_var {
                                        Expr::Assign(unpacked.clone(), Box::new(new_rhs), span.clone())
                                    } else {
                                        Expr::FieldAssign(
                                            Box::new(Expr::Ident("self".to_string(), span.clone())),
                                            cap.cap_field_name.clone(),
                                            Box::new(new_rhs),
                                            span.clone(),
                                        )
                                    }
                                }
                                CaptureMode::ByMutRef | CaptureMode::ByRef => Expr::DerefAssign(
                                    Box::new(self_cap_expr(cap, span)),
                                    Box::new(new_rhs),
                                    span.clone(),
                                ),
                            };
                        } else {
                            let recv = cap_access_with_tail(cap, &tail[..tail.len() - 1], false, span);
                            return Expr::FieldAssign(
                                Box::new(recv),
                                tail.last().unwrap().clone(),
                                Box::new(new_rhs),
                                span.clone(),
                            );
                        }
                    }
                }
            }
            Expr::FieldAssign(
                Box::new(rewrite_closure_body(target, captures, locals)),
                field.clone(),
                Box::new(new_rhs),
                span.clone(),
            )
        }
        Expr::Ref(inner, is_mut, span) => {
            if let Some((root, fields)) = extract_raw_projection(inner) {
                if !is_local_name(locals, &root) {
                    if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                        if tail.is_empty() && matches!(cap.mode, CaptureMode::ByRef | CaptureMode::ByMutRef) && !matches!(cap.proj_ty, Type::Ref(_) | Type::MutRef(_)) {
                            return self_cap_expr(cap, span);
                        }
                        let base = cap_access_with_tail(cap, &tail, false, span);
                        return Expr::Ref(Box::new(base), *is_mut, span.clone());
                    }
                }
            }
            Expr::Ref(Box::new(rewrite_closure_body(inner, captures, locals)), *is_mut, span.clone())
        }
        Expr::Deref(inner, span) => {
            if let Some((root, fields)) = extract_raw_projection(inner) {
                if !is_local_name(locals, &root) {
                    if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                        let base = cap_access_with_tail(cap, &tail, true, span);
                        return Expr::Deref(Box::new(base), span.clone());
                    }
                }
            }
            Expr::Deref(Box::new(rewrite_closure_body(inner, captures, locals)), span.clone())
        }
        Expr::DerefAssign(ptr, rhs, span) => {
            let new_rhs = rewrite_closure_body(rhs, captures, locals);
            let new_ptr = if let Some((root, fields)) = extract_raw_projection(ptr) {
                if !is_local_name(locals, &root) {
                    if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                        cap_access_with_tail(cap, &tail, true, span)
                    } else {
                        rewrite_closure_body(ptr, captures, locals)
                    }
                } else {
                    rewrite_closure_body(ptr, captures, locals)
                }
            } else {
                rewrite_closure_body(ptr, captures, locals)
            };
            Expr::DerefAssign(Box::new(new_ptr), Box::new(new_rhs), span.clone())
        }
        Expr::Call(raw_name, args, span) => {
            let is_method = raw_name.starts_with('.');
            let mut new_args = Vec::with_capacity(args.len());
            for (i, a) in args.iter().enumerate() {
                if i == 0 && is_method {
                    if let Some((root, fields)) = extract_raw_projection(a) {
                        if !is_local_name(locals, &root) {
                            if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                                // Preserve `&T`/`&mut T` directly as method receiver to avoid E0507 on deref.
                                new_args.push(cap_access_with_tail(cap, &tail, false, &a.span()));
                                continue;
                            }
                        }
                    }
                }
                new_args.push(rewrite_closure_body(a, captures, locals));
            }
            if !is_method && !is_local_name(locals, raw_name) {
                if let Some((_, cap, _)) = find_capture_for_projection(captures, raw_name, &[]) {
                    let closure_target = self_cap_expr(cap, span);
                    let mut all_args = Vec::with_capacity(1 + new_args.len());
                    all_args.push(closure_target);
                    all_args.extend(new_args);
                    return Expr::Call("__call_fn_ptr".to_string(), all_args, span.clone());
                }
            }
            Expr::Call(raw_name.clone(), new_args, span.clone())
        }
        Expr::MacroCall(name, args, span) => {
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                if let Some((root, fields)) = extract_raw_projection(a) {
                    if !is_local_name(locals, &root) {
                        if let Some((_, cap, tail)) = find_capture_for_projection(captures, &root, &fields) {
                            new_args.push(cap_access_with_tail(cap, &tail, !cap.proj_ty.is_copy() == false, &a.span()));
                            continue;
                        }
                    }
                }
                new_args.push(rewrite_closure_body(a, captures, locals));
            }
            Expr::MacroCall(name.clone(), new_args, span.clone())
        }
        Expr::Let(name, opt_ty, is_mut, val, span) => {
            let nv = Box::new(rewrite_closure_body(val, captures, locals));
            if let Some(cur) = locals.last_mut() {
                cur.insert(name.clone());
            }
            Expr::Let(name.clone(), *opt_ty, *is_mut, nv, span.clone())
        }
        Expr::LetTuple(pat, opt_ty, val, span) => {
            let nv = Box::new(rewrite_closure_body(val, captures, locals));
            if let Some(cur) = locals.last_mut() {
                bind_tuple_pattern_locals(pat, cur);
            }
            Expr::LetTuple(pat.clone(), *opt_ty, nv, span.clone())
        }
        Expr::Block(stmts, span) => {
            locals.push(HashSet::new());
            let out: Vec<Expr> = stmts.iter().map(|s| rewrite_closure_body(s, captures, locals)).collect();
            locals.pop();
            Expr::Block(out, span.clone())
        }
        Expr::Unsafe(stmts, span) => {
            locals.push(HashSet::new());
            let out: Vec<Expr> = stmts.iter().map(|s| rewrite_closure_body(s, captures, locals)).collect();
            locals.pop();
            Expr::Unsafe(out, span.clone())
        }
        Expr::While(c, b, span) => {
            let nc = Box::new(rewrite_closure_body(c, captures, locals));
            locals.push(HashSet::new());
            let nb = Box::new(rewrite_closure_body(b, captures, locals));
            locals.pop();
            Expr::While(nc, nb, span.clone())
        }
        Expr::If(c, b, span) => {
            let nc = Box::new(rewrite_closure_body(c, captures, locals));
            locals.push(HashSet::new());
            let nb = Box::new(rewrite_closure_body(b, captures, locals));
            locals.pop();
            Expr::If(nc, nb, span.clone())
        }
        Expr::IfElse(c, t, e, span) => {
            let nc = Box::new(rewrite_closure_body(c, captures, locals));
            locals.push(HashSet::new());
            let nt = Box::new(rewrite_closure_body(t, captures, locals));
            locals.pop();
            locals.push(HashSet::new());
            let ne = Box::new(rewrite_closure_body(e, captures, locals));
            locals.pop();
            Expr::IfElse(nc, nt, ne, span.clone())
        }
        Expr::Match(target, arms, span) => {
            let nt = Box::new(rewrite_closure_body(target, captures, locals));
            let new_arms = arms
                .iter()
                .map(|arm| {
                    locals.push(arm.bindings.iter().cloned().collect());
                    let body = arm.body.iter().map(|s| rewrite_closure_body(s, captures, locals)).collect();
                    locals.pop();
                    crate::ast::MatchArm {
                        variant_name: arm.variant_name.clone(),
                        bindings: arm.bindings.clone(),
                        body,
                        span: arm.span.clone(),
                    }
                })
                .collect();
            Expr::Match(nt, new_arms, span.clone())
        }
        Expr::Closure(is_mv, inner_ps, inner_body, span) => {
            let mut s = HashSet::new();
            for p in inner_ps {
                s.insert(p.split_once(':').map(|(n, _)| n.trim()).unwrap_or(p.as_str()).to_string());
            }
            locals.push(s);
            let nb = Box::new(rewrite_closure_body(inner_body, captures, locals));
            locals.pop();
            Expr::Closure(*is_mv, inner_ps.clone(), nb, span.clone())
        }
        Expr::Add(l, r, s) => Expr::Add(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Sub(l, r, s) => Expr::Sub(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Mul(l, r, s) => Expr::Mul(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Div(l, r, s) => Expr::Div(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Mod(l, r, s) => Expr::Mod(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::GreaterThan(l, r, s) => Expr::GreaterThan(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::LessThan(l, r, s) => Expr::LessThan(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::GreaterEqual(l, r, s) => Expr::GreaterEqual(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::LessEqual(l, r, s) => Expr::LessEqual(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Equal(l, r, s) => Expr::Equal(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::NotEqual(l, r, s) => Expr::NotEqual(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::And(l, r, s) => Expr::And(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Or(l, r, s) => Expr::Or(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Pipe(l, r, s) => Expr::Pipe(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Ampersand(l, r, s) => Expr::Ampersand(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Caret(l, r, s) => Expr::Caret(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Shl(l, r, s) => Expr::Shl(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Shr(l, r, s) => Expr::Shr(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::IndexAccess(l, r, s) => Expr::IndexAccess(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::Range(l, r, s) => Expr::Range(Box::new(rewrite_closure_body(l, captures, locals)), Box::new(rewrite_closure_body(r, captures, locals)), s.clone()),
        Expr::IndexAssign(t, i, v, s) => Expr::IndexAssign(
            Box::new(rewrite_closure_body(t, captures, locals)),
            Box::new(rewrite_closure_body(i, captures, locals)),
            Box::new(rewrite_closure_body(v, captures, locals)),
            s.clone(),
        ),
        Expr::Neg(i, s) => Expr::Neg(Box::new(rewrite_closure_body(i, captures, locals)), s.clone()),
        Expr::Not(i, s) => Expr::Not(Box::new(rewrite_closure_body(i, captures, locals)), s.clone()),
        Expr::Try(i, s) => Expr::Try(Box::new(rewrite_closure_body(i, captures, locals)), s.clone()),
        Expr::Cast(i, ty, s) => Expr::Cast(Box::new(rewrite_closure_body(i, captures, locals)), *ty, s.clone()),
        Expr::Return(opt_e, s) => Expr::Return(opt_e.as_ref().map(|e| Box::new(rewrite_closure_body(e, captures, locals))), s.clone()),
        Expr::ArrayInit(elems, s) => Expr::ArrayInit(elems.iter().map(|e| rewrite_closure_body(e, captures, locals)).collect(), s.clone()),
        Expr::TupleInit(elems, s) => Expr::TupleInit(elems.iter().map(|e| rewrite_closure_body(e, captures, locals)).collect(), s.clone()),
        Expr::ObjInit(n, fs, s) => Expr::ObjInit(n.clone(), fs.iter().map(|(fnm, e)| (fnm.clone(), rewrite_closure_body(e, captures, locals))).collect(), s.clone()),
        Expr::EnumConstruct(en, vn, args, s) => Expr::EnumConstruct(en.clone(), vn.clone(), args.iter().map(|e| rewrite_closure_body(e, captures, locals)).collect(), s.clone()),
        _ => expr.clone(),
    }
}

fn build_projection_expr(root: &str, fields: &[String], span: &Span) -> Expr {
    let mut cur = Expr::Ident(root.to_string(), span.clone());
    for f in fields {
        cur = Expr::FieldAccess(Box::new(cur), f.clone(), span.clone());
    }
    cur
}

fn build_projection_typed_expr(
    root: &str,
    fields: &[String],
    root_ty: Type,
    type_ctx: &TypeCtx<'_>,
    span: &Span,
) -> TypedExpr {
    let mut cur_expr = TypedExpr::Ident(root.to_string(), root_ty, span.clone());
    let mut cur_ty = type_ctx.infer.borrow_mut().resolve(root_ty);
    for f in fields {
        cur_ty = resolve_projection_type(cur_ty, std::slice::from_ref(f), type_ctx);
        cur_expr = TypedExpr::FieldAccess(Box::new(cur_expr), f.clone(), cur_ty, span.clone());
    }
    cur_expr
}

/// Type-checks a closure expression (capturing or non-capturing) using an expected parameter type list.
///
/// Zero-capture closures emit `TypedExpr::Closure` (`Type::FnPtr`), remaining C-ABI coercible.
/// Capturing closures synthesize an unboxed `obj __Closure_N` struct + call methods (`Fn`/`FnMut`/`FnOnce`).
pub fn build_closure<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    is_move: bool,
    raw_params: &[String],
    fallback_param_tys: &[Type],
    body: &Expr,
    span: &Span,
) -> TypedExpr {
    let typed_params = parse_closure_params(raw_params, fallback_param_tys, type_ctx, span);
    let param_names: HashSet<String> = typed_params.iter().map(|(n, _)| n.clone()).collect();
    let mut locals = vec![param_names];

    let mut raw_uses = Vec::new();
    collect_raw_capture_uses(body, CaptureNeed::Consume, &mut locals, scopes, type_ctx, &mut raw_uses);
    let captures = coalesce_captures(raw_uses, is_move, scopes, type_ctx);

    if captures.is_empty() {
        return build_zero_capture_closure(&typed_params, errors, type_ctx, body, span);
    }

    // 1. Validate borrows and build initializers for each captured field on the outer scope.
    let mut init_fields: Vec<(String, TypedExpr)> = Vec::with_capacity(captures.len());
    let mut field_offsets = std::collections::HashMap::new();
    let mut field_vis = std::collections::HashMap::new();
    let mut total_size = 0u32;

    for cap in &captures {
        let proj_path = if cap.fields.is_empty() {
            cap.root.clone()
        } else {
            format!("{}.{}", cap.root, cap.fields.join("."))
        };
        let root_info = scopes.lookup(&cap.root).copied();
        let root_ty = root_info.map(|i| i.ty).unwrap_or(Type::Int);

        if let Some(info) = root_info {
            if info.is_moved {
                errors.push(SemanticError {
                    code: "E0382",
                    message: format!("Closure captures moved value `{}`", cap.root),
                    label: "Value used after move".to_string(),
                    secondary_label: None,
                    help: None,
                    span: cap.span.clone(),
                });
            }
        }

        let init_val = match cap.mode {
            CaptureMode::ByValue => {
                if !cap.proj_ty.is_copy() {
                    check_not_borrowed_on_move(scopes, errors, &cap.root, &cap.span);
                    if cap.fields.is_empty() {
                        scopes.mark_moved(&cap.root);
                    }
                }
                build_projection_typed_expr(&cap.root, &cap.fields, root_ty, type_ctx, &cap.span)
            }
            CaptureMode::ByMutRef => {
                if let Some(info) = root_info {
                    if !info.is_mutable && !matches!(info.ty, Type::MutRef(_) | Type::Ptr(_)) {
                        errors.push(SemanticError {
                            code: "E0596",
                            message: format!(
                                "Cannot borrow `{proj_path}` as mutable inside closure, as `{}` is not declared as mutable",
                                cap.root
                            ),
                            label: "Cannot borrow as mutable".to_string(),
                            secondary_label: None,
                            help: Some(format!("Consider changing this to be mutable: `let mut {}`", cap.root)),
                            span: cap.span.clone(),
                        });
                    }
                }
                if let Some((was_mut, holder)) = scopes.active_borrow(&proj_path) {
                    errors.push(SemanticError {
                        code: if was_mut { "E0499" } else { "E0502" },
                        message: if was_mut {
                            format!("Cannot borrow `{proj_path}` as mutable more than once at a time (already borrowed by `{holder}`)")
                        } else {
                            format!("Cannot borrow `{proj_path}` as mutable because it is also borrowed as immutable by `{holder}`")
                        },
                        label: "Conflicting closure capture".to_string(),
                        secondary_label: None,
                        help: None,
                        span: cap.span.clone(),
                    });
                }
                let proj_ast = build_projection_expr(&cap.root, &cap.fields, &cap.span);
                let mut tmp_errs = Vec::new();
                let mut ref_expr = type_check_expr(scopes, &mut tmp_errs, type_ctx, &Expr::Ref(Box::new(proj_ast), true, cap.span.clone()))
                    .unwrap_or_else(|| TypedExpr::Ref(Box::new(build_projection_typed_expr(&cap.root, &cap.fields, root_ty, type_ctx, &cap.span)), true, cap.field_ty, cap.span.clone()));
                if let Type::MutRef(inner) = cap.proj_ty {
                    // Already `&mut T`: capture reborrow `&mut *r` or direct ref value cleanly.
                    let deref_t = TypedExpr::Deref(
                        Box::new(build_projection_typed_expr(&cap.root, &cap.fields, root_ty, type_ctx, &cap.span)),
                        *inner,
                        cap.span.clone(),
                    );
                    ref_expr = TypedExpr::Ref(Box::new(deref_t), true, cap.field_ty, cap.span.clone());
                }
                ref_expr
            }
            CaptureMode::ByRef => {
                if let Some((true, holder)) = scopes.active_borrow(&proj_path) {
                    errors.push(SemanticError {
                        code: "E0502",
                        message: format!(
                            "Cannot borrow `{proj_path}` as immutable because it is also borrowed as mutable by `{holder}`"
                        ),
                        label: "Conflicting closure capture".to_string(),
                        secondary_label: None,
                        help: None,
                        span: cap.span.clone(),
                    });
                }
                let inner_typed = build_projection_typed_expr(&cap.root, &cap.fields, root_ty, type_ctx, &cap.span);
                if matches!(cap.proj_ty, Type::Ref(_)) {
                    inner_typed
                } else {
                    TypedExpr::Ref(Box::new(inner_typed), false, cap.field_ty, cap.span.clone())
                }
            }
        };

        field_offsets.insert(cap.cap_field_name.clone(), (total_size, cap.field_ty));
        field_vis.insert(cap.cap_field_name.clone(), Visibility::Pub);
        total_size += 8;
        init_fields.push((cap.cap_field_name.clone(), init_val));
    }

    // 2. Register concrete closure environment struct `__Closure_N`.
    let env_id = CLOSURE_ENV_COUNTER.fetch_add(1, Ordering::Relaxed);
    let closure_struct_name = format!("__Closure_{env_id}");
    let closure_ty = Type::Obj(intern_str(&closure_struct_name));

    type_ctx.struct_map.borrow_mut().insert(
        closure_struct_name.clone(),
        StructLayout {
            name: closure_struct_name.clone(),
            total_size,
            field_offsets,
            vis: Visibility::Pub,
            module_path: type_ctx.current_module.clone(),
            field_vis,
        },
    );

    // 3. Determine Fn / FnMut / FnOnce kind and rewrite body against `self.__cap_i`.
    let calls_fn_once_capture = captures.iter().any(|c| {
        !c.consumes_in_body
            && matches!(c.proj_ty, Type::Obj(s) if s.starts_with("__Closure_"))
            && {
                let sname = match c.proj_ty { Type::Obj(s) => s, _ => "" };
                type_ctx.get_fn(&format!("{sname}_call_ref")).is_none()
                    && type_ctx.get_fn(&format!("{sname}_call_mut")).is_none()
                    && type_ctx.get_fn(&format!("{sname}_call_once")).is_some()
            }
    });
    let has_mut_capture = captures.iter().any(|c| c.mode == CaptureMode::ByMutRef);
    let kind = if captures.iter().any(|c| c.consumes_in_body) || calls_fn_once_capture {
        ClosureKind::FnOnce
    } else if has_mut_capture {
        ClosureKind::FnMut
    } else {
        ClosureKind::Fn
    };

    let mut unpack_stmts = Vec::new();
    let mut captures = captures;
    if kind == ClosureKind::FnOnce {
        for cap in &mut captures {
            if cap.mode == CaptureMode::ByValue {
                let unpacked = format!("__unpacked_{}", cap.cap_field_name);
                unpack_stmts.push(Expr::Let(
                    unpacked.clone(),
                    None,
                    true,
                    Box::new(Expr::FieldAccess(
                        Box::new(Expr::Ident("self".to_string(), span.clone())),
                        cap.cap_field_name.clone(),
                        span.clone(),
                    )),
                    span.clone(),
                ));
                cap.unpacked_var = Some(unpacked);
            }
        }
    }

    let mut rw_locals = vec![typed_params.iter().map(|(n, _)| n.clone()).collect()];
    let rewritten_body = rewrite_closure_body(body, &captures, &mut rw_locals);
    let mut full_body_stmts = unpack_stmts;
    let body_ends_with_return = matches!(rewritten_body, Expr::Return(..));
    if let Expr::Block(inner_stmts, _) = &rewritten_body {
        full_body_stmts.extend(inner_stmts.clone());
    } else {
        full_body_stmts.push(rewritten_body.clone());
    }
    let probe_body = if full_body_stmts.len() == 1 && !matches!(rewritten_body, Expr::Block(..)) {
        full_body_stmts[0].clone()
    } else {
        Expr::Block(full_body_stmts.clone(), span.clone())
    };

    // 4. Probe/infer parameter and return types by type-checking rewritten body once cleanly.
    let mut probe_scopes = ScopeStack::new();
    let self_probe_ty = match kind {
        ClosureKind::Fn => Type::Ref(intern_type(closure_ty)),
        ClosureKind::FnMut => Type::MutRef(intern_type(closure_ty)),
        ClosureKind::FnOnce => closure_ty,
    };
    probe_scopes.declare_with_caller("self".to_string(), kind != ClosureKind::Fn, self_probe_ty, true);
    for (p_name, p_ty) in &typed_params {
        probe_scopes.declare(p_name.clone(), false, *p_ty);
    }

    let mut probe_ctx = type_ctx.clone();
    probe_ctx.current_return_type = None;
    probe_ctx.current_expected_type = None;
    let typed_probe = type_check_expr(&mut probe_scopes, errors, &probe_ctx, &probe_body);

    let resolved_params: Vec<(String, Type)> = typed_params
        .iter()
        .map(|(n, t)| (n.clone(), type_ctx.infer.borrow_mut().resolve(*t)))
        .collect();
    let ret_ty = match typed_probe {
        Some(ref tb) => {
            if body_ends_with_return {
                type_ctx
                    .infer
                    .borrow_mut()
                    .resolve(infer_return_expr_type(tb).unwrap_or(Type::Unit))
            } else {
                type_ctx.infer.borrow_mut().resolve(tb.ty())
            }
        }
        None => Type::Unit,
    };

    // Normalize body statement list.
    let body_stmts = full_body_stmts;
    let make_call_params = |self_ty: Type, self_mut: bool| {
        let mut ps = Vec::with_capacity(1 + resolved_params.len());
        ps.push(Param {
            name: "self".to_string(),
            is_mutable: self_mut,
            ty: self_ty,
            span: span.clone(),
        });
        for (pn, pt) in &resolved_params {
            ps.push(Param {
                name: pn.clone(),
                is_mutable: false,
                ty: *pt,
                span: span.clone(),
            });
        }
        ps
    };
    let forward_arg_exprs = |self_expr: Expr| -> Vec<Expr> {
        let mut args = Vec::with_capacity(1 + resolved_params.len());
        args.push(self_expr);
        for (pn, _) in &resolved_params {
            args.push(Expr::Ident(pn.clone(), span.clone()));
        }
        args
    };
    let forward_ref_from_mut_self = || -> Expr {
        Expr::Ref(
            Box::new(Expr::Deref(
                Box::new(Expr::Ident("self".to_string(), span.clone())),
                span.clone(),
            )),
            false,
            span.clone(),
        )
    };
    let forward_mut_ref_from_owned_self = || -> Expr {
        Expr::Ref(
            Box::new(Expr::Ident("self".to_string(), span.clone())),
            true,
            span.clone(),
        )
    };
    let wrap_forward_ret = |call_expr: Expr| -> Vec<Expr> {
        if ret_ty == Type::Unit {
            vec![call_expr]
        } else {
            vec![Expr::Return(Some(Box::new(call_expr)), span.clone())]
        }
    };

    // 5. Register trait impls and synthesize call methods in `fn_map` + `worklist`.
    {
        let mut mono = type_ctx.mono.borrow_mut();
        mono.trait_impls.insert((closure_struct_name.clone(), "FnOnce".to_string()));
        if matches!(kind, ClosureKind::FnMut | ClosureKind::Fn) {
            mono.trait_impls.insert((closure_struct_name.clone(), "FnMut".to_string()));
        }
        if kind == ClosureKind::Fn {
            mono.trait_impls.insert((closure_struct_name.clone(), "Fn".to_string()));
        }
    }

    let register_fn = |f: FuncDecl| {
        type_ctx.fn_map.borrow_mut().insert(f.name.clone(), f.clone());
        type_ctx.worklist.borrow_mut().push(f);
    };

    match kind {
        ClosureKind::Fn => {
            let ref_name = format!("{closure_struct_name}_call_ref");
            let mut_name = format!("{closure_struct_name}_call_mut");
            let once_name = format!("{closure_struct_name}_call_once");

            register_fn(FuncDecl {
                name: ref_name.clone(),
                params: make_call_params(Type::Ref(intern_type(closure_ty)), false),
                return_type: ret_ty,
                where_clause: None,
                body: body_stmts,
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: type_ctx.current_module.clone(),
                is_trait_impl: true,
            });
            register_fn(FuncDecl {
                name: mut_name.clone(),
                params: make_call_params(Type::MutRef(intern_type(closure_ty)), true),
                return_type: ret_ty,
                where_clause: None,
                body: wrap_forward_ret(Expr::Call(
                    ref_name,
                    forward_arg_exprs(forward_ref_from_mut_self()),
                    span.clone(),
                )),
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: type_ctx.current_module.clone(),
                is_trait_impl: true,
            });
            register_fn(FuncDecl {
                name: once_name,
                params: make_call_params(closure_ty, true),
                return_type: ret_ty,
                where_clause: None,
                body: wrap_forward_ret(Expr::Call(
                    mut_name,
                    forward_arg_exprs(forward_mut_ref_from_owned_self()),
                    span.clone(),
                )),
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: type_ctx.current_module.clone(),
                is_trait_impl: true,
            });
        }
        ClosureKind::FnMut => {
            let mut_name = format!("{closure_struct_name}_call_mut");
            let once_name = format!("{closure_struct_name}_call_once");
            register_fn(FuncDecl {
                name: mut_name.clone(),
                params: make_call_params(Type::MutRef(intern_type(closure_ty)), true),
                return_type: ret_ty,
                where_clause: None,
                body: body_stmts,
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: type_ctx.current_module.clone(),
                is_trait_impl: true,
            });
            register_fn(FuncDecl {
                name: once_name,
                params: make_call_params(closure_ty, true),
                return_type: ret_ty,
                where_clause: None,
                body: wrap_forward_ret(Expr::Call(
                    mut_name,
                    forward_arg_exprs(forward_mut_ref_from_owned_self()),
                    span.clone(),
                )),
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: type_ctx.current_module.clone(),
                is_trait_impl: true,
            });
        }
        ClosureKind::FnOnce => {
            let once_name = format!("{closure_struct_name}_call_once");
            register_fn(FuncDecl {
                name: once_name,
                params: make_call_params(closure_ty, true),
                return_type: ret_ty,
                where_clause: None,
                body: body_stmts,
                is_track_caller: false,
                vis: Visibility::Pub,
                module_path: type_ctx.current_module.clone(),
                is_trait_impl: true,
            });
        }
    }

    TypedExpr::ObjInit(closure_struct_name, init_fields, closure_ty, span.clone())
}

fn infer_return_expr_type(tb: &TypedExpr) -> Option<Type> {
    match tb {
        TypedExpr::Return(opt, _) => opt.as_ref().map(|e| e.ty()),
        _ => Some(tb.ty()),
    }
}

fn build_zero_capture_closure<'a>(
    typed_params: &[(String, Type)],
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    body: &Expr,
    span: &Span,
) -> TypedExpr {
    let closure_id = CLOSURE_ENV_COUNTER.fetch_add(1, Ordering::Relaxed);
    let closure_name = format!("__closure_{closure_id}");

    let mut closure_scopes = ScopeStack::new();
    for (p_name, p_ty) in typed_params {
        closure_scopes.declare(p_name.clone(), false, *p_ty);
    }

    let mut closure_ctx = type_ctx.clone();
    closure_ctx.current_return_type = None;
    closure_ctx.current_expected_type = None;

    let typed_body = type_check_expr(&mut closure_scopes, errors, &closure_ctx, body)
        .unwrap_or(TypedExpr::Int(0, span.clone()));
    let resolved_params: Vec<(String, Type)> = typed_params
        .iter()
        .map(|(n, t)| (n.clone(), type_ctx.infer.borrow_mut().resolve(*t)))
        .collect();
    let ret_ty = type_ctx.infer.borrow_mut().resolve(typed_body.ty());

    TypedExpr::Closure(
        closure_name,
        resolved_params,
        Box::new(typed_body),
        ret_ty,
        span.clone(),
    )
}

/// Legacy alias retained for explicit non-capturing closure call sites (`Type::FnPtr` expectation).
pub fn build_non_capturing_closure<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    raw_params: &[String],
    fallback_param_ty: Type,
    body: &Expr,
    span: &Span,
) -> TypedExpr {
    build_closure(
        scopes,
        errors,
        type_ctx,
        false,
        raw_params,
        &[fallback_param_ty],
        body,
        span,
    )
}

pub fn type_check_closure<'a>(
    scopes: &mut ScopeStack,
    errors: &mut Vec<SemanticError>,
    type_ctx: &TypeCtx<'a>,
    is_move: bool,
    params: &[String],
    body: &Expr,
    span: &Span,
) -> Option<TypedExpr> {
    let mut fallback_tys = Vec::new();
    if let Some(exp) = type_ctx.current_expected_type {
        let resolved = type_ctx.infer.borrow_mut().probe(exp);
        if let Type::FnPtr(ps, _) = resolved {
            fallback_tys = ps.to_vec();
        }
    }
    Some(build_closure(
        scopes,
        errors,
        type_ctx,
        is_move,
        params,
        &fallback_tys,
        body,
        span,
    ))
}

/// Extracts all active `(path, is_mut)` borrows captured inside a `TypedExpr` (e.g. a closure
/// literal `__Closure_N` or an iterator adapter wrapping a closure).
pub fn collect_borrowed_paths_from_typed_expr(
    expr: &TypedExpr,
    scopes: &ScopeStack,
    out: &mut Vec<(String, bool)>,
) {
    match expr {
        TypedExpr::ObjInit(name, fields, _, _) if name.starts_with("__Closure_") => {
            for (_, val) in fields {
                if let TypedExpr::Ref(inner, is_mut, _, _) = val {
                    if let Some(path) = typed_projection_path(inner) {
                        out.push((path, *is_mut));
                    }
                } else if let TypedExpr::Ident(src, ty, _) = val {
                    if matches!(ty, Type::Ref(_) | Type::MutRef(_)) {
                        for (t, m) in scopes.borrows_for_holder(src) {
                            out.push((t, m));
                        }
                    }
                } else {
                    collect_borrowed_paths_from_typed_expr(val, scopes, out);
                }
            }
        }
        TypedExpr::ObjInit(_, fields, _, _) => {
            for (_, val) in fields {
                collect_borrowed_paths_from_typed_expr(val, scopes, out);
            }
        }
        TypedExpr::TupleInit(elems, _, _) | TypedExpr::ArrayInit(elems, _, _) => {
            for elem in elems {
                collect_borrowed_paths_from_typed_expr(elem, scopes, out);
            }
        }
        TypedExpr::EnumConstruct(_, _, _, args, _, _) => {
            for arg in args {
                collect_borrowed_paths_from_typed_expr(arg, scopes, out);
            }
        }
        TypedExpr::Call(_, args, ret_ty, _) => {
            if contains_closure_obj(ret_ty) {
                for a in args {
                    collect_borrowed_paths_from_typed_expr(a, scopes, out);
                }
            }
        }
        TypedExpr::Ident(src, ty, _) => {
            if contains_closure_obj(ty) {
                for (t, m) in scopes.borrows_for_holder(src) {
                    out.push((t, m));
                }
            }
        }
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            if let Some(last) = stmts.last() {
                collect_borrowed_paths_from_typed_expr(last, scopes, out);
            }
        }
        _ => {}
    }
}

fn typed_projection_path(expr: &TypedExpr) -> Option<String> {
    match expr {
        TypedExpr::Ident(name, _, _) => Some(name.clone()),
        TypedExpr::FieldAccess(inner, field, _, _) => {
            typed_projection_path(inner).map(|p| format!("{p}.{field}"))
        }
        TypedExpr::Deref(inner, _, _) => typed_projection_path(inner),
        _ => None,
    }
}

/// Returns true if `ty` is or embeds a compiler-synthesized `__Closure_N` type.
pub fn contains_closure_obj(ty: &Type) -> bool {
    match ty {
        Type::Obj(name) => {
            name.starts_with("__Closure_") || name.contains("___Closure_") || name.contains("__Closure_")
        }
        Type::Enum(name) => name.contains("__Closure_"),
        Type::Tuple(elems) => elems.iter().any(contains_closure_obj),
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Vec(inner)
        | Type::Box(inner)
        | Type::Rc(inner)
        | Type::Arc(inner)
        | Type::Ref(inner)
        | Type::MutRef(inner) => contains_closure_obj(inner),
        _ => false,
    }
}

/// Checks if a return expression escapes a local borrowing closure and emits `[E0373]`.
pub fn check_return_closure_escape(
    expr: &TypedExpr,
    type_ctx: &TypeCtx<'_>,
    errors: &mut Vec<SemanticError>,
) {
    let ty = type_ctx.infer.borrow_mut().resolve(expr.ty());
    if !contains_closure_obj(&ty) {
        return;
    }
    if type_contains_ref_closure(ty, type_ctx) {
        errors.push(SemanticError {
            code: "E0373",
            message: "Closure may outlive the current function, because it borrows local variable(s) owned by the current function".to_string(),
            label: "May outlive borrowed value".to_string(),
            secondary_label: None,
            help: Some("To force the closure to take ownership of referenced variables, use `move |...| ...`".to_string()),
            span: expr.span(),
        });
    }
}

fn type_contains_ref_closure(ty: Type, type_ctx: &TypeCtx<'_>) -> bool {
    match ty {
        Type::Obj(name) => {
            if name.starts_with("__Closure_") {
                if let Some(layout) = type_ctx.struct_map.borrow().get(name) {
                    return layout
                        .field_offsets
                        .values()
                        .any(|(_, fty)| matches!(fty, Type::Ref(_) | Type::MutRef(_)));
                }
            }
            if let Some((_, args)) = crate::sanal::mono::lookup_mangled(name) {
                return args.iter().any(|a| type_contains_ref_closure(*a, type_ctx));
            }
            false
        }
        Type::Enum(name) => crate::sanal::mono::lookup_mangled(name)
            .is_some_and(|(_, args)| args.iter().any(|a| type_contains_ref_closure(*a, type_ctx))),
        Type::Tuple(elems) => elems.iter().any(|e| type_contains_ref_closure(*e, type_ctx)),
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Vec(inner)
        | Type::Box(inner)
        | Type::Rc(inner)
        | Type::Arc(inner)
        | Type::Ref(inner)
        | Type::MutRef(inner) => type_contains_ref_closure(*inner, type_ctx),
        _ => false,
    }
}
