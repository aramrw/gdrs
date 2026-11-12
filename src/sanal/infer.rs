//! sanal/infer.rs
//! Function-local Hindley-Milner type inference using union-find inference variables,
//! deferred generic method/function monomorphization, and E0282 diagnostics.

use crate::{
    ast::{intern_str, intern_type, Span, Type, TypedExpr},
    sanal::{compat, mono, types::TypeCtx, SemanticError},
};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU32, Ordering};

static NEXT_INFER_ID: AtomicU32 = AtomicU32::new(1);

#[derive(Debug, Clone)]
enum InferSlot {
    Unbound { span: Span, origin: String },
    Link(u32),
    Resolved(Type),
}

/// Call whose monomorphization was deferred until inference variables resolve.
#[derive(Debug, Clone)]
pub enum DeferredCall {
    StructMethod {
        base_struct: String,
        method_name: String,
        type_args: Vec<Type>,
    },
    EnumMethod {
        base_enum: String,
        method_name: String,
        type_args: Vec<Type>,
    },
    GenericFn {
        base_fn: String,
        type_args: Vec<Type>,
    },
}

/// Union-find inference state scoped to a single function body.
#[derive(Debug, Default)]
pub struct InferCtx {
    slots: HashMap<u32, InferSlot>,
    deferred_calls: HashMap<String, DeferredCall>,
    next_deferred_call: u32,
}

impl InferCtx {
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocates a fresh globally-unique `Type::Infer(id)` with origin metadata for E0282 errors.
    pub fn fresh(&mut self, span: Span, origin: impl Into<String>) -> Type {
        let id = NEXT_INFER_ID.fetch_add(1, Ordering::Relaxed);
        self.slots.insert(
            id,
            InferSlot::Unbound {
                span,
                origin: origin.into(),
            },
        );
        Type::Infer(id)
    }

    /// Allocates one fresh inference variable per generic parameter name and returns
    /// `(param_env, ordered_type_args)` for template substitution.
    pub fn instantiate_params(
        &mut self,
        param_names: &[String],
        span: &Span,
        owner_desc: &str,
    ) -> (HashMap<String, Type>, Vec<Type>) {
        let mut env = HashMap::new();
        let mut args = Vec::with_capacity(param_names.len());
        for p in param_names {
            let clean = p.trim_start_matches('$');
            let var = self.fresh(
                span.clone(),
                format!("type parameter `${clean}` of `{owner_desc}`"),
            );
            env.insert(clean.to_string(), var);
            env.insert(format!("${clean}"), var);
            args.push(var);
        }
        (env, args)
    }

    pub fn register_deferred_call(&mut self, call: DeferredCall) -> String {
        let id = self.next_deferred_call;
        self.next_deferred_call += 1;
        let key = format!("__infer_call_{id}");
        self.deferred_calls.insert(key.clone(), call);
        key
    }

    pub fn take_deferred_call(&mut self, name: &str) -> Option<DeferredCall> {
        self.deferred_calls.remove(name)
    }

    fn find_root(&mut self, id: u32) -> u32 {
        match self.slots.get(&id).cloned() {
            Some(InferSlot::Link(parent)) => {
                let root = self.find_root(parent);
                if root != parent {
                    self.slots.insert(id, InferSlot::Link(root));
                }
                root
            }
            _ => id,
        }
    }

    /// Follows outer `Type::Infer` links until either an unbound root or non-`Infer` type is reached.
    pub fn probe(&mut self, mut ty: Type) -> Type {
        while let Type::Infer(id) = ty {
            let root = self.find_root(id);
            match self.slots.get(&root).cloned() {
                Some(InferSlot::Resolved(resolved)) => ty = resolved,
                _ => return Type::Infer(root),
            }
        }
        ty
    }

    /// Deeply resolves all inference variables inside `ty` (including containers and mangled names).
    pub fn resolve(&mut self, ty: Type) -> Type {
        let head = self.probe(ty);
        match head {
            Type::Infer(_) => head,
            Type::Ptr(inner) => Type::Ptr(intern_type(self.resolve(*inner))),
            Type::Ref(inner) => Type::Ref(intern_type(self.resolve(*inner))),
            Type::MutRef(inner) => Type::MutRef(intern_type(self.resolve(*inner))),
            Type::Rc(inner) => Type::Rc(intern_type(self.resolve(*inner))),
            Type::Arc(inner) => Type::Arc(intern_type(self.resolve(*inner))),
            Type::Vec(inner) => Type::Vec(intern_type(self.resolve(*inner))),
            Type::Slice(inner) => Type::Slice(intern_type(self.resolve(*inner))),
            Type::Array(inner, len) => Type::Array(intern_type(self.resolve(*inner)), len),
            Type::Tuple(elems) => {
                let resolved: Vec<Type> = elems.iter().map(|t| self.resolve(*t)).collect();
                Type::Tuple(crate::ast::intern_tuple(&resolved))
            }
            Type::Obj(name) | Type::Enum(name) => {
                if let Some((base, args)) = mono::lookup_mangled(name) {
                    let resolved_args: Vec<Type> =
                        args.iter().map(|a| self.resolve(*a)).collect();
                    if resolved_args != args {
                        let new_mangled = mono::mangle_name(&base, &resolved_args);
                        let interned = intern_str(&new_mangled);
                        if matches!(head, Type::Enum(_)) {
                            return Type::Enum(interned);
                        }
                        return Type::Obj(interned);
                    }
                }
                head
            }
            other => other,
        }
    }

    fn occurs_in(&mut self, root_id: u32, ty: Type) -> bool {
        let resolved = self.probe(ty);
        match resolved {
            Type::Infer(id) => self.find_root(id) == root_id,
            Type::Ptr(inner)
            | Type::Ref(inner)
            | Type::MutRef(inner)
            | Type::Rc(inner)
            | Type::Arc(inner)
            | Type::Vec(inner)
            | Type::Slice(inner)
            | Type::Array(inner, _) => self.occurs_in(root_id, *inner),
            Type::Tuple(elems) => elems.iter().any(|e| self.occurs_in(root_id, *e)),
            Type::Obj(name) | Type::Enum(name) => mono::lookup_mangled(name)
                .is_some_and(|(_, args)| args.iter().any(|a| self.occurs_in(root_id, *a))),
            _ => false,
        }
    }

    /// Unifies `expected` with `actual`, binding inference variables when possible.
    /// Returns `Err((resolved_expected, resolved_actual))` on structural/type mismatch.
    pub fn unify(&mut self, expected: Type, actual: Type) -> Result<(), (Type, Type)> {
        let a = self.probe(expected);
        let b = self.probe(actual);
        if a == b || a == Type::Void || b == Type::Void || a == Type::Error || b == Type::Error {
            return Ok(());
        }
        if matches!(a, Type::Generic(_)) || matches!(b, Type::Generic(_)) {
            return Ok(());
        }

        match (a, b) {
            (Type::Infer(id1), Type::Infer(id2)) => {
                if id1 != id2 {
                    self.slots.insert(id2, InferSlot::Link(id1));
                }
                Ok(())
            }
            (Type::Infer(id), other) | (other, Type::Infer(id)) => {
                if self.occurs_in(id, other) {
                    return Err((a, b));
                }
                self.slots.insert(id, InferSlot::Resolved(other));
                Ok(())
            }
            (Type::Vec(e1), Type::Vec(e2))
            | (Type::Slice(e1), Type::Slice(e2))
            | (Type::Vec(e1), Type::Slice(e2))
            | (Type::Slice(e1), Type::Vec(e2))
            | (Type::Vec(e1), Type::Array(e2, _))
            | (Type::Slice(e1), Type::Array(e2, _))
            | (Type::Array(e1, _), Type::Vec(e2)) => self.unify(*e1, *e2),
            (Type::Array(e1, n1), Type::Array(e2, n2)) => {
                if n1 == n2 {
                    self.unify(*e1, *e2)
                } else {
                    Err((a, b))
                }
            }
            (Type::Tuple(t1), Type::Tuple(t2)) => {
                if t1.len() != t2.len() {
                    return Err((a, b));
                }
                for (e1, e2) in t1.iter().zip(t2.iter()) {
                    self.unify(*e1, *e2)?;
                }
                Ok(())
            }
            (Type::Ptr(e1), Type::Ptr(e2)) => {
                if *e1 == Type::Void || *e2 == Type::Void {
                    Ok(())
                } else {
                    self.unify(*e1, *e2)
                }
            }
            (Type::Ref(e1), Type::Ref(e2))
            | (Type::MutRef(e1), Type::MutRef(e2))
            | (Type::Ref(e1), Type::MutRef(e2)) => self.unify(*e1, *e2),
            (Type::Rc(e1), Type::Rc(e2)) | (Type::Arc(e1), Type::Arc(e2)) => self.unify(*e1, *e2),
            (Type::Vec(_), Type::Obj(s)) | (Type::Obj(s), Type::Vec(_)) if s.contains("Vec") => {
                Ok(())
            }
            (Type::Obj(n1) | Type::Enum(n1), Type::Obj(n2) | Type::Enum(n2)) => {
                if let (Some((b1, args1)), Some((b2, args2))) =
                    (mono::lookup_mangled(n1), mono::lookup_mangled(n2))
                {
                    let bases_match = b1 == b2
                        || b1.ends_with(&format!("_{b2}"))
                        || b2.ends_with(&format!("_{b1}"));
                    if bases_match {
                        if args1.len() == args2.len() {
                            for (p1, p2) in args1.into_iter().zip(args2.into_iter()) {
                                self.unify(p1, p2)?;
                            }
                            return Ok(());
                        }
                        // Support 1-arg `Result<T>` shorthand unified with 2-param `Result<T, E>` template.
                        if (b1.ends_with("Result") || b2.ends_with("Result"))
                            && !args1.is_empty()
                            && !args2.is_empty()
                        {
                            return self.unify(args1[0], args2[0]);
                        }
                    }
                }
                if compat::is_type_compatible(&a, &b) {
                    Ok(())
                } else {
                    Err((a, b))
                }
            }
            _ => {
                if compat::is_type_compatible(&a, &b) {
                    Ok(())
                } else {
                    Err((a, b))
                }
            }
        }
    }

    /// Symmetric branch unification (used by `if/else` and `match` arms).
    pub fn unify_branches(&mut self, t1: Type, t2: Type) -> Result<(), (Type, Type)> {
        self.unify(t1, t2).or_else(|_| self.unify(t2, t1))
    }

    /// Returns metadata `(span, origin)` for an unbound inference variable.
    pub fn slot_info(&mut self, id: u32) -> Option<(Span, String)> {
        let root = self.find_root(id);
        match self.slots.get(&root) {
            Some(InferSlot::Unbound { span, origin }) => Some((span.clone(), origin.clone())),
            _ => None,
        }
    }
}

fn collect_unresolved_infers(infer: &mut InferCtx, ty: Type, out: &mut Vec<u32>) {
    let resolved = infer.resolve(ty);
    match resolved {
        Type::Infer(id) => {
            let root = infer.find_root(id);
            if !out.contains(&root) {
                out.push(root);
            }
        }
        Type::Ptr(inner)
        | Type::Ref(inner)
        | Type::MutRef(inner)
        | Type::Rc(inner)
        | Type::Arc(inner)
        | Type::Vec(inner)
        | Type::Slice(inner)
        | Type::Array(inner, _) => collect_unresolved_infers(infer, *inner, out),
        Type::Tuple(elems) => {
            for e in elems {
                collect_unresolved_infers(infer, *e, out);
            }
        }
        Type::Obj(name) | Type::Enum(name) => {
            if let Some((_, args)) = mono::lookup_mangled(name) {
                for a in args {
                    collect_unresolved_infers(infer, a, out);
                }
            }
        }
        _ => {}
    }
}

fn ensure_concrete_monomorphized(ty: Type, type_ctx: &TypeCtx<'_>) {
    match ty {
        Type::Ptr(inner)
        | Type::Ref(inner)
        | Type::MutRef(inner)
        | Type::Rc(inner)
        | Type::Arc(inner)
        | Type::Vec(inner)
        | Type::Slice(inner)
        | Type::Array(inner, _) => ensure_concrete_monomorphized(*inner, type_ctx),
        Type::Tuple(elems) => {
            for e in elems {
                ensure_concrete_monomorphized(*e, type_ctx);
            }
        }
        Type::Obj(name) => {
            if let Some((base, args)) = mono::lookup_mangled(name) {
                for a in &args {
                    ensure_concrete_monomorphized(*a, type_ctx);
                }
                if !args.iter().any(compat::type_contains_infer)
                    && !args.iter().any(compat::type_contains_generic)
                {
                    let _ = mono::monomorphize_struct(
                        type_ctx.mono,
                        &base,
                        &args,
                        type_ctx.struct_map,
                        type_ctx.enum_map,
                        type_ctx.fn_map,
                        type_ctx.worklist,
                    );
                }
            }
        }
        Type::Enum(name) => {
            if let Some((base, args)) = mono::lookup_mangled(name) {
                for a in &args {
                    ensure_concrete_monomorphized(*a, type_ctx);
                }
                if !args.iter().any(compat::type_contains_infer)
                    && !args.iter().any(compat::type_contains_generic)
                {
                    let _ = mono::monomorphize_enum(
                        type_ctx.mono,
                        &base,
                        &args,
                        type_ctx.enum_map,
                        type_ctx.fn_map,
                        type_ctx.worklist,
                    );
                }
            }
        }
        _ => {}
    }
}

fn resolve_and_record_type(
    ty: &mut Type,
    infer: &mut InferCtx,
    type_ctx: &TypeCtx<'_>,
    reported_infers: &mut HashSet<u32>,
    errors: &mut Vec<SemanticError>,
    fallback_span: &Span,
) {
    let resolved = infer.resolve(*ty);
    *ty = resolved;

    let mut unresolved = Vec::new();
    collect_unresolved_infers(infer, resolved, &mut unresolved);
    for root in unresolved {
        if reported_infers.insert(root) {
            let (err_span, origin) = infer
                .slot_info(root)
                .unwrap_or_else(|| (fallback_span.clone(), "expression type".to_string()));
            errors.push(SemanticError {
                code: "E0282",
                message: format!("Type annotations needed: cannot infer {origin}"),
                label: format!("Cannot infer {origin}"),
                secondary_label: None,
                help: Some(
                    "Consider giving an explicit type annotation (e.g. `let x: Vec<f64> = ...` or `Matrix<f64>`)"
                        .to_string(),
                ),
                span: err_span,
            });
        }
    }

    ensure_concrete_monomorphized(resolved, type_ctx);
}

fn finalize_typed_expr(
    expr: &mut TypedExpr,
    infer: &mut InferCtx,
    type_ctx: &TypeCtx<'_>,
    reported_infers: &mut HashSet<u32>,
    errors: &mut Vec<SemanticError>,
) {
    let span = expr.span();
    match expr {
        TypedExpr::Int(..)
        | TypedExpr::Float(..)
        | TypedExpr::Bool(..)
        | TypedExpr::String(..)
        | TypedExpr::Break(..)
        | TypedExpr::Continue(..) => {}

        TypedExpr::Ident(_, ty, _) => {
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::Add(l, r, ty, _)
        | TypedExpr::Sub(l, r, ty, _)
        | TypedExpr::Mul(l, r, ty, _)
        | TypedExpr::Div(l, r, ty, _)
        | TypedExpr::Mod(l, r, ty, _)
        | TypedExpr::Pipe(l, r, ty, _)
        | TypedExpr::Ampersand(l, r, ty, _)
        | TypedExpr::Caret(l, r, ty, _)
        | TypedExpr::Shl(l, r, ty, _)
        | TypedExpr::Shr(l, r, ty, _)
        | TypedExpr::Range(l, r, ty, _) => {
            finalize_typed_expr(l, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(r, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::GreaterThan(l, r, _)
        | TypedExpr::LessThan(l, r, _)
        | TypedExpr::GreaterEqual(l, r, _)
        | TypedExpr::LessEqual(l, r, _)
        | TypedExpr::Equal(l, r, _)
        | TypedExpr::NotEqual(l, r, _)
        | TypedExpr::And(l, r, _)
        | TypedExpr::Or(l, r, _) => {
            finalize_typed_expr(l, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(r, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::Neg(inner, ty, _)
        | TypedExpr::Ref(inner, _, ty, _)
        | TypedExpr::Deref(inner, ty, _)
        | TypedExpr::Cast(inner, ty, _) => {
            finalize_typed_expr(inner, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::Not(inner, _)
        | TypedExpr::CoerceToDyn(inner, _, _)
        | TypedExpr::CastF32(inner, _)
        | TypedExpr::CastI32(inner, _) => {
            finalize_typed_expr(inner, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::Let(_, _, val, ty, _) => {
            finalize_typed_expr(val, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::LetTuple(pat, ty, val, _) => {
            fn resolve_pattern(
                pat: &mut crate::ast::TypedTuplePattern,
                infer: &mut InferCtx,
                type_ctx: &TypeCtx<'_>,
                reported_infers: &mut HashSet<u32>,
                errors: &mut Vec<SemanticError>,
            ) {
                match pat {
                    crate::ast::TypedTuplePattern::Ident { ty, span, .. } => {
                        resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, span);
                    }
                    crate::ast::TypedTuplePattern::Tuple(items, ty, span) => {
                        resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, span);
                        for item in items {
                            resolve_pattern(item, infer, type_ctx, reported_infers, errors);
                        }
                    }
                }
            }
            finalize_typed_expr(val, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
            resolve_pattern(pat, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::Block(stmts, ty, _) | TypedExpr::Unsafe(stmts, ty, _) => {
            for s in stmts {
                finalize_typed_expr(s, infer, type_ctx, reported_infers, errors);
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::Assign(_, val, _) => {
            finalize_typed_expr(val, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::While(c, b, _) | TypedExpr::If(c, b, _) => {
            finalize_typed_expr(c, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(b, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::IfElse(c, t, e, ty, _) => {
            finalize_typed_expr(c, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(t, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(e, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::Return(opt_e, _) => {
            if let Some(e) = opt_e {
                finalize_typed_expr(e, infer, type_ctx, reported_infers, errors);
            }
        }

        TypedExpr::MacroCall(_, args, ty, _) => {
            for a in args {
                finalize_typed_expr(a, infer, type_ctx, reported_infers, errors);
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::Call(fn_name, args, ty, _) => {
            for a in args.iter_mut() {
                finalize_typed_expr(a, infer, type_ctx, reported_infers, errors);
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);

            if let Some(deferred) = infer.take_deferred_call(fn_name) {
                match deferred {
                    DeferredCall::StructMethod {
                        base_struct,
                        method_name,
                        type_args,
                    } => {
                        let resolved_args: Vec<Type> =
                            type_args.into_iter().map(|t| infer.resolve(t)).collect();
                        if base_struct == "std_vec_Vec" && method_name == "new" {
                            *fn_name = "std_vec_Vec_new".to_string();
                        } else if !resolved_args
                            .iter()
                            .any(|t| compat::type_contains_infer(t) || compat::type_contains_generic(t))
                        {
                            if let Some(mangled) = mono::monomorphize_struct(
                                type_ctx.mono,
                                &base_struct,
                                &resolved_args,
                                type_ctx.struct_map,
                                type_ctx.enum_map,
                                type_ctx.fn_map,
                                type_ctx.worklist,
                            ) {
                                *fn_name = format!("{mangled}_{method_name}");
                            }
                        }
                    }
                    DeferredCall::EnumMethod {
                        base_enum,
                        method_name,
                        type_args,
                    } => {
                        let resolved_args: Vec<Type> =
                            type_args.into_iter().map(|t| infer.resolve(t)).collect();
                        if !resolved_args
                            .iter()
                            .any(|t| compat::type_contains_infer(t) || compat::type_contains_generic(t))
                        {
                            if let Some(mangled) = mono::monomorphize_enum(
                                type_ctx.mono,
                                &base_enum,
                                &resolved_args,
                                type_ctx.enum_map,
                                type_ctx.fn_map,
                                type_ctx.worklist,
                            ) {
                                *fn_name = format!("{mangled}_{method_name}");
                            }
                        }
                    }
                    DeferredCall::GenericFn { base_fn, type_args } => {
                        let resolved_args: Vec<Type> = if type_args.is_empty() {
                            args.iter().map(|a| a.ty()).collect()
                        } else {
                            type_args.into_iter().map(|t| infer.resolve(t)).collect()
                        };
                        if !resolved_args
                            .iter()
                            .any(|t| compat::type_contains_infer(t) || compat::type_contains_generic(t))
                        {
                            if let Some(mangled) = mono::monomorphize_fn(
                                type_ctx.mono,
                                &base_fn,
                                &resolved_args,
                                type_ctx.fn_map,
                                type_ctx.struct_map,
                                type_ctx.enum_map,
                                type_ctx.worklist,
                            ) {
                                *fn_name = mangled;
                            }
                        }
                    }
                }
            }
        }

        TypedExpr::ObjInit(obj_name, fields, ty, _) => {
            for (_, f_expr) in fields {
                finalize_typed_expr(f_expr, infer, type_ctx, reported_infers, errors);
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
            if let Type::Obj(resolved_name) = *ty {
                *obj_name = resolved_name.to_string();
            }
        }

        TypedExpr::FieldAccess(target, _, ty, _) => {
            finalize_typed_expr(target, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::FieldAssign(target, _, val, _) => {
            finalize_typed_expr(target, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(val, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::ArrayInit(elems, ty, _) | TypedExpr::TupleInit(elems, ty, _) => {
            for e in elems {
                finalize_typed_expr(e, infer, type_ctx, reported_infers, errors);
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::IndexAccess(target, idx, ty, _) => {
            finalize_typed_expr(target, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(idx, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::IndexAssign(target, idx, val, _) => {
            finalize_typed_expr(target, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(idx, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(val, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::EnumConstruct(enum_name, _, _, args, ty, _) => {
            for a in args {
                finalize_typed_expr(a, infer, type_ctx, reported_infers, errors);
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
            if let Type::Enum(resolved_name) = *ty {
                *enum_name = resolved_name.to_string();
            }
        }

        TypedExpr::DynCall(recv, _, args, ty, _) => {
            finalize_typed_expr(recv, infer, type_ctx, reported_infers, errors);
            for a in args {
                finalize_typed_expr(a, infer, type_ctx, reported_infers, errors);
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::Match(target, arms, ty, _) => {
            finalize_typed_expr(target, infer, type_ctx, reported_infers, errors);
            for arm in arms {
                for (_, b_ty) in &mut arm.bindings {
                    resolve_and_record_type(
                        b_ty,
                        infer,
                        type_ctx,
                        reported_infers,
                        errors,
                        &arm.span,
                    );
                }
                for stmt in &mut arm.body {
                    finalize_typed_expr(stmt, infer, type_ctx, reported_infers, errors);
                }
            }
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }

        TypedExpr::DerefAssign(ptr, val, _) => {
            finalize_typed_expr(ptr, infer, type_ctx, reported_infers, errors);
            finalize_typed_expr(val, infer, type_ctx, reported_infers, errors);
        }

        TypedExpr::Closure(_, caps, body, ty, _) => {
            for (_, c_ty) in caps {
                resolve_and_record_type(c_ty, infer, type_ctx, reported_infers, errors, &span);
            }
            finalize_typed_expr(body, infer, type_ctx, reported_infers, errors);
            resolve_and_record_type(ty, infer, type_ctx, reported_infers, errors, &span);
        }
    }
}

/// Resolves all inference variables in a finished function body, triggers monomorphization
/// for any newly-concrete generic types/calls, and emits `[E0282]` for unconstrained ones.
pub fn finalize_function_body(
    body: &mut Vec<TypedExpr>,
    infer: &mut InferCtx,
    type_ctx: &TypeCtx<'_>,
    errors: &mut Vec<SemanticError>,
) {
    let mut reported_infers = HashSet::new();
    for stmt in body.iter_mut() {
        finalize_typed_expr(stmt, infer, type_ctx, &mut reported_infers, errors);
    }
}
