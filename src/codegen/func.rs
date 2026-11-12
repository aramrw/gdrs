//! codegen/func.rs
//! Translates TypedAST function declarations into native compiled functions using Cranelift.

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{InstBuilder, Value};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr, TypedFuncDecl};
use crate::codegen::branching::expr_is_terminator;
use crate::codegen::ctx::{CodegenCtx, ProgramMeta};
use crate::codegen::expr::{coerce_typed_val, compile_expr};
use crate::codegen::layout::{
    abi_signature_for_fn, alloc_stack_slot, emit_memcpy_bytes, load_multireg_chunks,
    pass_mode_for_type, store_multireg_chunks, PassMode,
};

fn stage_return_value<M: Module>(
    builder: &mut FunctionBuilder,
    ret_val: Value,
    expr_ty: &Type,
    ret_mode: &PassMode,
    ret_var: Option<Variable>,
    cg: &CodegenCtx,
    module: &mut M,
) {
    match ret_mode {
        PassMode::Ignore => {}
        PassMode::Direct(target_cl_ty) => {
            let coerced = coerce_typed_val(builder, ret_val, expr_ty, *target_cl_ty);
            if let Some(rv) = ret_var {
                builder.def_var(rv, coerced);
            }
        }
        PassMode::MultiReg { size, .. } => {
            if let Some(slot) = cg.ret_slot {
                let slot_addr = builder.ins().stack_addr(types::I64, slot, 0);
                emit_memcpy_bytes(builder, module, slot_addr, ret_val, *size);
            }
        }
        PassMode::Indirect { size, .. } => {
            if let Some(sret_addr) = cg.sret_ptr {
                emit_memcpy_bytes(builder, module, sret_addr, ret_val, *size);
            }
        }
    }
}

fn emit_return_inst<M: Module>(
    builder: &mut FunctionBuilder,
    ret_mode: &PassMode,
    scalar_val: Option<Value>,
    cg: &CodegenCtx,
    module: &mut M,
) {
    match ret_mode {
        PassMode::Ignore | PassMode::Indirect { .. } => {
            builder.ins().return_(&[]);
        }
        PassMode::Direct(_) => {
            let v = scalar_val.expect("scalar return value missing");
            builder.ins().return_(&[v]);
        }
        PassMode::MultiReg { size, chunks, .. } => {
            let slot = cg.ret_slot.expect("MultiReg ret_slot missing");
            let slot_addr = builder.ins().stack_addr(types::I64, slot, 0);
            let loaded = load_multireg_chunks(builder, module, slot_addr, *size, chunks);
            builder.ins().return_(&loaded);
        }
    }
}

pub fn emit_explicit_return<M: Module>(
    builder: &mut FunctionBuilder,
    opt_expr: Option<&TypedExpr>,
    cg: &mut CodegenCtx,
    module: &mut M,
) -> Value {
    let ret_mode = pass_mode_for_type(
        &cg.ret_type,
        false,
        &cg.meta.struct_layouts,
        cg.meta.enum_layouts,
    );
    if let Some(e) = opt_expr {
        let ret_val = compile_expr(builder, e, cg, module);
        cg.cancel_temp(ret_val);
        if let TypedExpr::Ident(ret_name, ret_ty, _) = e {
            if !ret_ty.is_copy() {
                cg.mark_moved(builder, ret_name);
            }
        }
        let prepared_scalar = match &ret_mode {
            PassMode::Direct(target_ty) => Some(coerce_typed_val(builder, ret_val, &e.ty(), *target_ty)),
            PassMode::MultiReg { size, .. } => {
                if let Some(slot) = cg.ret_slot {
                    let slot_addr = builder.ins().stack_addr(types::I64, slot, 0);
                    emit_memcpy_bytes(builder, module, slot_addr, ret_val, *size);
                }
                None
            }
            PassMode::Indirect { size, .. } => {
                if let Some(sret_addr) = cg.sret_ptr {
                    emit_memcpy_bytes(builder, module, sret_addr, ret_val, *size);
                }
                None
            }
            PassMode::Ignore => None,
        };
        cg.emit_temp_drops_down_to_depth(builder, module, 0);
        cg.emit_drops_down_to_depth(builder, module, 0);
        emit_return_inst(builder, &ret_mode, prepared_scalar, cg, module);
        ret_val
    } else {
        cg.emit_temp_drops_down_to_depth(builder, module, 0);
        cg.emit_drops_down_to_depth(builder, module, 0);
        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[]);
        zero
    }
}

/// Compiles a single function declaration to native machine code in the Module.
pub fn compile_func<M: Module>(
    func: &TypedFuncDecl,
    meta: &mut ProgramMeta,
    module: &mut M,
    ctx: &mut Context,
    builder_context: &mut FunctionBuilderContext,
) -> Option<cranelift_module::FuncId> {
    let export_name = if func.name == "main" {
        "gdrs_main"
    } else {
        &func.name
    };

    let is_drop_impl = func.name.ends_with("_drop");
    let param_tys: Vec<Type> = func.params.iter().map(|p| p.ty).collect();
    let (sig, fn_abi) = abi_signature_for_fn(
        module.isa().default_call_conv(),
        &param_tys,
        &func.return_type,
        is_drop_impl,
        &meta.struct_layouts,
        meta.enum_layouts,
    );

    let func_id = match module.get_name(export_name) {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        _ => module
            .declare_function(export_name, Linkage::Export, &sig)
            .unwrap(),
    };

    ctx.func.clear();
    *builder_context = FunctionBuilderContext::new();
    ctx.func.signature = sig.clone();

    let mut builder = FunctionBuilder::new(&mut ctx.func, builder_context);

    let entry_block = builder.create_block();
    builder.switch_to_block(entry_block);
    builder.append_block_params_for_function_params(entry_block);

    let mut cg = CodegenCtx::new(meta);
    cg.func_name = func.name.clone();
    cg.ret_type = func.return_type;
    for expr in &func.body {
        collect_addr_taken_expr(expr, &mut cg.addr_taken);
    }

    let block_params = builder.block_params(entry_block).to_vec();
    let mut param_cursor = 0usize;
    if fn_abi.has_sret {
        cg.sret_ptr = Some(block_params[0]);
        param_cursor = 1;
    }

    let is_non_consuming_self = cg.meta.non_consuming_self_fns.contains(&func.name);
    for (param, pmode) in func.params.iter().zip(fn_abi.param_modes.iter()) {
        let var = Variable::from_u32(cg.var_counter as u32);
        cg.var_counter += 1;
        match pmode {
            PassMode::Ignore => {
                builder.declare_var(var, types::I64);
                let zero = builder.ins().iconst(types::I64, 0);
                builder.def_var(var, zero);
                cg.bind_var(&param.name, var, param.ty);
            }
            PassMode::Direct(param_ty) => {
                let pval = block_params[param_cursor];
                param_cursor += 1;
                builder.declare_var(var, *param_ty);
                builder.def_var(var, pval);
                cg.bind_var(&param.name, var, param.ty);
                cg.track_addr_taken_slot(&mut builder, &param.name, &param.ty, *param_ty, pval);
            }
            PassMode::MultiReg { size, align, chunks } => {
                let n = chunks.len();
                let incoming: Vec<Value> = block_params[param_cursor..param_cursor + n].to_vec();
                param_cursor += n;
                let (_, slot_addr) = alloc_stack_slot(&mut builder, *size, *align);
                store_multireg_chunks(&mut builder, module, slot_addr, *size, &incoming);
                builder.declare_var(var, types::I64);
                builder.def_var(var, slot_addr);
                cg.bind_var(&param.name, var, param.ty);
            }
            PassMode::Indirect { .. } => {
                let addr_val = block_params[param_cursor];
                param_cursor += 1;
                builder.declare_var(var, types::I64);
                builder.def_var(var, addr_val);
                cg.bind_var(&param.name, var, param.ty);
            }
        }

        // Owned parameters (and consuming by-value `self` methods) are owned by this function and dropped on exit,
        // unless this function is `Drop::drop`, `fmt`/`to_string`, or a non-consuming trait method.
        let track_drop = if param.name == "self" {
            !is_drop_impl
                && !is_non_consuming_self
                && !matches!(param.ty, Type::Ref(_) | Type::MutRef(_))
        } else {
            !is_drop_impl
        };
        if track_drop {
            cg.track_var_if_droppable(&mut builder, &param.name, &param.ty, true);
        }
    }

    let is_void = matches!(fn_abi.ret_mode, PassMode::Ignore);

    let ret_var = match fn_abi.ret_mode {
        PassMode::Direct(ret_cl_ty) => {
            let v = Variable::from_u32(cg.var_counter as u32);
            cg.var_counter += 1;
            builder.declare_var(v, ret_cl_ty);
            let zero = match ret_cl_ty {
                types::F32 => builder.ins().f32const(0.0),
                types::F64 => builder.ins().f64const(0.0),
                _ => builder.ins().iconst(ret_cl_ty, 0),
            };
            builder.def_var(v, zero);
            Some(v)
        }
        PassMode::MultiReg { size, align, .. } => {
            let (slot, _) = alloc_stack_slot(&mut builder, size, align);
            cg.ret_slot = Some(slot);
            None
        }
        PassMode::Ignore | PassMode::Indirect { .. } => None,
    };

    let body_len = func.body.len();
    for (idx, expr) in func.body.iter().enumerate() {
        if builder.is_unreachable() {
            break;
        }
        cg.push_temp_scope();
        let val = compile_expr(&mut builder, expr, &mut cg, module);
        if builder.is_unreachable() || expr_is_terminator(expr) {
            cg.pop_temp_scope_without_drop();
            break;
        }
        let is_last = idx + 1 == body_len;
        if is_last && !is_void {
            cg.cancel_temp(val);
            if let TypedExpr::Ident(ret_name, ret_ty, _) = expr {
                if !ret_ty.is_copy() {
                    cg.mark_moved(&mut builder, ret_name);
                }
            }
            stage_return_value(
                &mut builder,
                val,
                &expr.ty(),
                &fn_abi.ret_mode,
                ret_var,
                &cg,
                module,
            );
        }
        cg.pop_temp_scope_and_drop(&mut builder, module);
    }

    let is_last_term = func.body.last().map(expr_is_terminator).unwrap_or(false);
    if !builder.is_unreachable() && !is_last_term {
        cg.pop_scope_and_drop(&mut builder, module);
        let scalar_val = ret_var.map(|rv| builder.use_var(rv));
        emit_return_inst(&mut builder, &fn_abi.ret_mode, scalar_val, &cg, module);
    }
    builder.seal_all_blocks();
    builder.finalize();

    if let Err(e) = module.define_function(func_id, ctx) {
        match e {
            cranelift_module::ModuleError::DuplicateDefinition(_) => {
                module.clear_context(ctx);
                return Some(func_id);
            }
            err => panic!("define_function error: {:?}", err),
        }
    }
    module.clear_context(ctx);

    Some(func_id)
}

fn collect_addr_taken_expr(expr: &TypedExpr, out: &mut std::collections::HashSet<String>) {
    match expr {
        TypedExpr::Ref(inner, _, _, _) => {
            if let TypedExpr::Ident(name, _, _) = inner.as_ref() {
                out.insert(name.clone());
            }
            collect_addr_taken_expr(inner, out);
        }
        TypedExpr::Add(l, r, _, _)
        | TypedExpr::Sub(l, r, _, _)
        | TypedExpr::Mul(l, r, _, _)
        | TypedExpr::Div(l, r, _, _)
        | TypedExpr::Mod(l, r, _, _)
        | TypedExpr::GreaterThan(l, r, _)
        | TypedExpr::LessThan(l, r, _)
        | TypedExpr::GreaterEqual(l, r, _)
        | TypedExpr::LessEqual(l, r, _)
        | TypedExpr::Equal(l, r, _)
        | TypedExpr::NotEqual(l, r, _)
        | TypedExpr::And(l, r, _)
        | TypedExpr::Or(l, r, _)
        | TypedExpr::Pipe(l, r, _, _)
        | TypedExpr::Ampersand(l, r, _, _)
        | TypedExpr::Caret(l, r, _, _)
        | TypedExpr::Shl(l, r, _, _)
        | TypedExpr::Shr(l, r, _, _)
        | TypedExpr::IndexAccess(l, r, _, _)
        | TypedExpr::DerefAssign(l, r, _)
        | TypedExpr::Range(l, r, _, _) => {
            collect_addr_taken_expr(l, out);
            collect_addr_taken_expr(r, out);
        }
        TypedExpr::Neg(inner, _, _)
        | TypedExpr::Not(inner, _)
        | TypedExpr::Assign(_, inner, _)
        | TypedExpr::Let(_, _, inner, _, _)
        | TypedExpr::LetTuple(_, _, inner, _)
        | TypedExpr::FieldAccess(inner, _, _, _)
        | TypedExpr::Deref(inner, _, _)
        | TypedExpr::CastF32(inner, _)
        | TypedExpr::CastI32(inner, _)
        | TypedExpr::Cast(inner, _, _)
        | TypedExpr::CoerceToDyn(inner, _, _) => collect_addr_taken_expr(inner, out),
        TypedExpr::Return(opt, _) => {
            if let Some(inner) = opt {
                collect_addr_taken_expr(inner, out);
            }
        }
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            for s in stmts {
                collect_addr_taken_expr(s, out);
            }
        }
        TypedExpr::While(c, b, _) | TypedExpr::If(c, b, _) => {
            collect_addr_taken_expr(c, out);
            collect_addr_taken_expr(b, out);
        }
        TypedExpr::IfElse(c, t, e, _, _) => {
            collect_addr_taken_expr(c, out);
            collect_addr_taken_expr(t, out);
            collect_addr_taken_expr(e, out);
        }
        TypedExpr::Match(t, arms, _, _) => {
            collect_addr_taken_expr(t, out);
            for arm in arms {
                for s in &arm.body {
                    collect_addr_taken_expr(s, out);
                }
            }
        }
        TypedExpr::FieldAssign(t, _, v, _) => {
            collect_addr_taken_expr(t, out);
            collect_addr_taken_expr(v, out);
        }
        TypedExpr::IndexAssign(t, i, v, _) => {
            collect_addr_taken_expr(t, out);
            collect_addr_taken_expr(i, out);
            collect_addr_taken_expr(v, out);
        }
        TypedExpr::Call(_, args, _, _)
        | TypedExpr::MacroCall(_, args, _, _)
        | TypedExpr::ArrayInit(args, _, _)
        | TypedExpr::TupleInit(args, _, _)
        | TypedExpr::EnumConstruct(_, _, _, args, _, _) => {
            for a in args {
                collect_addr_taken_expr(a, out);
            }
        }
        TypedExpr::DynCall(r, _, args, _, _) => {
            collect_addr_taken_expr(r, out);
            for a in args {
                collect_addr_taken_expr(a, out);
            }
        }
        TypedExpr::ObjInit(_, fields, _, _) => {
            for (_, v) in fields {
                collect_addr_taken_expr(v, out);
            }
        }
        TypedExpr::Closure(_, _, body, _, _) => collect_addr_taken_expr(body, out),
        TypedExpr::Int(..)
        | TypedExpr::Float(..)
        | TypedExpr::Ident(..)
        | TypedExpr::Bool(..)
        | TypedExpr::String(..)
        | TypedExpr::Break(..)
        | TypedExpr::Continue(..) => {}
    }
}
