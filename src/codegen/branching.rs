use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::ast::{Type, TypedExpr, TypedMatchArm};
use crate::codegen::ctx::CodegenCtx;
use crate::codegen::drops::{emit_drop_for_value, find_enum_layout, has_drop_glue, is_npo_enum};
use crate::codegen::expr::{coerce_val, compile_expr, cranelift_type_of};
use crate::codegen::layout::{
    alloc_stack_slot, emit_memcpy_bytes, enum_variant_offsets, is_aggregate_type, repr_kind,
    size_and_align, ReprKind,
};

pub fn expr_is_terminator(expr: &TypedExpr) -> bool {
    match expr {
        TypedExpr::Return(..) | TypedExpr::Break(..) | TypedExpr::Continue(..) => true,
        TypedExpr::Block(stmts, _, _) | TypedExpr::Unsafe(stmts, _, _) => {
            stmts.last().map(expr_is_terminator).unwrap_or(false)
        }
        _ => false,
    }
}

pub fn compile_if<M: Module>(
    builder: &mut FunctionBuilder,
    cg: &mut CodegenCtx,
    module: &mut M,
    cond: &TypedExpr,
    body: &TypedExpr,
) -> Value {
    let then_block = builder.create_block();
    let exit_block = builder.create_block();

    cg.push_temp_scope();
    let cond_val = compile_expr(builder, cond, cg, module);
    cg.pop_temp_scope_and_drop(builder, module);
    builder
        .ins()
        .brif(cond_val, then_block, &[], exit_block, &[]);

    // THEN BLOCK
    builder.switch_to_block(then_block);
    builder.seal_block(then_block);
    cg.push_scope();
    cg.push_temp_scope();
    let _body_val = compile_expr(builder, body, cg, module);
    if !builder.is_unreachable() && !expr_is_terminator(body) {
        cg.pop_temp_scope_and_drop(builder, module);
        cg.pop_scope_and_drop(builder, module);
        builder.ins().jump(exit_block, &[]);
    } else {
        cg.pop_temp_scope_without_drop();
        cg.pop_scope_without_drop();
    }

    // EXIT BLOCK
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    builder.ins().iconst(types::I64, 0)
}

pub fn compile_if_else<M: Module>(
    builder: &mut FunctionBuilder,
    cg: &mut CodegenCtx,
    ty: &Type,
    module: &mut M,
    cond: &TypedExpr,
    then_b: &TypedExpr,
    else_b: &TypedExpr,
) -> Value {
    let then_block = builder.create_block();
    let else_block = builder.create_block();
    let exit_block = builder.create_block();

    let res_repr = repr_kind(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
    let out_addr_opt = match res_repr {
        ReprKind::Aggregate { size, align } => Some(alloc_stack_slot(builder, size, align).1),
        ReprKind::Scalar(cl_ty) => {
            builder.append_block_param(exit_block, cl_ty);
            None
        }
        ReprKind::Zst => None,
    };

    cg.push_temp_scope();
    let cond_val = compile_expr(builder, cond, cg, module);
    cg.pop_temp_scope_and_drop(builder, module);
    builder
        .ins()
        .brif(cond_val, then_block, &[], else_block, &[]);

    let mut compile_branch = |branch_blk, branch_expr: &TypedExpr| -> bool {
        builder.switch_to_block(branch_blk);
        builder.seal_block(branch_blk);
        cg.push_scope();
        cg.push_temp_scope();
        let val = compile_expr(builder, branch_expr, cg, module);
        let term = builder.is_unreachable() || expr_is_terminator(branch_expr);
        if !term {
            let mut jump_args = Vec::new();
            match res_repr {
                ReprKind::Zst => {}
                ReprKind::Scalar(cl_ty) => {
                    cg.cancel_temp(val);
                    if let TypedExpr::Ident(v, _, _) = branch_expr {
                        cg.mark_moved(builder, v);
                    }
                    jump_args.push(coerce_val(builder, val, cl_ty));
                }
                ReprKind::Aggregate { size, .. } => {
                    cg.cancel_temp(val);
                    if let TypedExpr::Ident(v, v_ty, _) = branch_expr {
                        if !v_ty.is_copy() {
                            cg.mark_moved(builder, v);
                        }
                    }
                    let out_addr = out_addr_opt.unwrap();
                    emit_memcpy_bytes(builder, module, out_addr, val, size);
                }
            }
            cg.pop_temp_scope_and_drop(builder, module);
            cg.pop_scope_and_drop(builder, module);
            builder.ins().jump(exit_block, &jump_args);
        } else {
            cg.pop_temp_scope_without_drop();
            cg.pop_scope_without_drop();
        }
        term
    };

    let then_term = compile_branch(then_block, then_b);
    let else_term = compile_branch(else_block, else_b);

    // EXIT
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    if then_term && else_term {
        let dummy = match res_repr {
            ReprKind::Scalar(types::F32) => builder.ins().f32const(0.0),
            ReprKind::Scalar(types::F64) => builder.ins().f64const(0.0),
            ReprKind::Scalar(cl_ty) => builder.ins().iconst(cl_ty, 0),
            ReprKind::Aggregate { .. } | ReprKind::Zst => builder.ins().iconst(types::I64, 0),
        };
        builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
        dummy
    } else if let Some(out_addr) = out_addr_opt {
        out_addr
    } else if matches!(res_repr, ReprKind::Zst) {
        builder.ins().iconst(types::I64, 0)
    } else {
        builder.block_params(exit_block)[0]
    }
}

fn compile_arm_body<M: Module>(
    builder: &mut FunctionBuilder,
    arm: &TypedMatchArm,
    res_repr: ReprKind,
    out_addr_opt: Option<Value>,
    exit_block: cranelift_codegen::ir::Block,
    cg: &mut CodegenCtx,
    module: &mut M,
) {
    let is_unit = matches!(res_repr, ReprKind::Zst);
    let mut arm_val = builder.ins().iconst(types::I64, 0);
    let mut arm_terminated = false;
    let body_len = arm.body.len();
    for (idx, stmt) in arm.body.iter().enumerate() {
        if builder.is_unreachable() || arm_terminated {
            break;
        }
        cg.push_temp_scope();
        arm_val = compile_expr(builder, stmt, cg, module);
        if builder.is_unreachable() || expr_is_terminator(stmt) {
            cg.pop_temp_scope_without_drop();
            arm_terminated = true;
        } else {
            if idx + 1 == body_len && !is_unit {
                cg.cancel_temp(arm_val);
                if let TypedExpr::Ident(v, v_ty, _) = stmt {
                    if !v_ty.is_copy() {
                        cg.mark_moved(builder, v);
                    }
                }
                if let (ReprKind::Aggregate { size, .. }, Some(out_addr)) = (res_repr, out_addr_opt) {
                    emit_memcpy_bytes(builder, module, out_addr, arm_val, size);
                }
            }
            cg.pop_temp_scope_and_drop(builder, module);
        }
    }

    if !builder.is_unreachable() && !arm_terminated {
        cg.pop_scope_and_drop(builder, module);
        match res_repr {
            ReprKind::Zst | ReprKind::Aggregate { .. } => {
                builder.ins().jump(exit_block, &[]);
            }
            ReprKind::Scalar(cl_ty) => {
                let coerced = coerce_val(builder, arm_val, cl_ty);
                builder.ins().jump(exit_block, &[coerced]);
            }
        }
    } else {
        cg.pop_scope_without_drop();
    }
}

pub fn compile_match<M: Module>(
    builder: &mut FunctionBuilder,
    target: &TypedExpr,
    arms: &[TypedMatchArm],
    cg: &mut CodegenCtx,
    ty: &Type,
    module: &mut M,
) -> Value {
    let res_repr = repr_kind(ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);

    let is_ref_target = matches!(target.ty(), Type::Ref(_) | Type::MutRef(_));
    let unwrapped_target_ty = match target.ty() {
        Type::Ref(inner) | Type::MutRef(inner) => *inner,
        other => other,
    };

    let is_npo = match unwrapped_target_ty {
        Type::Enum(n) => is_npo_enum(n),
        _ => false,
    };

    let exit_block = builder.create_block();
    let out_addr_opt = match res_repr {
        ReprKind::Aggregate { size, align } => Some(alloc_stack_slot(builder, size, align).1),
        ReprKind::Scalar(cl_ty) => {
            builder.append_block_param(exit_block, cl_ty);
            None
        }
        ReprKind::Zst => None,
    };

    if is_npo {
        let raw_ptr_val = compile_expr(builder, target, cg, module);
        for arm in arms {
            let arm_block = builder.create_block();
            let next_check_block = builder.create_block();

            if arm.variant_name.ends_with("None") || arm.tag == 1 {
                let is_match = builder.ins().icmp_imm(IntCC::Equal, raw_ptr_val, 0);
                builder
                    .ins()
                    .brif(is_match, arm_block, &[], next_check_block, &[]);
            } else if arm.variant_name.ends_with("Some") || arm.tag == 0 {
                let is_match = builder.ins().icmp_imm(IntCC::NotEqual, raw_ptr_val, 0);
                builder
                    .ins()
                    .brif(is_match, arm_block, &[], next_check_block, &[]);
            } else {
                builder.ins().jump(arm_block, &[]);
            }

            builder.switch_to_block(arm_block);
            builder.seal_block(arm_block);

            cg.push_scope();
            for (b_name, b_ty) in &arm.bindings {
                if b_name != "_" {
                    let var = cranelift_frontend::Variable::from_u32(cg.var_counter as u32);
                    cg.var_counter += 1;
                    builder.declare_var(var, types::I64);
                    builder.def_var(var, raw_ptr_val);
                    cg.bind_var(b_name, var, *b_ty);
                }
            }

            compile_arm_body(builder, arm, res_repr, out_addr_opt, exit_block, cg, module);

            builder.switch_to_block(next_check_block);
            builder.seal_block(next_check_block);
        }

        if builder.is_unreachable() {
            return raw_ptr_val;
        }

        let dummy_zero = builder.ins().iconst(types::I64, 0);
        builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());

        builder.switch_to_block(exit_block);
        builder.seal_block(exit_block);

        return if let Some(out_addr) = out_addr_opt {
            out_addr
        } else if matches!(res_repr, ReprKind::Zst) {
            dummy_zero
        } else {
            builder.block_params(exit_block)[0]
        };
    }

    let target_ptr = compile_expr(builder, target, cg, module);
    let is_self_ident = matches!(target, TypedExpr::Ident(n, _, _) if n == "self");
    let self_is_consuming = cg.drop_flags.contains_key("self");
    let is_owned_target = !is_ref_target
        && (!is_self_ident || self_is_consuming)
        && !matches!(
            target,
            TypedExpr::FieldAccess(..) | TypedExpr::IndexAccess(..) | TypedExpr::Deref(..)
        );
    if is_owned_target {
        cg.cancel_temp(target_ptr);
        if let TypedExpr::Ident(v_name, v_ty, _) = target {
            if !v_ty.is_copy() {
                cg.mark_moved(builder, v_name);
            }
        }
    }
    let enum_variants = match unwrapped_target_ty {
        Type::Enum(n) | Type::Obj(n) => find_enum_layout(n, cg.meta.enum_layouts).cloned(),
        _ => None,
    };

    let tag_val = builder
        .ins()
        .load(types::I64, MemFlags::new(), target_ptr, 0);

    for arm in arms {
        let arm_block = builder.create_block();
        let next_check_block = builder.create_block();

        if arm.tag == -1 {
            builder.ins().jump(arm_block, &[]);
        } else {
            let expected_tag = builder.ins().iconst(types::I64, arm.tag);
            let is_match = builder.ins().icmp(IntCC::Equal, tag_val, expected_tag);
            builder
                .ins()
                .brif(is_match, arm_block, &[], next_check_block, &[]);
        }

        builder.switch_to_block(arm_block);
        builder.seal_block(arm_block);

        cg.push_scope();
        if arm.tag == -1 {
            if is_owned_target {
                emit_drop_for_value(
                    builder,
                    target_ptr,
                    &target.ty(),
                    &cg.meta.known_drop_fns,
                    &cg.meta.struct_layouts,
                    cg.meta.enum_layouts,
                    module,
                );
            }
        } else {
            let variant_payload_tys = enum_variants
                .as_ref()
                .and_then(|vs| vs.iter().find(|(_, tag, _)| *tag == arm.tag))
                .map(|(_, _, pts)| pts.as_slice());
            let payload_tys_for_layout: Vec<Type> = variant_payload_tys
                .map(|s| s.to_vec())
                .unwrap_or_else(|| arm.bindings.iter().map(|(_, t)| *t).collect());
            let (_, _, offsets) = enum_variant_offsets(
                &payload_tys_for_layout,
                &cg.meta.struct_layouts,
                cg.meta.enum_layouts,
            );

            for (idx, (b_name, b_ty)) in arm.bindings.iter().enumerate() {
                let off = offsets.get(idx).copied().unwrap_or(((idx + 1) * 8) as u32);
                let field_addr = builder.ins().iadd_imm(target_ptr, off as i64);

                if b_name != "_" {
                    let var = cranelift_frontend::Variable::from_u32(cg.var_counter as u32);
                    cg.var_counter += 1;
                    if is_aggregate_type(b_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts) {
                        let (b_size, b_align) =
                            size_and_align(b_ty, &cg.meta.struct_layouts, cg.meta.enum_layouts);
                        let (_, b_slot_addr) = alloc_stack_slot(builder, b_size, b_align);
                        emit_memcpy_bytes(builder, module, b_slot_addr, field_addr, b_size);
                        builder.declare_var(var, types::I64);
                        builder.def_var(var, b_slot_addr);
                        cg.bind_var(b_name, var, *b_ty);
                    } else {
                        let target_c_ty = cranelift_type_of(b_ty);
                        let payload_val =
                            builder
                                .ins()
                                .load(target_c_ty, MemFlags::new(), target_ptr, off as i32);
                        builder.declare_var(var, target_c_ty);
                        builder.def_var(var, payload_val);
                        cg.bind_var(b_name, var, *b_ty);
                        cg.track_addr_taken_slot(builder, b_name, b_ty, target_c_ty, payload_val);
                    }
                    if is_owned_target {
                        cg.track_var_if_droppable(builder, b_name, b_ty, true);
                    }
                } else if is_owned_target {
                    let p_ty = variant_payload_tys
                        .and_then(|pts| pts.get(idx).copied())
                        .unwrap_or(*b_ty);
                    if has_drop_glue(
                        &p_ty,
                        &cg.meta.known_drop_fns,
                        &cg.meta.struct_layouts,
                        cg.meta.enum_layouts,
                    ) {
                        let drop_arg = if is_aggregate_type(
                            &p_ty,
                            &cg.meta.struct_layouts,
                            cg.meta.enum_layouts,
                        ) {
                            field_addr
                        } else {
                            builder.ins().load(
                                cranelift_type_of(&p_ty),
                                MemFlags::new(),
                                target_ptr,
                                off as i32,
                            )
                        };
                        emit_drop_for_value(
                            builder,
                            drop_arg,
                            &p_ty,
                            &cg.meta.known_drop_fns,
                            &cg.meta.struct_layouts,
                            cg.meta.enum_layouts,
                            module,
                        );
                    }
                }
            }

            if is_owned_target {
                if let Some(pts) = variant_payload_tys {
                    for (idx, p_ty) in pts.iter().enumerate().skip(arm.bindings.len()) {
                        if has_drop_glue(
                            p_ty,
                            &cg.meta.known_drop_fns,
                            &cg.meta.struct_layouts,
                            cg.meta.enum_layouts,
                        ) {
                            let off = offsets.get(idx).copied().unwrap_or(((idx + 1) * 8) as u32);
                            let drop_arg = if is_aggregate_type(
                                p_ty,
                                &cg.meta.struct_layouts,
                                cg.meta.enum_layouts,
                            ) {
                                builder.ins().iadd_imm(target_ptr, off as i64)
                            } else {
                                builder.ins().load(
                                    cranelift_type_of(p_ty),
                                    MemFlags::new(),
                                    target_ptr,
                                    off as i32,
                                )
                            };
                            emit_drop_for_value(
                                builder,
                                drop_arg,
                                p_ty,
                                &cg.meta.known_drop_fns,
                                &cg.meta.struct_layouts,
                                cg.meta.enum_layouts,
                                module,
                            );
                        }
                    }
                }
            }
        }

        compile_arm_body(builder, arm, res_repr, out_addr_opt, exit_block, cg, module);

        builder.switch_to_block(next_check_block);
        builder.seal_block(next_check_block);
    }

    if !builder.is_unreachable() {
        builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
    }

    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);

    if let Some(out_addr) = out_addr_opt {
        out_addr
    } else if matches!(res_repr, ReprKind::Zst) {
        builder.ins().iconst(types::I64, 0)
    } else {
        builder.block_params(exit_block)[0]
    }
}
