//! codegen/intrinsics.rs
//! Central dispatcher for compiler intrinsic macro calls (`name!(args...)`).

use std::collections::HashMap;

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};

use crate::ast::{Type, TypedExpr};
use crate::codegen::expr::compile_expr;
use crate::sanal::StructLayout;

/// Type Tag ABI:
/// 0 = Int (i64)
/// 1 = Bool (1 = true, 0 = false)
/// 2 = String (*const c_char pointer)
pub extern "C" fn intrinsic_log(type_tag: u64, value_bits: u64) -> i64 {
    match type_tag {
        0 => println!("{}", value_bits as i64),
        1 => println!("{}", value_bits != 0),
        2 => {
            let ptr = value_bits as *const std::os::raw::c_char;
            if ptr.is_null() {
                println!("<null>");
            } else {
                let c_str = unsafe { std::ffi::CStr::from_ptr(ptr) };
                println!("{}", c_str.to_string_lossy());
            }
        }
        3 => println!("{}", f64::from_bits(value_bits)),
        _ => println!("<unknown type 0x{:x}: 0x{:x}>", type_tag, value_bits),
    }
    0
}

use std::sync::atomic::{AtomicUsize, Ordering};
static STR_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn compile_string_constant(
    builder: &mut FunctionBuilder,
    s: &str,
    _var_counter: &mut usize,
    module: &mut JITModule,
) -> Value {
    use cranelift_module::DataDescription;
    let mut data_ctx = DataDescription::new();
    let mut bytes = s.as_bytes().to_vec();
    bytes.push(0);
    data_ctx.define(bytes.into_boxed_slice());

    let name = format!("__str_{}", STR_COUNTER.fetch_add(1, Ordering::SeqCst));

    let data_id = module
        .declare_data(&name, Linkage::Export, true, false)
        .unwrap();
    module.define_data(data_id, &data_ctx).unwrap();

    let local_data = module.declare_data_in_func(data_id, builder.func);
    builder.ins().symbol_value(types::I64, local_data)
}

/// Central dispatcher for all compiler macro intrinsics (`macro_name!(...)`)
pub fn compile_macro_call(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[TypedExpr],
    vars: &mut HashMap<String, Variable>,
    var_counter: &mut usize,
    module: &mut JITModule,
    struct_layouts: &HashMap<String, StructLayout>,
) -> Value {
    match name {
        "log" | "println" => {
            let mut last_val = builder.ins().iconst(types::I64, 0);
            for arg in args {
                let type_tag = match arg.ty() {
                    Type::Int => 0,
                    Type::Bool => 1,
                    Type::String => 2,
                    Type::Float => 3,
                    Type::Unit | Type::Obj(_) | Type::Enum(_) | Type::Array(_, _) => 0,
                };

                let type_tag_val = builder.ins().iconst(types::I64, type_tag);
                let raw_val = compile_expr(builder, arg, vars, var_counter, module, struct_layouts);

                let value_bits = if arg.ty() == Type::Float {
                    builder.ins().bitcast(types::I64, MemFlags::new(), raw_val)
                } else {
                    raw_val
                };

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64)); // type_tag
                sig.params.push(AbiParam::new(types::I64)); // value_bits
                sig.returns.push(AbiParam::new(types::I64));

                let callee = module
                    .declare_function("intrinsic_log", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                let call_inst = builder.ins().call(local_callee, &[type_tag_val, value_bits]);
                last_val = builder.inst_results(call_inst)[0];
            }
            last_val
        }
        "typeof" => {
            let mut last_val = builder.ins().iconst(types::I64, 0);
            for arg in args {
                let type_name = match arg.ty() {
                    Type::Int => "Int",
                    Type::Float => "Float",
                    Type::Bool => "Bool",
                    Type::String => "String",
                    Type::Unit => "Unit",
                    Type::Obj(name) => name,
                    Type::Enum(name) => name,
                    Type::Array(_, _) => "Array",
                };

                let ptr_val = compile_string_constant(builder, type_name, var_counter, module);
                let type_tag_val = builder.ins().iconst(types::I64, 2);

                let mut sig = module.make_signature();
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));

                let callee = module
                    .declare_function("intrinsic_log", Linkage::Import, &sig)
                    .unwrap();
                let local_callee = module.declare_func_in_func(callee, builder.func);
                let call_inst = builder.ins().call(local_callee, &[type_tag_val, ptr_val]);
                last_val = builder.inst_results(call_inst)[0];
            }
            last_val
        }
        _ => panic!("Unknown intrinsic macro: '{name}!'"),
    }
}

