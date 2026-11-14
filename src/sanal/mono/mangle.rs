//! sanal/mono/mangle.rs
//! Type mangling, type suffixes, and registry of mangled generic symbols.

use crate::ast::Type;
use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

static MANGLED_REGISTRY: LazyLock<Mutex<HashMap<String, (String, Vec<Type>)>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

pub fn lookup_mangled(mangled: &str) -> Option<(String, Vec<Type>)> {
    MANGLED_REGISTRY.lock().ok()?.get(mangled).cloned()
}

pub fn type_suffix(ty: &Type) -> String {
    match ty {
        Type::Int => "i64".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I8 => "i8".to_string(),
        Type::U64 => "u64".to_string(),
        Type::U32 => "u32".to_string(),
        Type::U16 => "u16".to_string(),
        Type::U8 => "u8".to_string(),
        Type::Float => "f64".to_string(),
        Type::F32 => "f32".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str => "str".to_string(),
        Type::String => "string".to_string(),
        Type::Unit => "unit".to_string(),
        Type::Obj(n) | Type::Enum(n) | Type::Generic(n) | Type::DynTrait(n) => {
            n.replace("::", "_").to_lowercase()
        }
        Type::Array(t, len) => format!("arr_{}_{len}", type_suffix(t)),
        Type::Tuple(tys) => {
            let parts: Vec<String> = tys.iter().map(type_suffix).collect();
            format!("tup_{}", parts.join("_"))
        }
        Type::Slice(t) => format!("slice_{}", type_suffix(t)),
        Type::Vec(t) => format!("vec_{}", type_suffix(t)),
        Type::Box(t) => format!("box_{}", type_suffix(t)),
        Type::Rc(t) => format!("rc_{}", type_suffix(t)),
        Type::Arc(t) => format!("arc_{}", type_suffix(t)),
        Type::FnPtr(params, ret) => {
            let ps: Vec<String> = params.iter().map(type_suffix).collect();
            format!("fn_{}_ret_{}", ps.join("_"), type_suffix(ret))
        }
        Type::Void => "void".to_string(),
        Type::Ptr(t) => format!("ptr_{}", type_suffix(t)),
        Type::Ref(t) => format!("ref_{}", type_suffix(t)),
        Type::MutRef(t) => format!("mutref_{}", type_suffix(t)),
        Type::Infer(id) => format!("infer_{id}"),
        Type::Error => "error".to_string(),
    }
}

pub fn mangle_name(base: &str, type_args: &[Type]) -> String {
    if type_args.is_empty() {
        base.to_string()
    } else {
        let suffixes: Vec<String> = type_args.iter().map(type_suffix).collect();
        let mangled = format!("{}_{}", base, suffixes.join("_"));
        if let Ok(mut reg) = MANGLED_REGISTRY.lock() {
            reg.entry(mangled.clone())
                .or_insert_with(|| (base.to_string(), type_args.to_vec()));
        }
        mangled
    }
}

pub fn mangle_name_update(base: &str, type_args: &[Type]) -> String {
    if type_args.is_empty() {
        base.to_string()
    } else {
        let suffixes: Vec<String> = type_args.iter().map(type_suffix).collect();
        let mangled = format!("{}_{}", base, suffixes.join("_"));
        if let Ok(mut reg) = MANGLED_REGISTRY.lock() {
            reg.insert(mangled.clone(), (base.to_string(), type_args.to_vec()));
        }
        mangled
    }
}

pub fn register_intrinsic_mangled(base: &str, ty: Type) -> String {
    let mangled = format!("{base}::{ty:?}");
    if let Ok(mut reg) = MANGLED_REGISTRY.lock() {
        reg.insert(mangled.clone(), (base.to_string(), vec![ty]));
    }
    mangled
}

