# Result Unwrapping & Raylib Bouncing Balls Analysis

This document details every step taken during the investigation of `Result::unwrap()`, why the initial backend fixes broke the Raylib bouncing balls animation, and how to cleanly resolve both issues without side effects.

---

## 1. Overview & Context

- **The Symptom**: In `examples/option.gdrs`, `Res::Ok(777).unwrap()` returned `4650045780097236992` instead of `777`.
- **The Observation**: `Option::Some(1).unwrap()` appeared to work, leading to confusion as to why `Option` and `Result` behaved differently despite similar enum definitions in `std/core.gdrs`.
- **The Side-Effect**: Fixing the generic type mapping to return integer `777` caused the balls in `examples/raylib/raylib.gdrs` to either fly off-screen or freeze at `(0, 0)`.

---

## 2. Step-by-Step Breakdown of the Initial Fix

### Step 1: Investigating `Type::Generic(_)` Mapping
In `src/codegen/expr.rs`, the function `cranelift_type_of(ty: &Type)` contained the following mapping:
```rust
pub fn cranelift_type_of(ty: &Type) -> cranelift_codegen::ir::Type {
    match ty {
        Type::I32 => types::I32,
        Type::Int => types::I64,
        Type::F32 => types::F32,
        Type::Float => types::F64,
        Type::Bool => types::I8,
        Type::Generic(_) => types::F64, // <-- Mapped all generic payload parameters to F64!
        _ => types::I64,
    }
}
```
When constructing `Res::Ok(777)`, `777` was an integer (`Type::Int`), but `Res::Ok($T)` had generic type `$T`. Because `Type::Generic(_)` mapped to `types::F64`, Cranelift converted integer `777` to float `777.0` (`0x4088480000000000`). When `unwrap()` loaded the payload, it printed `0x4088480000000000` as an integer: `4650045780097236992`.

### Step 2: Fixing Generic Type Payload to `types::I64`
Changing `Type::Generic(_)` to `types::I64` ensured that generic payloads (`Option<T>` / `Result<T, E>`) stored 64-bit integer values as true integers without float conversion. This fixed `Res::Ok(777).unwrap()` to return `777`.

### Step 3: Resolving Import Alias Constructors (`Res::Ok`)
In `examples/option.gdrs`, `Result` was imported with an alias:
```gdrs
use std::core::{Result as Res, Option as Opt}
```
`Some(1)` resolved directly to `std_core_Option_Some`. But `Res::Ok(777)` was parsed as `"Res::Ok"`. In `src/sanal/calls.rs`, constructor lookup searched for `"Res"` in `enum_map`, which failed because `enum_map` registered the enum under its full canonical name `"std_core_Result"`. As a result, `Res::Ok` failed to construct a `TypedExpr::EnumConstruct` node.

Fixing `src/sanal/calls.rs` to match variant names (`"Ok"`, `"Err"`, `"Some"`, `"None"`) directly across `enum_map` enabled alias constructors like `Res::Ok` to generate valid `EnumConstruct` AST nodes.

---

## 3. Why the `Result` Fix Broke Raylib (The Root Cause)

`Vec2` in `std/math.gdrs` is defined with generic fields:
```gdrs
obj Vec2 where $T: Add:
	x: $T
	y: $T
```

In `examples/raylib/raylib.gdrs`, `Vec2` is initialized with float coordinates:
```gdrs
let pos = Vec2.new(50.0, 100.0)
let speed = Vec2.new(3.0, 4.0)
```

When `Type::Generic(_)` was changed to `types::I64`, three severe breakdown points occurred in Raylib:

### Breakdown Point 1: Float Truncation in Field Assignment
When `50.0` (`F32` float) was stored into `Vec2`'s field `x` (type `$T`):
`coerce_val` in `src/codegen/expr.rs` saw `val_ty == types::F32` and `target_ty == types::I64`. It executed `fcvt_to_sint(types::I64, val)` (float-to-int truncation), converting `50.0` float down to integer `50`.

### Breakdown Point 2: Integer Arithmetic on Float Bit Patterns
When `self.pos.x += self.speed.x` was compiled:
- `self.pos.x` and `self.speed.x` were loaded as Cranelift `types::I64` generic slots holding float bit patterns (`50.0` = `0x4049000000000000`, `3.0` = `0x4008000000000000`).
- Because Cranelift saw `lt == types::I64` and `rt == types::I64`, binary addition emitted **integer addition (`iadd`)** instead of float addition (`fadd`).
- Adding raw float bits with integer addition produced `0x4049000000000000 + 0x4008000000000000 = 0x8051000000000000` (`-9193817164300156928`), completely corrupting the position data!

### Breakdown Point 3: Raylib Foreign Function Call Truncation
Raylib's drawing function expects 32-bit integers:
```gdrs
fn DrawCircle(centerX: i32, centerY: i32, radius: f32, color_hex: i32)
```
When `ball.pos.x` (holding a 64-bit float bit pattern `0x4049000000000000`) was passed to `centerX: i32`:
`coerce_val` called `ireduce(types::I32, val)` to shrink 64-bit `I64` to 32-bit `I32`. This stripped the upper 32 exponent bits (`0x40490000`), leaving lower bits `0x00000000` (`0`). `DrawCircle` received `centerX = 0` and `centerY = 0`, drawing all 10 balls at `(0, 0)` in the top-left corner!

---

## 4. Architectural Plan for a Clean Long-Term Fix

To cleanly support both generic integer types (`Result<i64, E>`, `Option<i64>`) and generic float types (`Vec2<f32>`), we should implement **Monomorphization** in the semantic analyzer:

1. **Concrete Generic Substitution**: During `sanal`, when `Vec2.new(50.0, 100.0)` is instantiated, substitute `$T` -> `Type::F32` so field `x` has concrete type `Type::F32` instead of remaining `Type::Generic("T")`.
2. **Explicit C ABI Casts**: Automatically insert `TypedExpr::CastI32` when passing float fields (`f32`/`f64`) to `i32` FFI parameters (`DrawCircle`), ensuring `fcvt_to_sint` is explicitly emitted for foreign function calls.
3. **Clean Codegen**: Keep `cranelift_type_of(Type::Generic(_))` mapped to `types::I64` for un-monomorphized pointers, while monomorphized fields use their exact concrete scalar types (`types::F32` / `types::I64`).

To clarify: **Monomorphization is NOT hardcoding `Vec2` to `f32`**. 

Hardcoding `Vec2` to `f32` *would* be a hotfix and would indeed break `Vec2` if someone instantiated `Vec2.new(10, 20)` (integers) or `Vec2.new("hello", "world")` (strings).

### What True Monomorphization Does (Rust / C++ Model)

True monomorphization dynamically inspects the **actual argument types** passed at the callsite and substitutes `$T` with that exact concrete type during semantic analysis:

| Code Written by User | Inferred Type for `$T` | Concrete Struct Generated | Field `x` / `y` Types | Cranelift IR Generated |
| :--- | :--- | :--- | :--- | :--- |
| `Vec2.new(50.0, 100.0)` | `Type::F32` | `Vec2_f32` | `Type::F32` | `types::F32`, `fadd`, `fcmp` |
| `Vec2.new(10, 20)` | `Type::Int` (`i64`) | `Vec2_i64` | `Type::Int` | `types::I64`, `iadd`, `icmp` |
| `Vec2.new("a", "b")` | `Type::Str` | `Vec2_str` | `Type::Str` | `types::I64` (pointer) |
| `Res::Ok(777)` | `Type::Int` (`i64`) | `Result_i64` | `Type::Int` | `types::I64`, `iadd` |

---

### Why Monomorphization Eliminates the Bug Completely

Without monomorphization, the compiler tries to treat `$T` as a single uniform scalar type in Cranelift (`types::F64` or `types::I64`). 
- If mapped to `types::F64`, integer generic values (`Result::Ok(777)`) get turned into floats (`4650045780097236992`).
- If mapped to `types::I64`, float generic values (`Vec2.new(50.0, 100.0)`) get corrupted by integer math (`iadd`).

With monomorphization:
1. `Vec2.new(50.0, 100.0)` knows its fields are `Type::F32`, so Cranelift uses float registers and float instructions.
2. `Res::Ok(777)` knows its payload is `Type::Int`, so Cranelift uses integer registers and integer instructions.
3. `Vec2.new("a", "b")` knows its fields are `Type::Str`, so Cranelift uses string pointers.

This is how Rust (`rustc`) and C++ (`templates`) handle generics—it gives zero runtime overhead, 100% type safety, and supports any type for `$T`.

make sure to add a cache too
