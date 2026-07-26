# GDRS

A compiled programming language featuring Python/Nim-style indented syntax with Rust-like type semantics, compiled to native machine code via Cranelift.

## Usage

Run scripts using Cargo or `build.nu`:

```bash
cargo run -- run examples/option.gdrs
```

## Features

- **Indented Syntax**: Python/Nim-style block indentation combined with Rust-like keywords (`fn`, `let mut`, `obj`, `impl`, `enum`, `use`).
- **Type System**: Primitive types (`i32`, `i64`, `f32`, `f64`, `bool`, `str`), explicit structs (`obj`), enums with payload variants, references (`&`, `&mut`), and unsafe pointers (`*const`, `*mut`).
- **Standard Library**:
  - `std::core`: `Option`, `Result`
  - `std::math`: Vector types (`Vec2`) and mathematical operations
  - `std::collections`: Resizable arrays (`Vec`)
  - `std::fs`: File system I/O (reading, writing, file inspection)
  - `std::time`: High-resolution timers (`Instant`)
- **C FFI**: Foreign function interface supporting `extern "C"` declarations for calling dynamic libraries (e.g., Raylib).
- **Control Flow & Functions**: Free functions, `impl` method blocks, closures, `while` loops, conditional branching (`if`/`else`), and `match` expressions.
- **Backend**: Type checking with semantic analysis, emitting native assembly via Cranelift IR.

## Code Example

```gdrs
use std::core::{Result as Res, Option as Opt}

obj Vec2:
    x: f32
    y: f32

impl Vec2:
    fn add(&self, other: Vec2) -> Vec2:
        return Vec2{x: self.x + other.x, y: self.y + other.y}

fn main():
    let v1 = Vec2{x: 10.0, y: 20.0}
    let v2 = Vec2{x: 5.0, y: 5.0}
    let v3 = v1.add(v2)
    log!("v3.x:", v3.x, "v3.y:", v3.y)

    let res = Res::Ok(42)
    log!("res:", res.unwrap())
```

## Roadmap

- **Semantic Monomorphization**: Substitute generic type parameters during semantic analysis to generate specialized, zero-cost layouts for generic structs (`Vec2<T>`) and enums (`Option<T>`, `Result<T, E>`).
- **Pattern Matching**: Complete pattern matching support for generic enum destructuring and nested patterns.
- **Standard Library Expansion**: Add memory management utilities, string manipulation functions, and process handling.
- **AOT Compilation**: Support ahead-of-time compilation to produce standalone binary executables alongside JIT mode.
