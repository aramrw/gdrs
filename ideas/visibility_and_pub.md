# Design: Public vs. Private Visibility (`pub`) in GDRS

## 1. Overview

In systems programming, **encapsulation** is essential to prevent data invariants from being violated and to maintain stable API boundaries.

In GDRS today, all functions, structs, enums, traits, methods, and struct fields are implicitly public. This creates two immediate risks:
1. **Safety & Invariants**: Complex types like `Vec<T>` (`ptr`, `len`, `cap`) and `Matrix` (`data`, `rows`, `cols`) can have their internal state corrupted by external code (e.g. `m.rows = 999` without resizing `m.data`).
2. **The "Private by Default" Breaking-Change Trap**: If visibility is introduced late after extensive code is written, turning on private-by-default breaks every file across the ecosystem unless retrofitted with `pub`.

This document specifies the design for Rust-compatible visibility in GDRS.

---

## 2. Core Visibility Rules (Matching Rust)

### Rule 1: Private by Default
Any item, field, or method without an explicit `pub` modifier is private to its declaring module.

```gdrs
// std/math/matrix.gdrs
pub obj Matrix:
    pub rows: i32
    pub cols: i32
    data: Vec<f64> // private to std::math::matrix!

pub fn helper(): // public to importers
    ...

fn internal_compute(): // private to std::math::matrix
    ...
```

### Rule 2: Module-Scoped Privacy (The Intra-Module Exception)
Inside the **same module/file**, all code has full access to all private items, methods, and struct fields declared in that module.
- Single-file scripts and test files (`examples/test.gdrs`) will **not** be broken by private-by-default, because their `main()` function lives in the same module as the structs it defines.
- Privacy boundaries only take effect when crossing module/file boundaries (`use ...`).

### Rule 3: Struct Field Privacy & Constructor Enforcement
If a struct has **at least one private field**:
- External modules **cannot access or mutate** that field (`m.data` -> `[E0616] field 'data' is private`).
- External modules **cannot instantiate the struct using a struct literal** (`Matrix { rows: 1, cols: 1, data: v }` -> `[E0603] cannot construct 'Matrix' directly; field 'data' is private`).
- External modules **must** call a public constructor (e.g. `Matrix::new(...)`, `Matrix::zeros(...)`, `Matrix::from_vec(...)`).

### Rule 4: Enum Variant Visibility
Enums are public as an atomic unit: if `pub enum Result<T, E>` is marked `pub`, all of its variants (`Ok(T)`, `Err(E)`) are automatically public.

### Rule 5: Methods in `impl` Blocks
- In inherent `impl Foo:` blocks, methods default to private unless marked `pub fn`.
- In trait `impl Trait for Foo:` blocks, methods automatically inherit the visibility of `Trait` (they cannot be made private).

### Rule 6: Re-exporting (`pub use`)
Modules can re-export items from submodules:
```gdrs
// std/math.gdrs
pub use matrix::Matrix
pub use matrix::MatrixError
```
This allows consumers to write `use std::math::Matrix` without knowing the internal file structure.

---

## 3. Implementation Architecture in `gdrsc`

### Phase 1: Lexer & AST
1. Add `Token::Pub` (`#[token("pub")]`) to `src/ast/mod.rs`.
2. Add `is_pub: bool` to AST definitions:
   - `StructDecl { is_pub: bool, ... }`
   - `FieldDecl { is_pub: bool, ... }`
   - `EnumDecl { is_pub: bool, ... }`
   - `FuncDecl { is_pub: bool, ... }`
   - `TraitDecl { is_pub: bool, ... }`
   - `UseDecl { is_pub: bool, ... }`

### Phase 2: Parser (`src/parser/`)
- In `src/parser/mod.rs`, parse optional `Token::Pub` before item declarations.
- In struct field parser, parse optional `Token::Pub` before each field definition:
  ```gdrs
  pub obj Matrix:
      pub rows: i32
      data: Vec<f64>
  ```

### Phase 3: Module Loader (`src/loader/files.rs`)
- Each parsed item is stamped with `module_path: String` (e.g. `"std::math::matrix"` or `""` for root crate).
- When resolving `use path::Item`:
  - Check if `Item.is_pub || Item.module_path == current_file.module_path`.
  - If not, emit `[E0603] Error: struct 'Item' in module 'path' is private`.

### Phase 4: Semantic Analysis Checks (`src/sanal/`)
1. **Field Access (`m.data`)**:
   In `src/sanal/objects.rs` (`type_check_field_access`):
   ```rust
   if !field.is_pub && struct_def.module_path != current_module {
       errors.push(SemanticError {
           code: "E0616",
           message: format!("Field '{}' of type '{}' is private", field_name, struct_name),
           ...
       });
   }
   ```
2. **Struct Literal Construction (`Matrix { ... }`)**:
   In `src/sanal/objects.rs` (`type_check_obj_init`):
   If any field has `!field.is_pub` and `struct_def.module_path != current_module`:
   Emit `[E0603] Cannot construct struct '{}' directly because field '{}' is private. Use a constructor function instead.`
3. **Method Calls (`m.internal_helper()`)**:
   In `src/sanal/calls.rs` (`type_check_method_call`):
   If `!method.is_pub && method.module_path != current_module`:
   Emit `[E0624] Method '{}' of type '{}' is private`.

---

## 4. Rollout Strategy

1. **Step 1**: Add `pub` keyword to lexer and parser. Mark items with `is_pub`.
2. **Step 2**: Mark all public APIs in `std/` (`std::vec::Vec`, `std::math::matrix::Matrix`, `std::string::String`, etc.) as `pub`.
3. **Step 3**: Turn on compiler enforcement in `sanal` and verify existing tests pass.
