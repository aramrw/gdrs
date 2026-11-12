# Design: Rust-Compatible Visibility (`pub`) in GDRS

## 1. Overview

In GDRS today, all functions, structs (`obj`), enums, traits, methods, and struct fields are implicitly public. This spec defines **100% Rust-compatible visibility** for `gdrsc`:
- Everything is **private by default**.
- Visibility is **module-tree-scoped** (a module and all of its descendant submodules can see private items in that module).
- `pub`, `pub(crate)`, `pub(super)`, and `pub use` re-exports work just like Rust.

---

## 2. Visibility Rules (Matching Rust)

### 2.1 Visibility Levels (`Visibility`)
Every item, struct field, and inherent `impl` method carries a `Visibility`:
* **`Private` (default, no modifier):** Visible to the declaring module **and all of its descendant submodules** (`caller_mod.starts_with(decl_mod)`).
* **`pub` (`Pub`):** Visible everywhere, across all modules and crates (`std` and user code).
* **`pub(crate)` (`PubCrate`):** Visible anywhere within the same crate (`std` items are visible throughout `std`; user program items are visible throughout the user program).
* **`pub(super)` (`PubSuper`):** Visible to the parent module of the declaring module and all of its descendants (`caller_mod.starts_with(parent(decl_mod))`).

### 2.2 Structs (`obj`) & Fields
* Fields default to private; mark public fields with `pub field: T`.
* **Field access / mutation (`m.data`):** Rejected with `[E0616]` if `!is_visible(field.vis, struct.module_path, caller_mod)`.
* **Struct literal construction (`Matrix { ... }`):** Rejected with `[E0603]` if *any* field of the struct is not visible from `caller_mod` (even if the caller tries to supply a value for it). Callers must use a `pub` constructor (e.g. `Matrix::new(...)`).

### 2.3 Enums & Variants
* Enums are visible as a unit: if `pub enum Result` is visible, all of its variants (`Ok`, `Err`) are visible. Per-variant `pub` is not allowed.

### 2.4 `impl` Blocks & Methods
* **Inherent `impl Foo:` blocks:** Methods default to private; mark public methods with `pub fn`. Calling a private method from outside emits `[E0624]`.
* **Trait `impl Trait for Foo:` blocks:** Trait impl methods automatically share the visibility of `Trait` (no `pub` needed or allowed on individual trait impl methods).

### 2.5 Traits & Trait Bounds
* `trait` declarations default to private; mark public traits with `pub trait`.

### 2.6 Re-exports (`pub use`)
* `use path::Item` imports `Item` privately into the current module (cannot be re-imported by callers of the current module).
* `pub use path::Item` (and `pub use path::{A, B}`) re-exports `Item` with `pub` visibility under the current module's path, provided `Item` is visible from the current module.

### 2.7 `extern "C"` & `type` Aliases
* `extern "C"` declarations and `type` trait aliases follow the same default-private / `pub` rules.

---

## 3. Compiler Architecture

### Phase 1: Lexer & AST (`src/ast/mod.rs`)
1. Add `Token::Pub` (`#[token("pub")]`), `Token::Crate` (`#[token("crate")]`), and `Token::Super` (`#[token("super")]`).
2. Add `Visibility` enum (`Private`, `Pub`, `PubCrate`, `PubSuper`).
3. Add `vis: Visibility` and `module_path: Vec<String>` to:
   * `StructDecl`, `FieldDecl`, `EnumDecl`, `FuncDecl`, `TraitDecl`, `TraitAliasDecl`, `ExternFnDecl`, `UseDecl`.
4. Add `is_trait_impl: bool` (or preserve `trait_name: Option<String>`) on lowered `FuncDecl`s so trait impl methods are recognized during visibility checks.

### Phase 2: Parser (`src/parser/mod.rs`)
* Parse optional `vis` prefix (`pub`, `pub(crate)`, `pub(super)`) before:
  * Top-level declarations (`obj`, `enum`, `fn`, `trait`, `type`, `use`, `extern "C"` functions).
  * Struct fields (`pub rows: i32`).
  * Methods inside `impl` blocks (`pub fn ...`).

### Phase 3: Module Loader (`src/loader/files.rs` & `src/loader/mod.rs`)
* Stamp every parsed item with its `module_path: Vec<String>` (e.g. `["std", "math", "matrix"]`, `[]` for entry file).
* Resolve `use` and `pub use` paths with visibility checking:
  * An imported item must be visible to the importing module (`is_visible`).
  * `pub use` creates a visible alias/re-export entry at the current `module_path` so downstream modules can `use` it.

### Phase 4: Semantic Analysis (`src/sanal/`)
Track `caller_mod: &[String]` from the enclosing `FuncDecl.module_path` (defaulting to `[]` for top-level/entry) and enforce `is_visible` at:
1. **Type resolution (`sanal/mod.rs`, `sanal/vars.rs`):** Referring to a private `obj`, `enum`, or `trait` from another module emits `[E0603]`.
2. **Field access (`sanal/objects.rs`):** Accessing or assigning a non-visible field emits `[E0616]`.
3. **Struct literal construction (`sanal/objects.rs`):** Constructing a struct with any non-visible field emits `[E0603]`.
4. **Function & method calls (`sanal/calls.rs`):** Calling a non-visible free function emits `[E0603]`; calling a non-visible inherent method emits `[E0624]`.

---

## 4. Standard Library (`std/`) Migration & Verification

1. Mark all public types, traits, constructors, and public methods/fields in `std/*.gdrs` with `pub` (keeping internal representation fields like `Vec.{ptr, len, cap}`, `String.{ptr, len, cap}`, and `Matrix.data` private).
2. Keep single-file examples/tests working automatically (since `main()` and its types share `module_path = []`).
3. Add multi-module positive & negative tests (`E0603`, `E0616`, `E0624`, `pub use`, `pub(crate)`, `pub(super)`, child-module access to parent private items).
