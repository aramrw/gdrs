# GDRS Low-Level Foundations Specification (Batch 1 + Closures Blueprint)

This specification defines the immediate low-level fixes and foundations (**Batch 1**) required for C/Zig-level FFI parity, deterministic memory management, explicit pointer APIs, compile-time `const`s, and reliable multi-file modules, followed by the architectural blueprint for **Priority 2: Rust-1:1 Capturing Closures**.

---

## 1. Batch 1 Implementation Specification

### 1.1 macOS ARM64 C-ABI Parity (`src/codegen/layout.rs`, `src/codegen/vtables.rs`)
Goal: Any GDRS `obj` passed or returned by value to/from `extern "C"` functions matches the native platform ABI (`aarch64-apple-darwin` first, marked with `#[cfg(target_arch = "aarch64")]` and `// TODO(cross-platform)` comments for x86_64/Linux/Windows).

1. **Homogeneous Floating-Point Aggregates (HFA)**:
   - On ARM64 AAPCS64, a struct containing **1 to 4 leaf fields all of the same float scalar type** (`f32` or `f64`, with no interior padding) is an HFA and is passed/returned in `F32`/`F64` floating-point registers (`s0..s3` / `d0..d3`), even if total size is 24 bytes (`3 x f64`) or 32 bytes (`4 x f64`).
   - Add `hfa_chunks_for_type(ty, struct_layouts, enum_layouts) -> Option<Vec<cranelift_codegen::ir::Type>>` gated on `#[cfg(target_arch = "aarch64")]`.
   - In `pass_mode_for_type`, when `!force_indirect`, check `hfa_chunks_for_type` *before* checking `size > 16`, returning `PassMode::MultiReg { size, align, chunks }`.
   - Update `load_multireg_chunks` and `store_multireg_chunks` to load/store per-chunk element sizes (`4` bytes for `F32`, `8` bytes for `F64`/`I64`) at cumulative byte offsets (`offset = sum(chunk_bytes)`), allocating an aligned scratch stack slot whenever `size` is not an exact multiple of the chunk stride or `size < total_chunk_bytes`.

2. **ARM64 `sret` in `x8` (`ArgumentPurpose::StructReturn`)**:
   - On ARM64 AAPCS64, C compilers pass the indirect return pointer for aggregates `> 16` bytes (non-HFA) in dedicated register `x8`, whereas `x0` is reserved for normal arguments.
   - Add `pub fn sret_abi_param() -> AbiParam`:
     - On `#[cfg(target_arch = "aarch64")]`: `AbiParam::special(types::I64, cranelift_codegen::ir::ArgumentPurpose::StructReturn)`
     - On other architectures (`// TODO(cross-platform)`): `AbiParam::new(types::I64)`.
   - Use `sret_abi_param()` in `abi_signature_for_fn` (`src/codegen/layout.rs`) and `build_vtable_byval_thunk` (`src/codegen/vtables.rs`).

---

### 1.2 Memory & Type-Safety Fixes (`src/codegen/expr.rs`, `src/sanal/binops.rs`, `std/ops.gdrs`)

1. **`DynCall` Temporary Drop Tracking (`src/codegen/expr.rs`)**:
   - Currently `TypedExpr::DynCall` returns the result of `compile_dyn_call` without registering it in `cg.register_temp(val, ret_ty)`.
   - Registering `cg.register_temp(val, ret_ty)` ensures any droppable owned return value (`String`, `Vec`, `Box`, etc.) from a `dyn Trait` method is dropped at statement end if unused.

2. **Overloaded Operator Validation & `std::ops` Expansion (`src/sanal/binops.rs`, `std/ops.gdrs`)**:
   - Expand `std/ops.gdrs` to declare `Mul`, `Div`, `Rem`, and `Neg` alongside `Add` and `Sub`.
   - In `src/sanal/binops.rs`, unify overloaded operator checking via `try_type_check_overloaded_binop` (`+`, `-`, `*`, `/`, `%` -> `add`, `sub`, `mul`, `div`, `rem`) and `try_type_check_overloaded_unop` (unary `-` -> `neg`).
   - Support resolution on both `Type::Obj(name)` and `Type::Ref(Type::Obj(name))` / `Type::MutRef(Type::Obj(name))`, auto-borrowing operands when the operator method expects `&T` (`Type::Ref`), and validating argument types + move semantics via `crate::sanal::calls::validation::validate_call_arguments` (catching `E0382` use-after-move and `E0308` argument mismatches).

---

### 1.3 Explicit Memory Intrinsics & Raw Pointer APIs (`src/parser/math.rs`, `src/sanal/`, `src/codegen/calls.rs`, `std/mem.gdrs`, `std/vec.gdrs`, `std/libc.gdrs`)

1. **Turbofish Call Syntax `fn::<T>(...)`**:
   - Extend `call_expr` in `src/parser/math.rs` to allow optional `::<T1, T2, ...>` between the call path and `(...)`, mangling the call target with `crate::sanal::mono::mangle_name`.
   - Rewrite/substitute mangled type arguments in `src/loader/mod.rs` (`rewrite_expr`) and `src/sanal/mono/subst.rs` (`substitute_expr`).

2. **`size_of::<T>()` and `align_of::<T>()` Intrinsics**:
   - Declare `pub fn size_of() -> i64` and `pub fn align_of() -> i64` in `std/mem.gdrs`.
   - Handle `size_of` / `std::mem::size_of` and `align_of` / `std::mem::align_of` in `src/sanal/calls/mod.rs` and `src/codegen/calls.rs` (supporting `size_of::<T>()` and `size_of(&val)`), emitting compile-time constants from `crate::codegen::layout::size_and_align`.

3. **Explicit Pointer & Aligned Allocation APIs**:
   - `std/libc.gdrs`: declare `calloc(count: i64, size: i64) -> *void` and `posix_memalign(memptr: *(*void), alignment: i64, size: i64) -> i32`.
   - `std/mem.gdrs`: add `pub fn alloc_aligned(size: i64, align: i64) -> *void`.
   - `std/vec.gdrs`: replace `((0 as *$T) + 1) as i64` with `size_of::<$T>()`, and add `pub fn as_ptr(&self) -> *$T`, `pub fn as_mut_ptr(&mut self) -> *$T`, and `pub fn from_raw_parts(ptr: *$T, len: i64, cap: i64) -> Vec`.

---

### 1.4 Top-Level `const` & IEEE-754 Math Constants

1. **AST, Parser & Loader (`src/ast/mod.rs`, `src/parser/mod.rs`, `src/loader/`)**:
   - Add `Token::Const`, `ConstDecl { name, ty, value, vis, module_path, span }`, and `Program.consts`.
   - Parse `[vis] const NAME: TYPE = EXPR`.
   - Mangle module-scoped `const` names and include `consts` in AST symbol resolution.

2. **Compile-Time Evaluation & Visibility (`src/sanal/`)**:
   - Evaluate `program.consts` into a compile-time `const_map` (`i64`, `u64`, `f64`, `bool`, `str`) with type checking (`E0308`) and visibility enforcement (`E0603`).
   - Resolve `const` identifiers in `src/sanal/vars.rs` to typed literal `TypedExpr` values (`Int`, `Float`, `Bool`, `String`, or `Cast` for sized numeric consts like `i32`/`u8`/`f32`).
   - Support referencing earlier `const` items inside constant expressions (`eval_const_expr`).

3. **IEEE-754 & Math Constants (`std/math/math.gdrs`)**:
   - Add `pub const PI: f64`, `pub const E: f64`, `pub const INFINITY: f64`, `pub const NEG_INFINITY: f64`, `pub const NAN: f64`, `pub const EPSILON: f64`, and helper predicates `is_nan(x: f64) -> bool`, `is_infinite(x: f64) -> bool`, `is_finite(x: f64) -> bool`.

---

### 1.5 AST-Indexed Module Loader (`src/loader/files.rs`, `src/sanal/types.rs`)

1. **AST Symbol Discovery**:
   - Replace `content.contains("obj ...")` / `"enum ..."` / `"fn ..."` / `"trait ..."` substring matching in `src/loader/files.rs` with `file_declares_symbol(&source, sym)` that lexes/parses the candidate file's AST and inspects `structs`, `enums`, `functions`, `traits`, `trait_aliases`, `consts`, `externs`, and `pub use` re-exports.
2. **Transitive `pub use` Re-exports**:
   - Resolve `use` targets through `merged_program.uses` when an imported module re-exports an item with `pub use`.
3. **Intra-Module Sibling Function Resolution**:
   - Update `TypeCtx::get_fn` (`src/sanal/types.rs`) to check `format!("{}_{}", self.caller_mod.join("_"), name)` before falling back to global or `std_` prefix matching, so free functions in the same submodule resolve unambiguously.

---

## 2. Priority 2 Complete Implementation Specification: Rust-1:1 Capturing Closures, `std::ops`, and Lazy Iterators

> **Status**: Batch 1 (Sections 1.1–1.5) is **implemented and verified** (`cargo test` all passing). Section 2 is the complete, "do-once, extend-later" specification for Priority 2 so it can be implemented in the next session without architectural rework.

---

### 2.1 Why Rust's Closure Architecture Wins (vs. Haskell, C++, Swift)

| Model | Low-Level IR / Memory Representation | Pros | Cons for GDRS |
| :--- | :--- | :--- | :--- |
| **Haskell (STG / PAPs)** | Heap-allocated closure header (`info_ptr` + payload pointers); curried partial applications (PAPs). | Uniform representation; effortless currying and higher-order composition. | **Requires a tracing GC**; every captured closure heap-allocates; pointer chasing destroys SIMD/loop vectorization and C FFI compatibility. |
| **C++11/20 Lambdas** | Unboxed anonymous `struct` with `operator()`; explicit capture lists `[&x, y = std::move(y)]`. | Zero-cost, stack-allocated, inlines completely. | **Unsafe by default** (`[&]` silently creates dangling references); verbose capture lists; no unified trait hierarchy until `std::function` (which heap-allocates). |
| **Rust (2021 Edition RFC 2229)** | Unboxed anonymous `struct __ClosureEnv_N` + `FnOnce` / `FnMut` / `Fn` traits + inferred minimal capture mode + `move` keyword + **disjoint field capture**. | **Zero heap allocation**; static dispatch monomorphizes iterator chains into a single loop; dynamic dispatch (`&dyn Fn` / `Box<dyn Fn>`) is explicit; borrow-checked lifetimes prevent dangling captures. | Requires compiler capture-analysis pass and monomorphizing `Fn*` call traits. |

**Decision**: Follow **Rust (2021 Edition)** 1-to-1, including **RFC 2229 disjoint field capture** from day one so we never repeat Rust 2015/2018's mistake where referencing `p.x` inside a closure captured all of `p` instead of just `p.x`.

---

### 2.2 Syntax & AST Specification (`src/ast/mod.rs`, `src/parser/math.rs`, `src/parser/mod.rs`)

#### 1. Closure Expression Syntax
Support both borrowed-capture (default) and `move`-capture closures in both inline and indented/braced block forms:
```gdrs
// 1. Default capture (compiler infers minimal borrow: &T, &mut T, or move if consumed)
let f = |x: i64| x + offset

// 2. Explicit move capture (all captured variables/projections are moved or copied by value into the environment struct)
let g = move |x: i64|:
	return x + owned_vec.len()
```

#### 2. AST Changes (`src/ast/mod.rs`)
- Add `#[token("move")] Move,` to `Token`.
- Extend `Expr::Closure`:
  ```rust
  Expr::Closure {
      is_move: bool,
      params: Vec<String>,
      body: Box<Expr>,
      span: Span,
  }
  ```
- Add capture metadata to `TypedExpr::Closure` (or lower directly to struct init + synthesized methods during `sanal`):
  ```rust
  #[derive(Debug, Clone, Copy, PartialEq, Eq)]
  pub enum CaptureMode {
      ByRef,      // &T      -> closure implements Fn, FnMut, FnOnce
      ByMutRef,   // &mut T  -> closure implements FnMut, FnOnce
      ByValue,    // T       -> closure implements FnOnce (and Fn/FnMut if T: Copy and not mutated)
  }

  #[derive(Debug, Clone)]
  pub struct ClosureCapture {
      pub field_name: String,       // e.g. "__cap_0"
      pub root_var: String,         // e.g. "p"
      pub projection: Vec<String>,  // e.g. ["x"] for disjoint capture `p.x` (empty if whole var)
      pub mode: CaptureMode,
      pub captured_ty: Type,        // Type of the field in __ClosureEnv_N (&T, &mut T, or T)
      pub span: Span,
  }
  ```
- Extend `Type`:
  - Keep `Type::FnPtr(&'static [Type], &'static Type)` for non-capturing C-ABI function pointers (`fn(i64) -> i64`, 8 bytes).
  - Represent closure trait bounds in `WhereClause` (`where F: Fn(i64) -> i64`, `where F: FnMut(i64) -> bool`, `where F: FnOnce() -> T`):
    ```rust
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum ClosureKind {
        Fn,      // &self receiver
        FnMut,   // &mut self receiver
        FnOnce,  // self receiver (consuming)
    }
    ```

---

### 2.3 Capture Analysis & Borrow Checker Rules (`src/sanal/calls/closures.rs`)

#### 1. Minimal Capture Inference (When `is_move == false`)
For each outer variable or field path `v.f1.f2` referenced inside the closure body (excluding locals declared inside the closure, global functions, and `const` items):
1. **Consumed by value** (passed to a consuming parameter, returned by value, or `std::mem::drop`ped) and not `Copy`:
   - `CaptureMode::ByValue` (`field_ty = T`).
   - Marks `v` (or projection `v.f1.f2`) as **moved** in the enclosing scope at the closure creation point (`E0382` on subsequent use of `v`).
2. **Mutated or mutably borrowed** (`v = ...`, `v.f += ...`, `&mut v`, or calling a `&mut self` method on `v`):
   - `CaptureMode::ByMutRef` (`field_ty = Type::MutRef(T)`).
   - Require `v` to be declared `let mut` in the outer scope (`E0596` if immutable).
   - Register an active mutable borrow of `v` in `ScopeStack` held by the closure binding (`E0499`/`E0502` if accessed while the closure is alive).
3. **Read-only** (only read or shared-borrowed `&v` / `&self` method):
   - `CaptureMode::ByRef` (`field_ty = Type::Ref(T)`).
   - Register an active shared borrow of `v` in `ScopeStack` (`E0502` if `v` is mutably borrowed while the closure is alive; `E0505` if `v` is moved while the closure is alive).

#### 2. `move` Capture Rules (When `is_move == true`)
- Every referenced outer binding/projection uses `CaptureMode::ByValue` (`field_ty = T`).
- If `T` is `Copy`, it is copied into `__ClosureEnv_N` and remains usable in the outer scope.
- If `T` is not `Copy`, it is **moved** into `__ClosureEnv_N` at closure creation (`mark_expr_moved_if_ident`), and `__ClosureEnv_N`'s synthesized `Drop` glue automatically drops `T` when the closure is dropped without being consumed by `FnOnce::call_once`.

#### 3. Escape & Lifetime Safety
- **Non-`move` closures** (`ByRef` / `ByMutRef` captures) **cannot be returned from a function** or stored in a longer-lived outer binding (`E0373` / `E0597`: closure may outlive borrowed value; help message: *"Use `move |...|` to transfer ownership of captured variables into the closure"*).
- **`move` closures** contain no stack references (`&T` / `&mut T`) unless they explicitly captured a reference variable, so they can be safely returned from functions, stored in structs/iterators (`Map<I, F>`), or sent across threads!

---

### 2.4 Lowering to Concrete Structs & `Fn` / `FnMut` / `FnOnce` (`src/sanal/`, `src/codegen/`)

1. **Zero-Capturing Closures (`captures.is_empty()`)**:
   - Synthesize a zero-sized `obj __Closure_N {}` AND a top-level function `__closure_fn_N(args...) -> R`.
   - Coerces automatically to `Type::FnPtr(params, ret)` (`fn(Args...) -> R`) so C callbacks (`qsort`, pthread entrypoints, `Matrix::map(fn(f64) -> f64)`) continue to work at 8-byte C-ABI function pointer cost.

2. **Capturing Closures (`!captures.is_empty()`)**:
   - Synthesize concrete struct `obj __Closure_N`:
     ```gdrs
     obj __Closure_N:
         __cap_0: <captured_ty_0>
         __cap_1: <captured_ty_1>
     ```
   - Synthesize call methods on `__Closure_N` according to capability:
     - Always synthesize `__Closure_N_call_once(self, args...) -> R` (`FnOnce`).
     - If no non-`Copy` capture is moved out of the environment during the body, also synthesize `__Closure_N_call_mut(&mut self, args...) -> R` (`FnMut`).
     - If no capture is mutated or moved in the body, also synthesize `__Closure_N_call_ref(&self, args...) -> R` (`Fn`).
   - Inside the synthesized method body, rewrite each captured variable reference `v` to:
     - `*(self.__cap_i)` when `mode` is `ByRef` or `ByMutRef`.
     - `self.__cap_i` when `mode` is `ByValue`.
   - Direct call `f(x)` on a local closure variable `f: Type::Obj("__Closure_N")`:
     - Resolves to `__Closure_N_call_ref(&f, x)` if available, else `__Closure_N_call_mut(&mut f, x)` (requiring `let mut f` if it mutates captures!), else `__Closure_N_call_once(f, x)` (moving `f` so calling `f(x)` a second time triggers `E0382`!).

---

### 2.5 Monomorphized Iterator Chaining (`std/iter.gdrs`)

With closures lowered to concrete `Type::Obj("__Closure_N")` structs:
1. **`Map<I, F>`**:
   ```gdrs
   pub obj Map:
       iter: $I
       func: $F
   ```
   `next(&mut self) -> Option<$U>` calls `self.iter.next()`, and on `Option::Some(item)` invokes `(self.func)(item)` (`__Closure_N_call_mut(&mut self.func, item)`).
2. **`Filter<I, P>`**:
   ```gdrs
   pub obj Filter:
       iter: $I
       pred: $P
   ```
   `next(&mut self) -> Option<$T>` loops on `self.iter.next()` until `(self.pred)(&item)` returns `true`.
3. **`FilterMap<I, F>`**, **` fold(init, f)`**, **`reduce(f)`**, **`collect()`**:
   - Every adapter holds its upstream iterator and closure struct **inline by value** on the stack.
   - Chaining `v.iter().map(|x| x * scale).filter(|x| *x > min_val).fold(0, |acc, x| acc + x)` monomorphizes to direct calls with zero heap allocation and zero vtable indirection.

---

### 2.6 Remaining `std::ops` Traits (Alongside Priority 2)

Expand [ops.gdrs](file:///Users/aramsamifanni/Programming/gdrsc/std/ops.gdrs) and [indexing.rs](file:///Users/aramsamifanni/Programming/gdrsc/src/sanal/objects/indexing.rs) / [binops.rs](file:///Users/aramsamifanni/Programming/gdrsc/src/sanal/binops.rs):
1. **`Index` and `IndexMut`** (`a[i]` -> `*a.index(i)` for read, `*a.index_mut(i) = v` for write, following Rust's `&Output` / `&mut Output` signature so non-`Copy` elements can be borrowed in-place without moving out of a container).
2. **Bitwise & Compound Assignment Traits**: `BitAnd`, `BitOr`, `BitXor`, `Shl`, `Shr`, `AddAssign`, `SubAssign`, `MulAssign`, `DivAssign`.
