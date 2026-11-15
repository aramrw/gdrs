# GDRS Low-Level Foundations, C Interop & Library Roadmap

This document captures the architectural decisions, tradeoffs vs. Rust, codebase audit findings, and reprioritized roadmap for GDRS—focusing **first on low-level IR, ABI, and memory guarantees** (so passing native GDRS data to C libraries like NumPy's `ndarray` or Apple Accelerate/OpenBLAS never requires rewriting codegen later), and **second on Rust-aligned ergonomics** before building `gpm`.

---

## 1. Core Architectural Decisions & Rust Tradeoffs

### 1.1 Following Rust 1-to-1 vs. Deviating: Why Rust Made Its Choices

#### A. Why `Index` (`a[i]`) Must Return `&$Output` (Place Semantics) — *Follow Rust 1-to-1*
- **Why Rust requires `&Self::Output`**: In Rust, `a[i]` is not just a getter call; in the compiler IR it is a **place expression (L-value)** equivalent to `*a.index(i)` (or `*a.index_mut(i)`).
- **What breaks if `Index` returns a value instead of a reference**:
  1. Writing `a[i].x = 5` would silently mutate a temporary copy and discard it instead of mutating element `i` in-place.
  2. Writing `&a[i]` would borrow a temporary on the stack that immediately dies at the end of the statement instead of borrowing the element inside `a`.
  3. Indexing a collection of non-`Copy` types (`Vec<String>`) would move out of the collection on read (`let s = v[0]`), leaving a partially invalid buffer.
- **Decision**: Stick 1-to-1 with Rust. `Index` returns `&$Output` and `IndexMut` returns `&mut $Output`. For returning a new strided matrix view by value, use an explicit method like `m.slice(r_range, c_range)` or `m.view(...)`—zero hidden temporary pitfalls.

#### B. Heterogeneous Operators (`Matrix * f64`) & Reference Operators (`&a + &b`) — *Follow Rust 1-to-1*
- **Does Rust allow this?** **Yes, 100%.** In Rust, `pub trait Add<Rhs = Self> { type Output; fn add(self, rhs: Rhs) -> Self::Output; }` allows `Rhs` and `Output` to be different types, and allows implementing `Add` on reference types (`impl Add<&Matrix> for &Matrix`).
- **Why it is completely safe**:
  - In Rust (and GDRS), `a + b` is pure syntactic desugaring to `Add::add(a, b)`.
  - If implemented on owned `Matrix`, `a + b` moves `a` and `b` (enforced by the move checker).
  - If implemented on `&Matrix`, `&a + &b` passes two immutable borrows (`&Matrix`), mutates neither, and returns a newly allocated `Matrix`.
- **Current GDRS gap**: `std/ops.gdrs` currently hardcodes `fn add(self, other: $T) -> $T` (forcing `self`, `other`, and the return type to all be the same type). Updating `std/ops.gdrs` to allow distinct `Rhs` and `Output` types brings GDRS to true Rust parity.

#### C. Statement-Level Temporary Drop Rules — *Follow Rust 1-to-1*
- **Why Rust drops R-value temporaries at the end of the statement**:
  - In an expression like `let d = (&a + &b) + &c`, the sub-expression `(&a + &b)` produces an unnamed intermediate `Matrix` on the heap.
  - Rust binds that unnamed R-value to a compiler-generated stack slot for the duration of the enclosing statement, passes it into `+ &c`, and emits its `Drop` call at the statement boundary (newline/semicolon).
  - If someone writes `let p = (&a + &b).as_ptr()`, dropping the temporary at the end of the statement means `p` would dangle—so the borrow/lifetime checker rejects it and forces `let tmp = &a + &b; let p = tmp.as_ptr()`.
- **Decision**: Maintain Rust's exact temporary drop semantics in GDRS (`src/sanal/` and `src/codegen/drops/`).

### 1.2 Explicit Over Implicit
- No implicit slice-to-pointer decay or secret compiler coercions: use explicit `.as_ptr()` and `.as_mut_ptr()`.
- Default `obj` memory layout to canonical C-ABI field order (`src/codegen/layout.rs`), with opt-in `#[repr(packed)]` / `#[repr(align(N))]` attributes when needed.
- `Drop` is only implemented on leaf resource-owning types (`Vec`, `String`, `NdArray`, C handles); Plain Old Data (POD) structs have zero drop glue, and composite structs synthesize drop glue automatically (`src/codegen/drops/synthesis.rs`).

### 1.3 Platform Strategy: macOS (`aarch64`) First, Greppable Cross-Platform Markers
- Focus implementation, verification, and instruction/ABI accuracy on **macOS (`aarch64-apple-darwin`)** first.
- Do not hardcode architectural dead-ends: where code is OS- or ISA-specific (such as ARM64 HFA register rules or macOS linker flags), gate it with `#[cfg(target_os = "macos")]` or annotate with `// TODO(cross-platform: target_os = "linux" / "windows")` so it is trivially greppable in the future.

### 1.4 Licensing & Optimization Flags
- **License**: Dual **MIT / Apache-2.0** so `runtime.c` and generated binaries have zero GPL contamination risk.
- **Optimization Flag (`--release`)**: Keep Cranelift's `opt_level = "none"` as the default for fast debug compilation (matching `cargo build`), and wire a `--release` (or `--opt-level`) CLI flag to set `flag_builder.set("opt_level", "speed")` in `src/codegen/object.rs`.

---

## 2. Reprioritized Roadmap: Low-Level Foundations First

### Priority 1: Low-Level Memory, ABI & Compiler IR Foundations (Critical)
*Goal: Guarantee that passing any GDRS struct, array, or pointer to/from C (OpenBLAS, Accelerate, NumPy C-API, Raylib) emits the exact hardware instructions and memory layout expected, with zero leaks or silent corruption.*

1. **Exact Hardware C-ABI in `src/codegen/layout.rs` (macOS ARM64 Focus + Greppable ISA Hooks)**
   - **Homogeneous Floating-Point Aggregates (HFA)**: Currently `pass_mode_for_type` (`src/codegen/layout.rs:391-413`) packs all `1..=16`-byte structs into integer `I64` registers (`x0`, `x1`). On ARM64, C functions taking float structs by value (e.g., `obj Vec2: x: f32, y: f32` or up to 4 floats/doubles) expect them in floating-point registers (`s0..s3` / `d0..d3`). Update `PassMode` to classify HFA structs into `F32`/`F64` registers.
   - **ARM64 Indirect Return (`sret` in `x8`)**: Currently `abi_signature_for_fn` (`src/codegen/layout.rs:426-427`) passes `sret` (`> 16`-byte struct returns) as a normal `I64` parameter (`x0`). On ARM64 AAPCS64, C compilers expect `sret` in `x8` (`AbiParam::special(types::I64, ArgumentPurpose::StructReturn)`).
   - **Struct Alignment & Packing Attributes**: Verify padding/alignment parity with `clang` on ARM64 and add `#[repr(packed)]` / `#[repr(align(N))]` support if a C header requires unaligned/aligned structs.

2. **Statement-End R-Value Temporary Drop Tracking (`src/codegen/drops/`, `src/sanal/`)**
   - Audit and enforce that every unnamed intermediate value owning heap memory (e.g., `f(g(x))`, `(a + b) + c`, chained method calls returning owned structs/enums) is registered in a temporary stack slot and dropped at the end of the statement, matching Rust's temporary lifetime rules and verified under the Tier 4 `DYLD_INTERPOSE` zero-leak fuzzer.

3. **Low-Level Memory Primitives, `const`, and `static`**
   - **`const` Declarations**: Compile-time typed constants (`const CBLAS_ROW_MAJOR: i32 = 101`, `const ALIGNMENT: i64 = 64`) inlined into codegen.
   - **`static` Declarations**: Global variables emitted into the object file's data/rodata section (`static GLOBAL_LOCK: ...`) required for locks (`LazyLock`, `Mutex`), global allocators, and FFI state.
   - **Compiler Intrinsics `size_of::<T>()` & `align_of::<T>()`**: Add to `std/mem.gdrs` + compiler intrinsics to replace the pointer-offset workaround `((0 as *$T) + 1) as i64` in `std/vec.gdrs`.
   - **Explicit Raw Pointer & Aligned Allocation APIs**:
     - `.as_ptr(&self) -> *$T`, `.as_mut_ptr(&mut self) -> *$T`, and `unsafe Vec::from_raw_parts(ptr, len, cap)` in `std/vec.gdrs`.
     - `posix_memalign` / `aligned_alloc` in `std/libc.gdrs` for 32/64-byte SIMD and BLAS buffer alignment.

4. **Separating `[T; N]`, `&[T]`, `&mut [T]`, and `Vec<T>` (`ideas/arrays_slices_and_vec.md`)**
   - Ensure `[T; N]` is a true inline stack/struct array, `&[T]` / `&mut [T]` are 16-byte `(ptr, len)` fat pointers, and `Vec<T>` is a 24-byte heap vector constructed via `vec![...]` or `Vec::new()`.
   - Ensures C FFI structs containing fixed arrays (e.g. `matrix: [f32; 16]`) have the exact inline C layout rather than a pointer to a heap `Vec`.

5. **AST-Indexed Module Loader (`src/loader/files.rs`, `src/loader/mod.rs`)**
   - Replace raw substring scanning (`content.contains("obj ...")` in `files.rs:154-163`) with AST-based symbol discovery.
   - Track module-local free functions, traits, `const`, `static`, and `extern "C"` declarations during name mangling so multi-file modules never fail intra-module calls.
   - Support transitive `pub use` re-exports and `--extern <crate>=<path>` roots.

---

### Priority 2: Rust-Aligned Type System & Functional Ergonomics
*Goal: Make writing complex algorithms, data pipelines, and ML training loops in GDRS feel as expressive as Rust.*

1. **Capturing Closures (`Fn`, `FnMut`, `FnOnce`) & Lazy Iterator Chaining**
   - Upgrade closures from non-capturing function pointers to compiler-synthesized environment structs that capture local variables (by reference or move).
   - Implement lazy iterator adapters in `std/iter.gdrs` (`.map()`, `.filter()`, `.filter_map()`, `.enumerate()`, `.zip()`, `.fold()`, `.reduce()`, `.collect()`) so functional pipelines chain zero-cost.

2. **Full Rust-Parity `std::ops` Traits (`std/ops.gdrs`)**
   - Upgrade `Add` and `Sub` and add `Mul`, `Div`, `Rem`, `Neg`, `Index`, and `IndexMut` with parameterized `Rhs` and `Output` types.
   - Support trait implementations on reference types (`&T`) so `&a + &b` and `&a * scalar` work cleanly without moving operands.

3. **`let ... else:` Diverging Pattern Bindings**
   - Support `let Option::Some(x) = expr else: return ...` to prevent rightward indentation drift in error/option handling.

4. **Parameterized Trait `impl`s & Scoped Conversion Traits (`From<T>` / `Into<T>`)**
   - Key trait dispatch by `(SelfType, TraitName, TraitTypeArgs)` so `impl<T> From<T> for Wrapper` / multiple `From<A>`, `From<B>` impls on the same type don't collide.
   - Add scoped target-type inference for expected-type call sites (like `let x: Wrapper = y.into()`), while intentionally skipping Rust's universal blanket `impl<T, U> Into<U> for T where U: From<T>` unless full coherence/bidirectional inference is justified.

---

### Priority 3: Higher-Level Polish, Release Flag & Build System (`gpm`)
*Goal: Package external libraries cleanly outside `std` and provide numerical convenience constants.*

1. **CLI `--release` / `--opt-level` Flag (`src/cli.rs`, `src/codegen/object.rs`)**
   - Keep `opt_level = "none"` as default for fast compilation; set `opt_level = "speed"` when `--release` is passed.
2. **IEEE-754 Float Constants & Methods (`std/math`)**
   - Expose hardware IEEE-754 bit-pattern constants (`f64::INFINITY`, `f64::NEG_INFINITY`, `f64::NAN`, `f64::EPSILON`) and bit-check methods (`.is_nan()`, `.is_infinite()`, `.is_finite()`). *(Note: IEEE-754 `INFINITY` and `NaN` are standard hardware float bit-patterns already supported by the CPU's `f32`/`f64` instructions, not a separate compiler type).*
3. **Crate Targets, `gpm`, and `gdrs bindgen` (`ideas/BUILD.md`)**
   - Add `--crate-type lib|staticlib|bin` and `--extern` to `gdrs`.
   - Build `gpm` (`gdrs.toml`) and `gdrs bindgen <header.h>` to wrap C libraries (OpenBLAS, Accelerate, Raylib) into standalone GDRS packages.
