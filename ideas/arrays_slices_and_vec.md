# Design: Separating Arrays `[T; N]`, Slices `&[T]`, and `Vec<T>`

## 1. Current State & Problem

Currently in `src/parser/mod.rs`:
```rust
let array_type = just(Token::LBracket)
    .ignore_then(type_parser.clone())
    .then_ignore(just(Token::RBracket))
    .map(|t| Type::Vec(intern_type(t)));
```
Type syntax `[T]` is aliased directly to `Type::Vec(T)`. Meanwhile, `Type::Slice(T)` and `Type::Array(T, N)` already exist in the AST, semantic analyzer, and Cranelift codegen (`layout.rs` gives `Type::Slice` a 16-byte `(ptr, len)` fat-pointer layout), but they are unreachable from type annotations.

This causes friction with Rust-style expectations:
- Writing `let s: [f64] = [0.0, 1.0, 2.0]` secretly allocates a heap `Vec<f64>`.
- Writing `Vec::from_slice(&s)` fails with `expected Vec(Float), found Ref(Vec(Float))`, because `std/vec.gdrs` declares `fn from_slice(slice: [$T]) -> Vec` (taking an owned `Vec` by value rather than a borrowed slice `&[T]`).

---

## 2. Target Rust-Aligned Semantics

| Syntax | Type | Memory Representation | Ownership |
| :--- | :--- | :--- | :--- |
| `[T; N]` | `Type::Array(T, N)` | Inline stack array (`N * stride` bytes) | Owned, `Copy` if `T: Copy` |
| `&[T]` | `Type::Slice(T)` | 16-byte fat pointer `(ptr: *T, len: i64)` | Borrowed immutable view |
| `&mut [T]` | `Type::MutSlice(T)` (or `MutRef(Slice(T))`) | 16-byte fat pointer `(ptr: *T, len: i64)` | Borrowed mutable view |
| `Vec<T>` | `Type::Vec(T)` | 24-byte header `(ptr: *T, len: i64, cap: i64)` + heap buffer | Owned, RAII `Drop` |

---

## 3. Migration Plan

### Phase 1: Introduce `vec!` Macro for Heap Vectors
- Use `vec![a, b, c]` and `vec![]` as the idiomatic way to construct `Vec<T>` (replacing `[a, b, c]` -> `Vec<T>` sugar).

### Phase 2: Parser Type Syntax (`src/parser/mod.rs`)
1. Parse `[T; N]` into `Type::Array(intern_type(T), N)`.
2. Parse `[T]` (when inside `&[T]` / `&mut [T]`) into `Type::Slice(intern_type(T))`.
   - Reject bare unsized `[T]` in value position (parameters, locals) with a clear error: `"size for values of type [T] cannot be known at compilation time; use &[T] or Vec<T>"`.

### Phase 3: Auto-Coercion & Borrowing (`src/sanal/`)
1. **Array to Slice Coercion**:
   - `&[T; N]` and `&arr` (where `arr: [T; N]`) automatically coerce to `&[T]` (`Type::Slice(T)`), constructing the 16-byte `(ptr, len)` fat pointer.
2. **Vec to Slice Deref Coercion**:
   - `&Vec<T>` automatically coerces to `&[T]` by reading `(vec.ptr, vec.len)` into a 16-byte fat pointer.
3. **Update `std/vec.gdrs`**:
   - Change `fn from_slice(slice: &[$T]) -> Vec<$T>` to borrow a slice `&[T]` instead of moving a `Vec<T>`.

### Phase 4: Codegen Verification (`src/codegen/`)
- Ensure `Type::Array` allocates inline on the stack (not `malloc`).
- Ensure `Type::Slice` passes/stores the 16-byte `(ptr, len)` fat pointer cleanly across function boundaries.
- Update existing tests/examples from `[T]` to `Vec<T>` / `vec![...]` / `&[T]`.
