# `PartialEq` and `Eq` Specification

## 1. Traits (`std/core.gdrs`)

* **`PartialEq`**: Defines structural / value equality without moving either operand.
  ```gdrs
  trait PartialEq:
  	fn eq(&self, other: &Self) -> bool
  ```
* **`Eq`**: Empty marker trait indicating a reflexive, symmetric, and transitive equivalence relation (`x == x` is always `true`).
  ```gdrs
  trait Eq {}
  ```
  * Floating-point types (`f32`, `f64`) satisfy `PartialEq`, **not** `Eq` (because `NaN != NaN`).
  * Integer types, `bool`, `str`, `String`, `()`, raw pointers, tuples of `Eq` types, and user types implementing `Eq` satisfy `Eq`.

---

## 2. Operator Lowering (`==` and `!=`)

In `src/sanal/binops.rs`:
1. **Built-in fast paths** remain for primitives (integers, floats, `bool`, pointers), `str`/`String`, tuples, and enums without custom `PartialEq` impls.
2. **User types (`Type::Obj` / `Type::Enum` with `eq`):**
   * `a == b` looks up `eq` on the operand type.
   * Both `lhs` and `rhs` are **auto-borrowed** (`&lhs`, `&rhs`) via `TypedExpr::Ref(..., false, ...)` so `==` never moves or drops non-`Copy` values.
   * `a == b` lowers to `TypedExpr::Call(eq_fn, [&lhs, &rhs], Type::Bool, span)`.
   * `a != b` lowers to `TypedExpr::Call(ne_fn, ...)` if `ne` exists, otherwise `TypedExpr::Not(TypedExpr::Call(eq_fn, ...), Type::Bool, span)`.
3. **Missing `PartialEq` on structs:** Comparing two `obj` values that do not implement `PartialEq` produces a compile-time error instead of falling through to a raw `icmp`.

---

## 3. Generic Bounds (`where $T: PartialEq` / `where $T: Eq`)

In `src/sanal/mono.rs` (`type_satisfies_bound`):
* **`PartialEq`:** Satisfied by all numeric types, `bool`, `str`, `String`, `()`, raw pointers, tuples whose elements satisfy `PartialEq`, references to `PartialEq` types, enums, and structs implementing `PartialEq` / `eq`.
* **`Eq`:** Satisfied by integer types (not `f32`/`f64`), `bool`, `str`, `String`, `()`, raw pointers, tuples whose elements satisfy `Eq`, references to `Eq` types, and structs/enums explicitly implementing `Eq`.

---

## 4. `#[derive(PartialEq, Eq)]` (`src/loader/derives.rs`)

* **`#[derive(PartialEq)]` on `obj`:** Synthesizes `impl PartialEq for <Name>` with `fn eq(&self, other: &<Name>) -> bool` returning `true` when all fields satisfy `self.field == other.field` (or `true` for unit structs).
* **`#[derive(Eq)]` on `obj` / `enum`:** Synthesizes `impl Eq for <Name> {}`.
* **`#[derive(PartialEq)]` on `enum`:** Synthesizes `impl PartialEq for <Name>` delegating to structural enum equality (or variant-by-variant `match`).
