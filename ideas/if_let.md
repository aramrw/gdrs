# Future Feature: `if let`, `while let`, and `let ... else`

## Overview

`if let` provides concise single-pattern matching without writing a full `match` block with a `_ => ()` fallback arm.

```gdrs
if let Result::Ok(val) = res:
	log!("got: {}", val)
else:
	log!("failed")
```

---

## 1. Recommended Implementation: Parser-Level Desugaring to `Expr::Match`

In Rust (since RFC 160), `if let` is lowered to `match`:

```gdrs
// Written:
if let Some(x) = opt:
	use_val(x)
else:
	handle_empty()

// Lowered to:
match opt:
	Some(x) => use_val(x)
	_ => handle_empty()
```

If there is no `else:` branch, the `_` arm evaluates to `()` (`Expr::TupleInit(vec![], span)`).

### Why This Approach Fits `gdrsc`
- **Zero new semantic analysis**: `sanal/control_flow.rs` (`type_check_match`) already handles enum variant resolution, generic `Option`/`Result` instantiation, move checking, and scope bindings.
- **Zero new codegen**: `codegen/branching.rs` (`compile_match`) already handles discriminants, Null-Pointer Optimization (NPO) enums, aggregate vs. scalar payloads, and branch-exit drops.
- **Future-proof**: Whenever `match` gains nested patterns, tuple patterns, or literal patterns in `arm_pattern` (`src/parser/stmt.rs`), `if let` inherits them automatically.
- **`else if let` chaining**: Naturally desugars into nested `Expr::Match` inside the `_` arm.

---

## 2. Temporary Lifetime Semantics (Rust vs. GDRS)

A well-known pitfall in Rust is that `match EXPR` keeps temporaries created in `EXPR` alive until the **end of the entire `match`** (so arms can safely borrow from `EXPR`, e.g., `match get_string().as_str()`). When `if let` desugared directly to `match`, locks or guards created in `EXPR` (like `mutex.lock().unwrap().get()`) stayed locked across the entire `if let` body, causing deadlocks. Rust 2024 had to adjust `if let` temporary drop scopes to drop earlier.

In `gdrsc`:
- `compile_if` / `compile_if_else` (`src/codegen/branching.rs`) wrap the condition in its own `push_temp_scope()` / `pop_temp_scope_and_drop()`, dropping condition temporaries **before** entering the branch.
- `compile_match` (`src/codegen/branching.rs`) cancels the matched `target_ptr` temporary and leaves any intermediate temporaries in the enclosing statement's `temp_scope` (dropped after the `match` completes).
- Desugaring `if let` to `Expr::Match` matches `match` semantics safely. If locks (`MutexGuard`) are added later, `pop_temp_scope_and_drop` can be added before the `else` branch.

---

## 3. Related Future Pattern Sugars

| Construct | Example | Lowering / Notes |
| :--- | :--- | :--- |
| **`while let`** | `while let Some(x) = iter.next():` | Lowers to a `while true:` loop containing `match iter.next(): Some(x) => body, _ => break`. |
| **`let ... else`** | `let Ok(f) = File::open(p) else: return Err(...)` | Binds `f` in the outer scope; `sanal` must verify the `else` block diverges (`is_diverging_expr`). |
| **`if let` chains** | `if let Some(x) = a && x > 0:` | Cannot trivially desugar to a single `match` when an `else:` arm exists (failing `x > 0` must jump to the same `else:` as `None`). |

---

## 4. Parser Prerequisites

1. Lookahead in `src/parser/stmt.rs` for `Token::If` followed by `Token::Let` to distinguish `if let <arm_pattern> = <expr>:` from `if <cond>:`.
2. Support optional `else:` and `else if let ...:` chaining, matching existing `if`/`else if`/`else` indentation rules.
3. Preserve the `if let` `Span` on the desugared `Expr::Match` so diagnostics point to the user's `if let` expression.
