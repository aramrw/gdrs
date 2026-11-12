# Iterator Design: What We Have vs. What Rust Does

## What We Have Now (and Why It's Broken)

The current implementation treats `iter`, `map`, and `for_each` as **special-cased compiler macros** with hardcoded behaviour baked into the semantic analyser and codegen. There is no concept of an iterator as a *value* or a *type*. Each step in a chain is dispatched independently, with no shared abstraction between them.

### The current data flow

```
(0..5)           → Range { start, end }          — a heap struct
.iter()          → NO-OP. Literally returns its argument unchanged.
.map(|x| x*10)  → ???  (never resolves — this is the current crash)
.for_each(|x|…) → hardcoded branch: Range → intrinsic_iter_for_each
                                     Vec  → intrinsic_vec_for_each
```

`iter_map` and `map_for_each` exist in the C runtime and are linked into the JIT, but are completely unreachable because `map` never survives the semantic analysis pass. The sanal doesn't know what `map` is, has no return type for it, and now that monomorphization tightened up the unknown-function fallback, it correctly errors instead of silently passing garbage to codegen.

### Why the runtime primitives aren't enough

Even if we wired `map` up as another hardcoded macro, we'd still have these problems:

- `map` over a `Vec` would need a *different* intrinsic than `map` over a `Range`.
- Chaining `map` twice (`.map(f).map(g)`) would require yet another intrinsic.
- `filter` would need its own intrinsics for every source type.
- `collect` — materialising the chain into a `Vec`, `HashMap`, etc. — is impossible because there is no unified value being passed along the chain that codegen can drive.
- Every new source type (a custom struct implementing something iterator-like) would require new hardcoded branches everywhere.

The root problem is that **the compiler, not the type system, is doing the work of knowing what an iterator is**. Rust does the opposite.

---

## How Rust's Iterator System Actually Works

Rust's iterators are entirely defined in terms of **one trait and one method**. Everything else — `map`, `filter`, `collect`, `zip`, `chain`, `flat_map`, `take`, `skip` — falls out of that single abstraction with zero runtime overhead.

### The core: the `Iterator` trait

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

That's it. An iterator is any type that can produce a sequence of values one at a time, or `None` when exhausted. The `Item` associated type carries the element type through the chain statically, so the compiler always knows what type each step yields.

### Sources implement Iterator directly

```rust
// Range<i64> implements Iterator<Item = i64>
// Vec<T>'s IntoIter<T> implements Iterator<Item = T>
// HashMap<K,V>'s Iter<K,V> implements Iterator<Item = (&K, &V)>
```

`.iter()` on a `Vec` or `Range` simply returns a value whose type implements `Iterator`. It doesn't do anything at runtime — it just produces the starting value of the chain.

### Adapters are structs that wrap an inner iterator

```rust
struct Map<I, F> {
    inner: I,   // the source iterator
    func: F,    // the mapping function
}

impl<I: Iterator, F: Fn(I::Item) -> B, B> Iterator for Map<I, F> {
    type Item = B;
    fn next(&mut self) -> Option<B> {
        self.inner.next().map(|x| (self.func)(x))
    }
}
```

`Map` is a **lazy wrapper**. It doesn't allocate a new collection. It doesn't loop over anything. It just stores the source and the function. The loop only happens when something *drives* the iterator — and that something is `for_each` or `collect`.

The same pattern applies to every adapter:

```rust
struct Filter<I, P> { inner: I, predicate: P }
struct Take<I>      { inner: I, remaining: usize }
struct Zip<A, B>    { a: A, b: B }
struct FlatMap<I, F, U> { inner: I, func: F, current: Option<U> }
```

Each one is just a struct. Each one implements `Iterator`. They compose freely because they all speak the same protocol — `next()`.

### Consumers drive the chain

A consumer calls `next()` in a loop until it gets `None`. The two most important ones:

**`for_each`** — just loops, discarding the output:
```rust
fn for_each<F: FnMut(Self::Item)>(mut self, mut f: F) {
    while let Some(item) = self.next() {
        f(item);
    }
}
```

**`collect`** — loops and feeds items into any collection that implements `FromIterator`:
```rust
fn collect<C: FromIterator<Self::Item>>(self) -> C {
    C::from_iter(self)
}

trait FromIterator<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self;
}
```

`Vec<T>` implements `FromIterator<T>`. So does `HashMap<K, V>` (over `(K, V)` tuples). So does `HashSet<T>`, `String`, etc. When you call `.collect::<Vec<_>>()`, the compiler monomorphizes `collect` for that specific output type, and the entire chain from source to sink becomes a single tight loop with no intermediate allocations.

### The zero-cost guarantee

Because every adapter is a concrete generic struct, the compiler monomorphizes the full chain. A call like:

```rust
(0..100).filter(|x| x % 2 == 0).map(|x| x * x).collect::<Vec<_>>()
```

compiles down to a single loop that does the filter, the multiply, and the push — no intermediate `Vec` for the filter output, no intermediate `Vec` for the map output. The type of the full expression is:

```
Collect<Map<Filter<Range<i64>, fn(&i64)->bool>, fn(i64)->i64>, Vec<i64>>
```

The entire chain is encoded in the type. Monomorphization makes it all concrete. The optimizer sees through it and produces a tight loop.

---

## What GDRS Needs: A Self-Hosted Stdlib

The lesson is: **don't hardcode adapters in the compiler. Define `Iterator` as a real trait and let the type system and monomorphizer do the work — entirely in GDRS code.**

Because GDRS already supports `extern "C"`, calling `malloc`, `realloc`, and `free` directly from GDRS is possible today. This means the entire collection and iterator stack can be written as GDRS stdlib code with no special compiler knowledge. The compiler only needs to know about things that *genuinely cannot be expressed* in user code.

### The target stdlib layout

```
std/libc.gdrs       → extern "C" { malloc, realloc, free, memcpy, ... }
std/vec.gdrs        → Vec<T> implemented in GDRS calling malloc/realloc
std/hashmap.gdrs    → HashMap<K,V> implemented in GDRS calling malloc
std/iter.gdrs       → Iterator<T> trait + Map, Filter, Take, Zip, etc.
std/core.gdrs       → FromIterator<T>, IntoIterator<T> traits
```

None of these require new compiler intrinsics. They are regular GDRS structs and trait impls that flow through the existing generic monomorphizer. The compiler remains thin.

### Array vs Vec desugaring

The one place the compiler still participates in collection syntax is the `[]` literal:

- **`let x = [1, 2, 3]`** — stays as a fixed-size array intrinsic. This is a stack/compile-time-sized allocation and cannot be expressed in pure GDRS without dependent types. The compiler keeps this.
- **`let mut x = [1, 2, 3]`** — desugars to `Vec::new()` followed by pushes. The `mut` signals that the user wants a growable collection. The compiler just rewrites the AST node; `Vec` itself is stdlib GDRS code.

This means `let x = []` gives you a true fixed array (no heap, no length tracking), and `let mut x = []` gives you a `Vec<T>` — the same distinction Rust makes between `[T; N]` and `Vec<T>`, expressed through mutability as a syntactic shorthand.

### What gets deleted from the compiler

Once this is in place, the following can be removed entirely:

- `runtime.c` iterator functions: `intrinsic_iter_for_each`, `intrinsic_vec_for_each`, `intrinsic_iter_map`, `intrinsic_map_for_each`
- `codegen/intrinsics/iterators.rs` — the entire file
- The `runtime.c` vec allocation helpers: `intrinsic_vec_new`, `intrinsic_vec_push`, `intrinsic_vec_pop` — replaced by `Vec` methods in `std/vec.gdrs` calling `malloc` directly
- `iter`, `for_each`, `map`, `push`, `pop`, `len` from the intrinsic macro list in the sanal
- The hardcoded `Range` / `Vec` type dispatch in `codegen/intrinsics/macros.rs`

### What legitimately stays as compiler intrinsics

The only things that cannot be expressed in GDRS user code and must remain hardcoded:

- `log!`, `print!`, `println!` — variadic formatting, needs compiler string magic
- `panic!` — needs compiler unwind/abort support
- `assert!`, `assert_eq!` — need source location injection
- `format!` — string interpolation is inherently compiler-level
- `vec!` literal syntax — pure syntactic sugar, desugars to `Vec::new()` + pushes (no runtime knowledge needed, just parser/AST rewriting)
- Fixed-size array `[T; N]` init — stack allocation of a known size

### The payoff

Once this is in place:

- A user can implement `Iterator<T>` on any of their own types and immediately get `.map()`, `.filter()`, `.collect()`, etc. for free — the same as stdlib types.
- `HashMap` can implement `Iterator<(K, V)>` for free iteration, and `FromIterator<(K, V)>` for `collect` into it.
- The compiler gets meaningfully smaller and simpler — no more `runtime.c` growing to accommodate every new collection method.
- The stdlib is testable in GDRS itself. Bugs in `Vec` or `Map` show up as GDRS errors, not mysterious JIT crashes.
- Custom allocators become possible in the future by swapping what `std/libc.gdrs` points at.
