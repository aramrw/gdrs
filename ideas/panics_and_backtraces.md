# Design: Panics, Source Locations, and Backtraces in GDRS

## Overview

In systems programming, panics represent **unrecoverable contract violations and programmer bugs** (e.g. index out of bounds, assertion failures, null pointer dereferences, broken data invariants). Recoverable errors in GDRS are handled explicitly via `Result<T, E>` and the `?` operator.

This document outlines the architecture for GDRS panics, focusing on:
1. **Rust-identical panic banners** with exact source file, line, and column reporting.
2. **Deterministic process abort semantics** (`panic = "abort"`).
3. **Call stack backtraces** via POSIX `execinfo.h` triggered by `GDRS_BACKTRACE=1`.
4. **Why stack unwinding is intentionally avoided** in Cranelift.

---

## 1. Why `panic = "abort"` instead of Stack Unwinding

Rust offers two panic strategies: `panic = "unwind"` and `panic = "abort"`.

| Feature | `panic = "unwind"` | `panic = "abort"` (GDRS Model) |
| :--- | :--- | :--- |
| **Destructors (`Drop`)** | Executed up the stack during panic | Not executed on panic (OS reclaims memory) |
| **Catching (`catch_unwind`)** | Allowed | Process aborts immediately |
| **Binary Size & Overhead** | Large `.eh_frame` tables, landing pads at every call | Zero landing pad overhead, minimal binary footprint |
| **Cranelift Suitability** | Extremely difficult (no native `landingpad` IR) | Ideal fit for Cranelift's native trap/abort model |
| **Source Line & Stack Trace** | Full backtrace | **Full backtrace with file, line, and column** |

### The Cranelift Constraint
Cranelift was designed for fast compilation and JIT/Wasm runtimes. It does not possess LLVM's `invoke` / `landingpad` exception model. Implementing full unwinding requires:
- Generating DWARF Call Frame Information (`.eh_frame`) for every instruction.
- Generating landing pad cleanup blocks at every call site.
- Implementing platform-specific personality routines (`libunwind`).

Even `rustc_codegen_cranelift` (the Cranelift backend for `rustc`) defaulted to `-C panic=abort` for years. For GDRS, `panic = "abort"` is both technically pragmatic and philosophically aligned with game development and systems programming.

---

## 2. Architecture

```
                  ┌────────────────────────────────────────┐
                  │ Panic Trigger                          │
                  │ (assert!, assert_eq!, panic!, a[idx])  │
                  └──────────────────┬─────────────────────┘
                                     │
                     Passes compile-time span info:
                     (msg, file_str, line_u32, col_u32)
                                     │
                                     ▼
                  ┌────────────────────────────────────────┐
                  │ intrinsic_panic / bounds_panic         │
                  │ in src/codegen/runtime.c               │
                  └──────────────────┬─────────────────────┘
                                     │
         ┌───────────────────────────┴───────────────────────────┐
         ▼                                                       ▼
┌──────────────────────────────┐                ┌──────────────────────────────┐
│ Standard Panic Banner        │                │ If GDRS_BACKTRACE=1          │
│                              │                │                              │
│ thread 'main' panicked at    │                │ stack backtrace:             │
│ examples/matrix.gdrs:42:5:   │                │   0: intrinsic_panic         │
│ assertion failed             │                │   1: std_math_matrix_matmul  │
└──────────────────────────────┘                │   2: gdrs_main               │
                                                └──────────────┬───────────────┘
                                                               │
                                                               ▼
                                                ┌──────────────────────────────┐
                                                │ exit(101) or abort()         │
                                                └──────────────────────────────┘
```

---

## 3. Specification

### Layer 1: Panic Location Banner

The runtime functions in `src/codegen/runtime.c` are updated to accept caller location information:

```c
void intrinsic_panic_loc(const char* msg, const char* file, int64_t line, int64_t col);
void intrinsic_bounds_panic_loc(int64_t idx, int64_t len, const char* file, int64_t line, int64_t col);
```

#### Banner Format (Matching Rust 1:1):
```text
thread 'main' panicked at examples/std_matrix.gdrs:34:12:
index out of bounds: the len is 2 but the index is 5
note: run with `GDRS_BACKTRACE=1` environment variable to display a backtrace
```

#### Codegen Emission:
In `src/codegen/intrinsics/macros.rs`:
- When emitting `assert!`, `assert_eq!`, `assert_ne!`, or `panic!`, the compiler extracts location from `cg.source_map.get_location(&span)`:
  - `file`: Global constant string pointer in the object data section.
  - `line`: `types::I64` constant.
  - `col`: `types::I64` constant.
- Calls `intrinsic_panic_loc(msg_val, file_val, line_val, col_val)`.
- Follows immediately with Cranelift `trap(TrapCode::User(1))`.

In `src/codegen/arrays.rs`:
- Vector and array bounds checks emit calls to `intrinsic_bounds_panic_loc(idx, len, file, line, col)`.

---

### Layer 2: Call Stack Backtraces (`GDRS_BACKTRACE=1`)

In `src/codegen/runtime.c`:
1. Check if `getenv("GDRS_BACKTRACE")` equals `"1"` or `"full"`.
2. On panic:
   - On POSIX platforms (`macOS`, `Linux`):
     ```c
     #include <execinfo.h>

     void print_backtrace(void) {
         void* callstack[128];
         int frames = backtrace(callstack, 128);
         char** strs = backtrace_symbols(callstack, frames);
         if (!strs) return;

         fprintf(stderr, "stack backtrace:\n");
         for (int i = 0; i < frames; ++i) {
             fprintf(stderr, "  %2d: %s\n", i, strs[i]);
         }
         free(strs);
     }
     ```
3. Because `gdrsc` exports native function symbols with module names (e.g. `std_math_matrix_Matrix_matmul`, `gdrs_main`), `backtrace_symbols` displays readable function names automatically.

---

### Layer 3: Future DWARF Line Resolution (Optional)

To map stack frame addresses to exact source lines in callers without relying on runtime banners:
- Cranelift supports emitting `.debug_line` tables through `gimli`.
- Backtraces can pipe addresses through `addr2line` / `atos` (macOS) or embed `libbacktrace`.
