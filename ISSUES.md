# GDRSC Base Language Grounding Status

All single-threaded base language issues identified before async/multithreading have been resolved:

- **Unified AOT (`gdrs build` / `gdrs run`)**: Removed Cranelift JIT (`src/codegen/jit.rs`, `src/codegen/intrinsics/ffi.rs`, `cranelift-jit`, `libc`), cached `runtime.c` as `gdrs_runtime_<hash>.o`, forward-declared program functions in `src/codegen/object.rs`, preserved unmangled `extern "C"` symbol names (`ExternFnDecl.c_name`), and added `-L` / `-l` native linker flags to `src/cli.rs` and `src/codegen/object.rs`.
- **Reference & Memory Safety Guardrails**: Enforced immutable `&T` (`E0594`), mutable borrow checks for `&mut` and `&mut self` (`E0596`), non-escaping references (`E0106`), and no raw integer deref (`E0614`).
- **RAII Scope Drops & `std::mem::drop`**: Extracted `CodegenCtx` (`src/codegen/ctx.rs`) and wired lexical scope-exit drops, early `return` / `break` / `continue` drops, move-flag invalidation across assignments/calls/structs/enums/deref/index writes, `std/mem.gdrs` (`std::mem::drop`), and 24-byte `rc`/`arc` destructors for inner heap values.
- **Control Flow & Syntax Fundamentals**: Added `break`, `continue`, `else if` chaining, string escape unescaping (`\n`, `\r`, `\t`, `\\`, `\"`, `\0`, `\xNN`), bitwise float rejection (`E0308`), and removed dead parser rules in `src/parser/stmt.rs`.
- **Real `dyn Trait` Vtables**: Added `src/codegen/vtables.rs` and `sanal/calls.rs` trait method resolution to dispatch `dyn Trait` through real fat pointers `{ data_ptr, vtable_ptr }`.
- **Generic Monomorphization & Diagnostics**: Registered structured type args via `MANGLED_REGISTRY` (`src/sanal/mono.rs`), updated `VecIter::next` to `Option<$T>` (`std/vec.gdrs`), fixed `std/error.gdrs` and `std/fs.gdrs` `buffer_to_string`, added `SourceMap` cross-file error spans (`src/loader/mod.rs`, `src/diagnostics.rs`), made `format!` dynamically sized via `intrinsic_format_join`, and isolated non-capturing closures cleanly.

Next phase (when ready): designing and adding multithreading / async primitives (`Send`/`Sync` gates, structured concurrency) on top of this solid base.
