# GDRS Build System Specification (`BUILD_SYSTEM.md`)

This document specifies the decoupled architecture for the **GDRS Build System**, separating the core compiler (`gdrsc`) from the build system orchestrator and package manager (`gpm` / `gdrs-build`).

---

## 1. Architectural Separation

Following the Unix philosophy and Rust's `rustc` / `cargo` model:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           gpm / gdrs-build                                  │
│             (Package Manager & Build Graph Orchestrator)                    │
│                                                                             │
│  - Parses gdrs.toml manifest                                                │
│  - Resolves dependency tree & versions                                      │
│  - Downloads/caches remote & path dependencies                              │
│  - Manages target/ build directories & artifact caching                      │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
                               Invokes per-crate
                                       │
┌──────────────────────────────────────▼──────────────────────────────────────┐
│                                   gdrsc                                     │
│                     (Core GDRS Compiler & JIT Engine)                       │
│                                                                             │
│  - Compiles a single crate (lib or bin target)                              │
│  - Resolves --extern dependency paths                                       │
│  - Performs semantic analysis & type checking                               │
│  - Emits .rlib / .a library archives or native binary executables           │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. Compiler Interface (`gdrsc` CLI Flags)

To allow external build tools (`gpm`, CMake, `build.nu`, Ninja) to drive compilation, `gdrsc` exposes explicit single-crate flags:

### Command Line Flags

| Flag | Argument | Description | Example |
| :--- | :--- | :--- | :--- |
| `--crate-type` | `bin` \| `lib` \| `staticlib` | Output target type | `--crate-type lib` |
| `--crate-name` | `<name>` | Name of the crate being compiled | `--crate-name raylib_wrapper` |
| `--extern` | `<alias>=<path>` | Register a compiled dependency artifact | `--extern math=target/deps/libmath.rlib` |
| `-L` | `<dir>` | Native C library search directory | `-L /opt/homebrew/lib` |
| `-l` | `<libname>` | Link native C shared/static library | `-l raylib` |
| `-o` | `<path>` | Output artifact path | `-o target/debug/libmath.rlib` |
| `--out-dir` | `<dir>` | Output directory for artifacts | `--out-dir target/debug/deps` |
| `--opt-level` | `0` \| `1` \| `2` \| `3` | Optimization level for Cranelift | `--opt-level 3` |
| `--emit` | `asm,llvm-ir,clif,obj,link` | Emit specific build stages | `--emit obj,link` |

---

## 3. Package Manifest Specification (`gdrs.toml`)

Projects define their metadata and dependencies in `gdrs.toml`:

```toml
[package]
name = "bouncing_ball"
version = "0.1.0"
edition = "2026"
authors = ["Aram <aram@example.com>"]

[lib]
name = "bouncing_ball_lib"
path = "src/lib.gdrs"

[[bin]]
name = "bouncing_ball"
path = "src/main.gdrs"

[dependencies]
std_math = { path = "../std_math" }
# raylib_wrapper = { git = "https://github.com/example/raylib-gdrs", tag = "v0.2" }

[link]
libraries = ["raylib"]
search_paths = ["/opt/homebrew/lib", "/usr/local/lib"]
```

---

## 4. Artifact & Library File Format (`.rlib`)

When `gdrsc` compiles a library (`--crate-type lib`), it generates a `.rlib` container containing:

1. **`metadata.json`**:
   - Exported public struct definitions, enums, traits, and function signatures.
2. **`code.o`**:
   - Compiled Cranelift machine code object file for library functions.

---

## 5. Build Orchestrator Execution Pipeline (`gpm`)

When the user runs `gpm build` or `gpm run`:

```
Step 1: Read gdrs.toml
        │
Step 2: Construct Dependency DAG
        │
Step 3: Topologically Sort Build Order
        │
Step 4: For each dependency (leaf to root):
        └─► Exec: gdrsc --crate-type lib src/lib.gdrs \
                          --crate-name <dep> \
                          --out-dir target/debug/deps
        │
Step 5: Compile Final Application Target:
        └─► Exec: gdrsc src/main.gdrs \
                          --crate-type bin \
                          --extern dep1=target/debug/deps/libdep1.rlib \
                          --extern dep2=target/debug/deps/libdep2.rlib \
                          -L /opt/homebrew/lib -l raylib \
                          -o target/debug/bouncing_ball
```

---

## 6. Implementation Roadmap for Compiler Support

To prepare `gdrsc` for external build tools:

- [ ] **CLI Update (`src/cli.rs`)**: Add `--crate-type`, `--crate-name`, `--extern`, `-L`, `-l`, and `--out-dir` arguments.
- [ ] **Loader Update (`src/loader/mod.rs`)**: Accept `--extern alias=path` mappings to automatically load and prefix pre-compiled dependency metadata into the program AST.
- [ ] **Object Codegen (`src/codegen/object.rs`)**: Support `--crate-type lib` to emit object archives/metadata bundles instead of invoking `clang` linking for binary targets.
