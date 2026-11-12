### Roadmap

1. Enums & Pattern Matching
       │
       ▼
2. Basic Heap Types (Strings & Dynamic Vectors/Slices)
       │
       ▼
3. Intrinsic Iterators (.iter(), .map(), .collect())
       │
       ▼
4. C FFI (Direct C function calling for native speed)
       │
       ▼
5. Standard Library & Allocator Wiring (System malloc/free, File I/O)
       │
       ▼
6. Smart Pointers & Move Tracking (*rc / *arc in `sanal`)
       │
       ▼
7. Async & Parallel Iterators (Plugging into the finished memory model)
       │
       ▼
8. Module & Import System

### Smart Pointers 

Here is the markdown breakdown of the design for your reference:newlang Memory & Ownership SpecificationDesign Goal: Achieve C-like execution speed and Python-like ergonomics without requiring a complex compile-time borrow checker or a heavy tracing Garbage Collector.1. Core ArchitectureThe memory model relies on two foundational decoupled rules:Allocation Choice is Explicit (let vs *rc / *arc). You decide where memory lives when creating an object.Parameter Passing is Implicitly Reference/Pointer Based. Passing a struct into a function passes a 64-bit address in a Cranelift register by default—whether the struct lives on the stack frame or on the heap.2. Rule 1: Explicit AllocationPython// 1. Stack Allocation (Default)
// Allocates directly on the current function's stack frame. Zero heap, zero ref counting.
let pos = Vec2{ x: 10, y: 20 }

// 2. Heap Allocation (Thread-Local Reference Counting)
// Allocates on heap with a fast, non-atomic reference count header. 
let config = *rc Config{ debug: true }

// 3. Heap Allocation (Atomic Reference Counting)
// Allocates on heap with atomic inc/dec. Safe to pass across thread/goroutine boundaries.
let user = *arc User{ name: "Aram", id: 1 }
3. Rule 2: Function Parameters & Reference PassingPassing a struct into a function hands over a 64-bit pointer in a register. The call site remains completely clean—no mandatory & or * visual clutter required.Python// `v` receives a 64-bit pointer directly to main's stack slot. No heap, no copying!
fn read_player(v: Vec2):
    log!(v.x, v.y)

fn main():
    let pos = Vec2{ x: 10, y: 20 }
    read_player(pos) // Clean call site, 0-cost pointer pass
Explicit DuplicationIf you genuinely want an independent stack copy, invoke an explicit .clone() or copy keyword:Pythonlet original = Vec2{ x: 1, y: 2 }
let duplicate = copy original // Creates a new, distinct stack slot
4. Parameter Passing MatrixSyntaxSemanticsCranelift Codegen StrategyRef-Count Deltax: Vec2Immutable Borrow (Default)Passes 64-bit stack/heap pointer. Reads allowed, writes illegal.0mut x: Vec2Mutable ReferencePasses 64-bit pointer. Mutates caller frame in-place.0move x: Vec2Moved OwnershipPasses 64-bit pointer. Caller unregisters x; callee drops on exit.05. Code ExamplesA. Mutable References (In-Place Stack Mutation)Pythonfn scale(mut v: Vec2, factor: i64):
    v.x *= factor
    v.y *= factor

fn main():
    let mut position = Vec2{ x: 10, y: 20 }
    scale(mut position, 2)
    log!(position.x) // Logs 20!
B. Rust-Style Move SemanticsPythonfn consume(move u: User):
    log!("Processing user:", u.name)
    // `u` is dropped here when `consume` ends

fn main():
    let user = *rc User{ name: "Aram", id: 1 }
    consume(move user)
    
    // TYPECHECK ERROR: Use of moved value `user`
    // log!(user.name)
6. Why No Borrow Checker is RequiredTo prevent dangling pointers without a lifetime graph engine, newlang enforces The Escape Restriction Rule:Rule: A mut reference exists only for the scope of the function call. The typechecker strictly forbids returning a mut parameter or assigning a mut reference into a long-lived struct or global variable.Because references cannot escape the function execution boundary, lifetime graphs are completely unnecessary. The compiler typechecker enforces three simple local rules:mut arguments require the caller variable to be declared with let mut.Functions cannot return a borrowed reference parameter.Using a variable after it has been passed via move triggers an immediate compile-time error (tracked via a simple is_moved: bool flag per variable in the local scope table).
