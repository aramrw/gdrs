use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static BUG_TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn gdrs_bin() -> &'static str {
    env!("CARGO_BIN_EXE_gdrs")
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn make_temp_dir(prefix: &str) -> PathBuf {
    let id = BUG_TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = std::env::temp_dir().join(format!("gdrs_bug_{prefix}_{}_{id}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn run_gdrs_source(name: &str, src: &str) -> Output {
    let dir = make_temp_dir(name);
    let file_path = dir.join(format!("{name}.gdrs"));
    fs::write(&file_path, src).unwrap();
    let out = Command::new(gdrs_bin())
        .current_dir(repo_root())
        .arg(&file_path)
        .output()
        .expect("failed to execute gdrs binary");
    let _ = fs::remove_dir_all(&dir);
    out
}

fn build_gdrs_binary(name: &str, src: &str) -> (PathBuf, PathBuf) {
    let dir = make_temp_dir(name);
    let src_path = dir.join(format!("{name}.gdrs"));
    let bin_path = dir.join(name);
    fs::write(&src_path, src).unwrap();
    let out = Command::new(gdrs_bin())
        .current_dir(repo_root())
        .arg("build")
        .arg(&src_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .expect("failed to execute gdrs build");
    assert!(
        out.status.success(),
        "Expected `{name}` to build, got exit {:?}\nSTDOUT:\n{}\nSTDERR:\n{}",
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (dir, bin_path)
}

fn combined_output(out: &Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[cfg(target_os = "macos")]
fn build_dylib(dir: &std::path::Path, c_name: &str, c_src: &str) -> PathBuf {
    let c_path = dir.join(format!("{c_name}.c"));
    let dylib_path = dir.join(format!("lib{c_name}.dylib"));
    fs::write(&c_path, c_src).unwrap();
    let out = Command::new("clang")
        .arg("-shared")
        .arg("-fPIC")
        .arg(&c_path)
        .arg("-o")
        .arg(&dylib_path)
        .output()
        .expect("failed to invoke clang");
    assert!(
        out.status.success(),
        "clang failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    dylib_path
}

#[cfg(target_os = "macos")]
fn measure_net_allocs_macos(src_for_n: &dyn Fn(usize) -> String, n: usize, args: &[&str]) -> i64 {
    let dir = make_temp_dir("leak_probe");
    let src_path = dir.join("prog.gdrs");
    let bin_path = dir.join("prog");
    fs::write(&src_path, src_for_n(n)).unwrap();

    let build_out = Command::new(gdrs_bin())
        .current_dir(repo_root())
        .arg("build")
        .arg(&src_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .expect("failed to run gdrs build");
    assert!(
        build_out.status.success(),
        "build failed:\n{}",
        combined_output(&build_out)
    );

    let hook_src = r#"
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>

static _Atomic long g_allocs = 0;
static _Atomic long g_frees = 0;

void* hook_malloc(size_t sz) {
    void* p = malloc(sz);
    if (p) atomic_fetch_add(&g_allocs, 1);
    return p;
}
void* hook_calloc(size_t count, size_t sz) {
    void* p = calloc(count, sz);
    if (p) atomic_fetch_add(&g_allocs, 1);
    return p;
}
void* hook_realloc(void* ptr, size_t sz) {
    void* p = realloc(ptr, sz);
    if (!ptr && p) atomic_fetch_add(&g_allocs, 1);
    return p;
}
void hook_free(void* ptr) {
    if (ptr) atomic_fetch_add(&g_frees, 1);
    free(ptr);
}

#define DYLD_INTERPOSE(_replacement,_replacee) \
   __attribute__((used)) static struct{ const void* replacement; const void* replacee; } _interpose_##_replacee \
   __attribute__ ((section ("__DATA,__interpose"))) = { (const void*)(unsigned long)&_replacement, (const void*)(unsigned long)&_replacee };

DYLD_INTERPOSE(hook_malloc, malloc)
DYLD_INTERPOSE(hook_calloc, calloc)
DYLD_INTERPOSE(hook_realloc, realloc)
DYLD_INTERPOSE(hook_free, free)

__attribute__((destructor)) static void report_leaks(void) {
    fprintf(stderr, "NET_ALLOCS=%ld\n", atomic_load(&g_allocs) - atomic_load(&g_frees));
}
"#;
    let dylib = build_dylib(&dir, "alloc_hook", hook_src);

    let run_out = Command::new(&bin_path)
        .args(args)
        .env("DYLD_INSERT_LIBRARIES", &dylib)
        .output()
        .expect("failed to run instrumented binary");
    let _ = fs::remove_dir_all(&dir);

    assert!(
        run_out.status.success(),
        "instrumented binary failed:\n{}",
        combined_output(&run_out)
    );
    let stderr = String::from_utf8_lossy(&run_out.stderr);
    stderr
        .lines()
        .find_map(|line| line.strip_prefix("NET_ALLOCS="))
        .and_then(|v| v.trim().parse::<i64>().ok())
        .unwrap_or_else(|| panic!("Missing NET_ALLOCS in stderr:\n{stderr}"))
}

// ============================================================================
// Regression tests for previously confirmed memory-safety and resource-management bugs
// ============================================================================

/// std/vec.gdrs: Vec::iter/into_iter + VecIter::next copies non-Copy elements bitwise,
/// causing Tracked to be dropped twice for one constructed instance.
#[test]
fn confirmed_bug_vec_iter_double_free_tracked() {
    let out = run_gdrs_source(
        "vec_iter_double_free_tracked",
        r#"
use std::core::Drop
use std::vec::Vec

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

fn main():
	let mut v: Vec<Tracked> = Vec::new()
	v.push(Tracked{ id: 1 })
	for x in v:
		log!("iter {}", x.id)
"#,
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let drop_count = stdout.matches("drop_t 1").count();
    assert!(
        !out.status.success() || drop_count == 1,
        "Expected Tracked(1) to be dropped once (or rejected at compile time), got {drop_count} drops:\n{stdout}"
    );
    if out.status.success() {
        assert_eq!(drop_count, 1, "Double drop in stdout:\n{stdout}");
    }
}

/// std/vec.gdrs: Iterating Vec<String> compiles cleanly and aborts at runtime due to double-free.
#[test]
fn confirmed_bug_vec_string_for_loop_double_free_crash() {
    let out = run_gdrs_source(
        "vec_string_double_free",
        r#"
use std::vec::Vec
use std::string::String

fn main():
	let mut v: Vec<String> = Vec::new()
	v.push(String::from("hello_world_heap_string"))
	for s in v:
		log!("item {}", s.as_str())
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() || combined.contains("[E"),
        "Expected either safe execution or a compile-time error, but binary crashed at runtime:\n{combined}"
    );
}

/// std/vec.gdrs: Vec::iter(&self) returns VecIter without registering a borrow of `v`,
/// allowing drop(v) while `it` is alive and UAF read in `it.next()`.
#[test]
fn confirmed_bug_vec_iter_uaf_after_drop() {
    let out = run_gdrs_source(
        "vec_iter_uaf",
        r#"
use std::vec::Vec
use std::mem::drop

fn main():
	let mut v: Vec<i64> = Vec::new()
	v.push(10)
	let mut it = v.iter()
	drop(v)
	match it.next():
		Option::Some(x) => log!("val {}", x)
		Option::None => log!("none")
"#,
    );
    let combined = combined_output(&out);
    assert!(
        !out.status.success() && combined.contains("E0"),
        "Expected compile-time borrow error when dropping `v` while `it` borrows it, got:\n{combined}"
    );
}

/// src/codegen/branching.rs: `compile_match` refuses to mark `self` as moved outside `*_unwrap`
/// methods (`!is_self_ident || is_unwrap_fn`), double-dropping moved enum payloads on return.
#[test]
fn confirmed_bug_match_self_double_drop() {
    let out = run_gdrs_source(
        "match_self_double_drop",
        r#"
use std::core::Drop

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

enum Wrap:
	One(Tracked)
	Empty

impl Wrap:
	fn into_tracked(self) -> Tracked:
		let mut out = Tracked{ id: 99 }
		match self:
			Wrap::One(t) =>
				out = t
			Wrap::Empty =>
				out = Tracked{ id: 0 }
		return out

fn main():
	let w = Wrap::One(Tracked{ id: 7 })
	let t = w.into_tracked()
	log!("got {}", t.id)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success(),
        "Expected clean exit, got:\n{combined}"
    );
    let drop_7_count = String::from_utf8_lossy(&out.stdout).matches("drop_t 7").count();
    assert_eq!(
        drop_7_count, 1,
        "Expected Tracked(7) to be dropped once, got {drop_7_count}:\n{combined}"
    );
}

/// src/sanal/calls/closures.rs & src/sanal/control_flow/lifetimes.rs:
/// Closures bypass E0106 return-ref checks and `check_block_escape_lifetime` ignores tuples.
#[test]
fn confirmed_bug_closure_escape_local_ref() {
    let out = run_gdrs_source(
        "closure_escape_local_ref",
        r#"
fn main():
	let f = |x|:
		let local = x + 42
		(&local, 1)
	log!("ok")
"#,
    );
    let combined = combined_output(&out);
    assert!(
        !out.status.success() && combined.contains("E0"),
        "Expected compile-time lifetime error for closure returning &local in tuple, got:\n{combined}"
    );
}

/// src/sanal/control_flow/lifetimes.rs & src/sanal/vars.rs:
/// Reassigning an outer `let mut r` to `&inner` inside an `if` block escapes undetected and UAFs.
#[test]
fn confirmed_bug_block_escape_mut_ref_reassignment() {
    let out = run_gdrs_source(
        "block_escape_mut_ref",
        r#"
use std::string::String

fn main():
	let outer = String::from("outer")
	let mut r = &outer
	if true:
		let inner = String::from("inner_dropped")
		r = &inner
	log!("after {}", r.as_str())
"#,
    );
    let combined = combined_output(&out);
    assert!(
        !out.status.success() && combined.contains("E0"),
        "Expected compile-time lifetime error for `&inner` escaping block via `r = &inner`, got:\n{combined}"
    );
}

/// std/string.gdrs & src/ast/mod.rs:
/// `String::as_str(&self) -> str` returns an untracked Copy `str`, allowing use after temp drop.
#[test]
fn confirmed_bug_string_as_str_dangling_temp() {
    let out = run_gdrs_source(
        "string_as_str_dangling",
        r#"
use std::string::String

fn main():
	let s = String::from("temporary_heap").as_str()
	let _other = String::from("overwrite_heap")
	log!("as_str {}", s)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        !out.status.success() && combined.contains("E0"),
        "Expected compile-time borrow error for retaining `.as_str()` past temp drop, got:\n{combined}"
    );
}

/// src/sanal/calls/mod.rs: `TypedExpr::DynCall` skips `validate_call_arguments`,
/// permitting use-after-move (`s` dropped by callee then read by caller).
#[test]
fn confirmed_bug_dyn_call_use_after_move() {
    let out = run_gdrs_source(
        "dyn_call_uam",
        r#"
use std::string::String

trait Sink:
	fn consume(&self, s: String)

obj MySink:
	tag: i64

impl Sink for MySink:
	fn consume(&self, s: String):
		log!("sink {}", s.as_str())

fn main():
	let d: dyn Sink = MySink{ tag: 1 }
	let s = String::from("owned")
	d.consume(s)
	log!("uam {}", s.as_str())
"#,
    );
    let combined = combined_output(&out);
    assert!(
        !out.status.success() && combined.contains("E0382"),
        "Expected E0382 use-after-move on `s` after `d.consume(s)`, got:\n{combined}"
    );
}

/// src/sanal/calls/mod.rs: Calling a closure variable hits `scopes.lookup(&resolved_name).is_some()`,
/// returning `Type::Int` without checking argument types or move semantics.
#[test]
fn confirmed_bug_indirect_closure_call_skips_validation() {
    let out = run_gdrs_source(
        "indirect_closure_uam",
        r#"
use std::string::String

fn main():
	let take = |s|:
		log!("took {}", s)
	let mut f = take
	let s = String::from("hello")
	f(s)
	log!("after {}", s.as_str())
"#,
    );
    let combined = combined_output(&out);
    assert!(
        !out.status.success() && combined.contains("E0"),
        "Expected compile-time error for invalid/moved String passed to closure var `f`, got:\n{combined}"
    );
}

/// src/codegen/intrinsics/macros.rs & src/codegen/runtime.c:
/// `thread!` coerces stack aggregate pointer directly to i64; parent stack unwind causes child UAF crash.
#[test]
fn confirmed_bug_thread_stack_aggregate_uaf() {
    let out = run_gdrs_source(
        "thread_stack_uaf",
        r#"
use std::string::String

extern "C":
	fn usleep(usec: u32) -> i32

fn read_after_sleep(x: String):
	unsafe:
		usleep(50000 as u32)
	log!("child {}", x.as_str())

fn spawn_from_dead_frame():
	let s = String::from("stack_secret_data")
	thread!(|x|: read_after_sleep(x), s)

fn clobber_stack(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64):
	let arr = [a, b, c, d, e, f]
	log!("clobber {}", arr[0])

fn main():
	spawn_from_dead_frame()
	clobber_stack(111, 222, 333, 444, 555, 666)
	unsafe:
		usleep(150000 as u32)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("child stack_secret_data"),
        "Expected child thread to safely read moved String `stack_secret_data`, got:\n{combined}"
    );
}

/// src/codegen/drops/mod.rs (`is_npo_enum`) & src/codegen/objects.rs:
/// `.contains("_ptr_")` misclassifies `Result<*i64, String>` as an NPO enum, discarding `Err` and crashing.
#[test]
fn confirmed_bug_npo_result_ptr_err_corrupts_payload() {
    let out = run_gdrs_source(
        "npo_result_ptr_err",
        r#"
use std::core::Result
use std::string::String

fn main():
	let r: Result<*i64, String> = Result::Err(String::from("bad_err"))
	match r:
		Result::Ok(p) => log!("ok")
		Result::Err(e) => log!("err {}", e.as_str())
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("err bad_err"),
        "Expected clean exit with `err bad_err`, got:\n{combined}"
    );
}

/// src/sanal/macros.rs & src/codegen/runtime.c:
/// `format!` returns heap-allocated `char*` typed as Copy `Type::Str`, leaking on every call.
#[cfg(target_os = "macos")]
#[test]
fn confirmed_bug_format_macro_leaks() {
    let make_src = |n: usize| {
        format!(
            r#"
fn main():
	let mut i = 0
	while i < {n}:
		let s = format!("item {{}}", i)
		i = i + 1
"#
        )
    };
    let net_small = measure_net_allocs_macos(&make_src, 10, &[]);
    let net_large = measure_net_allocs_macos(&make_src, 510, &[]);
    let leaked = net_large - net_small;
    assert!(
        leaked < 50,
        "Expected format! loop not to leak per iteration, leaked {leaked} allocations over 500 calls"
    );
}

/// std/string.gdrs: `push_str` mutates `self.cap` before checking `malloc`/`realloc` for NULL;
/// a subsequent `push_str` then treats `self.ptr == NULL` as allocated `cap > 0` and crashes in memcpy.
#[cfg(target_os = "macos")]
#[test]
fn confirmed_bug_string_push_str_oom_cap_corruption() {
    let sentinel = "x".repeat(77777);
    let src = format!(
        r#"
use std::string::String

fn main():
	let mut s = String::new()
	s = s.push_str("{sentinel}")
	s = s.push_str("a")
	log!("survived {{}}", s.len())
"#
    );
    let (dir, bin_path) = build_gdrs_binary("string_push_oom", &src);

    let oom_hook = r#"
#include <stdlib.h>

void* oom_malloc(size_t sz) {
    if (sz == 77778) {
        return NULL;
    }
    return malloc(sz);
}

#define DYLD_INTERPOSE(_replacement,_replacee) \
   __attribute__((used)) static struct{ const void* replacement; const void* replacee; } _interpose_##_replacee \
   __attribute__ ((section ("__DATA,__interpose"))) = { (const void*)(unsigned long)&_replacement, (const void*)(unsigned long)&_replacee };

DYLD_INTERPOSE(oom_malloc, malloc)
"#;
    let dylib = build_dylib(&dir, "oom_hook", oom_hook);

    let run_out = Command::new(&bin_path)
        .env("DYLD_INSERT_LIBRARIES", &dylib)
        .output()
        .expect("failed to execute oom probe binary");
    let _ = fs::remove_dir_all(&dir);

    assert!(
        run_out.status.success(),
        "Expected String::push_str to remain valid (`cap == 0`) after OOM instead of crashing on next push_str:\n{}",
        combined_output(&run_out)
    );
}

/// src/sanal/mod.rs & src/sanal/mono/instances.rs:
/// Struct fields and enum payloads holding `enum` types (including generic enums like `Option<String>`)
/// stayed `Type::Obj(enum_name)` or remained unmonomorphized during layout synthesis, leaking 100%.
#[cfg(target_os = "macos")]
#[test]
fn confirmed_bug_struct_and_enum_holding_enum_leak() {
    let make_src = |n: usize| {
        format!(
            r#"
use std::string::String

obj Holder:
	s: Option<String>

enum Wrap:
	Has(Option<String>)
	Empty

fn main():
	let mut i = 0
	while i < {n}:
		let h = Holder {{ s: Option::Some(String::from("hello world heap payload")) }}
		let w = Wrap::Has(Option::Some(String::from("nested enum heap payload")))
		i = i + 1
"#
        )
    };
    let net_small = measure_net_allocs_macos(&make_src, 10, &[]);
    let net_large = measure_net_allocs_macos(&make_src, 210, &[]);
    let leaked = net_large - net_small;
    assert!(
        leaked < 50,
        "Expected nested enum fields/payloads in structs and enums not to leak, leaked {leaked} allocations over 200 iterations"
    );
}

/// src/sanal/control_flow/try_op.rs:
/// `?` on non-Copy `Result<T, E>` failed to mark the scrutinee moved or reject moving out of a projection.
#[test]
fn confirmed_bug_try_operator_use_after_move_and_projection_move() {
    let out_uam = run_gdrs_source(
        "try_uam",
        r#"
use std::string::String

fn consume(s: String):
	log!("{}", s.len())

fn test_try(r: Result<String, i64>) -> Result<i64, i64>:
	let a = r?
	consume(a)
	let b = r?
	consume(b)
	return Result::Ok(1)

fn main():
	let _ = test_try(Result::Ok(String::from("hello")))
"#,
    );
    assert!(
        !out_uam.status.success() && combined_output(&out_uam).contains("E0382"),
        "Expected E0382 use-after-move on repeated `?` of Result<String, i64>, got:\n{}",
        combined_output(&out_uam)
    );

    let out_proj = run_gdrs_source(
        "try_proj",
        r#"
use std::string::String

obj Holder:
	res: Result<String, i64>

fn test_proj(h: Holder) -> Result<i64, i64>:
	let s = h.res?
	log!("{}", s.len())
	return Result::Ok(1)

fn main():
	let h = Holder { res: Result::Ok(String::from("hello")) }
	let _ = test_proj(h)
"#,
    );
    assert!(
        !out_proj.status.success() && combined_output(&out_proj).contains("E0507"),
        "Expected E0507 when `?` moves non-Copy payload out of field projection, got:\n{}",
        combined_output(&out_proj)
    );
}

/// src/sanal/control_flow/patterns.rs & src/sanal/scope.rs:
/// `match self:` inside a consuming method did not mark `self` moved, enabling double-free on second match/use.
#[test]
fn confirmed_bug_match_self_consuming_method_use_after_move() {
    let out = run_gdrs_source(
        "match_self_uam",
        r#"
use std::string::String

enum E:
	A(String)
	B

impl E:
	fn bad(self):
		match self:
			E::A(s) => log!("first {}", s.len())
			E::B => log!("b")
		match self:
			E::A(s2) => log!("second {}", s2.len())
			E::B => log!("b2")

fn main():
	let e = E::A(String::from("boom"))
	e.bad()
"#,
    );
    assert!(
        !out.status.success() && combined_output(&out).contains("E0382"),
        "Expected E0382 when `match self:` consumes `self` twice, got:\n{}",
        combined_output(&out)
    );
}

/// src/sanal/calls/mod.rs & src/codegen/calls.rs:
/// Consuming `self` trait-object calls double-freed even on a single call and allowed use-after-move.
#[test]
fn confirmed_bug_dyn_trait_consuming_self_drop_count_and_uam() {
    let single_out = run_gdrs_source(
        "dyn_consume_once",
        r#"
use std::string::String

trait Take:
	fn into_str(self) -> String

obj Hold:
	id: i64
	s: String

impl Drop for Hold:
	fn drop(&mut self):
		log!("drop_h {}", self.id)

impl Take for Hold:
	fn into_str(self) -> String:
		return String::from(self.s.as_str())

fn main():
	let h = Hold { id: 77, s: String::from("ok") }
	let d: dyn Take = h as dyn Take
	let out = d.into_str()
	log!("len={}", out.len())
"#,
    );
    let combined_single = combined_output(&single_out);
    let drop_count = combined_single.matches("drop_h 77").count();
    assert!(
        single_out.status.success() && combined_single.contains("len=2") && drop_count == 1,
        "Expected single `d.into_str()` to succeed and drop Hold once (got {drop_count}):\n{combined_single}"
    );

    let double_out = run_gdrs_source(
        "dyn_consume_twice",
        r#"
use std::string::String

trait Take:
	fn into_str(self) -> String

obj Hold:
	s: String

impl Take for Hold:
	fn into_str(self) -> String:
		return String::from(self.s.as_str())

fn main():
	let d: dyn Take = Hold { s: String::from("ok") } as dyn Take
	let a = d.into_str()
	let b = d.into_str()
	log!("{} {}", a.len(), b.len())
"#,
    );
    assert!(
        !double_out.status.success() && combined_output(&double_out).contains("E0382"),
        "Expected E0382 on second consuming `dyn Take` call, got:\n{}",
        combined_output(&double_out)
    );

    let borrow_out = run_gdrs_source(
        "dyn_consume_through_ref",
        r#"
use std::string::String

trait Take:
	fn into_str(self) -> String

obj Hold:
	s: String

impl Take for Hold:
	fn into_str(self) -> String:
		return String::from(self.s.as_str())

fn call_ref(d: &dyn Take):
	let _ = d.into_str()

fn main():
	let d: dyn Take = Hold { s: String::from("ok") } as dyn Take
	call_ref(&d)
"#,
    );
    assert!(
        !borrow_out.status.success() && combined_output(&borrow_out).contains("E0507"),
        "Expected E0507 when calling consuming dyn method through `&dyn Take`, got:\n{}",
        combined_output(&borrow_out)
    );
}

/// src/sanal/mod.rs, src/sanal/scope.rs & src/sanal/compat.rs:
/// Trait/display methods that treat bare `self` as borrowed at call sites must not move `self` internally.
#[test]
fn confirmed_bug_non_consuming_self_cannot_move_self() {
    let out = run_gdrs_source(
        "borrowed_self_move",
        r#"
use std::string::String

trait Score:
	fn score(self) -> i64

obj Boxed:
	name: String

fn consume(b: Boxed):
	log!("{}", b.name.len())

impl Score for Boxed:
	fn score(self) -> i64:
		consume(self)
		return 1

fn main():
	let b = Boxed { name: String::from("hi") }
	log!("{}", b.score())
"#,
    );
    assert!(
        !out.status.success() && combined_output(&out).contains("E0507"),
        "Expected E0507 when non-consuming `self` method moves `self`, got:\n{}",
        combined_output(&out)
    );
}

/// src/sanal/control_flow/lifetimes.rs & blocks.rs:
/// Returning `str` or `VecIter<T>` derived from locals/temporaries escaped dangling pointers.
#[test]
fn confirmed_bug_return_local_as_str_and_vec_iter() {
    let out_temp_str = run_gdrs_source(
        "return_temp_as_str",
        r#"
use std::string::String

fn bad() -> str:
	return String::from("ephemeral").as_str()

fn main():
	log!("{}", bad())
"#,
    );
    assert!(
        !out_temp_str.status.success() && combined_output(&out_temp_str).contains("E0515"),
        "Expected E0515 returning temp String.as_str(), got:\n{}",
        combined_output(&out_temp_str)
    );

    let out_local_str = run_gdrs_source(
        "return_local_as_str",
        r#"
use std::string::String

fn bad() -> str:
	let s = String::from("local")
	let p = s.as_str()
	return p

fn main():
	log!("{}", bad())
"#,
    );
    assert!(
        !out_local_str.status.success() && combined_output(&out_local_str).contains("E0515"),
        "Expected E0515 returning local String slice binding, got:\n{}",
        combined_output(&out_local_str)
    );

    let out_vec_iter = run_gdrs_source(
        "return_local_vec_iter",
        r#"
use std::vec::Vec
use std::vec::VecIter

fn bad() -> VecIter<i64>:
	let v: Vec<i64> = Vec::new()
	v.push(123)
	return v.iter()

fn main():
	let _ = bad()
"#,
    );
    assert!(
        !out_vec_iter.status.success() && combined_output(&out_vec_iter).contains("E0515"),
        "Expected E0515 returning VecIter of local Vec, got:\n{}",
        combined_output(&out_vec_iter)
    );

    let ok_param_borrow = run_gdrs_source(
        "return_param_as_str_ok",
        r#"
use std::string::String

fn view(s: &String) -> str:
	let sub = s.as_str()
	return sub

fn main():
	let s = String::from("hello")
	log!("v={}", view(&s))
"#,
    );
    let combined_ok = combined_output(&ok_param_borrow);
    assert!(
        ok_param_borrow.status.success() && combined_ok.contains("v=hello"),
        "Expected borrowing from `&String` parameter via local binding to compile & run, got:\n{combined_ok}"
    );
}

/// std/string.gdrs: `String::new().as_str()` previously cast `ptr == NULL` to `str`, crashing `strlen`.
#[test]
fn confirmed_bug_empty_string_as_str_non_null() {
    let out = run_gdrs_source(
        "empty_string_as_str",
        r#"
use std::string::String

extern "C":
	fn strlen(s: str) -> u64

fn main():
	let s = String::new()
	let p = s.as_str()
	let mut n = 0
	unsafe:
		n = strlen(p) as i64
	log!("len={} eq={}", n, p == "")
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("len=0 eq=true"),
        "Expected `String::new().as_str()` to return valid non-null `\"\"`, got:\n{combined}"
    );
}

/// src/codegen/intrinsics/macros.rs:
/// Named functions returning Indirect (`sret`) structs like `String` spawned via `thread!(f, arg)`
/// skipped trampoline synthesis, corrupting `sret` and crashing child threads.
#[test]
fn confirmed_bug_thread_named_fn_sret_no_crash() {
    let out = run_gdrs_source(
        "thread_named_fn_sret",
        r#"
use std::string::String

extern "C":
	fn usleep(usec: u32) -> i32

fn ret_str(x: i64) -> String:
	log!("arg={}", x)
	return String::from("threaded_sret_value")

fn main():
	let _ = thread!(ret_str, 42)
	unsafe:
		let _ = usleep(50000 as u32)
	log!("done")
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("arg=42") && combined.contains("done"),
        "Expected `thread!(ret_str, 42)` to pass arg=42 and handle sret cleanly, got:\n{combined}"
    );
}

/// src/sanal/control_flow/blocks.rs:
/// Blocks whose last statement is `let` returned the bound variable's type instead of `Type::Unit`,
/// causing false E0308 mismatches across `if`/`else` arms and re-registering dropped `let` values
/// as block result temps in `compile_block`.
#[test]
fn bug_fuzz1_if_else_trailing_let_unit_and_no_double_drop() {
    let out = run_gdrs_source(
        "fuzz1_trailing_let",
        r#"
use std::vec::Vec

fn check_branches(flag: bool) -> i64:
	if flag:
		let a: i64 = 10
	else:
		let v: Vec<i64> = vec![1, 2, 3]
	if flag:
		let x: Vec<i64> = vec![4, 5]
	else:
		let y: Vec<i64> = vec![6, 7]
	return 42

fn main():
	let r1 = check_branches(true)
	let r2 = check_branches(false)
	log!("r1={} r2={}", r1, r2)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("r1=42 r2=42"),
        "Expected trailing `let` inside `if`/`else` to check as Unit and run without double-drop, got:\n{combined}"
    );

    #[cfg(target_os = "macos")]
    {
        let make_src = |n: usize| {
            format!(
                r#"
use std::vec::Vec

fn step(flag: bool):
	if flag:
		let v: Vec<i64> = vec![10, 20, 30]
	else:
		let w: Vec<i64> = vec![40, 50, 60]

fn main():
	let mut i = 0
	while i < {n}:
		step((i % 2) == 0)
		i = i + 1
"#
            )
        };
        let net_small = measure_net_allocs_macos(&make_src, 10, &[]);
        let net_large = measure_net_allocs_macos(&make_src, 210, &[]);
        let leaked = net_large - net_small;
        assert_eq!(
            leaked, 0,
            "Expected trailing `let Vec` in `if`/`else` not to leak, leaked {leaked} allocations over 200 iterations"
        );
    }
}

/// src/codegen/expr.rs:
/// `coerce_val` and `coerce_typed_val` omitted `types::I16`, lacked signed/unsigned extension
/// distinction on widening, and passed `I8`/`I16` directly to `fcvt_from_*`.
#[test]
fn bug_fuzz2_i16_u16_coercion_reassignment_and_float_cast() {
    let out = run_gdrs_source(
        "fuzz2_i16_u16",
        r#"
fn main():
	let mut a: i16 = -154
	let mut b: u16 = 50000
	a = 11
	a = -88
	b = 1234
	let a32: i32 = a as i32
	let a64: i64 = a as i64
	let b32: u32 = b as u32
	let b64: u64 = b as u64
	let mut c8: i8 = -12
	let c16: i16 = c8 as i16
	let mut u8v: u8 = 250
	let u16v: u16 = u8v as u16
	let af32: f32 = a as f32
	let af64: f64 = a as f64
	let bf32: f32 = b as f32
	let bf64: f64 = b as f64
	assert_eq!(a32, -88 as i32)
	assert_eq!(a64, -88)
	assert_eq!(b32, 1234 as u32)
	assert_eq!(b64, 1234 as u64)
	assert_eq!(c16, -12 as i16)
	assert_eq!(u16v, 250 as u16)
	assert!(af32 < 0.0 as f32)
	assert!(af64 < 0.0)
	assert!(bf32 > 1000.0 as f32)
	assert!(bf64 > 1000.0)
	log!("ok {} {} {} {}", a, b, c16, u16v)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("ok -88 1234 -12 250"),
        "Expected i16/u16 locals, reassignments, width coercions, and float casts to work, got:\n{combined}"
    );
}

/// src/ast/mod.rs:
/// `Type::is_copy` omitted `Type::Array(elem, _) => elem.is_copy()`, causing arrays of `Copy`
/// elements like `[i64; 4]` to move on binding/assignment and trigger false `E0382`.
#[test]
fn bug_fuzz3_fixed_array_copy_semantics() {
    let ok_out = run_gdrs_source(
        "fuzz3_array_copy_pos",
        r#"
fn main():
	let a: [i64; 4] = [1, 2, 3, 4]
	let mut b: [i64; 4] = a
	b = a
	let tp: [(i64, bool); 2] = [(7, true), (8, false)]
	let tp2: [(i64, bool); 2] = tp
	log!("a={:?} b={:?} tp={}", a, b, tp[0].0 + tp2[1].0)
"#,
    );
    let ok_combined = combined_output(&ok_out);
    assert!(
        ok_out.status.success() && ok_combined.contains("a=[1, 2, 3, 4] b=[1, 2, 3, 4] tp=15"),
        "Expected `[i64; 4]` and `[(i64, bool); 2]` to be Copy without E0382, got:\n{ok_combined}"
    );

    let err_out = run_gdrs_source(
        "fuzz3_array_non_copy_neg",
        r#"
use std::string::String

fn main():
	let arr: [String; 2] = [String::from("a"), String::from("b")]
	let moved: [String; 2] = arr
	log!("{:?}", arr)
"#,
    );
    let err_combined = combined_output(&err_out);
    assert!(
        !err_out.status.success() && err_combined.contains("E0382"),
        "Expected `[String; 2]` not to be Copy and reject use-after-move with E0382, got:\n{err_combined}"
    );
}

/// src/codegen/func.rs & src/codegen/branching.rs:
/// Dead statements after `return`, `break`, `continue`, or all-diverging `if`/`else`/`match`
/// caused `compile_func` / `expr_is_terminator` to append terminators to already-filled Cranelift blocks.
#[test]
fn bug_fuzz4_dead_code_after_return_break_continue_and_diverging_branches() {
    let out = run_gdrs_source(
        "fuzz4_dead_after_term",
        r#"
enum Kind:
	A
	B

fn early_unit():
	return
	let mut total: i64 = 0

fn early_val(flag: bool) -> i64:
	if flag:
		return 10
	else:
		return 20
	let unreachable_x: i64 = 999
	return unreachable_x

fn match_diverge(k: Kind) -> i64:
	match k:
		Kind::A => return 1
		Kind::B => return 2
	let unreachable_y: i64 = 888
	return unreachable_y

fn loop_dead_code() -> i64:
	let mut acc: i64 = 0
	let mut i: i64 = 0
	while i < 4:
		i += 1
		if i == 2:
			continue
			acc += 100
		if i == 3:
			break
			let dead: i64 = 50
		acc += i
	return acc

fn main():
	early_unit()
	let a = early_val(true)
	let b = early_val(false)
	let m = match_diverge(Kind::B)
	let l = loop_dead_code()
	log!("a={} b={} m={} l={}", a, b, m, l)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("a=10 b=20 m=2 l=1"),
        "Expected dead statements after return/break/continue/diverging branches to compile cleanly, got:\n{combined}"
    );
}

/// src/sanal/calls/mod.rs & src/sanal/objects/construction.rs:
/// Enum variant calls were type-checked once in `type_check_call`'s `typed_args` loop and again in
/// `type_check_enum_construct`, moving arguments like `Box::new(v)` twice and triggering false E0382.
#[test]
fn bug_fuzz5_enum_variant_arg_evaluated_once_with_box_move() {
    let ok_out = run_gdrs_source(
        "fuzz5_enum_single_eval_pos",
        r#"
use std::boxed::Box
use std::string::String

#[derive(Debug)]
enum RecNode:
	Leaf(i64)
	Cons(i64, Box<RecNode>)

fn main():
	let mut v: RecNode = RecNode::Leaf(1)
	v = RecNode::Cons(34, Box::new(v))
	let s: String = String::from("boxed_opt")
	let o: Option<Box<String> > = Option::Some(Box::new(s))
	log!("{:?} {:?}", v, o)
"#,
    );
    let ok_combined = combined_output(&ok_out);
    assert!(
        ok_out.status.success()
            && ok_combined.contains("Cons(34, Leaf(1))")
            && ok_combined.contains("Some(\"boxed_opt\")"),
        "Expected enum constructor moving into Box::new(v) to evaluate args once without false E0382, got:\n{ok_combined}"
    );
}

// ============================================================================
// Batch 1 Low-Level Foundations Tests (ARM64 C-ABI HFA/sret, Ops, Intrinsics,
// Raw Pointers, Top-Level Consts, IEEE-754 Math, AST-Indexed Modules)
// ============================================================================

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn batch1_arm64_c_abi_hfa_and_sret() {
    let dir = make_temp_dir("batch1_abi_hfa_sret");
    let c_src = r#"
typedef struct { float x; float y; } Vec2f;
typedef struct { double x; double y; double z; } Vec3d;
typedef struct { double x; double y; double z; double w; } Vec4d;
typedef struct { long a; long b; long c; long d; } BigStruct;

Vec2f c_vec2f_add(Vec2f a, Vec2f b) {
    Vec2f out = { a.x + b.x, a.y + b.y };
    return out;
}

Vec3d c_vec3d_scale(Vec3d v, double s) {
    Vec3d out = { v.x * s, v.y * s, v.z * s };
    return out;
}

Vec4d c_vec4d_add(Vec4d a, Vec4d b) {
    Vec4d out = { a.x + b.x, a.y + b.y, a.z + b.z, a.w + b.w };
    return out;
}

BigStruct c_big_make(long seed, long step) {
    BigStruct out = { seed, seed + step, seed + 2 * step, seed + 3 * step };
    return out;
}

long c_big_sum(BigStruct bs) {
    return bs.a + bs.b + bs.c + bs.d;
}
"#;
    let _dylib = build_dylib(&dir, "abi_probe", c_src);

    let gdrs_src = r#"
obj Vec2f:
	x: f32
	y: f32

obj Vec3d:
	x: f64
	y: f64
	z: f64

obj Vec4d:
	x: f64
	y: f64
	z: f64
	w: f64

obj BigStruct:
	a: i64
	b: i64
	c: i64
	d: i64

extern "C":
	fn c_vec2f_add(a: Vec2f, b: Vec2f) -> Vec2f
	fn c_vec3d_scale(v: Vec3d, s: f64) -> Vec3d
	fn c_vec4d_add(a: Vec4d, b: Vec4d) -> Vec4d
	fn c_big_make(seed: i64, step: i64) -> BigStruct
	fn c_big_sum(bs: BigStruct) -> i64

fn main():
	unsafe:
		let v2 = c_vec2f_add(Vec2f{ x: 1.5 as f32, y: 2.5 as f32 }, Vec2f{ x: 4.0 as f32, y: 5.0 as f32 })
		let v3 = c_vec3d_scale(Vec3d{ x: 1.0, y: 2.0, z: 3.0 }, 2.5)
		let v4 = c_vec4d_add(
			Vec4d{ x: 1.0, y: 2.0, z: 3.0, w: 4.0 },
			Vec4d{ x: 10.0, y: 20.0, z: 30.0, w: 40.0 }
		)
		let big = c_big_make(10, 5)
		let total = c_big_sum(big)
		log!("v2={} {}", v2.x, v2.y)
		log!("v3={} {} {}", v3.x, v3.y, v3.z)
		log!("v4={} {} {} {}", v4.x, v4.y, v4.z, v4.w)
		log!("big={} {} {} {} sum={}", big.a, big.b, big.c, big.d, total)
"#;
    let src_path = dir.join("abi_test.gdrs");
    let bin_path = dir.join("abi_test");
    fs::write(&src_path, gdrs_src).unwrap();

    let build_out = Command::new(gdrs_bin())
        .current_dir(repo_root())
        .arg("build")
        .arg(&src_path)
        .arg("-o")
        .arg(&bin_path)
        .arg("-L")
        .arg(&dir)
        .arg("-l")
        .arg("abi_probe")
        .output()
        .expect("failed to build abi test");
    assert!(
        build_out.status.success(),
        "gdrs build failed:\n{}",
        combined_output(&build_out)
    );

    let run_out = Command::new(&bin_path)
        .env("DYLD_LIBRARY_PATH", &dir)
        .output()
        .expect("failed to run abi_test binary");
    let _ = fs::remove_dir_all(&dir);

    let out_str = combined_output(&run_out);
    assert!(
        run_out.status.success()
            && out_str.contains("v2=5.5 7.5")
            && out_str.contains("v3=2.5 5.0 7.5")
            && out_str.contains("v4=11.0 22.0 33.0 44.0")
            && out_str.contains("big=10 15 20 25 sum=70"),
        "ARM64 C-ABI HFA/sret test failed:\n{out_str}"
    );
}

#[cfg(target_os = "macos")]
#[test]
fn batch1_overloaded_ops_and_dyncall_temp_drop() {
    let ok_out = run_gdrs_source(
        "batch1_overloaded_ops_ok",
        r#"
use std::ops::{Add, Sub, Mul, Div, Rem, Neg}

obj Num:
	v: i64

impl Mul for Num:
	fn mul(&self, other: &Num) -> Num:
		return Num{ v: self.v * other.v }

impl Div for Num:
	fn div(&self, other: &Num) -> Num:
		return Num{ v: self.v / other.v }

impl Rem for Num:
	fn rem(&self, other: &Num) -> Num:
		return Num{ v: self.v % other.v }

impl Neg for Num:
	fn neg(&self) -> Num:
		return Num{ v: 0 - self.v }

obj RefBox:
	v: i64

impl Add for RefBox:
	fn add(&self, other: &RefBox) -> RefBox:
		return RefBox{ v: self.v + other.v }

fn main():
	let a = Num{ v: 20 }
	let b = Num{ v: 6 }
	let m = a * b
	let d = a / b
	let r = a % b
	let n = -b
	let rb1 = RefBox{ v: 12 }
	let rb2 = RefBox{ v: 30 }
	let rb_sum1 = &rb1 + &rb2
	let rb_sum2 = rb1 + rb2
	log!("ops={} {} {} {} {} {}", m.v, d.v, r.v, n.v, rb_sum1.v, rb_sum2.v)
"#,
    );
    let ok_str = combined_output(&ok_out);
    assert!(
        ok_out.status.success() && ok_str.contains("ops=120 3 2 -6 42 42"),
        "Overloaded Mul/Div/Rem/Neg/&T+T failed:\n{ok_str}"
    );

    let uam_out = run_gdrs_source(
        "batch1_overloaded_ops_move_err",
        r#"
use std::ops::Add
use std::string::String

obj Owned:
	label: String

impl Add for Owned:
	fn add(self, other: Owned) -> Owned:
		return Owned{ label: self.label }

fn main():
	let a = Owned{ label: String::from("a") }
	let b = Owned{ label: String::from("b") }
	let c = a + b
	log!("{}", a.label)
"#,
    );
    let uam_str = combined_output(&uam_out);
    assert!(
        !uam_out.status.success() && uam_str.contains("E0382"),
        "Expected E0382 use-after-move after moving non-Copy operand in `+`, got:\n{uam_str}"
    );

    let make_dyn_src = |n: usize| {
        format!(
            r#"
use std::string::String

trait Greeter:
	fn greet(&self) -> String

obj Bot:
	id: i64

impl Greeter for Bot:
	fn greet(&self) -> String:
		return String::from("hello_dyn_trait_temp_drop_check_payload")

fn main():
	let b = Bot{{ id: 1 }}
	let g: dyn Greeter = b
	let mut i = 0
	while i < {n}:
		g.greet()
		i = i + 1
"#
        )
    };
    let net1 = measure_net_allocs_macos(&make_dyn_src, 200, &[]);
    let net2 = measure_net_allocs_macos(&make_dyn_src, 2000, &[]);
    assert_eq!(
        net1, net2,
        "Expected DynCall temporary return String to drop with 0 leak growth (n=200 net={net1}, n=2000 net={net2})"
    );
}

#[test]
fn batch1_mem_intrinsics_and_vec_raw_parts() {
    let out = run_gdrs_source(
        "batch1_mem_and_vec_raw",
        r#"
use std::mem::{size_of, align_of, alloc_aligned}
use std::vec::Vec
use std::libc::{malloc, free}

obj Padded:
	flag: u8
	val: i64

fn main():
	let p = Padded{ flag: 1 as u8, val: 99 }
	log!(
		"sizes={} {} {} {} {} align={} {} vec={}",
		size_of::<i64>(),
		size_of::<i32>(),
		size_of::<u8>(),
		size_of::<Padded>(),
		size_of(&p),
		align_of::<Padded>(),
		align_of(&p),
		size_of::<Vec<i64> >()
	)
	let aligned = alloc_aligned(256, 64)
	let is_aligned = ((aligned as i64) != 0) && (((aligned as i64) % 64) == 0)
	unsafe:
		free(aligned)

	let mut v: Vec<i64> = Vec::new()
	v.push(10)
	v.push(20)
	v.push(30)
	unsafe:
		let p_mut = v.as_mut_ptr()
		let slot1 = p_mut + 1
		*slot1 = 222
		let p_const = v.as_ptr()
		let third = *(p_const + 2)

		let raw_buf = malloc(3 * size_of::<i64>()) as *i64
		*raw_buf = 100
		*(raw_buf + 1) = 200
		*(raw_buf + 2) = 300
		let rebuilt = Vec::from_raw_parts(raw_buf, 3, 3)
		log!(
			"aligned={} vec_raw={} {} rebuilt={} {}",
			is_aligned,
			v[1],
			third,
			rebuilt[0],
			rebuilt[2]
		)
"#,
    );
    let s = combined_output(&out);
    assert!(
        out.status.success()
            && s.contains("sizes=8 4 1 16 16 align=8 8 vec=24")
            && s.contains("aligned=true vec_raw=222 30 rebuilt=100 300"),
        "size_of/align_of/alloc_aligned/Vec raw parts test failed:\n{s}"
    );
}

#[test]
fn batch1_top_level_const_math_and_ast_modules() {
    let basic_out = run_gdrs_source(
        "batch1_const_and_math",
        r#"
use std::math::{PI, E, EPSILON, INFINITY, NEG_INFINITY, NAN, is_nan, is_infinite, is_finite}

const LIMIT: i64 = 10 + 2 * 3
const DOUBLE_LIMIT: i64 = LIMIT * 2
const BYTE_MAX: u8 = 250
const HALF: f32 = 1.5
const FLAG: bool = 3 < 5
const TAG: str = "const_ok"

fn main():
	log!(
		"const={} {} {} {} {} {}",
		LIMIT,
		DOUBLE_LIMIT,
		BYTE_MAX as i64,
		HALF,
		FLAG,
		TAG
	)
	log!(
		"ieee={} {} {} {} {} {} eps={}",
		is_nan(NAN),
		is_nan(PI),
		is_infinite(INFINITY),
		is_infinite(NEG_INFINITY),
		is_finite(E),
		is_finite(INFINITY),
		EPSILON > 0.0
	)
"#,
    );
    let basic_str = combined_output(&basic_out);
    assert!(
        basic_out.status.success()
            && basic_str.contains("const=16 32 250 1.5 true const_ok")
            && basic_str.contains("ieee=true false true true true false eps=true"),
        "Top-level const & math IEEE-754 constants test failed:\n{basic_str}"
    );

    let dir = make_temp_dir("batch1_ast_modules");
    let pkg_dir = dir.join("pkg");
    fs::create_dir_all(&pkg_dir).unwrap();

    fs::write(
        pkg_dir.join("fake.gdrs"),
        r#"
// obj Widget fn make_val const SCALE
pub fn dummy() -> i64:
	let note = "obj Widget fn make_val const SCALE"
	return 0
"#,
    )
    .unwrap();

    fs::write(
        pkg_dir.join("real.gdrs"),
        r#"
pub obj Widget:
	pub val: i64

pub const SCALE: i64 = 10
const SECRET: i64 = 99

fn sibling_secret() -> i64:
	return 7

pub fn make_val() -> i64:
	return sibling_secret() * SCALE
"#,
    )
    .unwrap();

    fs::write(
        dir.join("facade.gdrs"),
        r#"
pub use pkg::Widget
pub use pkg::make_val
"#,
    )
    .unwrap();

    let main_ok = dir.join("main_ok.gdrs");
    fs::write(
        &main_ok,
        r#"
use facade::{Widget, make_val}
use pkg::SCALE

fn main():
	let w = Widget{ val: make_val() + SCALE }
	log!("mod_ok={}", w.val)
"#,
    )
    .unwrap();

    let ok_mod_out = Command::new(gdrs_bin())
        .current_dir(repo_root())
        .arg(&main_ok)
        .output()
        .expect("failed to run AST module test");
    let ok_mod_str = combined_output(&ok_mod_out);

    let main_priv = dir.join("main_priv.gdrs");
    fs::write(
        &main_priv,
        r#"
use pkg::SECRET

fn main():
	log!("{}", SECRET)
"#,
    )
    .unwrap();

    let priv_out = Command::new(gdrs_bin())
        .current_dir(repo_root())
        .arg(&main_priv)
        .output()
        .expect("failed to run private const visibility test");
    let priv_str = combined_output(&priv_out);
    let _ = fs::remove_dir_all(&dir);

    assert!(
        ok_mod_out.status.success() && ok_mod_str.contains("mod_ok=80"),
        "AST-indexed module lookup + pub use + intra-module sibling fn + pub const failed:\n{ok_mod_str}"
    );
    assert!(
        !priv_out.status.success() && priv_str.contains("E0603"),
        "Expected E0603 when importing private `const SECRET`, got:\n{priv_str}"
    );
}

#[test]
fn priority2_closures_move_drop_fn_fnmut_fnonce() {
    // 1. Positive: move closure transfers Drop ownership and drops once; Fn / FnMut / FnOnce semantics
    let ok_out = run_gdrs_source(
        "p2_closures_ok",
        r#"
use std::core::Drop
use std::string::String

obj Canary:
	pub tag: i64

impl Drop for Canary:
	fn drop(mut self):
		log!("drop_canary={}", self.tag)

fn apply_fn(f: $F, x: i64) -> i64 where F: Fn(i64) -> i64:
	return f(x) + f(x + 1)

fn consume_str(s: String) -> i64:
	return s.len()

fn main():
	let base = 10
	let fn_closure = |x|: x + base
	log!("fn_res={}", apply_fn(fn_closure, 5))

	let mut acc = 0
	if true:
		let mut mut_closure = |x|:
			acc += x
			acc
		let a1 = mut_closure(3)
		let a2 = mut_closure(4)
		log!("fnmut_res={},{}", a1, a2)
	log!("acc_after={}", acc)

	let moved_msg = String::from("owned")
	let c_moved = Canary{ tag: 77 }
	if true:
		let once_closure = move ||:
			let len = consume_str(moved_msg)
			len + c_moved.tag
		log!("fnonce_res={}", once_closure())
	log!("after_inner")
"#,
    );
    let ok_str = combined_output(&ok_out);
    assert!(
        ok_out.status.success()
            && ok_str.contains("fn_res=31")
            && ok_str.contains("fnmut_res=3,7")
            && ok_str.contains("acc_after=7")
            && ok_str.contains("fnonce_res=82")
            && ok_str.matches("drop_canary=77").count() == 1
            && ok_str.contains("after_inner"),
        "Positive closure test failed:\n{ok_str}"
    );

    // 2. Negative: use after `move` closure capture (E0382)
    let uam_moved = run_gdrs_source(
        "p2_closure_move_uam",
        r#"
use std::string::String

fn main():
	let s = String::from("abc")
	let f = move ||: s.len()
	log!("{}", s.len())
"#,
    );
    let uam_str = combined_output(&uam_moved);
    assert!(
        !uam_moved.status.success() && uam_str.contains("E0382"),
        "Expected E0382 when using moved value after `move` closure capture, got:\n{uam_str}"
    );

    // 3. Negative: FnOnce closure called twice (E0382)
    let call_twice = run_gdrs_source(
        "p2_closure_fnonce_twice",
        r#"
use std::string::String

fn consume(s: String) -> i64:
	return s.len()

fn main():
	let s = String::from("hello")
	let f = move ||: consume(s)
	let a = f()
	let b = f()
	log!("{} {}", a, b)
"#,
    );
    let twice_str = combined_output(&call_twice);
    assert!(
        !call_twice.status.success() && twice_str.contains("E0382"),
        "Expected E0382 when calling FnOnce closure twice, got:\n{twice_str}"
    );

    // 4. Negative: FnMut closure bound without `let mut` (E0382/E0596) and outer mutation while borrowed (E0506)
    let immut_fnmut = run_gdrs_source(
        "p2_closure_immut_fnmut",
        r#"
fn main():
	let mut count = 0
	let f = ||:
		count += 1
		count
	f()
"#,
    );
    let immut_str = combined_output(&immut_fnmut);
    assert!(
        !immut_fnmut.status.success() && (immut_str.contains("E0382") || immut_str.contains("E0596")),
        "Expected E0382/E0596 calling FnMut closure stored in immutable `let`, got:\n{immut_str}"
    );

    let outer_mut_borrow = run_gdrs_source(
        "p2_closure_outer_mut_conflict",
        r#"
fn main():
	let mut count = 0
	let f = ||: count + 1
	count = 99
	log!("{}", f())
"#,
    );
    let conflict_str = combined_output(&outer_mut_borrow);
    assert!(
        !outer_mut_borrow.status.success() && conflict_str.contains("E0506"),
        "Expected E0506 mutating variable while borrowed by closure, got:\n{conflict_str}"
    );
}

#[test]
fn priority2_closures_rfc2229_disjoint_and_escape_rules() {
    // 1. Positive RFC 2229: capture `p.x` by ref while mutating `p.y` outside
    let ok_disjoint = run_gdrs_source(
        "p2_rfc2229_disjoint_ok",
        r#"
obj Pair:
	pub x: i64
	pub y: i64

fn main():
	let mut p = Pair{ x: 10, y: 20 }
	let read_x = ||: p.x * 2
	p.y = 50
	log!("disjoint={},{}", read_x(), p.y)
"#,
    );
    let disjoint_str = combined_output(&ok_disjoint);
    assert!(
        ok_disjoint.status.success() && disjoint_str.contains("disjoint=20,50"),
        "RFC 2229 disjoint field capture failed:\n{disjoint_str}"
    );

    // 2. Negative RFC 2229: mutating captured field `p.x` fails with E0506
    let bad_disjoint = run_gdrs_source(
        "p2_rfc2229_conflict",
        r#"
obj Pair:
	pub x: i64
	pub y: i64

fn main():
	let mut p = Pair{ x: 10, y: 20 }
	let read_x = ||: p.x * 2
	p.x = 99
	log!("{}", read_x())
"#,
    );
    let bad_disjoint_str = combined_output(&bad_disjoint);
    assert!(
        !bad_disjoint.status.success() && bad_disjoint_str.contains("E0506"),
        "Expected E0506 mutating field `p.x` captured by closure, got:\n{bad_disjoint_str}"
    );

    // 3. Returning a non-`move` borrowing closure fails with E0373
    let bad_escape = run_gdrs_source(
        "p2_closure_escape_e0373",
        r#"
fn leak() -> i64:
	let local = 42
	return |x|: x + local
fn main():
	log!("ok")
"#,
    );
    let bad_escape_str = combined_output(&bad_escape);
    assert!(
        !bad_escape.status.success() && bad_escape_str.contains("E0373"),
        "Expected E0373 when returning closure borrowing local variable, got:\n{bad_escape_str}"
    );

    // 4. Passing capturing closure to bare `fn(i64) -> i64` rejected with E0434
    let bad_fn_ptr = run_gdrs_source(
        "p2_closure_fn_ptr_e0434",
        r#"
fn run_ptr(f: fn(i64) -> i64, x: i64) -> i64:
	return f(x)

fn main():
	let k = 5
	log!("{}", run_ptr(|x|: x + k, 10))
"#,
    );
    let bad_fn_ptr_str = combined_output(&bad_fn_ptr);
    assert!(
        !bad_fn_ptr.status.success() && bad_fn_ptr_str.contains("E0434"),
        "Expected E0434 passing capturing closure as bare fn pointer, got:\n{bad_fn_ptr_str}"
    );
}

#[test]
fn priority2_lazy_iterator_chaining() {
    let out = run_gdrs_source(
        "p2_lazy_iter_chaining",
        r#"
use std::vec::Vec
use std::iter::Range
use std::core::Option

fn main():
	let v = Vec::from_slice([1, 2, 3, 4, 5, 6])
	let scale = 10
	let threshold = 25
	let filtered = v.iter().map(|x|: x * scale).filter(|x|: *x > threshold).collect()
	assert_eq!(filtered.len(), 4)
	log!("vec_chain={},{},{},{}", filtered[0], filtered[1], filtered[2], filtered[3])

	let range_sum = (Range{ start: 1, end: 6 }).map(|x|: x * 2).filter(|x|: *x >= 6).fold(0, |acc, x|: acc + x)
	log!("range_fold={}", range_sum)

	let mapper = |x|:
		if x % 2 == 0:
			Option::Some(x * 100)
		else:
			Option::None
	let fm_res = v.iter().filter_map(mapper).reduce(|a, b|: a + b)
	match fm_res:
		Option::Some(total) => log!("fm_reduce={}", total)
		Option::None => panic!("unexpected empty reduce")
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success()
            && combined.contains("vec_chain=30,40,50,60")
            && combined.contains("range_fold=24")
            && combined.contains("fm_reduce=1200"),
        "Lazy iterator chaining test failed:\n{combined}"
    );
}

#[test]
fn priority2_overloaded_index_bitwise_and_compound_assign() {
    let out = run_gdrs_source(
        "p2_ops_overloading",
        r#"
use std::ops::{Index, IndexMut, BitAnd, BitOr, BitXor, Shl, Shr, AddAssign, SubAssign, MulAssign, DivAssign}

obj Buf2:
	pub a: i64
	pub b: i64

impl Index for Buf2:
	fn index(&self, idx: i64) -> &i64:
		if idx == 0:
			return &self.a
		return &self.b

impl IndexMut for Buf2:
	fn index_mut(&mut self, idx: i64) -> &mut i64:
		if idx == 0:
			return &mut self.a
		return &mut self.b

obj Bits:
	pub v: i64

impl BitAnd for Bits:
	fn bitand(self, rhs: &Bits) -> Bits:
		return Bits{ v: self.v & rhs.v }

impl BitOr for Bits:
	fn bitor(self, rhs: &Bits) -> Bits:
		return Bits{ v: self.v | rhs.v }

impl BitXor for Bits:
	fn bitxor(self, rhs: &Bits) -> Bits:
		return Bits{ v: self.v ^ rhs.v }

impl Shl for Bits:
	fn shl(self, shift: i64) -> Bits:
		return Bits{ v: self.v << shift }

impl Shr for Bits:
	fn shr(self, shift: i64) -> Bits:
		return Bits{ v: self.v >> shift }

impl AddAssign for Bits:
	fn add_assign(&mut self, rhs: Bits):
		self.v = self.v + rhs.v

impl SubAssign for Bits:
	fn sub_assign(&mut self, rhs: Bits):
		self.v = self.v - rhs.v

impl MulAssign for Bits:
	fn mul_assign(&mut self, rhs: i64):
		self.v = self.v * rhs

impl DivAssign for Bits:
	fn div_assign(&mut self, rhs: i64):
		self.v = self.v / rhs

fn main():
	let mut buf = Buf2{ a: 10, b: 20 }
	buf[1] = 99
	buf[0] += 5
	log!("idx={},{}", buf[0], buf[1])

	let x = Bits{ v: 6 }
	let y = Bits{ v: 3 }
	let and_v = (Bits{ v: 6 } & y).v
	let or_v = (Bits{ v: 6 } | y).v
	let xor_v = (x ^ y).v
	let shl_v = (Bits{ v: 6 } << 2).v
	let shr_v = (Bits{ v: 16 } >> 2).v
	log!("bits={},{},{},{},{}", and_v, or_v, xor_v, shl_v, shr_v)

	let mut acc = Bits{ v: 10 }
	acc += Bits{ v: 5 }
	acc -= Bits{ v: 3 }
	acc *= 4
	acc /= 6
	log!("acc_bits={}", acc.v)

	let mut p = 100
	p += 20
	p -= 10
	p *= 2
	p /= 11
	log!("prim={}", p)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success()
            && combined.contains("idx=15,99")
            && combined.contains("bits=2,7,5,24,4")
            && combined.contains("acc_bits=8")
            && combined.contains("prim=20"),
        "Operator overloading (Index/IndexMut/Bitwise/CompoundAssign) failed:\n{combined}"
    );
}
