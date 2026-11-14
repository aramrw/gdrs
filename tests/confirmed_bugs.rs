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

#[test]
fn std_ops_not_bitwise_assign_and_deref() {
    let out = run_gdrs_source(
        "std_ops_not_bitassign_deref",
        r#"
use std::ops::{Not, RemAssign, BitAndAssign, BitOrAssign, BitXorAssign, ShlAssign, ShrAssign, Deref, DerefMut}
use std::string::String

obj Mask:
	pub v: i64

impl Not for Mask:
	fn not(self) -> Mask:
		return Mask{ v: self.v ^ 255 }

impl RemAssign for Mask:
	fn rem_assign(&mut self, rhs: i64):
		self.v = self.v % rhs

impl BitAndAssign for Mask:
	fn bitand_assign(&mut self, rhs: Mask):
		self.v = self.v & rhs.v

impl BitOrAssign for Mask:
	fn bitor_assign(&mut self, rhs: Mask):
		self.v = self.v | rhs.v

impl BitXorAssign for Mask:
	fn bitxor_assign(&mut self, rhs: Mask):
		self.v = self.v ^ rhs.v

impl ShlAssign for Mask:
	fn shl_assign(&mut self, shift: i64):
		self.v = self.v << shift

impl ShrAssign for Mask:
	fn shr_assign(&mut self, shift: i64):
		self.v = self.v >> shift

obj Inner:
	pub x: i64
	pub label: String

impl Inner:
	pub fn sum(&self) -> i64:
		return self.x + (self.label.len() as i64)

	pub fn bump(&mut self, delta: i64):
		self.x = self.x + delta

obj WrapScalar:
	val: i64

impl Deref for WrapScalar:
	fn deref(&self) -> &i64:
		return &self.val

impl DerefMut for WrapScalar:
	fn deref_mut(&mut self) -> &mut i64:
		return &mut self.val

obj WrapInner:
	inner: Inner

impl Deref for WrapInner:
	fn deref(&self) -> &Inner:
		return &self.inner

impl DerefMut for WrapInner:
	fn deref_mut(&mut self) -> &mut Inner:
		return &mut self.inner

fn main():
	let inv = !Mask{ v: 15 }
	let mut m = Mask{ v: 10 }
	m |= Mask{ v: 5 }
	m &= Mask{ v: 7 }
	m ^= Mask{ v: 2 }
	m <<= 3
	m >>= 1
	m %= 9
	log!("mask_not={},mask_acc={}", inv.v, m.v)

	let mut p = 29
	p %= 10
	p |= 4
	p &= 7
	p ^= 2
	p <<= 2
	p >>= 1
	log!("prim_bits={}", p)

	let mut ws = WrapScalar{ val: 10 }
	*ws = 25
	*ws += 5
	log!("ws={}", *ws)

	let mut wi = WrapInner{ inner: Inner{ x: 10, label: String::from("abc") } }
	let mut wi_rx = 0
	if true:
		let r = &*wi
		wi_rx = r.x
	let s0 = wi.sum()
	wi.x = 40
	wi.x += 2
	wi.bump(8)
	log!("wi_r={},s0={},x={}", wi_rx, s0, wi.x)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success()
            && combined.contains("mask_not=240,mask_acc=2")
            && combined.contains("prim_bits=14")
            && combined.contains("ws=30")
            && combined.contains("wi_r=10,s0=13,x=50"),
        "Not / bitwise-assign / Deref / DerefMut failed:\n{combined}"
    );

    // Negative: moving non-Copy *wrapper out of Deref triggers E0507; *immut = v triggers E0596
    let neg_move = run_gdrs_source(
        "std_ops_deref_non_copy_e0507",
        r#"
use std::ops::{Deref, DerefMut}
use std::string::String

obj WrapStr:
	s: String

impl Deref for WrapStr:
	fn deref(&self) -> &String:
		return &self.s

impl DerefMut for WrapStr:
	fn deref_mut(&mut self) -> &mut String:
		return &mut self.s

fn main():
	let w = WrapStr{ s: String::from("hi") }
	let moved = *w
	log!("{}", moved.as_str())
"#,
    );
    let neg_move_str = combined_output(&neg_move);
    assert!(
        !neg_move.status.success() && neg_move_str.contains("E0507"),
        "Expected E0507 moving non-Copy *Deref, got:\n{neg_move_str}"
    );

    let neg_immut = run_gdrs_source(
        "std_ops_deref_mut_immut_e0596",
        r#"
use std::ops::{Deref, DerefMut}

obj BoxInt:
	v: i64

impl Deref for BoxInt:
	fn deref(&self) -> &i64:
		return &self.v

impl DerefMut for BoxInt:
	fn deref_mut(&mut self) -> &mut i64:
		return &mut self.v

fn main():
	let w = BoxInt{ v: 1 }
	*w = 2
"#,
    );
    let neg_immut_str = combined_output(&neg_immut);
    assert!(
        !neg_immut.status.success() && neg_immut_str.contains("E0596"),
        "Expected E0596 on *immut_wrapper = val, got:\n{neg_immut_str}"
    );
}

#[test]
fn std_ops_reference_and_heterogeneous_binops() {
    let out = run_gdrs_source(
        "std_ops_ref_hetero_binops",
        r#"
use std::ops::{Add, Mul}
use std::core::Drop

obj Mat:
	pub a: f64
	pub b: f64
	pub id: i64

impl Drop for Mat:
	fn drop(mut self):
		log!("drop_mat={}", self.id)

impl Add for Mat:
	fn add(self, rhs: Mat) -> Mat:
		return Mat{ a: self.a + rhs.a, b: self.b + rhs.b, id: self.id + rhs.id }

impl Add for &Mat:
	fn add(self, rhs: &Mat) -> Mat:
		return Mat{ a: self.a + rhs.a, b: self.b + rhs.b, id: 99 }

impl Mul for Mat:
	fn mul(&self, scale: f64) -> Mat:
		return Mat{ a: self.a * scale, b: self.b * scale, id: 77 }

fn main():
	let m1 = Mat{ a: 1.5, b: 2.0, id: 1 }
	let m2 = Mat{ a: 2.5, b: 3.0, id: 2 }
	let ref_sum = &m1 + &m2
	let scaled = m1 * 2.0
	let ref_scaled = &m2 * 3.0
	let owned_sum = m1 + m2
	log!("ref_sum={},{};scaled={},{};ref_scaled={},{};owned={},{}", ref_sum.a, ref_sum.b, scaled.a, scaled.b, ref_scaled.a, ref_scaled.b, owned_sum.a, owned_sum.b)
"#,
    );
    let combined = combined_output(&out);
    assert!(
        out.status.success()
            && combined.contains("ref_sum=4")
            && combined.contains("scaled=3")
            && combined.contains("ref_scaled=7.5,9")
            && combined.contains("owned=4")
            && combined.contains("drop_mat=99")
            && combined.contains("drop_mat=77")
            && combined.contains("drop_mat=3"),
        "Reference & heterogeneous std::ops failed:\n{combined}"
    );
}

#[test]
fn repr_packed_and_align_layouts_and_abi() {
    let out = run_gdrs_source(
        "repr_packed_align_layouts",
        r#"
use std::mem::{size_of, align_of}

#[repr(packed)]
obj Packed:
	pub a: u8
	pub b: i64
	pub c: u16

#[repr(packed(2))]
obj Packed2:
	pub a: u8
	pub b: i64
	pub c: u8

#[repr(align(64))]
obj CacheLine:
	pub a: u8
	pub b: i32

#[repr(C, align(16))]
obj Vec2:
	pub x: f32
	pub y: f32

#[repr(C)]
obj WithPacked:
	pub tag: u8
	pub inner: Packed

#[repr(C)]
obj WithAligned:
	pub tag: u8
	pub buf: CacheLine

#[repr(packed)]
obj GenPacked:
	pub tag: u8
	pub val: $T

#[repr(packed)]
obj PackedF32:
	pub c: u8
	pub a: f32
	pub b: f32

#[repr(align(16))]
obj AlignedF32:
	pub a: f32
	pub b: f32

#[repr(align(32))]
obj EmptyAligned {}

fn pass_packed(p: Packed) -> Packed:
	return Packed{ a: p.a + 1, b: p.b + 2, c: p.c + 3 }

fn pass_packed_f32(p: PackedF32) -> f32:
	return p.a + p.b + (p.c as f32)

fn pass_aligned_f32(v: AlignedF32) -> AlignedF32:
	return AlignedF32{ a: v.a * 2.0, b: v.b * 3.0 }

fn main():
	let p = Packed{ a: 17 as u8, b: 0x0102030405060708, c: 0x0A0B as u16 }
	let raw_p = (&p as *Packed) as *u8
	let mut byte_sum: i64 = 0
	unsafe:
		let b0 = *raw_p as i64
		let b1 = *(raw_p + 1) as i64
		let b8 = *(raw_p + 8) as i64
		let b9 = *(raw_p + 9) as i64
		let b10 = *(raw_p + 10) as i64
		byte_sum = b0 + b1 + b8 + b9 + b10

	// Taking reference to a 1-byte aligned field inside #[repr(packed)] must be allowed
	let pa_val = *(&p.a) as i64
	let p2 = pass_packed(p)
	let p2a_val = *(&p2.a) as i64

	let cl = CacheLine{ a: 9 as u8, b: 123 }
	let cl_addr = (&cl as *CacheLine) as i64
	let cl_aligned = (cl_addr % 64) == 0

	let arr = [CacheLine{ a: 1 as u8, b: 10 }, CacheLine{ a: 2 as u8, b: 20 }]
	let arr_step = ((&arr[1] as *CacheLine) as i64) - ((&arr[0] as *CacheLine) as i64)

	let pf_sum = pass_packed_f32(PackedF32{ c: 2 as u8, a: 1.5, b: 2.5 })
	let af = pass_aligned_f32(AlignedF32{ a: 2.0, b: 4.0 })
	let gp: GenPacked<i64> = GenPacked{ tag: 3 as u8, val: 99 }

	log!(
		"packed={},{};p2={},{};cl={},{},{};vec2={},{};wp={},{};wa={},{};gp={},{};empty={},{};val={},{},{};bytes={};step={};f={},{},{};refs={}",
		size_of::<Packed>(),
		align_of::<Packed>(),
		size_of::<Packed2>(),
		align_of::<Packed2>(),
		size_of::<CacheLine>(),
		align_of::<CacheLine>(),
		cl_aligned,
		size_of::<Vec2>(),
		align_of::<Vec2>(),
		size_of::<WithPacked>(),
		align_of::<WithPacked>(),
		size_of::<WithAligned>(),
		align_of::<WithAligned>(),
		size_of::<GenPacked<i64> >(),
		align_of::<GenPacked<i64> >(),
		size_of::<EmptyAligned>(),
		align_of::<EmptyAligned>(),
		p2.a,
		p2.b,
		p2.c,
		byte_sum,
		arr_step,
		pf_sum,
		af.a,
		af.b,
		pa_val + p2a_val + gp.val
	)
"#,
    );
    let combined = combined_output(&out);
    // byte_sum = 17 + 0x08 (8) + 0x01 (1) + 0x0B (11) + 0x0A (10) = 47
    // p2.a = 18, p2.b = 0x010203040506070A = 72623859790382858, p2.c = 0x0A0E = 2574
    assert!(
        out.status.success()
            && combined.contains("packed=11,1;p2=12,2;cl=64,64,true;")
            && combined.contains("vec2=16,16;wp=12,1;wa=128,64;gp=9,1;empty=0,32;")
            && combined.contains("val=18,72623859790382858,2574;bytes=47;step=64;f=6.0,4.0,12.0;refs=134"),
        "#[repr(packed)] / #[repr(align)] runtime/layout failed:\n{combined}"
    );
}

#[test]
fn repr_packed_and_align_negative_errors() {
    let cases = [
        (
            "unaligned_imm_ref",
            r#"
#[repr(packed)]
obj P:
	pub a: u8
	pub b: i32
fn main():
	let p = P{ a: 1 as u8, b: 2 }
	let _r = &p.b
"#,
            "E0793",
        ),
        (
            "unaligned_mut_ref",
            r#"
#[repr(packed)]
obj P:
	pub a: u8
	pub b: i32
fn main():
	let mut p = P{ a: 1 as u8, b: 2 }
	let _r = &mut p.b
"#,
            "E0793",
        ),
        (
            "unaligned_packed2_i32_ref",
            r#"
#[repr(packed(2))]
obj P2:
	pub a: u8
	pub b: i16
	pub c: i32
fn main():
	let p = P2{ a: 1 as u8, b: 2 as i16, c: 3 }
	let _ok = &p.b
	let _bad = &p.c
"#,
            "E0793",
        ),
        (
            "unaligned_nested_struct_field_ref",
            r#"
obj Inner:
	pub x: u8
	pub y: i32
#[repr(packed)]
obj Outer:
	pub flag: u8
	pub inner: Inner
fn main():
	let o = Outer{ flag: 1 as u8, inner: Inner{ x: 2 as u8, y: 3 } }
	let _bad = &o.inner.y
"#,
            "E0793",
        ),
        (
            "unaligned_autoref_method",
            r#"
obj Inner:
	pub y: i32
impl Inner:
	fn get(&self) -> i32:
		return self.y
#[repr(packed)]
obj Outer:
	pub flag: u8
	pub inner: Inner
fn main():
	let o = Outer{ flag: 1 as u8, inner: Inner{ y: 7 } }
	let _bad = o.inner.get()
"#,
            "E0793",
        ),
        (
            "conflict_packed_align",
            r#"
#[repr(packed, align(8))]
obj Bad:
	pub a: i32
fn main():
	return
"#,
            "E0587",
        ),
        (
            "invalid_align_non_pow2",
            r#"
#[repr(align(3))]
obj Bad:
	pub a: i32
fn main():
	return
"#,
            "E0589",
        ),
        (
            "invalid_align_zero",
            r#"
#[repr(align(0))]
obj Bad:
	pub a: i32
fn main():
	return
"#,
            "E0589",
        ),
        (
            "invalid_align_negative",
            r#"
#[repr(align(-4))]
obj Bad:
	pub a: i32
fn main():
	return
"#,
            "E0589",
        ),
        (
            "conflicting_packed_hints",
            r#"
#[repr(packed(2), packed(4))]
obj Bad:
	pub a: i32
fn main():
	return
"#,
            "E0634",
        ),
        (
            "unknown_repr_specifier",
            r#"
#[repr(unknown_spec)]
obj Bad:
	pub a: i32
fn main():
	return
"#,
            "E0552",
        ),
        (
            "repr_on_enum",
            r#"
#[repr(packed)]
enum BadEnum:
	A(i32)
fn main():
	return
"#,
            "E0517",
        ),
    ];

    for (name, src, expected_code) in cases {
        let out = run_gdrs_source(&format!("repr_neg_{name}"), src);
        let combined = combined_output(&out);
        assert!(
            !out.status.success() && combined.contains(expected_code),
            "Case `{name}` expected error `{expected_code}`, got status={:?}\n{combined}",
            out.status.code()
        );
    }
}

#[test]
fn repr_packed_and_align_randomized_c_parity() {
    let mut seed: u64 = 0x5EED_C0DE_1234_5678;
    let mut next_u32 = || -> u32 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        (seed >> 16) as u32
    };

    let field_types = [
        ("u8", "uint8_t"),
        ("i16", "int16_t"),
        ("i32", "int32_t"),
        ("i64", "int64_t"),
        ("f32", "float"),
        ("f64", "double"),
    ];
    let repr_modes = [
        ("", ""),
        ("#[repr(C)]", ""),
        ("#[repr(packed)]", "__attribute__((packed))"),
        ("#[repr(packed(2))]", "__attribute__((packed, aligned(2)))"),
        ("#[repr(align(16))]", "__attribute__((aligned(16)))"),
        ("#[repr(align(64))]", "__attribute__((aligned(64)))"),
    ];

    let mut gdrs_defs = String::from("use std::mem::{size_of, align_of}\n\n");
    let mut gdrs_prints = String::new();
    let mut c_defs = String::from("#include <stdio.h>\n#include <stdint.h>\n\n");
    let mut c_prints = String::new();

    for i in 0..16 {
        let mode_idx = (next_u32() as usize) % repr_modes.len();
        let (g_repr, c_attr) = repr_modes[mode_idx];
        let num_fields = 2 + ((next_u32() as usize) % 5);

        if !g_repr.is_empty() {
            gdrs_defs.push_str(g_repr);
            gdrs_defs.push('\n');
        }
        gdrs_defs.push_str(&format!("obj RandStruct{i}:\n"));
        c_defs.push_str(&format!("struct {c_attr} RandStruct{i} {{\n"));

        for f in 0..num_fields {
            let (g_ty, c_ty) = if i > 2 && f == num_fields - 1 && (next_u32() % 3 == 0) {
                // Occasionally nest an earlier generated struct
                let prev = (next_u32() as usize) % i;
                (format!("RandStruct{prev}"), format!("struct RandStruct{prev}"))
            } else {
                let (gt, ct) = field_types[(next_u32() as usize) % field_types.len()];
                (gt.to_string(), ct.to_string())
            };
            gdrs_defs.push_str(&format!("\tpub f{f}: {g_ty}\n"));
            c_defs.push_str(&format!("    {c_ty} f{f};\n"));
        }
        gdrs_defs.push('\n');
        c_defs.push_str("};\n\n");

        gdrs_prints.push_str(&format!(
            "\tlog!(\"S{i}={{}},{{}}\", size_of::<RandStruct{i}>(), align_of::<RandStruct{i}>())\n"
        ));
        c_prints.push_str(&format!(
            "    printf(\"S{i}=%zu,%zu\\n\", sizeof(struct RandStruct{i}), _Alignof(struct RandStruct{i}));\n"
        ));
    }

    let gdrs_src = format!("{gdrs_defs}fn main():\n{gdrs_prints}");
    let c_src = format!("{c_defs}int main(void) {{\n{c_prints}    return 0;\n}}\n");

    let g_out = run_gdrs_source("repr_rand_parity", &gdrs_src);
    let g_stdout = String::from_utf8_lossy(&g_out.stdout).to_string();
    assert!(
        g_out.status.success(),
        "GDRS randomized repr program failed:\n{}\n{}",
        g_stdout,
        String::from_utf8_lossy(&g_out.stderr)
    );

    let dir = make_temp_dir("repr_rand_c");
    let c_path = dir.join("parity.c");
    let bin_path = dir.join("parity_c");
    fs::write(&c_path, &c_src).unwrap();
    let cc_out = Command::new("clang")
        .arg("-std=c11")
        .arg(&c_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .expect("failed to invoke clang");
    assert!(
        cc_out.status.success(),
        "clang failed:\n{}",
        String::from_utf8_lossy(&cc_out.stderr)
    );
    let c_run = Command::new(&bin_path).output().expect("failed to run C parity bin");
    let _ = fs::remove_dir_all(&dir);
    assert!(c_run.status.success());

    let c_lines: Vec<String> = String::from_utf8_lossy(&c_run.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| l.starts_with('S'))
        .collect();
    let g_lines: Vec<String> = g_stdout
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| l.starts_with('S'))
        .collect();
    assert_eq!(g_lines, c_lines, "GDRS vs clang C layout mismatch!\nGDRS:\n{g_stdout}\nC:\n{c_src}");
}

#[test]
fn let_else_runtime_drops_and_control_flow() {
    let src_fn = |n: usize| -> String {
        format!(
            r#"
use std::core::{{Option, Result, Drop}}
use std::string::String

enum Multi:
	Pair(i64, String, i64)
	Empty

obj Canary:
	pub id: i64

impl Drop for Canary:
	fn drop(mut self):
		if self.id < 0:
			log!("canary={{}}", self.id)

fn make_res(ok: bool) -> Result<String, String>:
	if ok:
		return Result::Ok(String::from("hello_payload_value"))
	return Result::Err(String::from("err_payload_should_drop_cleanly"))

fn unwrap_or_neg(ok: bool) -> i64:
	let c = Canary{{ id: 1 }}
	let outer = String::from("outer_still_alive_if_ok")
	let Result::Ok(mut s) = make_res(ok) else:
		// Move `outer` ONLY in the diverging else branch!
		let _consumed = outer
		return -2
	// `outer` must still be valid here when `Result::Ok` succeeded!
	s.append("_tail")
	let ok_len = (s.len() as i64) + (outer.len() as i64) + c.id
	return ok_len

fn make_multi(flag: bool) -> Multi:
	if flag:
		return Multi::Pair(10, String::from("mid"), 999)
	return Multi::Empty

fn make_opt(is_none: bool) -> Option<i64>:
	if is_none:
		return Option::None
	return Option::Some(42)

fn make_loop_opt(i: i64) -> Option<i64>:
	if i == 2 || i == 5:
		return Option::None
	return Option::Some(i * 10)

fn test_multi(flag: bool) -> i64:
	let m = make_multi(flag)
	let Multi::Pair(a, mut msg, _) = m else:
		return -4
	msg.append("!")
	return a + (msg.len() as i64)

fn test_zero_binding(is_none: bool) -> i64:
	let opt = make_opt(is_none)
	let Option::None = opt else:
		return -3
	return 7

fn test_loop_syntax_variants() -> i64:
	let mut acc: i64 = 0
	for i in 0..6:
		let opt = make_loop_opt(i)
		// Test indented else, braced else, inline else, and Rust-style else
		if i == 2:
			let Option::Some(v) = opt else:
				continue
			acc += v
		else if i == 5:
			let Option::Some(v) = opt else {{ break }}
			acc += v
		else:
			let Option::Some(v) = opt else: continue
			acc += v
	return acc

fn main():
	let mut total: i64 = 0
	for _k in 0..{n}:
		total += unwrap_or_neg(true)
		total += unwrap_or_neg(false)
		total += test_multi(true)
		total += test_multi(false)
		total += test_zero_binding(true)
		total += test_zero_binding(false)
	let loops = test_loop_syntax_variants()
	let cl = |x: i64|:
		let opt = make_opt(x <= 0)
		let Option::Some(y) = opt else: {{ return -9 }}
		y * 2
	log!("res={{}},{{}},{{}},{{}}", total, loops, cl(4), cl(0))
"#
        )
    };

    let out = run_gdrs_source("let_else_runtime", &src_fn(1));
    let combined = combined_output(&out);
    // unwrap_or_neg(true) = 24 ("hello_payload_value_tail") + 23 ("outer_still_alive_if_ok") + 1 = 48
    // unwrap_or_neg(false) = -2
    // test_multi(true) = 10 + 4 ("mid!") = 14; test_multi(false) = -4
    // test_zero_binding(true) = 7; test_zero_binding(false) = -3
    // total(1) = 48 - 2 + 14 - 4 + 7 - 3 = 60
    // loops = 0 + 10 + 30 + 40 = 80
	// cl(4) = 84, cl(0) = -9
    assert!(
        out.status.success() && combined.contains("res=60,80,84,-9"),
        "let...else runtime/control-flow failed:\n{combined}"
    );

    #[cfg(target_os = "macos")]
    {
        let net_small = measure_net_allocs_macos(&src_fn, 10, &[]);
        let net_large = measure_net_allocs_macos(&src_fn, 260, &[]);
        assert_eq!(
            net_large - net_small,
            0,
            "let...else leaked memory across 250 extra iterations (net_small={net_small}, net_large={net_large})"
        );
    }
}

#[test]
fn let_else_negative_errors() {
    let cases = [
        (
            "non_diverging_else",
            r#"
use std::core::Option
fn main():
	let opt = Option::Some(1)
	let Option::Some(x) = opt else:
		log!("oops")
	log!("{}", x)
"#,
            "E0308",
        ),
        (
            "non_diverging_zero_binding",
            r#"
use std::core::Option
fn main():
	let opt = Option::None
	let Option::None = opt else:
		let _z = 1
"#,
            "E0308",
        ),
        (
            "conditional_non_diverging_else",
            r#"
use std::core::Option
fn f(b: bool) -> i64:
	let opt = Option::Some(5)
	let Option::Some(x) = opt else:
		if b:
			return 0
	return x
fn main():
	let _ = f(true)
"#,
            "E0308",
        ),
        (
            "unknown_variant",
            r#"
use std::core::Option
fn main():
	let opt = Option::Some(1)
	let Option::Missing(x) = opt else:
		return
	log!("{}", x)
"#,
            "E0004",
        ),
        (
            "non_enum_target",
            r#"
use std::core::Option
fn main():
	let Option::Some(x) = 42 else:
		return
	log!("{}", x)
"#,
            "E0308",
        ),
        (
            "immutable_binding_mutation",
            r#"
use std::core::Option
fn main():
	let opt = Option::Some(1)
	let Option::Some(x) = opt else:
		return
	x = 2
"#,
            "E0382",
        ),
    ];

    for (name, src, expected_code) in cases {
        let out = run_gdrs_source(&format!("let_else_neg_{name}"), src);
        let combined = combined_output(&out);
        assert!(
            !out.status.success() && combined.contains(expected_code),
            "Case `{name}` expected error `{expected_code}`, got status={:?}\n{combined}",
            out.status.code()
        );
    }
}

#[test]
fn stage1_and_stage2_sugars_runtime_and_leaks() {
    let src_fn = |n: usize| {
        format!(
            r#"
use std::core::Option
use std::string::String
use std::vec::Vec

obj Pt:
	x: i64
	y: i64

obj Labeled:
	label: String
	pt: Pt

enum Packet:
	Alpha(String, String)
	Beta(String)
	Gamma(i64)
	Empty

fn next_opt(step: i64) -> Option<String>:
	if step >= 4:
		return Option::None
	if step == 1:
		return Option::Some(String::from("hi"))
	return Option::Some(String::from("hello_world"))

fn take_val(a: i64, s: String) -> i64:
	return a + (s.len() as i64)

fn classify_int(v: i64) -> i64:
	match v:
		-1 => return 100
		0 => return 200
		1 | 2 | 3 => return 300
		_ => return 400

fn classify_bool(b: bool) -> i64:
	return match b:
		true => 11
		false => 22

fn make_packet(kind: i64) -> Packet:
	if kind == 0:
		return Packet::Alpha(String::from("kept_payload_1"), String::from("dropped_second"))
	if kind == 1:
		return Packet::Beta(String::from("kept_payload_2"))
	if kind == 2:
		return Packet::Gamma(7)
	return Packet::Empty

fn check_packet_guards(p: Packet) -> i64:
	return match p:
		Packet::Alpha(s, _) | Packet::Beta(s) if s.len() > 20 =>
			999
		Packet::Alpha(s, _) | Packet::Beta(s) if s.len() == 14 =>
			(s.len() as i64) + 100
		Packet::Alpha(_, _) | Packet::Beta(_) =>
			55
		Packet::Gamma(v) if v < 0 =>
			-10
		Packet::Gamma(v) =>
			v * 2
		Packet::Empty =>
			1

fn main():
	let mut acc: i64 = 0
	for _k in 0..{n}:
		// 1. while let with mut binding, continue, break, and braced variant
		let mut i: i64 = 0
		while let Option::Some(mut item) = next_opt(i):
			i += 1
			if item.len() < 4:
				continue
			item.append("!")
			acc += item.len() as i64
			if i == 3:
				break
		let mut j: i64 = 0
		while let Option::Some(s) = next_opt(j): {{
			j += 1
			if j == 2: {{
				acc += s.len() as i64
			}}
		}}

		// 2. Expression-position if/else, if let, match
		let x: i64 = 10
		let y: i64 = 20
		let p = Pt {{ x, y }}
		let label = String::from("pt_shorthand")
		let labeled = Labeled {{ label, pt: Pt {{ x: 1, y }} }}
		acc += labeled.pt.x + labeled.pt.y + (labeled.label.len() as i64)

		let expr_res = take_val(
			if p.x < p.y: 5 else: 9,
			if let Option::Some(msg) = next_opt(0):
				msg
			else:
				String::from("fallback")
		)
		acc += expr_res

		let braced_match_val = match p.x: {{
			10 => String::from("ten_ok"),
			_ => String::from("other"),
		}}
		acc += braced_match_val.len() as i64

		// 3. Literal matching (int incl negative, or-patterns, bool) & guarded enum or-patterns
		acc += classify_int(-1) + classify_int(0) + classify_int(2) + classify_int(99)
		acc += classify_bool(true) + classify_bool(false)

		let b1 = true
		let small_u8: u8 = 2
		acc += match b1:
			true => 3
			_ => 4
		acc += match small_u8:
			1 | 2 => 7
			_ => 0

		acc += check_packet_guards(make_packet(0))
		acc += check_packet_guards(make_packet(1))
		acc += check_packet_guards(make_packet(2))
		acc += check_packet_guards(make_packet(3))

	log!("stage12={{}}", acc)
"#
        )
    };

    let out = run_gdrs_source("stage12_runtime", &src_fn(1));
    let combined = combined_output(&out);
    // Per iteration expectation:
    // while let 1: step=0 ("hello_world",11 -> "hello_world!",12), step=1 ("hi", len<4 continue), step=2 ("hello_world!",12 -> break) => 24
    // while let 2 (braced): j=2 hits "hi" (len 2) => 2
    // labeled: pt.x(1) + pt.y(20) + label("pt_shorthand",12) = 33
    // expr_res: take_val(5, "hello_world"(11)) = 16
    // braced_match_val: "ten_ok" = 6
    // classify_int: 100 + 200 + 300 + 400 = 1000
    // classify_bool: 11 + 22 = 33
    // bool/u8 inline match: 3 + 7 = 10
    // check_packet_guards:
    //   kind 0 -> Alpha("dropped_first", "kept_payload_1"(len 14)) -> falls through arm0, matches arm1 -> 114
    //   kind 1 -> Beta("kept_payload_2"(len 14)) -> matches arm1 -> 114
    //   kind 2 -> Gamma(7) -> falls through <0 guard -> 14
    //   kind 3 -> Empty -> 1
    // Total per iteration = 24 + 2 + 33 + 16 + 6 + 1000 + 33 + 10 + 114 + 114 + 14 + 1 = 1367
    assert!(
        out.status.success() && combined.contains("stage12=1367"),
        "stage1/stage2 sugar runtime failed:\n{combined}"
    );

    #[cfg(target_os = "macos")]
    {
        let net_small = measure_net_allocs_macos(&src_fn, 10, &[]);
        let net_large = measure_net_allocs_macos(&src_fn, 260, &[]);
        assert_eq!(
            net_large - net_small,
            0,
            "stage1/stage2 sugars leaked memory across 250 extra iterations (net_small={net_small}, net_large={net_large})"
        );
    }
}

#[test]
fn stage2_match_negative_errors() {
    let cases = [
        (
            "non_exhaustive_int",
            r#"
fn main():
	let x: i64 = 0
	let _ = match x:
		-1 => 1
		0 => 2
"#,
            "E0004",
        ),
        (
            "non_exhaustive_bool",
            r#"
fn main():
	let b: bool = true
	let _ = match b:
		true => 1
"#,
            "E0004",
        ),
        (
            "non_exhaustive_guarded_only",
            r#"
use std::core::Option
fn main():
	let opt = Option::Some(5)
	let _ = match opt:
		Option::Some(v) if v > 0 => v
		Option::None => 0
"#,
            "E0004",
        ),
        (
            "or_pattern_binding_mismatch",
            r#"
enum E:
	A(i64)
	B(i64)
fn main():
	let e = E::A(1)
	let _ = match e:
		E::A(x) | E::B(y) => 1
"#,
            "E0408",
        ),
        (
            "non_bool_guard",
            r#"
fn main():
	let x: i64 = 1
	let _ = match x:
		1 if 42 => 10
		_ => 20
"#,
            "E0308",
        ),
        (
            "int_pattern_on_enum",
            r#"
use std::core::Option
fn main():
	let opt = Option::Some(1)
	let _ = match opt:
		1 => 10
		_ => 20
"#,
            "E0308",
        ),
        (
            "enum_pattern_on_int",
            r#"
use std::core::Option
fn main():
	let x: i64 = 5
	let _ = match x:
		Option::Some(v) => v
		_ => 0
"#,
            "E0308",
        ),
    ];

    for (name, src, expected_code) in cases {
        let out = run_gdrs_source(&format!("stage2_neg_{name}"), src);
        let combined = combined_output(&out);
        assert!(
            !out.status.success() && combined.contains(expected_code),
            "Case `{name}` expected error `{expected_code}`, got status={:?}\n{combined}",
            out.status.code()
        );
    }
}

#[test]
fn sugars_loop_inclusive_struct_destructure_and_matrix_iter_runtime_and_leaks() {
    let runtime_src = r#"
use std::vec::Vec
use std::string::String

obj Pair:
	name: String
	count: i64

#[repr(C)]
obj MixedC:
	flag: u8
	big: i64
	label: String
	tag: u8

obj Matrix:
	data: Vec<i64>
	rows: i64
	cols: i64

fn pick_or_loop(flag: bool) -> i64:
	if flag:
		42
	else:
		loop:
			break 99

fn main():
	// 1. loop returning scalar & owned aggregate + nested loop with continue/break + diverging loop
	let mut i: i64 = 0
	let mut sum_even: i64 = 0
	let res: i64 = loop:
		i += 1
		if i == 2:
			continue
		if i > 4:
			break sum_even
		sum_even += i
	if res != 8:
		log!("FAIL loop_scalar")
		return

	let mut step: i64 = 0
	let s_res: String = loop:
		step += 1
		if step < 3:
			continue
		let tmp = String::from("ok_loop")
		break tmp
	if s_res != "ok_loop":
		log!("FAIL loop_string")
		return

	let mut outer: i64 = 0
	let mut total_nested: i64 = 0
	loop:
		outer += 1
		if outer > 3:
			break
		let mut inner: i64 = 0
		loop:
			inner += 1
			if inner == 2:
				continue
			if inner > 3:
				break
			total_nested += 1
	if total_nested != 6:
		log!("FAIL loop_nested")
		return

	if pick_or_loop(true) != 42:
		log!("FAIL pick_true")
		return

	// 2. Inclusive ranges ..=
	let mut r_sum: i64 = 0
	for x in 0..=4:
		if x == 2:
			continue
		r_sum += x
	if r_sum != 8:
		log!("FAIL range_inc_continue")
		return

	let mut zero_iters: i64 = 0
	for _x in 5..=3:
		zero_iters += 1
	if zero_iters != 0:
		log!("FAIL range_inc_empty")
		return

	let mut one_iter: i64 = 0
	for x in 3..=3:
		one_iter += x
	if one_iter != 3:
		log!("FAIL range_inc_single")
		return

	let arr: [i64; 5] = [10, 20, 30, 40, 50]
	let sl1 = arr[1..=3]
	if sl1.len() != 3 || sl1[0] != 20 || sl1[2] != 40:
		log!("FAIL arr_range_inc")
		return
	let sl2 = arr[..=2]
	if sl2.len() != 3 || sl2[0] != 10 || sl2[2] != 30:
		log!("FAIL arr_range_open_inc")
		return

	let txt = String::from("abcdef")
	let ts1 = txt[1..=3]
	if ts1 != "bcd":
		log!("FAIL str_range_inc")
		return
	let ts2 = txt[..=2]
	if ts2 != "abc":
		log!("FAIL str_range_open_inc")
		return

	// 3. Struct destructuring (owned String, mut, alias, .., repr(C), closure)
	let p = Pair { name: String::from("alpha"), count: 10 }
	let Pair { name, mut count } = p
	count += 5
	if name != "alpha" || count != 15:
		log!("FAIL destructure_basic")
		return

	let mc = MixedC { flag: 7, big: 1234567, label: String::from("dropped_label"), tag: 9 }
	let MixedC { flag: f, big, .. } = mc
	if f != 7 || big != 1234567:
		log!("FAIL destructure_repr_c")
		return

	let p2 = Pair { name: String::from("closure_ignored"), count: 21 }
	let add_ten = |item: Pair|:
		let Pair { name: _, count: c } = item
		c + 10
	if add_ten(p2) != 31:
		log!("FAIL destructure_closure")
		return

	// 4. `for x in matrix.data` iterating twice (non-consuming &self)
	let mut d: Vec<i64> = Vec::new()
	d.push(1)
	d.push(2)
	d.push(3)
	d.push(4)
	let mat = Matrix { data: d, rows: 2, cols: 2 }
	let mut pass1: i64 = 0
	for v in mat.data:
		pass1 += v
	let mut pass2: i64 = 0
	for v in mat.data:
		if v == 2:
			continue
		pass2 += v
	if pass1 != 10 || pass2 != 8:
		log!("FAIL matrix_data_iter")
		return

	log!("ALL_OK")
"#;

    let out = run_gdrs_source("sugars_stage3_runtime", runtime_src);
    let combined = combined_output(&out);
    assert!(
        out.status.success() && combined.contains("ALL_OK"),
        "sugars runtime test failed: status={:?}\n{combined}",
        out.status.code()
    );

    #[cfg(target_os = "macos")]
    {
        let leak_src = |n: usize| -> String {
            format!(
                r#"
use std::string::String
use std::vec::Vec

obj Item:
	a: String
	b: String
	num: i64

fn make_loop_str(k: i64) -> String:
	let mut c: i64 = 0
	loop:
		c += 1
		if c == 1:
			let _discard = String::from("discarded")
			continue
		let s = String::from("kept")
		if k >= 0:
			break s

fn main():
	let mut iter: i64 = 0
	for _i in 0..={iters}:
		let it = Item {{ a: String::from("hello_a"), b: String::from("hello_b"), num: iter }}
		let Item {{ a, .. }} = it
		let ls = make_loop_str(iter)
		let mut v: Vec<i64> = Vec::new()
		v.push(a.len() as i64)
		v.push(ls.len() as i64)
		for x in v:
			iter += x
	log!("{{}}", iter)
"#,
                iters = n
            )
        };
        let net_small = measure_net_allocs_macos(&leak_src, 5, &[]);
        let net_large = measure_net_allocs_macos(&leak_src, 200, &[]);
        assert_eq!(
            net_large - net_small,
            0,
            "Memory leak in stage 3 sugars (loop/..=/struct destructure/vec iter): net_small={net_small}, net_large={net_large}"
        );
    }
}

#[test]
fn sugars_stage3_negative_errors() {
    let cases = [
        (
            "break_val_in_while",
            r#"
fn main():
	while true:
		break 1
"#,
            "E0571",
        ),
        (
            "break_val_in_for",
            r#"
fn main():
	for i in 0..3:
		break i
"#,
            "E0571",
        ),
        (
            "loop_mismatched_break_types",
            r#"
fn main():
	let _ = loop:
		if true:
			break 1
		break "bad"
"#,
            "E0308",
        ),
        (
            "loop_break_empty_vs_val",
            r#"
fn main():
	let _ = loop:
		if true:
			break 1
		break
"#,
            "E0308",
        ),
        (
            "struct_destructure_use_after_move",
            r#"
use std::string::String
obj Pair:
	name: String
	count: i64
fn main():
	let p = Pair { name: String::from("x"), count: 1 }
	let Pair { name, count: _ } = p
	log!("{}", p.name)
"#,
            "E0382",
        ),
        (
            "struct_destructure_duplicate_field",
            r#"
obj Pair:
	a: i64
	b: i64
fn main():
	let p = Pair { a: 1, b: 2 }
	let Pair { a, a: c, b: _ } = p
"#,
            "E0025",
        ),
        (
            "struct_destructure_unknown_field",
            r#"
obj Pair:
	a: i64
fn main():
	let p = Pair { a: 1 }
	let Pair { a, z } = p
"#,
            "E0026",
        ),
        (
            "struct_destructure_missing_field",
            r#"
obj Pair:
	a: i64
	b: i64
fn main():
	let p = Pair { a: 1, b: 2 }
	let Pair { a } = p
"#,
            "E0027",
        ),
        (
            "struct_destructure_impl_drop",
            r#"
use std::core::Drop
obj Guard:
	x: i64
impl Drop for Guard:
	fn drop(&mut self):
		pass
fn main():
	let g = Guard { x: 1 }
	let Guard { x } = g
"#,
            "E0509",
        ),
        (
            "struct_destructure_private_field",
            r#"
use std::vec::Vec
fn main():
	let mut v: Vec<i64> = Vec::new()
	v.push(1)
	let Vec { ptr, len, cap } = v
"#,
            "E0616",
        ),
    ];

    for (name, src, expected_code) in cases {
        let out = run_gdrs_source(&format!("stage3_neg_{name}"), src);
        let combined = combined_output(&out);
        assert!(
            !out.status.success() && combined.contains(expected_code),
            "Case `{name}` expected error `{expected_code}`, got status={:?}\n{combined}",
            out.status.code()
        );
    }
}

