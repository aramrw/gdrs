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
