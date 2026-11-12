use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn gdrs_bin() -> &'static str {
    env!("CARGO_BIN_EXE_gdrs")
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn run_gdrs_file(path: &std::path::Path) -> std::process::Output {
    Command::new(gdrs_bin())
        .current_dir(repo_root())
        .arg(path)
        .output()
        .expect("failed to execute gdrs binary")
}

fn run_gdrs_source(name: &str, src: &str) -> std::process::Output {
    let id = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = std::env::temp_dir().join(format!("gdrs_test_{}_{id}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let file_path = dir.join(format!("{name}.gdrs"));
    fs::write(&file_path, src).unwrap();
    let out = run_gdrs_file(&file_path);
    let _ = fs::remove_dir_all(&dir);
    out
}

fn assert_ok_output(name: &str, src: &str, expected_substrings: &[&str]) {
    let out = run_gdrs_source(name, src);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "Expected `{name}` to succeed, got exit {:?}\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}",
        out.status.code()
    );
    for needle in expected_substrings {
        assert!(
            stdout.contains(needle),
            "Expected `{name}` stdout to contain `{needle}`.\nActual STDOUT:\n{stdout}"
        );
    }
}

fn assert_err_code(name: &str, src: &str, expected_code: &str) {
    let out = run_gdrs_source(name, src);
    let combined = format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !out.status.success(),
        "Expected `{name}` to fail with {expected_code}, but it succeeded!\nOutput:\n{combined}"
    );
    assert!(
        combined.contains(expected_code),
        "Expected `{name}` failure output to contain `{expected_code}`.\nActual output:\n{combined}"
    );
}

#[test]
fn examples_run_cleanly() {
    let ok_examples = [
        "arrays_vecs.gdrs",
        "benchmark_closures.gdrs",
        "closures.gdrs",
        "cmp.gdrs",
        "command.gdrs",
        "drop_demo.gdrs",
        "enums.gdrs",
        "env_demo.gdrs",
        "inferred_types.gdrs",
        "maths.gdrs",
        "matrix_test.gdrs",
        "nested_vec_test.gdrs",
        "option.gdrs",
        "ptrs.gdrs",
        "raw_ptr_demo.gdrs",
        "read_file.gdrs",
        "string_demo.gdrs",
        "test_exp.gdrs",
        "test_read_dir.gdrs",
    ];

    for ex in ok_examples {
        let path = repo_root().join("examples").join(ex);
        let out = run_gdrs_file(&path);
        assert!(
            out.status.success(),
            "Example `{ex}` failed with {:?}\nSTDOUT:\n{}\nSTDERR:\n{}",
            out.status.code(),
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn error_examples_fail_as_expected() {
    let cases = [
        ("explicit_drop_err.gdrs", "E0040"),
        ("moved_err.gdrs", "E0382"),
    ];
    for (ex, code) in cases {
        let path = repo_root().join("examples").join(ex);
        let out = run_gdrs_file(&path);
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(
            !out.status.success() && combined.contains(code),
            "Example `{ex}` should fail with {code}, got:\n{combined}"
        );
    }
}

#[test]
fn soundness_positive_suite() {
    assert_ok_output(
        "positive_soundness",
        r#"
use std::string::String
use std::core::Option
use std::mem::drop

obj Holder:
	s: String
	n: i64

obj GenBox where T: Clone:
	val: $T

impl GenBox:
	fn clone_in_unsafe(&self) -> GenBox:
		unsafe:
			return GenBox{ val: self.val }

fn swap_vals(a: &mut i64, b: &mut i64):
	let tmp = *a
	*a = *b
	*b = tmp

fn maybe_len(s: str, fail: bool) -> Option<i64>:
	if fail:
		return Option::None
	return Option::Some(3)

fn try_opt(fail: bool) -> Option<i64>:
	let v = maybe_len("hi", fail)?
	return Option::Some(v + 1)

fn main():
	// 1. Struct reassignment after move and while active (no UAF/double-free)
	let mut h = Holder{ s: String::from("first"), n: 1 }
	h = Holder{ s: String::from("second"), n: 2 }
	h.s = String::from("third")
	let _moved = h
	h = Holder{ s: String::from("fourth"), n: 4 }
	log!("h: {} {}", h.s.as_str(), h.n)

	// 2. Fixed-size array with f32 and String elements
	let fs = [1.5 as f32, 2.25 as f32]
	let strs = [String::from("a"), String::from("b")]
	log!("fs: {} {} {} {}", fs[0], fs[1], strs[0].as_str(), strs[1].as_str())

	// 3. Scoped borrows & separate mutable args
	let mut x = 10
	let mut y = 20
	if true:
		let rx = &x
		log!("rx: {}", *rx)
	swap_vals(&mut x, &mut y)
	log!("swapped: {} {}", x, y)

	// 4. Exhaustive match + Option + ?
	match try_opt(false):
		Option::Some(v) => log!("opt: {}", v)
		Option::None => log!("opt: none")

	// 5. Generic method constructing Self inside unsafe/while blocks
	let mut gen_box = GenBox{ val: 40 }
	let cloned = gen_box.clone_in_unsafe()
	log!("gen_box: {}", cloned.val)
"#,
        &[
            "h: fourth 4",
            "fs: 1.5 2.25 a b",
            "rx: 10",
            "swapped: 20 10",
            "opt: 4",
            "gen_box: 40",
        ],
    );
}

#[test]
fn soundness_negative_call_and_borrow_checks() {
    assert_err_code(
        "bad_fn_arg_type",
        "fn add1(x: i64) -> i64:\n\treturn x + 1\nfn main():\n\tadd1(\"oops\")\n",
        "E0308",
    );
    assert_err_code(
        "bad_extern_arg_arity",
        "use std::libc::strlen\nfn main():\n\tunsafe:\n\t\tstrlen(\"a\", \"b\")\n",
        "E0061",
    );
    assert_err_code(
        "bad_extern_arg_type",
        "use std::libc::strlen\nfn main():\n\tunsafe:\n\t\tstrlen(123)\n",
        "E0308",
    );
    assert_err_code(
        "imm_vec_push",
        "use std::vec::Vec\nfn main():\n\tlet v: Vec<i64> = Vec::new()\n\tv.push(1)\n",
        "E0596",
    );
    assert_err_code(
        "move_while_borrowed",
        "use std::string::String\nuse std::mem::drop\nfn main():\n\tlet s = String::from(\"hi\")\n\tlet r = &s\n\tdrop(s)\n\tlog!(\"{}\", r)\n",
        "E0505",
    );
    assert_err_code(
        "assign_while_borrowed",
        "fn main():\n\tlet mut x = 10\n\tlet r = &x\n\tx = 20\n\tlog!(\"{}\", *r)\n",
        "E0506",
    );
    assert_err_code(
        "dangling_temp_ref",
        "use std::string::String\nfn main():\n\tlet r = &String::from(\"tmp\")\n\tlog!(\"{}\", r)\n",
        "E0716",
    );
    assert_err_code(
        "aliasing_mut_call",
        "fn f(a: &mut i64, b: &mut i64):\n\t*a = *b\nfn main():\n\tlet mut x = 5\n\tf(&mut x, &mut x)\n",
        "E0499",
    );
    assert_err_code(
        "use_while_mut_borrowed",
        "fn main():\n\tlet mut x = 5\n\tlet r = &mut x\n\tlog!(\"{}\", x)\n",
        "E0502",
    );
    assert_err_code(
        "closure_capture",
        "use std::vec::Vec\nfn main():\n\tlet y = 1\n\tlet v = Vec::from_slice([1])\n\tv.map(|x|: x + y)\n",
        "E0434",
    );
    assert_err_code(
        "non_exhaustive_match",
        "enum E:\n\tA\n\tB\nfn main():\n\tlet e = E::A\n\tmatch e:\n\t\tE::A => log!(\"{}\", 1)\n",
        "E0004",
    );
}

#[test]
fn round4_control_flow_eq_and_drop_positive() {
    assert_ok_output(
        "round4_positive",
        r#"
use std::string::String
use std::core::{Option, Drop}
use std::math::Vec2

obj Counter:
	id: i64

impl Drop for Counter:
	fn drop(mut self):
		log!("drop_counter {}", self.id)

enum HolderEnum:
	Keep(Counter)
	Empty

trait Greeter:
	fn greet(self) -> i64

obj Dog:
	age: i64

impl Greeter for Dog:
	fn greet(self) -> i64:
		return self.age

fn bump(c: &mut i64) -> bool:
	*c = *c + 1
	return true

fn main():
	// 1. String content equality (str vs str, String vs String, String vs str)
	let f = format!("ab{}", "c")
	let s1 = String::from("abc")
	let s2 = String::from("abc")
	let s3 = String::from("xyz")
	log!("str_eq: {} {} {} {} {}", f == "abc", s1 == s2, s1 == s3, s1 == "abc", s1 != s3)

	// 2. Structural enum equality + NPO Option<*void> safety
	let o1 = Option::Some(10)
	let o2 = Option::Some(20)
	let o3 = Option::Some(10)
	let os1 = Option::Some(String::from("same"))
	let os2 = Option::Some(String::from("same"))
	let os3 = Option::Some(String::from("diff"))
	log!("enum_eq: {} {} {} {}", o1 == o2, o1 == o3, os1 == os2, os1 == os3)
	let npo_a: Option<*void> = Option::None
	let npo_b: Option<*void> = Option::None
	log!("npo_eq: {}", npo_a == npo_b)

	// 3. Short-circuit && and ||
	let mut sc = 0
	let a = false && bump(&mut sc)
	let b = true || bump(&mut sc)
	let c = true && bump(&mut sc)
	log!("short_circuit: {} {} {} {}", a, b, c, sc)

	// 4. Match arm payload drop, wildcard enum payload drop, and out-of-scope enum drop
	let he1 = HolderEnum::Keep(Counter{ id: 1 })
	match he1:
		HolderEnum::Keep(k) => log!("matched {}", k.id)
		HolderEnum::Empty => log!("empty")

	let he2 = HolderEnum::Keep(Counter{ id: 2 })
	match he2:
		_ => log!("wildcard_drop")

	let he3 = HolderEnum::Keep(Counter{ id: 3 })

	// 5. Index assign int->float coercion + overwrite drop
	let mut fs = [0.5, 1.5]
	fs[0] = 2
	log!("idx_coerce: {}", fs[0])
	let mut cs = [Counter{ id: 10 }, Counter{ id: 20 }]
	cs[0] = Counter{ id: 30 }

	// 6. Valid dyn Trait coercion & valid where bound
	let d: dyn Greeter = Dog{ age: 7 }
	log!("dyn_greet: {}", d.greet())
	let v2 = Vec2{ x: 3, y: 4 }
	log!("vec2: {} {}", v2.x, v2.y)
"#,
        &[
            "str_eq: true true false true true",
            "enum_eq: false true true false",
            "npo_eq: true",
            "short_circuit: false true true 1",
            "matched 1",
            "drop_counter 1",
            "wildcard_drop",
            "drop_counter 2",
            "idx_coerce: 2",
            "drop_counter 10",
            "dyn_greet: 7",
            "vec2: 3 4",
            "drop_counter 20",
            "drop_counter 30",
            "drop_counter 3",
        ],
    );
}

#[test]
fn round4_negative_soundness_checks() {
    assert_err_code(
        "match_double_move",
        "use std::string::String\nuse std::core::Option\nfn main():\n\tlet o = Option::Some(String::from(\"a\"))\n\tmatch o:\n\t\tOption::Some(s) => log!(\"{}\", s.as_str())\n\t\tOption::None => log!(\"{}\", 0)\n\tmatch o:\n\t\tOption::Some(s) => log!(\"{}\", s.as_str())\n\t\tOption::None => log!(\"{}\", 0)\n",
        "E0382",
    );
    assert_err_code(
        "while_loop_use_after_move",
        "use std::string::String\nuse std::mem::drop\nfn main():\n\tlet s = String::from(\"hi\")\n\tlet mut i = 0\n\twhile i < 2:\n\t\tdrop(s)\n\t\ti = i + 1\n",
        "E0382",
    );
    assert_err_code(
        "missing_trait_method",
        "trait Foo:\n\tfn bar(self) -> i64\nobj S:\n\tx: i64\nimpl Foo for S:\n\tfn other(self) -> i64:\n\t\treturn self.x\nfn main():\n\tlog!(\"{}\", 1)\n",
        "E0046",
    );
    assert_err_code(
        "wrong_trait_method_arity",
        "trait Foo:\n\tfn bar(self) -> i64\nobj S:\n\tx: i64\nimpl Foo for S:\n\tfn bar(self, y: i64) -> i64:\n\t\treturn self.x + y\nfn main():\n\tlog!(\"{}\", 1)\n",
        "E0050",
    );
    assert_err_code(
        "invalid_dyn_trait_coercion",
        "trait Foo:\n\tfn bar(self) -> i64\nobj S:\n\tx: i64\nfn main():\n\tlet d: dyn Foo = S{ x: 1 }\n",
        "E0277",
    );
    assert_err_code(
        "unsatisfied_where_bound",
        "use std::math::Vec2\nfn main():\n\tlet v = Vec2{ x: true, y: false }\n",
        "E0277",
    );
    assert_err_code(
        "immutable_array_index_assign",
        "fn main():\n\tlet a = [1, 2, 3]\n\ta[0] = 9\n",
        "E0596",
    );
    assert_err_code(
        "borrowed_array_index_assign",
        "fn main():\n\tlet mut a = [1, 2, 3]\n\tlet r = &a\n\ta[0] = 9\n\tlog!(\"{}\", (*r)[0])\n",
        "E0506",
    );
}

#[test]
fn round5_generics_macros_drops_and_stdlib_positive() {
    assert_ok_output(
        "round5_positive",
        r#"
use std::core::{Option, Drop}
use std::vec::Vec
use std::string::String
use std::fs::File
use ops::Add

fn id(x: $T) -> $T:
	return x

fn add_vals(a: $T, b: $T) -> $T where T: Add:
	return a + b

obj Counter:
	id: i64

impl Drop for Counter:
	fn drop(mut self):
		log!("drop_c {}", self.id)

trait Speak:
	fn speak(self) -> i64

impl Speak for Counter:
	fn speak(self) -> i64:
		return self.id

fn main():
	// 1. Standalone generic functions (int, str, float, where bound)
	let gi = id(42)
	let gs = id("ok")
	let gf = id(2.5)
	let sum_i = add_vals(10, 20)
	let sum_f = add_vals(1.25, 2.75)
	log!("gen: {} {} {} {} {}", gi, gs, gf, sum_i, sum_f)

	// 2. print!, assert!, assert_eq!
	print!("p1 {}", "p2")
	log!("")
	assert!(sum_i == 30)
	assert_eq!(gs, "ok")
	assert_eq!(String::from("ab"), "ab")
	assert_eq!(Option::Some(7), Option::Some(7))

	// 3. Vec<T> element drops & Vec::pop(&mut self)
	if true:
		let mut vc: Vec<Counter> = Vec::new()
		vc.push(Counter{ id: 101 })
		vc.push(Counter{ id: 102 })
		vc.push(Counter{ id: 103 })
		match vc.pop():
			Option::Some(popped) => log!("popped: {}", popped.id)
			Option::None => log!("empty")
		log!("remaining: {}", vc.len())

	// 4. dyn Trait drop glue
	if true:
		let dc: dyn Speak = Counter{ id: 201 }
		log!("dyn_speak: {}", dc.speak())

	// 5. File RAII Drop (unclosed File auto-closed on scope exit)
	let f_res = File::open("Cargo.toml")
	assert!(f_res.is_ok())
	log!("file_ok: true")
"#,
        &[
            "gen: 42 ok 2.5 30 4",
            "p1 p2",
            "popped: 103",
            "drop_c 103",
            "remaining: 2",
            "drop_c 101",
            "drop_c 102",
            "dyn_speak: 201",
            "drop_c 201",
            "file_ok: true",
        ],
    );

    // Verify failing assert! aborts with exit code 101 and diagnostic message
    let out = run_gdrs_source(
        "assert_fail",
        "fn main():\n\tassert!(false, \"boom\")\n",
    );
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("boom"),
        "Expected failing assert! stderr to mention `boom`, got:\n{stderr}"
    );
}

#[test]
fn round5_negative_soundness_checks() {
    assert_err_code(
        "standalone_generic_where_violation",
        "use ops::Add\nfn add_vals(a: $T, b: $T) -> $T where T: Add:\n\treturn a + b\nfn main():\n\tadd_vals(true, false)\n",
        "E0277",
    );
    assert_err_code(
        "assert_non_bool",
        "fn main():\n\tassert!(123)\n",
        "E0308",
    );
    assert_err_code(
        "assert_eq_mismatched",
        "fn main():\n\tassert_eq!(1, \"nope\")\n",
        "E0308",
    );
    assert_err_code(
        "raw_ptr_deref_requires_unsafe",
        "fn main():\n\tlet p = 0 as *i64\n\tlet v = *p\n\tlog!(\"{}\", v)\n",
        "E0133",
    );
    assert_err_code(
        "raw_ptr_write_requires_unsafe",
        "fn main():\n\tlet p = 0 as *i64\n\t*p = 5\n",
        "E0133",
    );
    assert_err_code(
        "raw_ptr_write_type_mismatch",
        "fn main():\n\tunsafe:\n\t\tlet p = 0 as *i64\n\t\t*p = \"bad\"\n",
        "E0308",
    );
    assert_err_code(
        "deref_move_out_of_ref",
        "use std::string::String\nfn main():\n\tlet s = String::from(\"hi\")\n\tlet r = &s\n\tlet moved = *r\n\tlog!(\"{}\", moved.as_str())\n",
        "E0507",
    );
    assert_err_code(
        "move_out_of_vec_index",
        "use std::vec::Vec\nuse std::string::String\nfn main():\n\tlet mut v: Vec<String> = Vec::new()\n\tv.push(String::from(\"a\"))\n\tlet s = v[0]\n\tlog!(\"{}\", s.as_str())\n",
        "E0507",
    );
}

#[test]
fn round6_bounds_moves_and_self_positive() {
    assert_ok_output(
        "round6_positive",
        r#"
use std::string::String
use std::vec::Vec
use std::core::{Option, Result, Drop}

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

obj Holder:
	label: String
	item: Tracked

fn main():
	// 1. Non-consuming &self methods on String, Vec, Option, Result
	let s = String::from("hello")
	assert!(!s.is_empty())
	assert_eq!(s.len(), 5)
	let s_copy = s.clone()
	assert_eq!(s.as_str(), "hello")
	assert_eq!(s_copy.as_str(), "hello")

	// 2. Borrowed enum match (&Option) followed by consuming unwrap() on droppable payload
	if true:
		let opt_t: Option<Tracked> = Option::Some(Tracked{ id: 301 })
		assert!(opt_t.is_some())
		assert!(!opt_t.is_none())
		match &opt_t:
			Option::Some(_) => log!("borrowed_some")
			Option::None => log!("borrowed_none")
		let unwrapped = opt_t.unwrap()
		log!("unwrapped_t {}", unwrapped.id)

	// 3. Struct with droppable fields: borrowing & cloning fields without moving
	if true:
		let h = Holder{ label: String::from("box"), item: Tracked{ id: 302 } }
		let cloned_lbl = h.label.clone()
		log!("holder {} {}", cloned_lbl.as_str(), h.item.id)

	// 4. `let mut` on string literal stays `str`
	let mut lit = "alpha"
	lit = "beta"
	log!("lit: {} {}", lit, typeof!(lit))
"#,
        &[
            "borrowed_some",
            "unwrapped_t 301",
            "drop_t 301",
            "holder box 302",
            "drop_t 302",
            "lit: beta str",
        ],
    );

    // 5. Runtime bounds check on fixed array index access
    let arr_out = run_gdrs_source(
        "bounds_array_read",
        "fn main():\n\tlet arr = [10, 20, 30]\n\tlet mut idx = 3\n\tlog!(\"{}\", arr[idx])\n",
    );
    assert!(!arr_out.status.success());
    let arr_err = String::from_utf8_lossy(&arr_out.stderr);
    assert!(
        arr_err.contains("index out of bounds: the len is 3 but the index is 3"),
        "Expected array bounds panic, got:\n{arr_err}"
    );

    // 6. Runtime bounds check on negative Vec index access
    let vec_out = run_gdrs_source(
        "bounds_vec_neg",
        "use std::vec::Vec\nfn main():\n\tlet mut v = Vec::new()\n\tv.push(99)\n\tlet neg = 0 - 1\n\tlog!(\"{}\", v[neg])\n",
    );
    assert!(!vec_out.status.success());
    let vec_err = String::from_utf8_lossy(&vec_out.stderr);
    assert!(
        vec_err.contains("index out of bounds: the len is 1 but the index is -1"),
        "Expected vec negative bounds panic, got:\n{vec_err}"
    );

    // 7. Runtime bounds check on array index assignment
    let assign_out = run_gdrs_source(
        "bounds_array_write",
        "fn main():\n\tlet mut arr = [1, 2]\n\tlet idx = 5\n\tarr[idx] = 42\n",
    );
    assert!(!assign_out.status.success());
    let assign_err = String::from_utf8_lossy(&assign_out.stderr);
    assert!(
        assign_err.contains("index out of bounds: the len is 2 but the index is 5"),
        "Expected array write bounds panic, got:\n{assign_err}"
    );
}

#[test]
fn round6_negative_soundness_checks() {
    assert_err_code(
        "move_droppable_field_in_let",
        "use std::string::String\nobj User:\n\tname: String\nfn main():\n\tlet u = User{ name: String::from(\"alice\") }\n\tlet moved = u.name\n\tlog!(\"{}\", moved.as_str())\n",
        "E0507",
    );
    assert_err_code(
        "move_droppable_field_in_return",
        "use std::string::String\nobj User:\n\tname: String\nfn take_name(u: &User) -> String:\n\treturn u.name\nfn main():\n\tlet u = User{ name: String::from(\"bob\") }\n\tlet n = take_name(&u)\n",
        "E0507",
    );
    assert_err_code(
        "move_droppable_field_in_call",
        "use std::string::String\nobj User:\n\tname: String\nfn consume(s: String):\n\tlog!(\"{}\", s.as_str())\nfn main():\n\tlet u = User{ name: String::from(\"carol\") }\n\tconsume(u.name)\n",
        "E0507",
    );
    assert_err_code(
        "move_out_of_borrowed_enum_match",
        "use std::core::Option\nuse std::string::String\nfn main():\n\tlet opt: Option<String> = Option::Some(String::from(\"hi\"))\n\tmatch &opt:\n\t\tOption::Some(s) => log!(\"{}\", s.as_str())\n\t\tOption::None => log!(\"none\")\n",
        "E0507",
    );
    assert_err_code(
        "double_unwrap_option",
        "use std::core::Option\nuse std::string::String\nfn main():\n\tlet opt: Option<String> = Option::Some(String::from(\"hi\"))\n\tlet a = opt.unwrap()\n\tlet b = opt.unwrap()\n",
        "E0382",
    );
    assert_err_code(
        "double_close_file",
        "use std::fs::File\nfn main():\n\tlet res = File::open(\"Cargo.toml\")\n\tlet f = res.unwrap()\n\tf.close()\n\tf.close()\n",
        "E0382",
    );
    assert_err_code(
        "use_file_after_read_to_string",
        "use std::fs::File\nfn main():\n\tlet res = File::open(\"Cargo.toml\")\n\tlet f = res.unwrap()\n\tlet content = f.read_to_string()\n\tf.close()\n",
        "E0382",
    );
}

#[test]
fn round7_tail_moves_borrows_and_discarded_drops_positive() {
    assert_ok_output(
        "round7_positive",
        r#"
use std::string::String
use std::core::{Drop, Option}

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

obj Boxed:
	val: String

fn make_tracked(id: i64) -> Tracked:
	return Tracked{ id: id }

fn take_mut_and_immut(a: &mut i64, b: &i64):
	*a = *a + *b

fn pick_or_new(opt: &Option<i64>, a: Tracked) -> Tracked:
	match opt:
		Option::Some(_) => a
		Option::None => make_tracked(405)

fn main():
	// 1. Discarded rvalue statements run Drop destructors immediately (not leaked)
	make_tracked(401)
	log!("after_401")
	Tracked{ id: 402 }
	log!("after_402")
	if true:
		make_tracked(403)
	log!("after_403")

	// 2. Yielding moved values from match arms works cleanly without double-free
	let opt_m: Option<i64> = Option::Some(1)
	let a = make_tracked(404)
	let moved = pick_or_new(&opt_m, a)
	log!("moved_id {}", moved.id)

	// 3. Non-aliasing borrows in call args & valid ref reassignment
	let mut x = 10
	let mut y = 5
	let mut r = &x
	assert_eq!(*r, 10)
	r = &y
	assert_eq!(*r, 5)
	take_mut_and_immut(&mut x, &y)
	assert_eq!(x, 15)
"#,
        &[
            "drop_t 401",
            "after_401",
            "drop_t 402",
            "after_402",
            "drop_t 403",
            "after_403",
            "moved_id 404",
            "drop_t 404",
        ],
    );
}

#[test]
fn round7_negative_soundness_checks() {
    assert_err_code(
        "use_after_match_arm_move",
        "use std::core::{Drop, Option}\nobj Tracked:\n\tid: i64\nimpl Drop for Tracked:\n\tfn drop(mut self):\n\t\tlog!(\"{}\", self.id)\nfn main():\n\tlet opt: Option<i64> = Option::Some(1)\n\tlet a = Tracked{ id: 1 }\n\tlet b = Tracked{ id: 2 }\n\tmatch &opt:\n\t\tOption::Some(_) => a\n\t\tOption::None => b\n\tlog!(\"{}\", a.id)\n",
        "E0382",
    );
    assert_err_code(
        "move_droppable_field_out_of_match_arm",
        "use std::string::String\nuse std::core::Option\nobj Boxed:\n\ts: String\nfn pick(opt: &Option<i64>, b1: &Boxed, b2: &Boxed) -> String:\n\tmatch opt:\n\t\tOption::Some(_) => b1.s\n\t\tOption::None => b2.s\nfn main():\n\tlet opt: Option<i64> = Option::Some(1)\n\tlet b1 = Boxed{ s: String::from(\"x\") }\n\tlet b2 = Boxed{ s: String::from(\"y\") }\n\tlet moved = pick(&opt, &b1, &b2)\n\tlog!(\"{}\", moved.as_str())\n",
        "E0507",
    );
    assert_err_code(
        "move_out_of_borrowed_var_in_fn_tail",
        "use std::string::String\nfn steal(s: String) -> String:\n\tlet r = &s\n\ts\nfn main():\n\tlet out = steal(String::from(\"z\"))\n",
        "E0505",
    );
    assert_err_code(
        "return_ref_to_local_var",
        "fn dangle() -> &i64:\n\tlet x = 42\n\treturn &x\nfn main():\n\tlet r = dangle()\n",
        "E0515",
    );
    assert_err_code(
        "return_local_ref_var_to_local",
        "fn dangle() -> &i64:\n\tlet x = 42\n\tlet r = &x\n\treturn r\nfn main():\n\tlet r = dangle()\n",
        "E0515",
    );
    assert_err_code(
        "return_ref_to_by_val_param",
        "fn dangle(x: i64) -> &i64:\n\treturn &x\nfn main():\n\tlet r = dangle(10)\n",
        "E0515",
    );
    assert_err_code(
        "escape_ref_from_if_block",
        "use std::string::String\nfn main():\n\tif true:\n\t\tlet s = String::from(\"hi\")\n\t\t&s\n",
        "E0597",
    );
    assert_err_code(
        "borrow_conflict_after_ref_reassignment",
        "fn main():\n\tlet x = 1\n\tlet mut y = 2\n\tlet mut r = &x\n\tr = &mut y\n\ty = 5\n\tlog!(\"{}\", *r)\n",
        "E0506",
    );
    assert_err_code(
        "temp_borrow_in_ref_reassignment",
        "fn main():\n\tlet x = 1\n\tlet mut r = &x\n\tr = &10\n\tlog!(\"{}\", *r)\n",
        "E0716",
    );
    assert_err_code(
        "double_mut_borrow_in_call_args",
        "fn two_mut(a: &mut i64, b: &mut i64):\n\t*a = 1\n\t*b = 2\nfn main():\n\tlet mut x = 0\n\ttwo_mut(&mut x, &mut x)\n",
        "E0499",
    );
    assert_err_code(
        "immut_and_mut_borrow_in_call_args",
        "fn imm_and_mut(a: &i64, b: &mut i64):\n\t*b = *a\nfn main():\n\tlet mut x = 5\n\timm_and_mut(&x, &mut x)\n",
        "E0502",
    );
    assert_err_code(
        "double_move_same_string_in_call_args",
        "use std::string::String\nfn take_two(a: String, b: String):\n\tlog!(\"{} {}\", a.as_str(), b.as_str())\nfn main():\n\tlet s = String::from(\"dup\")\n\ttake_two(s, s)\n",
        "E0382",
    );
}

#[test]
fn round8_shadowing_consuming_self_rc_and_format_positive() {
    assert_ok_output(
        "round8_positive",
        r#"
use std::core::Drop
use std::string::String
use std::fmt::Display
use std::error::Error

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

impl Tracked:
	fn consume(self):
		log!("consumed {}", self.id)

	fn chain(self) -> Tracked:
		log!("chaining {}", self.id)
		return self

obj Tag:
	label: str

impl Display for Tag:
	fn fmt(self) -> String:
		let r = format!("Tag:{}", self.label)
		return String::from(r)

#[derive(Error)]
enum MyErr:
	#[err("bad:{0}")]
	Bad(i64)
	#[err("plain")]
	Plain

fn main():
	// 1. Variable shadowing in same scope (same type + different type)
	if true:
		let u = Tracked{ id: 12 }
		let u = 99
		let t = Tracked{ id: 10 }
		let t = Tracked{ id: 11 }
		log!("shadow_same: {} {}", u, t.id)

	// 2. Variable shadowing across inner & outer scopes
	if true:
		let o = Tracked{ id: 20 }
		if true:
			let o = Tracked{ id: 21 }
			log!("inner_o: {}", o.id)
		log!("outer_o: {}", o.id)

	// 3. Consuming by-value `self` methods (`consume(self)` and `chain(self) -> Self`)
	if true:
		let c1 = Tracked{ id: 30 }
		c1.consume()
		log!("after_consume")
		let c2 = Tracked{ id: 40 }
		let c3 = c2.chain()
		log!("chained_id: {}", c3.id)

	// 4. Moving owned Tracked into rc.new / arc.new drops inner value exactly once
	if true:
		let raw_r = Tracked{ id: 50 }
		let r = rc.new(raw_r)
		let r2 = r.clone()
		log!("rc_cloned")
		let raw_a = Tracked{ id: 51 }
		let a = arc.new(raw_a)
		log!("arc_moved")

	// 5. Display::fmt (`String`) & #[derive(Error)] (`str`) in log! / format!
	let tg = Tag{ label: "ok" }
	log!("{}", tg)
	let ft = format!("[{}{}", tg, "]")
	log!("{}", ft)
	let e1 = MyErr::Bad(7)
	let e2 = MyErr::Plain
	log!("{} {}", e1, e2)
	log!("{}", format!("err={}", e1))
	log!("{} {}", String::from("temp_log"), format!("|={}", String::from("temp_fmt")))
"#,
        &[
            "shadow_same: 99 11",
            "drop_t 11",
            "drop_t 10",
            "drop_t 12",
            "inner_o: 21",
            "drop_t 21",
            "outer_o: 20",
            "drop_t 20",
            "consumed 30",
            "drop_t 30",
            "after_consume",
            "chaining 40",
            "chained_id: 40",
            "drop_t 40",
            "rc_cloned",
            "arc_moved",
            "drop_t 51",
            "drop_t 50",
            "Tag:ok",
            "[Tag:ok]",
            "\"bad:7\" plain",
            "err=\"bad:7\"",
            "temp_log |=temp_fmt",
        ],
    );
}

#[test]
fn round8_negative_soundness_checks() {
    assert_err_code(
        "rc_new_use_after_move",
        "use std::string::String\nfn main():\n\tlet s = String::from(\"a\")\n\tlet p = rc.new(s)\n\tlog!(\"{}\", s.as_str())\n",
        "E0382",
    );
    assert_err_code(
        "arc_new_double_move",
        "use std::string::String\nfn main():\n\tlet s = String::from(\"a\")\n\tlet p1 = arc.new(s)\n\tlet p2 = arc.new(s)\n",
        "E0382",
    );
    assert_err_code(
        "rc_new_move_while_borrowed",
        "use std::string::String\nfn main():\n\tlet s = String::from(\"a\")\n\tlet r = &s\n\tlet p = rc.new(s)\n\tlog!(\"{}\", r.as_str())\n",
        "E0505",
    );
    assert_err_code(
        "rc_new_projection_move",
        "use std::string::String\nuse std::vec::Vec\nfn main():\n\tlet mut v = Vec::new()\n\tv.push(String::from(\"x\"))\n\tlet p = rc.new(v[0])\n",
        "E0507",
    );
    assert_err_code(
        "consuming_self_use_after_move",
        "use std::core::Drop\nobj Tracked:\n\tid: i64\nimpl Drop for Tracked:\n\tfn drop(mut self):\n\t\tlog!(\"{}\", self.id)\nimpl Tracked:\n\tfn consume(self):\n\t\tlog!(\"{}\", self.id)\nfn main():\n\tlet c = Tracked{ id: 1 }\n\tc.consume()\n\tlog!(\"{}\", c.id)\n",
        "E0382",
    );
}

#[test]
fn round9_deref_and_projection_soundness() {
    assert_ok_output(
        "round9_positive",
        r#"
use std::core::Drop

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

fn main():
	if true:
		let r = rc.new(Tracked{ id: 60 })
		*r = Tracked{ id: 61 }
		log!("after_rc_overwrite")
	if true:
		let a = arc.new(Tracked{ id: 62 })
		*a = Tracked{ id: 63 }
		log!("after_arc_overwrite")
"#,
        &[
            "drop_t 60",
            "after_rc_overwrite",
            "drop_t 61",
            "drop_t 62",
            "after_arc_overwrite",
            "drop_t 63",
        ],
    );

    assert_err_code(
        "field_assign_through_immut_ref",
        "obj Point:\n\tx: i64\nfn main():\n\tlet p = Point{ x: 1 }\n\tlet r = &p\n\tr.x = 2\n",
        "E0594",
    );
    assert_err_code(
        "nested_field_assign_while_borrowed",
        "obj Inner:\n\tx: i64\nobj Outer:\n\ti: Inner\nfn main():\n\tlet mut o = Outer{ i: Inner{ x: 1 } }\n\tlet r = &o\n\to.i.x = 2\n\tlog!(\"{}\", r)\n",
        "E0506",
    );
    assert_err_code(
        "deref_assign_projection_move",
        "use std::string::String\nuse std::vec::Vec\nfn main():\n\tlet mut dst = String::from(\"a\")\n\tlet r = &mut dst\n\tlet mut v = Vec::new()\n\tv.push(String::from(\"b\"))\n\t*r = v[0]\n",
        "E0507",
    );
}

#[test]
fn round10_hindley_milner_inference() {
    assert_ok_output(
        "round10_inference_positive",
        r#"
use std::vec::Vec
use std::core::Option
use std::string::String

obj NumBox where $T: Add:
	rows: i32
	cols: i32
	data: Vec<$T>

impl NumBox:
	fn new_empty(rows: i32, cols: i32) -> NumBox:
		return NumBox{ rows: rows, cols: cols, data: Vec::new() }

	fn first(&self) -> $T:
		return self.data[0]

fn take_f64_vec(v: Vec<f64>):
	log!("vec_arg_len {}", v.len())

fn take_opt_i64(o: Option<i64>):
	log!("opt_arg {}", o.is_none())

fn make_none_str() -> Option<String>:
	return Option::None

fn id_generic(x: $T) -> $T:
	return x

fn pick_opt(flag: bool):
	if flag:
		let r = Option::Some(99)
		log!("o2_none {}", r.is_none())
	else:
		let r: Option<i64> = Option::None
		log!("o2_none {}", r.is_none())

fn main():
	// 1. Struct generic inferred backwards from nested field .push(f64)
	let mut m1 = NumBox{ rows: 1, cols: 2, data: Vec::new() }
	m1.data.push(3.5)
	log!("m1_0 {}", m1.data[0])

	// 2. Struct generic constrained directly by let annotation
	let mut m2: NumBox<f64> = NumBox{ rows: 1, cols: 1, data: Vec::new() }
	m2.data.push(4.25)
	log!("m2_0 {}", m2.data[0])

	// 3. Static constructor + retroactive binop constraint (+ 2.5)
	let mut m3 = NumBox::new_empty(1, 1)
	m3.data.push(1.5)
	let sum = m3.first() + 2.5
	log!("m3_sum {}", sum)

	// 4. Vec::new inferred backwards from function call parameter
	let v_fn = Vec::new()
	take_f64_vec(v_fn)

	// 5. Option::None + method call before constraining via call
	let o1 = Option::None
	let o1_empty = o1.is_none()
	log!("o1_empty {}", o1_empty)
	take_opt_i64(o1)

	// 6. Option::None constrained via if/else branch unification
	pick_opt(false)

	// 7. Option::None constrained via function return type
	let o3 = make_none_str()
	log!("o3_none {}", o3.is_none())

	// 8. Vec::len() and Vec::pop() called BEFORE Vec element type is constrained
	let mut v_late = Vec::new()
	let len0 = v_late.len()
	let pop0 = v_late.pop()
	v_late.push(7.5)
	log!("late_len {} {} {}", len0, v_late.len(), pop0.is_none())

	// 9. Generic identity function preserving Infer across call + match binding inference
	let o_match = Option::None
	match o_match:
		Option::Some(val) =>
			let _ = val + 1.25
		Option::None =>
			log!("match_infer_ok")

	let mut v_id = id_generic(Vec::new())
	v_id.push(8.5)
	log!("v_id_0 {}", v_id[0])

	// 10. Nested Vec<Vec<f64>>
	let mut mat = Vec::new()
	let r0 = Vec::new()
	mat.push(r0)
	let typed_mat: Vec<Vec<f64> > = mat
	log!("nested_mat_len {}", typed_mat.len())
"#,
        &[
            "m1_0 3.5",
            "m2_0 4.25",
            "m3_sum 4",
            "vec_arg_len 0",
            "o1_empty true",
            "opt_arg true",
            "o2_none true",
            "o3_none true",
            "late_len 0 1 true",
            "match_infer_ok",
            "v_id_0 8.5",
            "nested_mat_len 1",
        ],
    );

    assert_err_code(
        "unconstrained_vec_new",
        "use std::vec::Vec\nfn main():\n\tlet v = Vec::new()\n",
        "E0282",
    );
    assert_err_code(
        "unconstrained_empty_array",
        "fn main():\n\tlet mut v = []\n",
        "E0282",
    );
    assert_err_code(
        "unconstrained_option_none",
        "use std::core::Option\nfn main():\n\tlet o = Option::None\n",
        "E0282",
    );
    assert_err_code(
        "unconstrained_result_err_param",
        "use std::core::Result\nfn main():\n\tlet r = Result::Ok(7)\n",
        "E0282",
    );
    assert_err_code(
        "unconstrained_generic_struct_nested_vec",
        "use std::vec::Vec\nobj Matrix where $T: Add:\n\trows: i32\n\tcols: i32\n\tdata: Vec<$T>\nfn main():\n\tlet m = Matrix{ cols: 0, rows: 0, data: Vec::new() }\n",
        "E0282",
    );
    assert_err_code(
        "conflicting_vec_push_after_infer",
        "use std::vec::Vec\nfn main():\n\tlet mut v = Vec::new()\n\tv.push(3.5)\n\tv.push(\"bad\")\n",
        "E0308",
    );
    assert_err_code(
        "inferred_generic_struct_violates_bound",
        "use std::vec::Vec\nobj NumBox where $T: Add:\n\tdata: Vec<$T>\nfn main():\n\tlet mut b = NumBox{ data: Vec::new() }\n\tb.data.push(true)\n",
        "E0277",
    );
}

#[test]
fn round11_zero_leak_runtime_improvements() {
    assert_ok_output(
        "round11_temps_slices_vtables_and_ranges",
        r#"
use std::core::Drop
use std::string::String
use std::vec::Vec

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

trait Speak:
	fn speak(&self) -> i64

impl Speak for Tracked:
	fn speak(&self) -> i64:
		return self.id

fn make_tracked(id: i64) -> Tracked:
	return Tracked{ id: id }

fn inspect_tracked(t: &Tracked):
	log!("inspect {}", t.id)

fn sum_slice(s: [i64]) -> i64:
	let mut acc = 0
	for i in 0..s.len:
		acc = acc + s[i]
	return acc

fn early_return_with_temp() -> i64:
	return make_tracked(3).id

fn main():
	// 1. Statement-level temporary rvalue drops (borrow arg, field projection, discarded, early return)
	inspect_tracked(&make_tracked(1))
	let field_val = make_tracked(2).id
	log!("field_val {}", field_val)
	let ret_val = early_return_with_temp()
	log!("ret_val {}", ret_val)
	log!("temp_str {}", String::from("ok").as_str())

	// 2. Native Range loops (`for` and `.for_each`) with `continue` and `break`
	let mut sum = 0
	for i in 0..6:
		if i == 2:
			continue
		if i == 5:
			break
		sum = sum + i
	log!("for_sum {}", sum)

	let mut fe_sum = 0
	(1..5).for_each(|x|:
		fe_sum = fe_sum + x
	)
	log!("fe_sum {}", fe_sum)

	// 3. Stack-slot slice headers & static vtable dispatch
	let arr = [10, 20, 30]
	log!("slice_sum {}", sum_slice(arr))
	let sl: [i64] = [4, 5, 6]
	log!("let_slice {} {}", sl[0], sl[2])

	if true:
		let d1: dyn Speak = Tracked{ id: 40 }
		let d2: dyn Speak = Tracked{ id: 41 }
		log!("dyn {} {}", d1.speak(), d2.speak())
"#,
        &[
            "inspect 1",
            "drop_t 1",
            "drop_t 2",
            "field_val 2",
            "drop_t 3",
            "ret_val 3",
            "temp_str ok",
            "for_sum 8",
            "fe_sum 10",
            "slice_sum 60",
            "let_slice 4 6",
            "dyn 40 41",
            "drop_t 41",
            "drop_t 40",
        ],
    );
}

#[test]
fn round12_by_value_aggregates_and_std() {
    assert_ok_output(
        "round12_value_aggregates",
        r#"
use std::core::{Drop, Option, Result}
use std::string::String
use std::vec::Vec

obj Pair32:
	a: i32
	b: i32

obj Point64:
	x: i64
	y: i64

obj Big24:
	a: i64
	b: i64
	c: i64

obj Tracked:
	id: i64

impl Drop for Tracked:
	fn drop(mut self):
		log!("drop_t {}", self.id)

obj NestedHolder:
	label: String
	t: Tracked
	flag: bool

fn make_pair32(a: i32, b: i32) -> Pair32:
	return Pair32{ a: a, b: b }

fn swap_point(p: &Point64) -> Point64:
	return Point64{ x: p.y, y: p.x }

fn mutate_point(p: &mut Point64):
	p.x = 999

fn make_big(a: i64, b: i64, c: i64) -> Big24:
	return Big24{ a: a, b: b, c: c }

fn make_ok_string(s: str) -> Result<String, i64>:
	return Result::Ok(String::from(s))

fn main():
	// 1. MultiReg <=16B structs and value isolation across calls
	let p32 = make_pair32(7 as i32, 9 as i32)
	log!("pair32 {} {}", p32.a, p32.b)

	let mut pt1 = Point64{ x: 10, y: 20 }
	let pt2 = swap_point(&pt1)
	mutate_point(&mut pt1)
	log!("pts {} {} {} {}", pt1.x, pt1.y, pt2.x, pt2.y)

	// 2. Indirect >16B struct return (sret) and Copy isolation
	let b = make_big(1, 2, 3)
	log!("big {} {} {}", b.a, b.b, b.c)

	// 3. Tight loop constructing stack structs, non-NPO enums, and stack arrays
	let mut acc = 0
	for i in 0..1000:
		let p = Point64{ x: i, y: i + 1 }
		let arr = [p.x, p.y]
		let opt = Option::Some(arr[0] + arr[1])
		match opt:
			Option::Some(v) =>
				acc = acc + v
			Option::None =>
				acc = acc + 0
	log!("loop_acc {}", acc)

	// 4. Nested aggregate drop order (String + Tracked + bool padding) & Result<String, i64>
	if true:
		let h = NestedHolder{ label: String::from("lbl"), t: Tracked{ id: 77 }, flag: true }
		log!("holder {} {} {}", h.label.as_str(), h.t.id, h.flag)

	let res = make_ok_string("hello_sret")
	match res:
		Result::Ok(s) =>
			let cloned = s.clone()
			log!("ok_str {} {}", s.as_str(), cloned.as_str())
		Result::Err(_) =>
			log!("err")

	// 5. Option<String> equality and empty String::new()
	let os1 = Option::Some(String::from("abc"))
	let os2 = Option::Some(String::from("abc"))
	let os3 = Option::Some(String::from("xyz"))
	log!("opt_str_eq {} {}", os1 == os2, os1 == os3)
	let empty_s = String::new()
	log!("empty {} {}", empty_s, empty_s.len())

	// 6. Vec<String> (24B stride elements!), Vec<i32> (4B elements!), &arr[i], and VecIter::next(&mut self)
	if true:
		let mut vs: Vec<String> = Vec::new()
		vs.push(String::from("first"))
		vs.push(String::from("second"))
		vs.push(String::from("third"))
		let popped = vs.pop().unwrap()
		log!("vs_pop {} {} {} {}", popped.as_str(), vs.len(), vs[0].as_str(), vs[1].as_str())

	let mut v32: Vec<i32> = Vec::new()
	v32.push(11 as i32)
	v32.push(22 as i32)
	v32.push(33 as i32)
	let mut sum_v = 0
	for x in v32:
		sum_v = sum_v + x
	log!("vec_for_sum {}", sum_v)

	let mut prim_arr = [5, 10, 15]
	if true:
		let r_elem = &mut prim_arr[1]
		*r_elem = 100
	log!("arr_mut_ref {} {} {}", prim_arr[0], prim_arr[1], prim_arr[2])
"#,
        &[
            "pair32 7 9",
            "pts 999 20 20 10",
            "big 1 2 3",
            "loop_acc 1000000",
            "holder lbl 77 true",
            "drop_t 77",
            "ok_str hello_sret hello_sret",
            "opt_str_eq true false",
            "empty  0",
            "vs_pop third 2 first second",
            "vec_for_sum 66",
            "arr_mut_ref 5 100 15",
        ],
    );
}

#[test]
fn round13_rust_tuples() {
    assert_ok_output(
        "round13_rust_tuples",
        r#"
use std::vec::Vec

obj MiniMatrix:
	rows: i32
	cols: i32

impl MiniMatrix:
	fn shape(&self) -> (i32, i32):
		return (self.rows, self.cols)

obj Tracked:
	id: i64

impl Tracked:
	fn drop(&mut self):
		log!("drop_t {}", self.id)

fn make_sret_tuple() -> (Tracked, Tracked, Tracked, bool):
	return (Tracked{ id: 10 }, Tracked{ id: 20 }, Tracked{ id: 30 }, true)

fn swap_pair(pair: ($T, $U)) -> ($U, $T):
	let (a, b) = pair
	return (b, a)

fn take_unit(u: ()) -> i64:
	return 7

fn main():
	// 1. MultiReg return & destructuring (Matrix::shape pattern)
	let m = MiniMatrix{ rows: 3 as i32, cols: 4 as i32 }
	let (r, c) = m.shape()
	log!("shape {} {}", r, c)

	// 2. Copy semantics on Copy tuple + 1-tuple + unit + parens
	let p = (10 as i32, 20 as i32)
	let p_copy = p
	log!("copy_tup {} {} {} {} {}", p.0, p.1, p_copy.0, p_copy.1, typeof!(p))

	let single = (99,)
	let single2 = (99,)
	let (single_val,) = single
	log!("single {} {} {}", single.0, single_val, single == single2)

	let u: () = ()
	let paren_math = (1 + 2) * 3
	log!("unit_math {} {} {}", take_unit(u), paren_math, () == ())

	// 3. Large sret tuple, destructuring with mut & wildcard `_` immediate drop timing
	if true:
		let (mut first_t, _, second_t, flag) = make_sret_tuple()
		first_t.id = 11
		log!("sret_inner {} {} {}", first_t.id, second_t.id, flag)
	log!("after_sret_block")

	// 4. Nested tuples, chained indexing `.0.1`, field mutation, &mut ref to tuple field, nested let pattern
	let mut nested: ((i64, i32), (bool, i64)) = ((1, 2 as i32), (false, 4))
	nested.0.1 = 99 as i32
	if true:
		let r_num = &mut nested.1.1
		*r_num = 88
	log!("nested {} {} {} {}", nested.0.0, nested.0.1, nested.1.0, nested.1.1)
	let ((na, nb), (nc, _)) = nested
	log!("nested_pat {} {} {}", na, nb, nc)

	// 5. Generic tuple swap & structural equality
	let swapped = swap_pair((String::from("hi"), 123))
	log!("swapped {} {}", swapped.0, swapped.1.as_str())

	let eq_a = (1 as i32, String::from("same"))
	let eq_b = (1 as i32, String::from("same"))
	let eq_c = (2 as i32, String::from("same"))
	log!("tup_eq {} {} {}", eq_a == eq_b, eq_a != eq_c, eq_a == eq_c)

	let opt1 = Option::Some((5 as i32, 6 as i32))
	let opt2 = Option::Some((5 as i32, 6 as i32))
	log!("opt_tup_eq {}", opt1 == opt2)

	// 6. Vec<(i32, i32)> push / index / pop / for-loop pattern destructuring
	let mut coords: Vec<(i32, i32)> = Vec::new()
	coords.push((1 as i32, 2 as i32))
	coords.push((3 as i32, 4 as i32))
	coords.push((5 as i32, 6 as i32))
	let popped = coords.pop().unwrap()
	let mut x_sum: i32 = 0 as i32
	let mut y_sum: i32 = 0 as i32
	for (x, y) in coords:
		x_sum = x_sum + x
		y_sum = y_sum + y
	log!("vec_tup {} {} {} {}", popped.0, popped.1, x_sum, y_sum)
"#,
        &[
            "shape 3 4",
            "copy_tup 10 20 10 20 (i32, i32)",
            "single 99 99 true",
            "unit_math 7 9 true",
            "drop_t 20\nsret_inner 11 30 true",
            "drop_t 11",
            "drop_t 30",
            "after_sret_block",
            "nested 1 99 false 88",
            "nested_pat 1 99 false",
            "swapped 123 hi",
            "tup_eq true true false",
            "opt_tup_eq true",
            "vec_tup 5 6 4 6",
        ],
    );
}

#[test]
fn round13_tuple_negative_checks() {
    assert_err_code(
        "round13_use_after_tuple_move",
        r#"
fn main():
	let t = (String::from("hello"), 42)
	let (s, n) = t
	log!("{}", t.1)
"#,
        "E0382",
    );

    assert_err_code(
        "round13_move_out_of_tuple_field",
        r#"
fn main():
	let t = (String::from("hello"), 42)
	let s = t.0
"#,
        "E0507",
    );
}

#[test]
fn round14_explicit_borrows_positive() {
    assert_ok_output(
        "round14_explicit_borrows_pos",
        r#"
use std::core::Option
use std::math::matrix::Matrix
use std::vec::Vec

obj BoxedVal:
	val: i64
	items: Vec<i64>

impl BoxedVal:
	fn new(v: i64) -> BoxedVal:
		return BoxedVal{ val: v, items: Vec::new() }

	fn get(&self, idx: i64) -> i64:
		return self.val + idx

	fn push_item(&mut self, x: i64):
		self.items.push(x)

	fn add_val(&self, o: &BoxedVal) -> i64:
		return self.val + o.val

obj CounterIter:
	cur: i64
	end: i64

impl CounterIter:
	fn next(&mut self) -> Option<i64>:
		if self.cur >= self.end:
			return Option::None
		let v = self.cur
		self.cur = self.cur + 1
		return Option::Some(v)

obj CounterRange:
	end: i64

impl CounterRange:
	fn into_iter(&self) -> CounterIter:
		return CounterIter{ cur: 0, end: self.end }

fn read_box(b: &BoxedVal) -> i64:
	return b.val

fn bump_box(b: &mut BoxedVal):
	b.val = b.val + 10

fn main():
	// 1. Receiver auto-ref (&self and &mut self) + 2. Receiver through a field (self.items.push)
	let mut b1 = BoxedVal::new(5)
	b1.push_item(100)
	log!("get {} {}", b1.get(2), b1.items.len())

	// 3. Receiver that is a temporary (rvalue)
	let rval = Matrix::zeros(2 as i32, 2 as i32).get(0 as i32, 0 as i32)
	log!("rval {}", rval)

	// 4. Explicit borrows: free fn, method non-receiver arg, path call
	let b2 = BoxedVal::new(7)
	log!("read {}", read_box(&b2))
	bump_box(&mut b1)
	log!("bumped {}", b1.val)
	let sum = b1.add_val(&b2)
	log!("add_val {} {} {}", sum, b1.val, b2.val)
	log!("path_get {}", BoxedVal::get(&b2, 3))

	// 5. Passing an existing ref variable
	let r = &b2
	log!("existing_ref {}", read_box(r))

	// 6. &mut T -> &T coercion
	let rm = &mut b1
	log!("mut_to_ref {}", read_box(rm))

	// 7. for-loops over Vec and custom iterable
	let mut v: Vec<i64> = Vec::new()
	v.push(1)
	v.push(2)
	v.push(3)
	let mut v_sum = 0
	for x in v:
		v_sum = v_sum + x
	let mut c_sum = 0
	for n in CounterRange{ end: 4 }:
		c_sum = c_sum + n
	log!("loops {} {}", v_sum, c_sum)
"#,
        &[
            "get 7 1",
            "rval 0",
            "read 7",
            "bumped 15",
            "add_val 22 15 7",
            "path_get 10",
            "existing_ref 7",
            "mut_to_ref 15",
            "loops 6 6",
        ],
    );
}

fn assert_single_borrow_err(name: &str, src: &str, expected_help: &str) {
    let out = run_gdrs_source(name, src);
    let combined = format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !out.status.success(),
        "Expected `{name}` to fail with E0308, but it succeeded!\nOutput:\n{combined}"
    );
    let e0308_count = combined.matches("[E0308]").count();
    assert_eq!(
        e0308_count, 1,
        "Expected exactly 1 [E0308] error for `{name}`, got {e0308_count}.\nOutput:\n{combined}"
    );
    assert!(
        combined.contains(expected_help),
        "Expected `{name}` output to contain `{expected_help}`.\nActual output:\n{combined}"
    );
}

#[test]
fn round14_explicit_borrows_negative() {
    assert_single_borrow_err(
        "round14_missing_ref_free_fn",
        r#"
obj Pair:
	a: i64

fn take_ref(p: &Pair) -> i64:
	return p.a

fn main():
	let p = Pair{ a: 1 }
	log!("{}", take_ref(p))
"#,
        "Consider borrowing here: `&p`",
    );

    assert_single_borrow_err(
        "round14_missing_mut_ref_free_fn",
        r#"
obj Pair:
	a: i64

fn take_mut(p: &mut Pair):
	p.a = 2

fn main():
	let mut p = Pair{ a: 1 }
	take_mut(p)
"#,
        "Consider borrowing here: `&mut p`",
    );

    assert_single_borrow_err(
        "round14_missing_ref_method_arg",
        r#"
obj Pair:
	a: i64

impl Pair:
	fn add(&self, o: &Pair) -> i64:
		return self.a + o.a

fn main():
	let p1 = Pair{ a: 1 }
	let p2 = Pair{ a: 2 }
	log!("{}", p1.add(p2))
"#,
        "Consider borrowing here: `&p2`",
    );

    assert_single_borrow_err(
        "round14_missing_ref_path_call",
        r#"
obj Pair:
	a: i64

impl Pair:
	fn get(&self, offset: i64) -> i64:
		return self.a + offset

fn main():
	let p = Pair{ a: 1 }
	log!("{}", Pair::get(p, 5))
"#,
        "Consider borrowing here: `&p`",
    );
}

#[test]
fn round15_unified_macro_system() {
    // 1. Positive: format!, escaped braces, non-consuming assert_eq!/assert_ne!, reflection macros
    assert_ok_output(
        "round15_macro_positive",
        r#"
use std::string::String

fn main():
	let s = String::from("hello")
	assert_eq!(s, "hello")
	assert_ne!(s, "world")
	log!("val is {}", s)
	let braced = format!("{{ {} }}", 42)
	log!("braced={}", braced)
	log!("line={} col={} snip={}", line!(), column!(), stringify!(1 + 2))
	assert!(1 + 1 == 2, "math broke: {}", 2)
"#,
        &[
            "val is hello",
            "braced={ 42 }",
            "line=11 col=",
            "snip=1 + 2",
        ],
    );

    // 2. Failing assert_eq! prints left, right, and file:line:col with exit 101
    let eq_fail = run_gdrs_source(
        "round15_assert_eq_fail",
        "fn main():\n\tlet a = 10\n\tlet b = 20\n\tassert_eq!(a, b)\n",
    );
    assert_eq!(eq_fail.status.code(), Some(101));
    let eq_stderr = String::from_utf8_lossy(&eq_fail.stderr);
    assert!(
        eq_stderr.contains("thread 'main' panicked at")
            && eq_stderr.contains(":4:")
            && eq_stderr.contains("assertion `left == right` failed")
            && eq_stderr.contains("left: 10")
            && eq_stderr.contains("right: 20"),
        "Unexpected assert_eq! stderr:\n{eq_stderr}"
    );

    // 3. Failing assert_ne! prints left, right, and file:line:col with exit 101
    let ne_fail = run_gdrs_source(
        "round15_assert_ne_fail",
        "fn main():\n\tlet a = 42\n\tassert_ne!(a, 42)\n",
    );
    assert_eq!(ne_fail.status.code(), Some(101));
    let ne_stderr = String::from_utf8_lossy(&ne_fail.stderr);
    assert!(
        ne_stderr.contains("thread 'main' panicked at")
            && ne_stderr.contains(":3:")
            && ne_stderr.contains("assertion `left != right` failed")
            && ne_stderr.contains("left: 42")
            && ne_stderr.contains("right: 42"),
        "Unexpected assert_ne! stderr:\n{ne_stderr}"
    );

    // 4. Failing assert! prints snippet and file:line:col with exit 101
    let assert_fail = run_gdrs_source(
        "round15_assert_fail_loc",
        "fn main():\n\tlet x = 3\n\tassert!(x > 5)\n",
    );
    assert_eq!(assert_fail.status.code(), Some(101));
    let assert_stderr = String::from_utf8_lossy(&assert_fail.stderr);
    assert!(
        assert_stderr.contains("thread 'main' panicked at")
            && assert_stderr.contains(":3:")
            && assert_stderr.contains("assertion failed: x > 5"),
        "Unexpected assert! stderr:\n{assert_stderr}"
    );

    // 5. Negative diagnostics: format placeholder mismatch (E0061), {:?} (E0277),
    // missing Display (E0277), non-literal format arg (E0308), unknown macro (E0425)
    assert_err_code(
        "round15_fmt_arity_mismatch",
        "fn main():\n\tlog!(\"hello {}\")\n",
        "E0061",
    );
    assert_err_code(
        "round15_fmt_debug_unsupported",
        "fn main():\n\tlog!(\"hello {:?}\", 42)\n",
        "E0277",
    );
    assert_err_code(
        "round15_fmt_missing_display",
        "obj NoFmt:\n\tx: i64\nfn main():\n\tlet nf = NoFmt{ x: 1 }\n\tlog!(\"{}\", nf)\n",
        "E0277",
    );
    assert_err_code(
        "round15_fmt_non_literal",
        "fn main():\n\tlog!(123)\n",
        "E0308",
    );
    assert_err_code(
        "round15_unknown_macro",
        "fn main():\n\tunknown_macro!(1)\n",
        "E0425",
    );

    // 6. Tuple display in log!, format!, #[derive(Error)], and assert_eq!
    assert_ok_output(
        "round15_tuple_display",
        r#"
use std::string::String

#[derive(Error)]
enum MatrixError:
	#[err("cannot perform on matrices of different dimensions `{0}` and `{1}`")]
	ShapeMismatch((i32, i32), (i32, i32))

fn main():
	let t: (i32, i32) = (2, 3)
	let nested = (t, String::from("ok"))
	let single = (7,)
	log!("t={} nested={} single={}", t, nested, single)
	let e = MatrixError::ShapeMismatch((2, 2), (3, 4))
	log!("err={}", e)
"#,
        &[
            "t=(2, 3) nested=((2, 3), ok) single=(7,)",
            "err=\"cannot perform on matrices of different dimensions `(2, 2)` and `(3, 4)`\"",
        ],
    );

    // 7. Non-displayable element inside a tuple must still fail with E0277
    assert_err_code(
        "round15_tuple_non_displayable_elem",
        "obj NoFmt:\n\tx: i64\nfn main():\n\tlet t = (1, NoFmt{ x: 2 })\n\tlog!(\"{}\", t)\n",
        "E0277",
    );

    // 8. vec! macro: inferred elements, expected element type (i32/f64), empty vec![], and heterogeneous rejection
    assert_ok_output(
        "round15_vec_macro",
        r#"
use std::vec::Vec
fn main():
	let a = vec![1, 2, 3]
	let b: Vec<i32> = vec![10, 20]
	let mut c: Vec<f64> = vec![]
	c.push(3.5)
	log!("a={} b={} c={}", a.len(), b[1], c[0])
"#,
        &["a=3 b=20 c=3.5"],
    );
    assert_err_code(
        "round15_vec_macro_heterogeneous",
        "use std::vec::Vec\nfn main():\n\tlet v = vec![1, \"bad\"]\n",
        "E0308",
    );
}

#[test]
fn round16_if_let() {
    assert_ok_output(
        "round16_if_let_variants",
        r#"
use std::core::{Option, Result}

enum Custom:
	Pair(i64, i64)
	Empty

fn check_res(ok: bool) -> Result<i64, str>:
	if ok:
		return Ok(42)
	return Err("boom")

fn main():
	if let Err(e) = check_res(false):
		log!("err={}", e)

	if let Err(e) = check_res(true):
		log!("should_not_print={}", e)

	if let Ok(v) = check_res(true):
		log!("ok={}", v)
	else:
		log!("bad")

	let c = Custom::Pair(10, 20)
	if let Custom::Pair(a, b) = c:
		log!("pair={}+{}", a, b)

	let opt: Option<i64> = Option::Some(7)
	if let None = &opt:
		log!("none")
	else if let Some(x) = &opt:
		log!("some={}", x)
"#,
        &["err=boom", "ok=42", "pair=10+20", "some=7"],
    );
}

#[test]
fn round17_panic_locations_and_backtraces() {
    // 1. Explicit panic! prints file:line:col and GDRS_BACKTRACE note
    let panic_out = run_gdrs_source(
        "round17_panic_loc",
        "fn main():\n\tlet x = 1\n\tpanic!(\"kaboom {}\", x)\n",
    );
    assert_eq!(panic_out.status.code(), Some(101));
    let panic_stderr = String::from_utf8_lossy(&panic_out.stderr);
    assert!(
        panic_stderr.contains("thread 'main' panicked at")
            && panic_stderr.contains(":3:")
            && panic_stderr.contains("kaboom 1")
            && panic_stderr.contains("GDRS_BACKTRACE=1"),
        "Unexpected panic! stderr:\n{panic_stderr}"
    );

    // 2. Out-of-bounds index panic prints file:line:col and index/len
    let oob_out = run_gdrs_source(
        "round17_bounds_loc",
        "use std::vec::Vec\nfn main():\n\tlet v = vec![10, 20]\n\tlet x = v[5]\n\tlog!(\"{}\", x)\n",
    );
    assert_eq!(oob_out.status.code(), Some(101));
    let oob_stderr = String::from_utf8_lossy(&oob_out.stderr);
    assert!(
        oob_stderr.contains("thread 'main' panicked at")
            && oob_stderr.contains(":4:")
            && oob_stderr.contains("index out of bounds: the len is 2 but the index is 5"),
        "Unexpected bounds panic stderr:\n{oob_stderr}"
    );

    // 3. GDRS_BACKTRACE=1 prints stack backtrace with exported function symbols
    let id = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = std::env::temp_dir().join(format!("gdrs_test_{}_{id}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let file_path = dir.join("round17_backtrace.gdrs");
    fs::write(
        &file_path,
        "fn inner_boom():\n\tpanic!(\"trace me\")\nfn main():\n\tinner_boom()\n",
    )
    .unwrap();
    let bt_out = Command::new(gdrs_bin())
        .current_dir(repo_root())
        .env("GDRS_BACKTRACE", "1")
        .arg(&file_path)
        .output()
        .expect("failed to execute gdrs with GDRS_BACKTRACE=1");
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(bt_out.status.code(), Some(101));
    let bt_stderr = String::from_utf8_lossy(&bt_out.stderr);
    assert!(
        bt_stderr.contains("stack backtrace:")
            && bt_stderr.contains("inner_boom")
            && bt_stderr.contains("gdrs_main"),
        "Unexpected backtrace stderr:\n{bt_stderr}"
    );

    // 4. #[track_caller] on Result::unwrap blames the caller's line, not std/core.gdrs
    let unwrap_out = run_gdrs_source(
        "round17_track_caller_unwrap",
        "use std::core::Result\nfn make_err() -> Result<i64, str>:\n\treturn Err(\"bad\")\nfn main():\n\tlet r = make_err()\n\tlet x = r.unwrap()\n\tlog!(\"{}\", x)\n",
    );
    assert_eq!(unwrap_out.status.code(), Some(101));
    let unwrap_stderr = String::from_utf8_lossy(&unwrap_out.stderr);
    assert!(
        unwrap_stderr.contains("round17_track_caller_unwrap.gdrs:6:")
            && unwrap_stderr.contains("called `Result::unwrap()` on an `Err` value"),
        "Expected unwrap() panic to blame caller line 6, got:\n{unwrap_stderr}"
    );

    // 5. Nested #[track_caller] forwarding blames the outermost non-tracked caller
    let nested_tc_out = run_gdrs_source(
        "round17_track_caller_nested",
        "use std::core::Option\n#[track_caller]\nfn inner_unwrap(o: Option<i64>) -> i64:\n\treturn o.unwrap()\n#[track_caller]\nfn outer_helper(o: Option<i64>) -> i64:\n\treturn inner_unwrap(o)\nfn main():\n\tlet opt: Option<i64> = Option::None\n\tlet x = outer_helper(opt)\n\tlog!(\"{}\", x)\n",
    );
    assert_eq!(nested_tc_out.status.code(), Some(101));
    let nested_stderr = String::from_utf8_lossy(&nested_tc_out.stderr);
    assert!(
        nested_stderr.contains("round17_track_caller_nested.gdrs:10:")
            && nested_stderr.contains("called `Option::unwrap()` on a `None` value"),
        "Expected nested #[track_caller] to blame main line 10, got:\n{nested_stderr}"
    );
}

#[test]
fn round18_braced_declarations() {
    // 1. Single-line and multi-line braced functions, structs, enums, and impls
    assert_ok_output(
        "round18_braced_items",
        r#"
obj Point {
	x: i64,
	y: i64,
}

enum Color {
	Red,
	Green,
	Blue,
}

impl Point {
	fn new(x: i64, y: i64) -> Point {
		return Point{ x: x, y: y }
	}

	fn sum(&self) -> i64 {
		return self.x + self.y
	}
}

fn add_coords(p: &Point) -> i64 {
	return p.sum()
}

fn main() {
	let pt = Point::new(10, 25)
	log!("pt: {} {}", pt.x, pt.y)
	log!("sum: {}", add_coords(&pt))

	let c = Color::Green
	match c:
		Color::Red => log!("red")
		Color::Green => log!("green")
		Color::Blue => log!("blue")
}
"#,
        &["pt: 10 25", "sum: 35", "green"],
    );

    // 2. Inline single-line definitions
    assert_ok_output(
        "round18_single_line_braced",
        r#"
obj BoxedVal { val: i64 }

enum Action { Start, Stop }

impl BoxedVal {
	fn get_val(&self) -> i64 { return self.val }
}

fn compute(x: i64) -> i64 { return x * 2 }

fn main():
	let b = BoxedVal{ val: 21 }
	log!("boxed: {}", b.get_val())
	log!("computed: {}", compute(b.get_val()))
"#,
        &["boxed: 21", "computed: 42"],
    );

    // 3. Negative check: control-flow statements like `if` or `while` MUST NOT accept `{}`
    assert_err_code(
        "round18_disallow_braced_if",
        r#"
fn main():
	if true {
		log!("should fail")
	}
"#,
        "Parse error",
    );
}

#[test]
fn round19_unsigned_numbers_and_rand() {
    // 1. Numeric underscores, scientific notation, and unsigned arithmetic/shifts/modulo
    assert_ok_output(
        "round19_unsigned_and_literals",
        r#"
fn main() {
	let million = 1_000_000
	let hex_val = 0xdead_beef
	let sci_float = 2.5e3
	let small_sci = 1.0e-3
	log!("million: {}", million)
	log!("hex: {}", hex_val)
	log!("sci: {}", sci_float)
	log!("small: {}", small_sci)

	// Unsigned logical right shift vs signed arithmetic shift
	let u_max: u64 = 0x8000_0000_0000_0000
	let u_shifted = u_max >> 1
	log!("u_shifted: {}", u_shifted)

	// Unsigned comparison: 0xFF... is larger than 10
	let u_all_ones: u64 = 0xffff_ffff_ffff_ffff
	if u_all_ones > 10:
		log!("unsigned gt ok")

	// Unsigned modulo: 18446744073709551615 % 10 = 5
	let u_mod = u_all_ones % 10
	log!("u_mod: {}", u_mod)

	// u32 and u8
	let byte_val: u8 = 250
	let b_add = byte_val + 5
	log!("byte: {}", b_add)
}
"#,
        &[
            "million: 1000000",
            "hex: 3735928559",
            "sci: 2500",
            "small: 0.001",
            "u_shifted: 4611686018427387904",
            "unsigned gt ok",
            "u_mod: 5",
            "byte: 255",
        ],
    );

    // 2. Full std::rand::Rng test with SplitMix64 deterministic seed and time-based seed
    assert_ok_output(
        "round19_std_rand_test",
        r#"
use std::rand::Rng

fn main() {
	let mut rng = Rng::from_seed(42)
	let r1 = rng.next_u64()
	let r2 = rng.next_u64()
	log!("seed42 r1: {}", r1)
	log!("seed42 r2: {}", r2)

	let f = rng.next_f64()
	if f >= 0.0 && f < 1.0:
		log!("f64 in range: ok")

	let ri = rng.range_i64(10, 20)
	if ri >= 10 && ri <= 20:
		log!("range_i64: ok")

	let rf = rng.range_f64(10.0, 50.0)
	if rf >= 10.0 && rf <= 50.0:
		log!("range_f64: ok")

	let mut live_rng = Rng::new()
	let lr = live_rng.next_u64()
	let lf = live_rng.next_f64()
	if lf >= 0.0 && lf < 1.0:
		log!("live rng: ok")
}
"#,
        &[
            "seed42 r1: 13679457532755275413",
            "seed42 r2: 2949826092126892291",
            "f64 in range: ok",
            "range_i64: ok",
            "range_f64: ok",
            "live rng: ok",
        ],
    );
}

#[test]
fn round20_partial_eq_and_eq() {
    assert_ok_output(
        "round20_partial_eq_pos",
        r#"
use std::core::{PartialEq, Eq}
use std::string::String

#[derive(PartialEq, Eq)]
obj Point:
	x: i64
	y: i64

#[derive(PartialEq, Eq)]
enum Color:
	Red
	Rgb(i64, i64, i64)

obj Tag:
	name: String

impl PartialEq for Tag:
	fn eq(&self, other: &Tag) -> bool:
		return self.name == other.name

fn same_eq(a: $T, b: $T) -> bool where $T: Eq:
	return a == b

fn same_peq(a: $T, b: $T) -> bool where $T: PartialEq:
	return a == b

fn main():
	let p1 = Point{ x: 1, y: 2 }
	let p2 = Point{ x: 1, y: 2 }
	let p3 = Point{ x: 3, y: 4 }
	log!("p1==p2: {}", p1 == p2)
	log!("p1!=p3: {}", p1 != p3)
	// Verify p1 and p2 were borrowed, not moved
	log!("p1.x: {}", p1.x)
	log!("p2.y: {}", p2.y)

	let t1 = Tag{ name: String::from("alpha") }
	let t2 = Tag{ name: String::from("alpha") }
	let t3 = Tag{ name: String::from("beta") }
	log!("t1==t2: {}", t1 == t2)
	log!("t1!=t3: {}", t1 != t3)
	log!("t1: {}", t1.name.as_str())

	let c1 = Color::Rgb(10, 20, 30)
	let c2 = Color::Rgb(10, 20, 30)
	log!("c1==c2: {}", c1 == c2)

	log!("same_eq int: {}", same_eq(5, 5))
	log!("same_peq float: {}", same_peq(1.5, 1.5))
"#,
        &[
            "p1==p2: true",
            "p1!=p3: true",
            "p1.x: 1",
            "p2.y: 2",
            "t1==t2: true",
            "t1!=t3: true",
            "t1: alpha",
            "c1==c2: true",
            "same_eq int: true",
            "same_peq float: true",
        ],
    );

    assert_err_code(
        "round20_missing_partial_eq",
        r#"
obj NoEq:
	x: i64

fn main():
	let a = NoEq{ x: 1 }
	let b = NoEq{ x: 1 }
	log!("{}", a == b)
"#,
        "E0369",
    );

    assert_err_code(
        "round20_float_not_eq",
        r#"
use std::core::Eq

fn need_eq(a: $T, b: $T) -> bool where $T: Eq:
	return a == b

fn main():
	log!("{}", need_eq(1.0, 1.0))
"#,
        "E0277",
    );
}

#[test]
fn round21_visibility_and_pub() {
    // 1. Private struct field access on std::vec::Vec -> E0616
    assert_err_code(
        "round21_private_vec_field",
        r#"
use std::vec::Vec

fn main():
	let mut v: Vec<i64> = Vec::new()
	v.push(1)
	log!("{}", v.cap)
"#,
        "E0616",
    );

    // 2. Direct struct literal construction with private fields -> E0603
    assert_err_code(
        "round21_private_struct_literal",
        r#"
use std::vec::Vec

fn main():
	let v: Vec<i64> = Vec{ ptr: 0 as *u8, len: 0, cap: 0 }
"#,
        "E0603",
    );

    // 3. pub(crate) in std is not callable from user crate -> E0603
    assert_err_code(
        "round21_pub_crate_std_blocked",
        r#"
use std::string::String

fn main():
	let s = String::from_raw_parts(0 as *i64, 0, 0)
"#,
        "E0603",
    );

    // 4. Multi-file module visibility: pub works, private method -> E0624, private fn -> E0603
    let tmp_dir = std::env::temp_dir().join(format!("gdrs_vis_test_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp_dir);
    std::fs::create_dir_all(&tmp_dir).unwrap();

    let mod_file = tmp_dir.join("encap.gdrs");
    std::fs::write(
        &mod_file,
        r#"
pub obj Counter:
	pub label: str
	count: i64

impl Counter:
	pub fn new(label: str) -> Counter:
		return Counter{ label: label, count: 0 }

	pub fn inc(&mut self):
		self.bump()

	fn bump(&mut self):
		self.count = self.count + 1

	pub fn value(&self) -> i64:
		return self.count

fn secret_helper() -> i64:
	return 42

pub fn public_helper() -> i64:
	return 42
"#,
    )
    .unwrap();

    let ok_main = tmp_dir.join("main_ok.gdrs");
    std::fs::write(
        &ok_main,
        r#"
use encap::{Counter, public_helper}

fn main():
	let mut c = Counter::new("hits")
	c.inc()
	c.inc()
	log!("{} {} {}", c.label, c.value(), public_helper())
"#,
    )
    .unwrap();

    let ok_out = std::process::Command::new(env!("CARGO_BIN_EXE_gdrs"))
        .arg("run")
        .arg(&ok_main)
        .output()
        .expect("Failed to run gdrs");
    assert!(
        ok_out.status.success(),
        "Expected multi-module visibility test to succeed, got:\n{}\n{}",
        String::from_utf8_lossy(&ok_out.stdout),
        String::from_utf8_lossy(&ok_out.stderr)
    );
    let stdout = String::from_utf8_lossy(&ok_out.stdout);
    assert!(stdout.contains("hits 2 42"), "Unexpected stdout: {stdout}");

    let err_method = tmp_dir.join("main_err_method.gdrs");
    std::fs::write(
        &err_method,
        r#"
use encap::Counter

fn main():
	let mut c = Counter::new("hits")
	c.bump()
"#,
    )
    .unwrap();
    let method_out = std::process::Command::new(env!("CARGO_BIN_EXE_gdrs"))
        .arg("run")
        .arg(&err_method)
        .output()
        .expect("Failed to run gdrs");
    assert!(!method_out.status.success());
    let method_combined = format!(
        "{}{}",
        String::from_utf8_lossy(&method_out.stdout),
        String::from_utf8_lossy(&method_out.stderr)
    );
    assert!(
        method_combined.contains("E0624"),
        "Expected E0624, got:\n{method_combined}"
    );

    let err_import = tmp_dir.join("main_err_import.gdrs");
    std::fs::write(
        &err_import,
        r#"
use encap::secret_helper

fn main():
	log!("{}", secret_helper())
"#,
    )
    .unwrap();
    let import_out = std::process::Command::new(env!("CARGO_BIN_EXE_gdrs"))
        .arg("run")
        .arg(&err_import)
        .output()
        .expect("Failed to run gdrs");
    assert!(!import_out.status.success());
    let import_combined = format!(
        "{}{}",
        String::from_utf8_lossy(&import_out.stdout),
        String::from_utf8_lossy(&import_out.stderr)
    );
    assert!(
        import_combined.contains("E0603"),
        "Expected E0603, got:\n{import_combined}"
    );

    let _ = std::fs::remove_dir_all(&tmp_dir);
}
