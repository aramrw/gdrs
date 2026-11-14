use chumsky::Parser;
use gdrs::ast::*;
use gdrs::loader::inject_indentation;
use gdrs::parser::parser;
use gdrs::sanal::macros::parse_format_string;
use gdrs::{check_source_in_memory, codegen};
use logos::Logos;
use std::collections::HashMap;
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// Deterministic PRNG (SplitMix64) + Test-Case Delta Shrinker
// ============================================================================

#[derive(Clone)]
struct Rng {
    state: u64,
}

impl Rng {
    fn from_env_or_default() -> (Self, u64) {
        let seed = std::env::var("GDRS_FUZZ_SEED")
            .ok()
            .and_then(|raw| {
                let s = raw.trim();
                if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
                    u64::from_str_radix(hex, 16).ok()
                } else {
                    s.parse::<u64>().ok()
                }
            })
            .unwrap_or(0x5EED_CAFE_2026_0001);
        (Self { state: seed }, seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn gen_range(&mut self, upper: usize) -> usize {
        if upper == 0 {
            return 0;
        }
        (self.next_u64() % (upper as u64)) as usize
    }

    fn gen_bool(&mut self, num: usize, den: usize) -> bool {
        self.gen_range(den) < num
    }

    fn choose<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        let idx = self.gen_range(items.len());
        &items[idx]
    }
}

fn shrink_lines(source: &str, pred: &dyn Fn(&str) -> bool) -> String {
    let mut lines: Vec<&str> = source.lines().collect();
    if lines.len() <= 1 {
        return source.to_string();
    }

    let mut chunk = lines.len() / 2;
    let mut budget = 0usize;
    while chunk >= 1 && budget < 300 {
        let mut i = 0;
        while i < lines.len() && budget < 300 {
            let end = (i + chunk).min(lines.len());
            let mut candidate_lines = Vec::with_capacity(lines.len() - (end - i));
            candidate_lines.extend_from_slice(&lines[..i]);
            candidate_lines.extend_from_slice(&lines[end..]);
            let candidate = candidate_lines.join("\n");
            budget += 1;
            if !candidate.is_empty() && pred(&candidate) {
                lines = candidate_lines;
                if i >= lines.len() {
                    break;
                }
            } else {
                i += chunk;
            }
        }
        chunk /= 2;
    }
    lines.join("\n")
}

// ============================================================================
// AST Structural Equality (Ignoring Byte Spans) for Dual-Syntax Equivalence
// ============================================================================

fn params_eq(a: &[Param], b: &[Param]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|(x, y)| x.name == y.name && x.is_mutable == y.is_mutable && x.ty == y.ty)
}

fn tuple_pat_eq(a: &TuplePattern, b: &TuplePattern) -> bool {
    match (a, b) {
        (
            TuplePattern::Ident {
                name: n1,
                is_mutable: m1,
                ..
            },
            TuplePattern::Ident {
                name: n2,
                is_mutable: m2,
                ..
            },
        ) => n1 == n2 && m1 == m2,
        (TuplePattern::Tuple(v1, _), TuplePattern::Tuple(v2, _)) => {
            v1.len() == v2.len() && v1.iter().zip(v2.iter()).all(|(x, y)| tuple_pat_eq(x, y))
        }
        _ => false,
    }
}

fn expr_eq(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Int(x, _), Expr::Int(y, _)) => x == y,
        (Expr::Float(x, _), Expr::Float(y, _)) => x.to_bits() == y.to_bits(),
        (Expr::Ident(x, _), Expr::Ident(y, _)) => x == y,
        (Expr::Bool(x, _), Expr::Bool(y, _)) => x == y,
        (Expr::String(x, _), Expr::String(y, _)) => x == y,
        (Expr::Add(l1, r1, _), Expr::Add(l2, r2, _))
        | (Expr::Sub(l1, r1, _), Expr::Sub(l2, r2, _))
        | (Expr::Mul(l1, r1, _), Expr::Mul(l2, r2, _))
        | (Expr::Div(l1, r1, _), Expr::Div(l2, r2, _))
        | (Expr::Mod(l1, r1, _), Expr::Mod(l2, r2, _))
        | (Expr::GreaterThan(l1, r1, _), Expr::GreaterThan(l2, r2, _))
        | (Expr::LessThan(l1, r1, _), Expr::LessThan(l2, r2, _))
        | (Expr::GreaterEqual(l1, r1, _), Expr::GreaterEqual(l2, r2, _))
        | (Expr::LessEqual(l1, r1, _), Expr::LessEqual(l2, r2, _))
        | (Expr::Equal(l1, r1, _), Expr::Equal(l2, r2, _))
        | (Expr::NotEqual(l1, r1, _), Expr::NotEqual(l2, r2, _))
        | (Expr::And(l1, r1, _), Expr::And(l2, r2, _))
        | (Expr::Or(l1, r1, _), Expr::Or(l2, r2, _))
        | (Expr::While(l1, r1, _), Expr::While(l2, r2, _))
        | (Expr::If(l1, r1, _), Expr::If(l2, r2, _))
        | (Expr::IndexAccess(l1, r1, _), Expr::IndexAccess(l2, r2, _))
        | (Expr::Pipe(l1, r1, _), Expr::Pipe(l2, r2, _))
        | (Expr::Ampersand(l1, r1, _), Expr::Ampersand(l2, r2, _))
        | (Expr::Caret(l1, r1, _), Expr::Caret(l2, r2, _))
        | (Expr::Shl(l1, r1, _), Expr::Shl(l2, r2, _))
        | (Expr::Shr(l1, r1, _), Expr::Shr(l2, r2, _))
        | (Expr::DerefAssign(l1, r1, _), Expr::DerefAssign(l2, r2, _))
        | (Expr::Range(l1, r1, _), Expr::Range(l2, r2, _)) => expr_eq(l1, l2) && expr_eq(r1, r2),
        (Expr::Neg(x, _), Expr::Neg(y, _))
        | (Expr::Not(x, _), Expr::Not(y, _))
        | (Expr::Try(x, _), Expr::Try(y, _))
        | (Expr::Deref(x, _), Expr::Deref(y, _)) => expr_eq(x, y),
        (Expr::Ref(x, m1, _), Expr::Ref(y, m2, _)) => m1 == m2 && expr_eq(x, y),
        (Expr::Cast(x, t1, _), Expr::Cast(y, t2, _)) => t1 == t2 && expr_eq(x, y),
        (Expr::Let(n1, t1, m1, e1, _), Expr::Let(n2, t2, m2, e2, _)) => {
            n1 == n2 && t1 == t2 && m1 == m2 && expr_eq(e1, e2)
        }
        (Expr::LetTuple(p1, t1, e1, _), Expr::LetTuple(p2, t2, e2, _)) => {
            tuple_pat_eq(p1, p2) && t1 == t2 && expr_eq(e1, e2)
        }
        (Expr::Assign(n1, e1, _), Expr::Assign(n2, e2, _)) => n1 == n2 && expr_eq(e1, e2),
        (Expr::CompoundAssign(op1, t1, v1, _), Expr::CompoundAssign(op2, t2, v2, _)) => {
            op1 == op2 && expr_eq(t1, t2) && expr_eq(v1, v2)
        }
        (Expr::IfElse(c1, t1, f1, _), Expr::IfElse(c2, t2, f2, _))
        | (Expr::IndexAssign(c1, t1, f1, _), Expr::IndexAssign(c2, t2, f2, _)) => {
            expr_eq(c1, c2) && expr_eq(t1, t2) && expr_eq(f1, f2)
        }
        (Expr::Return(o1, _), Expr::Return(o2, _)) => match (o1, o2) {
            (Some(x), Some(y)) => expr_eq(x, y),
            (None, None) => true,
            _ => false,
        },
        (Expr::Break(_), Expr::Break(_)) | (Expr::Continue(_), Expr::Continue(_)) => true,
        (Expr::Block(v1, _), Expr::Block(v2, _))
        | (Expr::Unsafe(v1, _), Expr::Unsafe(v2, _))
        | (Expr::ArrayInit(v1, _), Expr::ArrayInit(v2, _))
        | (Expr::TupleInit(v1, _), Expr::TupleInit(v2, _)) => exprs_eq(v1, v2),
        (Expr::MacroCall(n1, a1, _), Expr::MacroCall(n2, a2, _))
        | (Expr::Call(n1, a1, _), Expr::Call(n2, a2, _)) => n1 == n2 && exprs_eq(a1, a2),
        (Expr::ObjInit(n1, f1, _), Expr::ObjInit(n2, f2, _)) => {
            n1 == n2
                && f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2.iter())
                    .all(|((k1, v1), (k2, v2))| k1 == k2 && expr_eq(v1, v2))
        }
        (Expr::FieldAccess(o1, f1, _), Expr::FieldAccess(o2, f2, _)) => {
            f1 == f2 && expr_eq(o1, o2)
        }
        (Expr::FieldAssign(o1, f1, v1, _), Expr::FieldAssign(o2, f2, v2, _)) => {
            f1 == f2 && expr_eq(o1, o2) && expr_eq(v1, v2)
        }
        (Expr::EnumConstruct(e1, v1, a1, _), Expr::EnumConstruct(e2, v2, a2, _)) => {
            e1 == e2 && v1 == v2 && exprs_eq(a1, a2)
        }
        (Expr::Closure(m1, p1, b1, _), Expr::Closure(m2, p2, b2, _)) => {
            m1 == m2 && p1 == p2 && expr_eq(b1, b2)
        }
        (Expr::Match(t1, arms1, _), Expr::Match(t2, arms2, _)) => {
            expr_eq(t1, t2)
                && arms1.len() == arms2.len()
                && arms1.iter().zip(arms2.iter()).all(|(x, y)| {
                    x.variant_name == y.variant_name
                        && x.bindings == y.bindings
                        && exprs_eq(&x.body, &y.body)
                })
        }
        _ => false,
    }
}

fn exprs_eq(a: &[Expr], b: &[Expr]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| expr_eq(x, y))
}

fn funcs_eq(a: &FuncDecl, b: &FuncDecl) -> bool {
    a.name == b.name
        && params_eq(&a.params, &b.params)
        && a.return_type == b.return_type
        && a.is_track_caller == b.is_track_caller
        && a.vis == b.vis
        && a.is_trait_impl == b.is_trait_impl
        && exprs_eq(&a.body, &b.body)
}

fn programs_eq_ignoring_spans(a: &Program, b: &Program) -> bool {
    let structs_ok = a.structs.len() == b.structs.len()
        && a.structs.iter().zip(b.structs.iter()).all(|(x, y)| {
            x.name == y.name
                && x.vis == y.vis
                && x.fields.len() == y.fields.len()
                && x.fields
                    .iter()
                    .zip(y.fields.iter())
                    .all(|(f1, f2)| f1.name == f2.name && f1.ty == f2.ty && f1.vis == f2.vis)
        });
    let enums_ok = a.enums.len() == b.enums.len()
        && a.enums.iter().zip(b.enums.iter()).all(|(x, y)| {
            x.name == y.name
                && x.vis == y.vis
                && x.variants.len() == y.variants.len()
                && x.variants
                    .iter()
                    .zip(y.variants.iter())
                    .all(|(v1, v2)| v1.name == v2.name && v1.payload_types == v2.payload_types)
        });
    let impls_ok = a.impls.len() == b.impls.len()
        && a.impls.iter().zip(b.impls.iter()).all(|(x, y)| {
            x.trait_name == y.trait_name
                && x.target_type == y.target_type
                && x.methods.len() == y.methods.len()
                && x.methods.iter().zip(y.methods.iter()).all(|(m1, m2)| funcs_eq(m1, m2))
        });
    let funcs_ok = a.functions.len() == b.functions.len()
        && a.functions
            .iter()
            .zip(b.functions.iter())
            .all(|(x, y)| funcs_eq(x, y));
    structs_ok && enums_ok && impls_ok && funcs_ok
}

fn parse_raw_ast(src: &str) -> Result<Program, String> {
    let raw_tokens: Vec<(Token, Span)> = Token::lexer(src)
        .spanned()
        .filter_map(|(res, span)| res.ok().map(|tok| (tok, span)))
        .collect();
    let processed = inject_indentation(raw_tokens);
    let eof_span = src.len()..src.len();
    let stream = chumsky::Stream::from_iter(eof_span, processed.into_iter());
    parser()
        .parse(stream)
        .map_err(|errs| format!("Parse errors: {:?}", errs))
}

// ============================================================================
// Tier 1: Lexer, Indentation, Format String, Parser & Dual-Syntax Equivalence
// ============================================================================

#[test]
fn fuzz_tier1_lexer_parser_and_dual_syntax() {
    let (mut rng, seed) = Rng::from_env_or_default();

    // 1A. Boundary & random lexer/parser robustness
    let mut boundary_inputs: Vec<String> = vec![
        "".to_string(),
        "\n\t\r\n   \t\t\n".to_string(),
        "\"unterminated string\\".to_string(),
        "\"\\\\\\\"".to_string(),
        "(".repeat(64),
        "[".repeat(64),
        "{".repeat(64),
        ":".repeat(32),
        "99999999999999999999999999999999999999999".to_string(),
        "0xffffffffffffffffffffffffffffffff".to_string(),
        "1e99999999999".to_string(),
        "0.0000000000000000000000000000000001e-99999".to_string(),
        "fn main():\n\t\t\t\tlet x = 1..2..3\n".to_string(),
        "fn (a, b,): -> :: => #[derive()]\n\t\x00🦀\u{202e}".to_string(),
        "log!(\"{}{}{:?}{:#?}{{}}\", a, b)".to_string(),
        "match x:\n\tOption::Some(y) => return y\n\t_ => break\n".to_string(),
    ];

    let tok_alphabet = [
        "fn", "obj", "enum", "impl", "trait", "let", "mut", "if", "else", "while", "for", "in",
        "match", "return", "break", "continue", "unsafe", "dyn", "as", "use", "pub", "true",
        "false", "i64", "u8", "f32", "bool", "str", "Box", "Rc", "Vec", ":", "::", "->", "=>",
        "=", "==", "!=", "<", ">", "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "..", "(",
        ")", "[", "]", "{", "}", ",", ".", "\"hi\"", "\"{:?}\"", "42", "3.14", "log!", "panic!",
        "x", "_", "#[derive(Debug)]", "\n", "\t", " ", "// comment\n",
    ];

    for i in 0..1200 {
        if i % 3 == 0 {
            let mut s = String::new();
            let count = 1 + rng.gen_range(40);
            for _ in 0..count {
                s.push_str(rng.choose(&tok_alphabet));
                if rng.gen_bool(2, 3) {
                    s.push(' ');
                }
            }
            boundary_inputs.push(s);
        } else {
            let len = rng.gen_range(160);
            let mut bytes = Vec::with_capacity(len);
            for _ in 0..len {
                let b = match rng.gen_range(6) {
                    0 => b'\n',
                    1 => b'\t',
                    2 => *rng.choose(&[b'(', b')', b'[', b']', b'{', b'}', b':', b'"', b'\\']),
                    3 => *rng.choose(&[b'+', b'-', b'*', b'&', b'|', b'<', b'>', b'=', b'.', b',']),
                    4 => b'a' + (rng.gen_range(26) as u8),
                    _ => (rng.next_u64() & 0xff) as u8,
                };
                bytes.push(b);
            }
            boundary_inputs.push(String::from_utf8_lossy(&bytes).into_owned());
        }
    }

    for (idx, src) in boundary_inputs.iter().enumerate() {
        let res = catch_unwind(AssertUnwindSafe(|| parse_raw_ast(src)));
        if let Err(_) = res {
            let shrunk = shrink_lines(src, &|cand| {
                catch_unwind(AssertUnwindSafe(|| parse_raw_ast(cand))).is_err()
            });
            panic!(
                "Tier 1 parser panic at case {idx}!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier1\nShrunk input:\n{shrunk:?}"
            );
        }
    }

    // 1B. parse_format_string fuzzing
    let fmt_alphabet = [
        "{", "}", ":", "#", "?", "!", "\\", "0", "1", "a", "\n", "\0", " ", "{:?}", "{:#?}",
        "{}", "{{", "}}", "🦀",
    ];
    for i in 0..1000 {
        let mut s = String::new();
        let pieces = rng.gen_range(16);
        for _ in 0..pieces {
            s.push_str(rng.choose(&fmt_alphabet));
        }
        let is_raw = i % 2 == 0;
        let span = 0..s.len();
        let res = catch_unwind(AssertUnwindSafe(|| parse_format_string(&s, is_raw, &span)));
        assert!(
            res.is_ok(),
            "Tier 1 parse_format_string panicked!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier1\nis_raw={is_raw} input={s:?}"
        );
    }

    // 1C. Dual-syntax AST equivalence (Pythonic colon blocks vs braced blocks)
    for iter in 0..250 {
        let field_count = 1 + rng.gen_range(3);
        let var_count = 1 + rng.gen_range(3);
        let op = *rng.choose(&["+", "-", "*", "&", "|", "^"]);
        let use_else = rng.gen_bool(1, 2);
        let use_while = rng.gen_bool(1, 2);

        let mut py_src = String::new();
        let mut rs_src = String::new();

        // Struct
        py_src.push_str("obj Pair:\n");
        rs_src.push_str("obj Pair {\n");
        for f in 0..field_count {
            let ty = *rng.choose(&["i64", "u32", "bool"]);
            py_src.push_str(&format!("\tf{f}: {ty}\n"));
            rs_src.push_str(&format!("\tf{f}: {ty},\n"));
        }
        rs_src.push_str("}\n");

        // Enum
        py_src.push_str("enum Mode:\n\tOne(i64)\n\tTwo\n");
        rs_src.push_str("enum Mode {\n\tOne(i64),\n\tTwo,\n}\n");

        // Helper fn
        py_src.push_str("fn compute(x: i64, y: i64) -> i64:\n");
        rs_src.push_str("fn compute(x: i64, y: i64) -> i64 {\n");

        py_src.push_str(&format!("\tlet mut acc: i64 = x {op} y\n"));
        rs_src.push_str(&format!("\tlet mut acc: i64 = x {op} y\n"));

        for v in 0..var_count {
            let c = (rng.gen_range(20) as i64) + 1;
            py_src.push_str(&format!("\tlet v{v}: i64 = acc + {c}\n"));
            rs_src.push_str(&format!("\tlet v{v}: i64 = acc + {c}\n"));
        }

        if use_while {
            py_src.push_str("\tlet mut k: i64 = 0\n\twhile k < 3:\n\t\tk += 1\n\t\tacc += k\n");
            rs_src.push_str("\tlet mut k: i64 = 0\n\twhile k < 3: {\n\t\tk += 1\n\t\tacc += k\n\t}\n");
        }

        if use_else {
            py_src.push_str("\tif acc > 10:\n\t\treturn acc\n\telse:\n\t\treturn acc + 1\n");
            rs_src.push_str("\tif acc > 10: {\n\t\treturn acc\n\t} else: {\n\t\treturn acc + 1\n\t}\n");
        } else {
            py_src.push_str("\tif acc > 10:\n\t\treturn acc\n\treturn 0\n");
            rs_src.push_str("\tif acc > 10: {\n\t\treturn acc\n\t}\n\treturn 0\n");
        }
        rs_src.push_str("}\n");

        let py_ast = parse_raw_ast(&py_src)
            .unwrap_or_else(|e| panic!("Colon syntax parse failed on iter {iter}: {e}\n{py_src}"));
        let rs_ast = parse_raw_ast(&rs_src)
            .unwrap_or_else(|e| panic!("Braced syntax parse failed on iter {iter}: {e}\n{rs_src}"));

        assert!(
            programs_eq_ignoring_spans(&py_ast, &rs_ast),
            "Dual-syntax AST mismatch on iter {iter} (GDRS_FUZZ_SEED=0x{seed:016x})!\n--- COLON ---\n{py_src}\n--- BRACED ---\n{rs_src}"
        );
    }
}

// ============================================================================
// Tier 2: Structure-Aware Corpus Mutation + Soundness Gate (Cranelift Verifier)
// ============================================================================

fn tier2_seed_corpus() -> Vec<&'static str> {
    vec![
        // 1. Moves, partial moves, re-init
        r#"
use std::string::String
#[derive(Debug)]
obj Pair:
	a: String
	b: i64
fn main():
	let mut p = Pair{ a: String::from("hi"), b: 1 }
	let s = p.a.clone()
	p.a = String::from("new")
	log!("{:?} {}", p, s)
"#,
        // 2. Mutable borrow & deref assignment
        r#"
fn bump(x: &mut i64, d: i64):
	*x += d
fn main():
	let mut v: i64 = 10
	{
		let r: &mut i64 = &mut v
		bump(r, 5)
	}
	log!("{}", v)
"#,
        // 3. Diverging match arms + early return
        r#"
#[derive(Debug, PartialEq)]
enum Msg:
	Quit
	Val(i64)
fn eval(m: Msg) -> i64:
	match m:
		Msg::Quit => return 0
		Msg::Val(n) => return n * 2
fn main():
	let x = eval(Msg::Val(21))
	log!("{}", x)
"#,
        // 4. Recursive Box<List> + Debug + Drop
        r#"
use std::boxed::Box
use std::core::Drop
#[derive(Debug)]
obj T:
	id: i64
impl Drop for T:
	fn drop(mut self):
		let _ = self.id
#[derive(Debug)]
enum List:
	Cons(T, Box<List>)
	Nil
fn main():
	let xs = List::Cons(T{ id: 1 }, Box::new(List::Cons(T{ id: 2 }, Box::new(List::Nil))))
	log!("{:?}", xs)
"#,
        // 5. Rc and Arc sharing + strong_count
        r#"
use std::rc::Rc
use std::sync::Arc
fn main():
	let r1: Rc<i64> = Rc::new(7)
	let r2 = Rc::clone(&r1)
	let a1: Arc<i64> = Arc::new(9)
	let a2 = Arc::clone(&a1)
	log!("{} {} {} {}", *r2, Rc::strong_count(&r1), *a2, Arc::strong_count(&a1))
"#,
        // 6. Slices & range expressions
        r#"
use std::vec::Vec
fn sum_slice(s: &[i64]) -> i64:
	let mut acc: i64 = 0
	for x in s:
		acc += x
	return acc
fn main():
	let mut arr: [i64; 5] = [1, 2, 3, 4, 5]
	let s1: &[i64] = &arr[1..4]
	let s2: &[i64] = &arr[..2]
	let mut v: Vec<i64> = vec![10, 20, 30]
	{
		let ms: &mut [i64] = &mut v[0..2]
		ms[0] = 99
	}
	log!("{} {} {}", sum_slice(s1), s2.len(), v[0])
"#,
        // 7. Function pointers + thin closures
        r#"
fn apply(f: fn(i64, i64) -> i64, a: i64, b: i64) -> i64:
	return f(a, b)
fn add(a: i64, b: i64) -> i64:
	return a + b
fn main():
	let f: fn(i64, i64) -> i64 = |x, y| x * y + 1
	log!("{} {}", apply(add, 3, 4), apply(f, 3, 4))
"#,
        // 8. Try operator (?) with Result & Option
        r#"
use std::string::String
fn may_fail(flag: bool) -> Result<i64, String>:
	if flag:
		return Result::Ok(42)
	return Result::Err(String::from("bad"))
fn caller(flag: bool) -> Result<i64, String>:
	let s = String::from("live_before_try")
	let v = may_fail(flag)?
	log!("{}", s)
	return Result::Ok(v + 1)
fn main():
	let r1 = caller(true)
	let r2 = caller(false)
	log!("{:?} {:?}", r1, r2)
"#,
        // 9. Unsigned types, shifts, bitwise ops, float casts
        r#"
fn main():
	let a: u8 = 200
	let b: u8 = 100
	let c: u64 = ((a as u64) << 4) | (b as u64)
	let f: f32 = 3.5 as f32
	let d: f64 = f as f64 + 1.25
	log!("{} {}", c, d)
"#,
        // 10. Nested loops with break / continue / drops
        r#"
use std::string::String
fn main():
	let mut i: i64 = 0
	let mut total: i64 = 0
	while i < 5:
		i += 1
		let s = String::from("iter")
		if i == 2:
			continue
		if i == 4:
			log!("{}", s)
			break
		total += i
	log!("{}", total)
"#,
        // 11. Traits & dyn Trait
        r#"
trait Greeter:
	fn greet(&self) -> i64
obj Bot:
	code: i64
impl Greeter for Bot:
	fn greet(&self) -> i64:
		return self.code * 10
fn run_greet(g: &dyn Greeter) -> i64:
	return g.greet()
fn main():
	let b = Bot{ code: 4 }
	log!("{}", run_greet(&b))
"#,
        // 12. Multi-field tuples & destructuring
        r#"
use std::string::String
fn mk() -> (i64, (bool, String)):
	return (7, (true, String::from("ok")))
fn main():
	let (n, (flag, msg)) = mk()
	log!("{} {} {}", n, flag, msg)
"#,
        // 13. Unsafe block & raw pointers
        r#"
fn main():
	let mut x: i64 = 10
	unsafe:
		let p: *i64 = (&mut x) as *i64
		*p = 77
	log!("{}", x)
"#,
        // 14. Box Deref coercion + Struct Debug alt format
        r#"
use std::boxed::Box
#[derive(Debug, PartialEq)]
obj Item:
	id: i64
	name: str
fn inspect(it: &Item) -> i64:
	return it.id
fn main():
	let b = Box::new(Item{ id: 12, name: "apple" })
	let s = format!("{:#?}", b)
	log!("{} {}", inspect(&b), s)
"#,
    ]
}

fn mutate_program(rng: &mut Rng, base: &str) -> String {
    let mut lines: Vec<String> = base.lines().map(|l| l.to_string()).collect();
    if lines.is_empty() {
        return base.to_string();
    }

    let num_mutations = 1 + rng.gen_range(3);
    for _ in 0..num_mutations {
        let mut_kind = rng.gen_range(9);
        match mut_kind {
            0 => {
                // Duplicate a random line (triggers double-move, double-mut-borrow, etc.)
                let idx = rng.gen_range(lines.len());
                let line = lines[idx].clone();
                if !line.trim().is_empty() && !line.starts_with("use ") {
                    lines.insert(idx, line);
                }
            }
            1 => {
                // Delete a random non-import body line
                if lines.len() > 3 {
                    let idx = rng.gen_range(lines.len());
                    if !lines[idx].contains("fn main") && !lines[idx].starts_with("use ") {
                        lines.remove(idx);
                    }
                }
            }
            2 => {
                // Inject early return / break / continue preserving indentation
                let idx = rng.gen_range(lines.len());
                let indent: String = lines[idx].chars().take_while(|c| *c == '\t').collect();
                if !indent.is_empty() {
                    let stmt = *rng.choose(&[
                        "return",
                        "return 0",
                        "break",
                        "continue",
                        "panic!(\"fuzz\")",
                    ]);
                    lines.insert(idx, format!("{indent}{stmt}"));
                }
            }
            3 => {
                // Swap &mut <-> & or *deref
                let idx = rng.gen_range(lines.len());
                if lines[idx].contains("&mut ") {
                    lines[idx] = lines[idx].replacen("&mut ", "&", 1);
                } else if lines[idx].contains('&') {
                    lines[idx] = lines[idx].replacen('&', "&mut ", 1);
                } else if lines[idx].contains('*') {
                    lines[idx] = lines[idx].replacen('*', "", 1);
                }
            }
            4 => {
                // Mutate types across numeric / heap boundaries
                let idx = rng.gen_range(lines.len());
                let from = *rng.choose(&["i64", "u8", "u64", "f32", "f64", "bool", "String"]);
                let to = *rng.choose(&["i64", "u8", "u64", "f32", "f64", "bool", "String", "Box<i64>"]);
                if lines[idx].contains(from) {
                    lines[idx] = lines[idx].replacen(from, to, 1);
                }
            }
            5 => {
                // Mutate binary operators
                let idx = rng.gen_range(lines.len());
                let from = *rng.choose(&[" + ", " - ", " * ", " == ", " != ", " < ", " > ", " << ", " | "]);
                let to = *rng.choose(&[" + ", " - ", " * ", " / ", " % ", " == ", " != ", " < ", " << ", " >> ", " ^ "]);
                if lines[idx].contains(from) {
                    lines[idx] = lines[idx].replacen(from, to, 1);
                }
            }
            6 => {
                // Mutate slice ranges
                let idx = rng.gen_range(lines.len());
                let from = *rng.choose(&["1..4", "..2", "0..2", ".."]);
                let to = *rng.choose(&["0..1", "..", "2..", "..0", "10..20"]);
                if lines[idx].contains(from) {
                    lines[idx] = lines[idx].replacen(from, to, 1);
                }
            }
            7 => {
                // Mutate format specifiers
                let idx = rng.gen_range(lines.len());
                let from = *rng.choose(&["{}", "{:?}", "{:#?}"]);
                let to = *rng.choose(&["{}", "{:?}", "{:#?}", "{unknown}"]);
                if lines[idx].contains(from) {
                    lines[idx] = lines[idx].replacen(from, to, 1);
                }
            }
            _ => {
                // Wrap expression or inject std::mem::drop on a variable
                let idx = rng.gen_range(lines.len());
                let trimmed = lines[idx].trim();
                if let Some(rest) = trimmed.strip_prefix("let ") {
                    let var_name = rest
                        .strip_prefix("mut ")
                        .unwrap_or(rest)
                        .split(|c: char| !c.is_alphanumeric() && c != '_')
                        .next()
                        .unwrap_or("");
                    if !var_name.is_empty() && idx + 1 < lines.len() {
                        let indent: String =
                            lines[idx].chars().take_while(|c| *c == '\t').collect();
                        lines.insert(idx + 1, format!("{indent}std::mem::drop({var_name})"));
                    }
                }
            }
        }
    }

    lines.join("\n")
}

fn check_no_panic_and_soundness_gate(src: &str, label: &str, seed: u64) {
    let sanal_res = catch_unwind(AssertUnwindSafe(|| check_source_in_memory(src)));
    match sanal_res {
        Err(_) => {
            let shrunk = shrink_lines(src, &|cand| {
                catch_unwind(AssertUnwindSafe(|| check_source_in_memory(cand))).is_err()
            });
            panic!(
                "ICE / Panic in loader or sanal ({label})!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests\nShrunk source:\n{shrunk}"
            );
        }
        Ok(Err(_)) => {
            // Expected semantic/parse rejection of an invalid mutant.
        }
        Ok(Ok((typed_prog, struct_layouts, source_map))) => {
            // THE SOUNDNESS GATE:
            // Anything accepted by sanal MUST lower to valid verified Cranelift IR and object bytes!
            let cg_res = catch_unwind(AssertUnwindSafe(|| {
                codegen::object::compile_program_to_object_bytes(
                    &typed_prog,
                    &struct_layouts,
                    &source_map,
                )
            }));
            match cg_res {
                Err(_) => {
                    let shrunk = shrink_lines(src, &|cand| match check_source_in_memory(cand) {
                        Ok((tp, sl, sm)) => catch_unwind(AssertUnwindSafe(|| {
                            codegen::object::compile_program_to_object_bytes(&tp, &sl, &sm)
                        }))
                        .is_err(),
                        Err(_) => false,
                    });
                    panic!(
                        "SOUNDNESS GATE FAILURE: codegen panicked or Cranelift verifier failed on sanal-accepted program ({label})!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests\nShrunk source:\n{shrunk}"
                    );
                }
                Ok(Err(e)) => {
                    panic!(
                        "SOUNDNESS GATE FAILURE: codegen returned Err on sanal-accepted program ({label}): {e}\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests\nSource:\n{src}"
                    );
                }
                Ok(Ok(_obj_bytes)) => {}
            }
        }
    }
}

#[test]
fn fuzz_tier2_mutated_corpus_and_soundness_gate() {
    let (mut rng, seed) = Rng::from_env_or_default();
    let corpus = tier2_seed_corpus();

    // Verify all unmutated seeds compile cleanly first
    for (idx, seed_src) in corpus.iter().enumerate() {
        let res = gdrs::compile_source_in_memory(seed_src);
        assert!(
            res.is_ok(),
            "Tier 2 baseline seed #{idx} failed to compile: {:?}",
            res.err()
        );
    }

    // Mutate across 500 iterations
    for iter in 0..500 {
        let base = rng.choose(&corpus);
        let mutated = mutate_program(&mut rng, base);
        let label = format!("tier2 iter={iter}");
        check_no_panic_and_soundness_gate(&mutated, &label, seed);
    }
}

// ============================================================================
// Tier 3 & Tier 4: GdrsSmith Type-Directed Stateful Program Generator
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum FuzzTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    String,
    SmallPair,
    OwnedWrap,
    DropTracker,
    Choice,
    RecNode,
    Boxed(Box<FuzzTy>),
    Rc(Box<FuzzTy>),
    Arc(Box<FuzzTy>),
    Vec(Box<FuzzTy>),
    Opt(Box<FuzzTy>),
    Res(Box<FuzzTy>),
    Tuple2(Box<FuzzTy>, Box<FuzzTy>),
    Arr4(Box<FuzzTy>),
    FnPtr,
}

impl FuzzTy {
    fn gdrs_name(&self) -> String {
        match self {
            FuzzTy::I8 => "i8".to_string(),
            FuzzTy::I16 => "i16".to_string(),
            FuzzTy::I32 => "i32".to_string(),
            FuzzTy::I64 => "i64".to_string(),
            FuzzTy::U8 => "u8".to_string(),
            FuzzTy::U16 => "u16".to_string(),
            FuzzTy::U32 => "u32".to_string(),
            FuzzTy::U64 => "u64".to_string(),
            FuzzTy::F32 => "f32".to_string(),
            FuzzTy::F64 => "f64".to_string(),
            FuzzTy::Bool => "bool".to_string(),
            FuzzTy::String => "String".to_string(),
            FuzzTy::SmallPair => "SmallPair".to_string(),
            FuzzTy::OwnedWrap => "OwnedWrap".to_string(),
            FuzzTy::DropTracker => "DropTracker".to_string(),
            FuzzTy::Choice => "Choice".to_string(),
            FuzzTy::RecNode => "RecNode".to_string(),
            FuzzTy::Boxed(t) => format!("Box<{}>", t.gdrs_name()),
            FuzzTy::Rc(t) => format!("Rc<{}>", t.gdrs_name()),
            FuzzTy::Arc(t) => format!("Arc<{}>", t.gdrs_name()),
            FuzzTy::Vec(t) => format!("Vec<{}>", t.gdrs_name()),
            FuzzTy::Opt(t) => format!("Option<{}>", t.gdrs_name()),
            FuzzTy::Res(t) => format!("Result<{}, String>", t.gdrs_name()),
            FuzzTy::Tuple2(a, b) => format!("({}, {})", a.gdrs_name(), b.gdrs_name()),
            FuzzTy::Arr4(t) => format!("[{}; 4]", t.gdrs_name()),
            FuzzTy::FnPtr => "fn(i64, i64) -> i64".to_string(),
        }
    }

    fn is_copy(&self) -> bool {
        match self {
            FuzzTy::I8
            | FuzzTy::I16
            | FuzzTy::I32
            | FuzzTy::I64
            | FuzzTy::U8
            | FuzzTy::U16
            | FuzzTy::U32
            | FuzzTy::U64
            | FuzzTy::F32
            | FuzzTy::F64
            | FuzzTy::Bool
            | FuzzTy::FnPtr => true,
            FuzzTy::Tuple2(a, b) => a.is_copy() && b.is_copy(),
            FuzzTy::Arr4(t) => t.is_copy(),
            _ => false,
        }
    }
}

#[derive(Clone)]
struct VarEntry {
    name: String,
    ty: FuzzTy,
    is_mut: bool,
    moved: bool,
}

struct GdrsSmith {
    rng: Rng,
    var_counter: usize,
    tracker_id_counter: usize,
    with_drop_tracker: bool,
    with_alloc_reset: bool,
    body_lines: Vec<String>,
}

impl GdrsSmith {
    fn new(rng: Rng, with_drop_tracker: bool, with_alloc_reset: bool) -> Self {
        Self {
            rng,
            var_counter: 0,
            tracker_id_counter: 1,
            with_drop_tracker,
            with_alloc_reset,
            body_lines: Vec::new(),
        }
    }

    fn fresh_var(&mut self, prefix: &str) -> String {
        let id = self.var_counter;
        self.var_counter += 1;
        format!("{prefix}_{id}")
    }

    fn fresh_tracker_id(&mut self) -> usize {
        let id = self.tracker_id_counter;
        self.tracker_id_counter += 1;
        id
    }

    fn emit(&mut self, indent: usize, line: String) {
        let tabs = "\t".repeat(indent);
        self.body_lines.push(format!("{tabs}{line}"));
    }

    fn find_live_var(&self, env: &[VarEntry], want: &FuzzTy) -> Option<usize> {
        let matches: Vec<usize> = env
            .iter()
            .enumerate()
            .filter(|(_, v)| !v.moved && &v.ty == want)
            .map(|(i, _)| i)
            .collect();
        if matches.is_empty() {
            None
        } else {
            Some(matches[0])
        }
    }

    fn gen_expr(&mut self, env: &mut [VarEntry], ty: &FuzzTy, depth: usize) -> String {
        // Occasionally consume or reuse a live variable
        if depth < 2 && self.rng.gen_bool(1, 3) {
            if let Some(idx) = self.find_live_var(env, ty) {
                let name = env[idx].name.clone();
                match ty {
                    FuzzTy::Rc(_) => return format!("Rc::clone(&{name})"),
                    FuzzTy::Arc(_) => return format!("Arc::clone(&{name})"),
                    FuzzTy::String => return format!("{name}.clone()"),
                    _ if ty.is_copy() => return name,
                    _ => {
                        // Only move variables when safe (inside top-level / not inside loop body across iterations;
                        // callers handle env snapshots for branches/loops)
                        env[idx].moved = true;
                        return name;
                    }
                }
            }
        }

        match ty {
            FuzzTy::I8 => format!("{}", (self.rng.gen_range(90) as i64) - 40),
            FuzzTy::I16 => format!("{}", (self.rng.gen_range(400) as i64) - 200),
            FuzzTy::I32 => {
                if depth == 0 && self.rng.gen_bool(1, 3) {
                    let a = (self.rng.gen_range(40) as i64) + 1;
                    let b = (self.rng.gen_range(20) as i64) + 1;
                    let op = *self.rng.choose(&["+", "-", "*", "&", "|", "^"]);
                    format!("({a} {op} {b})")
                } else {
                    format!("{}", (self.rng.gen_range(500) as i64) - 250)
                }
            }
            FuzzTy::I64 => {
                if depth == 0 && self.rng.gen_bool(1, 2) {
                    let a = self.gen_expr(env, &FuzzTy::I64, depth + 1);
                    let b = self.gen_expr(env, &FuzzTy::I64, depth + 1);
                    let op = *self.rng.choose(&["+", "-", "*", "&", "|", "^"]);
                    format!("({a} {op} {b})")
                } else {
                    format!("{}", (self.rng.gen_range(200) as i64) - 50)
                }
            }
            FuzzTy::U8 => format!("{}", self.rng.gen_range(200)),
            FuzzTy::U16 => format!("{}", self.rng.gen_range(5000)),
            FuzzTy::U32 => format!("{}", self.rng.gen_range(100_000)),
            FuzzTy::U64 => {
                if depth == 0 && self.rng.gen_bool(1, 3) {
                    let a = self.gen_expr(env, &FuzzTy::U64, depth + 1);
                    let sh = self.rng.gen_range(8);
                    format!("({a} << {sh})")
                } else {
                    format!("{}", self.rng.gen_range(100_000))
                }
            }
            FuzzTy::F32 | FuzzTy::F64 => {
                let w = self.rng.gen_range(50);
                let f = self.rng.gen_range(99);
                format!("{w}.{f:02}")
            }
            FuzzTy::Bool => {
                if depth == 0 && self.rng.gen_bool(1, 2) {
                    let a = (self.rng.gen_range(30) as i64) + 1;
                    let b = (self.rng.gen_range(30) as i64) + 1;
                    let cmp = *self.rng.choose(&["<", ">", "==", "!=", "<=", ">="]);
                    format!("({a} {cmp} {b})")
                } else {
                    format!("{}", self.rng.gen_bool(1, 2))
                }
            }
            FuzzTy::String => {
                let word = *self.rng.choose(&["alpha", "beta", "gamma", "fuzz", "gdrs"]);
                let n = self.rng.gen_range(100);
                format!("String::from(\"{word}_{n}\")")
            }
            FuzzTy::SmallPair => {
                let a = self.gen_expr(env, &FuzzTy::I64, depth + 1);
                let b = self.gen_expr(env, &FuzzTy::Bool, depth + 1);
                format!("SmallPair{{ a: {a}, b: {b} }}")
            }
            FuzzTy::OwnedWrap => {
                let id = self.rng.gen_range(1000);
                let inner = self.gen_expr(env, &FuzzTy::Boxed(Box::new(FuzzTy::I64)), depth + 1);
                let text = self.gen_expr(env, &FuzzTy::String, depth + 1);
                format!("OwnedWrap{{ id: {id}, ptr: {inner}, text: {text} }}")
            }
            FuzzTy::DropTracker => {
                let id = self.fresh_tracker_id();
                format!("make_tracker({id})")
            }
            FuzzTy::Choice => match self.rng.gen_range(4) {
                0 => {
                    let v = self.gen_expr(env, &FuzzTy::I64, depth + 1);
                    format!("Choice::Num({v})")
                }
                1 => {
                    let b = self.gen_expr(env, &FuzzTy::Bool, depth + 1);
                    format!("Choice::Flag({b})")
                }
                2 => {
                    let s = self.gen_expr(env, &FuzzTy::String, depth + 1);
                    format!("Choice::Text({s})")
                }
                _ => {
                    let b = self.gen_expr(env, &FuzzTy::Boxed(Box::new(FuzzTy::I64)), depth + 1);
                    format!("Choice::Boxed({b})")
                }
            },
            FuzzTy::RecNode => {
                if depth >= 1 || self.rng.gen_bool(1, 2) {
                    let v = self.rng.gen_range(50);
                    if self.with_drop_tracker {
                        let t = self.gen_expr(env, &FuzzTy::DropTracker, depth + 1);
                        format!("RecNode::Leaf({v}, {t})")
                    } else {
                        format!("RecNode::Leaf({v})")
                    }
                } else {
                    let v = self.rng.gen_range(50);
                    let tail = self.gen_expr(env, &FuzzTy::RecNode, depth + 1);
                    if self.with_drop_tracker {
                        let t = self.gen_expr(env, &FuzzTy::DropTracker, depth + 1);
                        format!("RecNode::Cons({v}, {t}, Box::new({tail}))")
                    } else {
                        format!("RecNode::Cons({v}, Box::new({tail}))")
                    }
                }
            }
            FuzzTy::Boxed(inner) => {
                let e = self.gen_expr(env, inner, depth + 1);
                format!("Box::new({e})")
            }
            FuzzTy::Rc(inner) => {
                let e = self.gen_expr(env, inner, depth + 1);
                format!("Rc::new({e})")
            }
            FuzzTy::Arc(inner) => {
                let e = self.gen_expr(env, inner, depth + 1);
                format!("Arc::new({e})")
            }
            FuzzTy::Vec(inner) => {
                let a = self.gen_expr(env, inner, depth + 1);
                let b = self.gen_expr(env, inner, depth + 1);
                format!("vec![{a}, {b}]")
            }
            FuzzTy::Opt(inner) => {
                if self.rng.gen_bool(2, 3) {
                    let e = self.gen_expr(env, inner, depth + 1);
                    format!("Option::Some({e})")
                } else {
                    "Option::None".to_string()
                }
            }
            FuzzTy::Res(inner) => {
                if self.rng.gen_bool(2, 3) {
                    let e = self.gen_expr(env, inner, depth + 1);
                    format!("Result::Ok({e})")
                } else {
                    let s = self.gen_expr(env, &FuzzTy::String, depth + 1);
                    format!("Result::Err({s})")
                }
            }
            FuzzTy::Tuple2(a, b) => {
                let ea = self.gen_expr(env, a, depth + 1);
                let eb = self.gen_expr(env, b, depth + 1);
                format!("({ea}, {eb})")
            }
            FuzzTy::Arr4(inner) => {
                let e0 = self.gen_expr(env, inner, depth + 1);
                let e1 = self.gen_expr(env, inner, depth + 1);
                let e2 = self.gen_expr(env, inner, depth + 1);
                let e3 = self.gen_expr(env, inner, depth + 1);
                format!("[{e0}, {e1}, {e2}, {e3}]")
            }
            FuzzTy::FnPtr => (*self
                .rng
                .choose(&["fuzz_add", "|a, b| a - b", "|a, b| a * b + 1"]))
            .to_string(),
        }
    }

    fn gen_type(&mut self) -> FuzzTy {
        let mut pool = vec![
            FuzzTy::I8,
            FuzzTy::I16,
            FuzzTy::I32,
            FuzzTy::I64,
            FuzzTy::U8,
            FuzzTy::U16,
            FuzzTy::U32,
            FuzzTy::U64,
            FuzzTy::F32,
            FuzzTy::F64,
            FuzzTy::Bool,
            FuzzTy::String,
            FuzzTy::SmallPair,
            FuzzTy::OwnedWrap,
            FuzzTy::Choice,
            FuzzTy::RecNode,
            FuzzTy::Boxed(Box::new(FuzzTy::I64)),
            FuzzTy::Boxed(Box::new(FuzzTy::String)),
            FuzzTy::Rc(Box::new(FuzzTy::I64)),
            FuzzTy::Rc(Box::new(FuzzTy::String)),
            FuzzTy::Arc(Box::new(FuzzTy::I64)),
            FuzzTy::Vec(Box::new(FuzzTy::I64)),
            FuzzTy::Vec(Box::new(FuzzTy::String)),
            FuzzTy::Opt(Box::new(FuzzTy::I64)),
            FuzzTy::Res(Box::new(FuzzTy::I64)),
            FuzzTy::Tuple2(Box::new(FuzzTy::I64), Box::new(FuzzTy::Bool)),
            FuzzTy::Tuple2(Box::new(FuzzTy::I32), Box::new(FuzzTy::String)),
            FuzzTy::Arr4(Box::new(FuzzTy::I64)),
            FuzzTy::FnPtr,
        ];
        if self.with_drop_tracker {
            pool.extend([
                FuzzTy::DropTracker,
                FuzzTy::DropTracker,
                FuzzTy::Boxed(Box::new(FuzzTy::DropTracker)),
                FuzzTy::Rc(Box::new(FuzzTy::DropTracker)),
                FuzzTy::Arc(Box::new(FuzzTy::DropTracker)),
                FuzzTy::Vec(Box::new(FuzzTy::DropTracker)),
                FuzzTy::Opt(Box::new(FuzzTy::DropTracker)),
                FuzzTy::Res(Box::new(FuzzTy::DropTracker)),
                FuzzTy::Tuple2(Box::new(FuzzTy::I64), Box::new(FuzzTy::DropTracker)),
            ]);
        }
        self.rng.choose(&pool).clone()
    }

    fn emit_random_stmts(&mut self, env: &mut Vec<VarEntry>, count: usize, indent: usize, in_loop: bool) {
        let start_len = self.body_lines.len();
        for _ in 0..count {
            let kind = self.rng.gen_range(8);
            match kind {
                0..=2 => {
                    // Bind a new typed variable
                    let ty = self.gen_type();
                    let name = self.fresh_var("v");
                    let is_mut = self.rng.gen_bool(1, 2);
                    let mut_kw = if is_mut { "mut " } else { "" };
                    let expr = self.gen_expr(env, &ty, 0);
                    let ty_str = ty.gdrs_name();
                    self.emit(indent, format!("let {mut_kw}{name}: {ty_str} = {expr}"));
                    env.push(VarEntry {
                        name,
                        ty,
                        is_mut,
                        moved: false,
                    });
                }
                3 => {
                    // Mutate an existing live mutable variable (exercises drop-before-reassign!)
                    let mut_idxs: Vec<usize> = env
                        .iter()
                        .enumerate()
                        .filter(|(_, v)| !v.moved && v.is_mut)
                        .map(|(i, _)| i)
                        .collect();
                    if let Some(&idx) = mut_idxs.first() {
                        let name = env[idx].name.clone();
                        let ty = env[idx].ty.clone();
                        let expr = self.gen_expr(env, &ty, 0);
                        env[idx].moved = false;
                        self.emit(indent, format!("{name} = {expr}"));
                    }
                }
                4 => {
                    // Emit if / else statement or Debug / method check
                    if indent < 3 {
                        let cond = self.gen_expr(env, &FuzzTy::Bool, 0);
                        self.emit(indent, format!("if {cond}:"));
                        let mut then_env: Vec<VarEntry> = env
                            .iter()
                            .cloned()
                            .map(|mut v| {
                                // Only introduce fresh bindings inside branch so outer env remains intact without cross-branch partial moves
                                v.moved = v.moved || !v.ty.is_copy();
                                v
                            })
                            .collect();
                        self.emit_random_stmts(&mut then_env, 2, indent + 1, in_loop);
                        if self.rng.gen_bool(1, 2) {
                            self.emit(indent, "else:".to_string());
                            let mut else_env: Vec<VarEntry> = env
                                .iter()
                                .cloned()
                                .map(|mut v| {
                                    v.moved = v.moved || !v.ty.is_copy();
                                    v
                                })
                                .collect();
                            self.emit_random_stmts(&mut else_env, 2, indent + 1, in_loop);
                        }
                    }
                }
                5 => {
                    // Bounded while loop with optional continue/break and local Drop values
                    if indent < 3 && !in_loop {
                        let loop_i = self.fresh_var("li");
                        let lim = 1 + self.rng.gen_range(3);
                        self.emit(indent, format!("let mut {loop_i}: i64 = 0"));
                        self.emit(indent, format!("while {loop_i} < {lim}:"));
                        self.emit(indent + 1, format!("{loop_i} += 1"));
                        let mut loop_env: Vec<VarEntry> = env
                            .iter()
                            .cloned()
                            .map(|mut v| {
                                // Outer non-Copy vars cannot be moved inside a loop body
                                v.moved = v.moved || !v.ty.is_copy();
                                v
                            })
                            .collect();
                        self.emit_random_stmts(&mut loop_env, 2, indent + 1, true);
                        if self.rng.gen_bool(1, 2) {
                            self.emit(indent + 1, format!("if {loop_i} == 1:"));
                            self.emit(indent + 2, "continue".to_string());
                        } else {
                            self.emit(indent + 1, format!("if {loop_i} == 2:"));
                            self.emit(indent + 2, "break".to_string());
                        }
                    }
                }
                6 => {
                    // Exercise match on Option / Choice / Result + slice + fn ptr
                    let sub = self.rng.gen_range(4);
                    match sub {
                        0 => {
                            let ch = self.fresh_var("ch");
                            let expr = self.gen_expr(env, &FuzzTy::Choice, 0);
                            self.emit(indent, format!("let {ch}: Choice = {expr}"));
                            self.emit(indent, format!("match {ch}:"));
                            self.emit(indent + 1, "Choice::Num(n) => assert_eq!(n, n)".to_string());
                            self.emit(indent + 1, "Choice::Flag(f) => assert_eq!(f, f)".to_string());
                            self.emit(indent + 1, "Choice::Text(s) => assert_eq!(s.len(), s.len())".to_string());
                            self.emit(indent + 1, "Choice::Boxed(b) => assert_eq!(*b, *b)".to_string());
                        }
                        1 => {
                            let arr_v = self.fresh_var("arr");
                            let sl_v = self.fresh_var("sl");
                            let sum_v = self.fresh_var("sacc");
                            let expr = self.gen_expr(env, &FuzzTy::Arr4(Box::new(FuzzTy::I64)), 0);
                            self.emit(indent, format!("let mut {arr_v}: [i64; 4] = {expr}"));
                            self.emit(indent, format!("let {sl_v}: &[i64] = &{arr_v}[1..3]"));
                            self.emit(indent, format!("let mut {sum_v}: i64 = 0"));
                            self.emit(indent, format!("for elem in {sl_v}:"));
                            self.emit(indent + 1, format!("{sum_v} += elem"));
                            self.emit(indent, format!("assert_eq!({sl_v}.len(), 2)"));
                        }
                        2 => {
                            let f_v = self.fresh_var("fp");
                            let r1_v = self.fresh_var("r1");
                            let r2_v = self.fresh_var("r2");
                            self.emit(indent, format!("let {f_v}: fn(i64, i64) -> i64 = fuzz_add"));
                            self.emit(indent, format!("let {r1_v}: i64 = fuzz_apply({f_v}, 7, 5)"));
                            self.emit(indent, format!("let {r2_v}: i64 = fuzz_apply(|x, y| x + y, 7, 5)"));
                            self.emit(indent, format!("assert_eq!({r1_v}, {r2_v})"));
                        }
                        _ => {
                            let p_v = self.fresh_var("sp");
                            let expr = self.gen_expr(env, &FuzzTy::SmallPair, 0);
                            let s_v = self.fresh_var("dbg");
                            self.emit(indent, format!("let {p_v}: SmallPair = {expr}"));
                            self.emit(indent, format!("assert_eq!({p_v}, {p_v})"));
                            self.emit(indent, format!("let {s_v}: String = format!(\"{{:?}} {{:#?}}\", {p_v}, {p_v})"));
                            self.emit(indent, format!("assert!({s_v}.len() > 0)"));
                        }
                    }
                }
                _ => {
                    // Format / algebraic checks on live variables without moving them
                    let live_idxs: Vec<usize> = env
                        .iter()
                        .enumerate()
                        .filter(|(_, v)| !v.moved)
                        .map(|(i, _)| i)
                        .collect();
                    if !live_idxs.is_empty() {
                        let idx = *self.rng.choose(&live_idxs);
                        let name = env[idx].name.clone();
                        let dbg_v = self.fresh_var("dbg");
                        let dbg2_v = self.fresh_var("dbg2");
                        self.emit(indent, format!("let {dbg_v}: String = format!(\"{{:?}}\", {name})"));
                        self.emit(indent, format!("let {dbg2_v}: String = format!(\"{{:?}}\", {name})"));
                        self.emit(indent, format!("assert_eq!({dbg_v}, {dbg2_v})"));
                    }
                }
            }
        }
        if self.body_lines.len() == start_len {
            let noop = self.fresh_var("noop");
            self.emit(indent, format!("let {noop}: i64 = 0"));
        }
    }

    fn generate_program(&mut self) -> String {
        let mut out = String::new();
        out.push_str(
            r#"use std::boxed::Box
use std::rc::Rc
use std::sync::Arc
use std::vec::Vec
use std::string::String
"#,
        );
        if self.with_drop_tracker {
            out.push_str("use std::core::Drop\n");
            out.push_str(
                r#"
#[derive(Debug)]
obj DropTracker:
	id: i64
	magic: i64

fn make_tracker(id: i64) -> DropTracker:
	log!("FUZZ_NEW {}", id)
	return DropTracker{ id: id, magic: 1511964894 }

impl Drop for DropTracker:
	fn drop(mut self):
		if self.magic != 1511964894:
			panic!("DropTracker corrupted magic: {}", self.magic)
		self.magic = 3735928559
		log!("FUZZ_DROP {}", self.id)
"#,
            );
        }

        out.push_str(
            r#"
#[derive(Debug, PartialEq, Eq)]
obj SmallPair:
	a: i64
	b: bool

#[derive(Debug)]
obj OwnedWrap:
	id: i64
	ptr: Box<i64>
	text: String

#[derive(Debug)]
enum Choice:
	Num(i64)
	Flag(bool)
	Text(String)
	Boxed(Box<i64>)
"#,
        );

        if self.with_drop_tracker {
            out.push_str(
                r#"
#[derive(Debug)]
enum RecNode:
	Leaf(i64, DropTracker)
	Cons(i64, DropTracker, Box<RecNode>)
"#,
            );
        } else {
            out.push_str(
                r#"
#[derive(Debug)]
enum RecNode:
	Leaf(i64)
	Cons(i64, Box<RecNode>)
"#,
            );
        }

        out.push_str(
            r#"
fn fuzz_add(a: i64, b: i64) -> i64:
	return a + b

fn fuzz_apply(f: fn(i64, i64) -> i64, a: i64, b: i64) -> i64:
	return f(a, b)
"#,
        );

        if self.with_drop_tracker {
            let h1 = self.fresh_tracker_id();
            let h2 = self.fresh_tracker_id();
            let h3 = self.fresh_tracker_id();
            let h4 = self.fresh_tracker_id();
            out.push_str(&format!(
                r#"
fn helper_early_return(flag: bool) -> i64:
	let t1: DropTracker = make_tracker({h1})
	let b1: Box<DropTracker> = Box::new(make_tracker({h2}))
	if flag:
		return t1.id + b1.id
	let t3: DropTracker = make_tracker({h3})
	return t1.id + t3.id

fn helper_try_ok(flag: bool) -> Result<DropTracker, String>:
	let live: DropTracker = make_tracker({h4})
	if !flag:
		return Result::Err(String::from("nope"))
	return Result::Ok(live)

fn helper_call_try(flag: bool) -> Result<i64, String>:
	let res_t: DropTracker = helper_try_ok(flag)?
	return Result::Ok(res_t.id)
"#,
            ));
        }

        let mut env = Vec::new();
        self.body_lines.clear();
        if self.with_drop_tracker {
            self.emit(1, "let _e1: i64 = helper_early_return(true)".to_string());
            self.emit(1, "let _e2: i64 = helper_early_return(false)".to_string());
            self.emit(1, "let _t1: Result<i64, String> = helper_call_try(true)".to_string());
            self.emit(1, "let _t2: Result<i64, String> = helper_call_try(false)".to_string());
            self.emit(1, "assert!(_t1.is_ok())".to_string());
            self.emit(1, "assert!(_t2.is_err())".to_string());
        }
        self.emit_random_stmts(&mut env, 18, 1, false);

        if self.with_alloc_reset {
            out.push_str("\nextern \"C\":\n\tfn fuzz_reset_alloc_counters()\n\nfn fuzz_body():\n");
            for line in &self.body_lines {
                out.push_str(line);
                out.push('\n');
            }
            out.push_str(
                "\nfn main():\n\tlog!(\"FUZZ_WARMUP {} {:?} {:?}\", 0, 14.66 as f32, 24.51)\n\tunsafe:\n\t\tfuzz_reset_alloc_counters()\n\tfuzz_body()\n",
            );
        } else {
            out.push_str("\nfn main():\n");
            for line in &self.body_lines {
                out.push_str(line);
                out.push('\n');
            }
        }
        out
    }
}

#[test]
fn fuzz_tier3_gdrs_smith_typed_generator() {
    let (mut rng, seed) = Rng::from_env_or_default();

    for iter in 0..150 {
        let sub_seed = rng.next_u64();
        let sub_rng = Rng { state: sub_seed };
        let with_drop = iter % 3 == 0;
        let mut smith = GdrsSmith::new(sub_rng, with_drop, false);
        let src = smith.generate_program();

        let compiled = catch_unwind(AssertUnwindSafe(|| gdrs::compile_source_in_memory(&src)));
        match compiled {
            Err(_) => {
                panic!(
                    "Tier 3 GdrsSmith caused compiler PANIC at iter={iter}!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier3\nSource:\n{src}"
                );
            }
            Ok(Err(e)) => {
                panic!(
                    "Tier 3 GdrsSmith generated program rejected at iter={iter}!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier3\nError:\n{e}\nSource:\n{src}"
                );
            }
            Ok(Ok(_)) => {}
        }
    }
}

// ============================================================================
// Tier 4: DropTracker Canary + DYLD_INTERPOSE Zero-Leak + Runtime Self-Checks
// ============================================================================

static FUZZ_BIN_COUNTER: AtomicUsize = AtomicUsize::new(0);

#[cfg(target_os = "macos")]
fn build_alloc_hook_dylib(dir: &Path) -> PathBuf {
    let hook_src = r#"
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>

static _Atomic long g_allocs = 0;
static _Atomic long g_frees = 0;

void* fuzz_hook_malloc(size_t sz) {
    void* p = malloc(sz);
    if (p) atomic_fetch_add(&g_allocs, 1);
    return p;
}
void* fuzz_hook_calloc(size_t count, size_t sz) {
    void* p = calloc(count, sz);
    if (p) atomic_fetch_add(&g_allocs, 1);
    return p;
}
void* fuzz_hook_realloc(void* ptr, size_t sz) {
    void* p = realloc(ptr, sz);
    if (!ptr && p) atomic_fetch_add(&g_allocs, 1);
    return p;
}
void fuzz_hook_free(void* ptr) {
    if (ptr) atomic_fetch_add(&g_frees, 1);
    free(ptr);
}

#define DYLD_INTERPOSE(_replacement,_replacee) \
   __attribute__((used)) static struct{ const void* replacement; const void* replacee; } _interpose_##_replacee \
   __attribute__ ((section ("__DATA,__interpose"))) = { (const void*)(unsigned long)&_replacement, (const void*)(unsigned long)&_replacee };

DYLD_INTERPOSE(fuzz_hook_malloc, malloc)
DYLD_INTERPOSE(fuzz_hook_calloc, calloc)
DYLD_INTERPOSE(fuzz_hook_realloc, realloc)
DYLD_INTERPOSE(fuzz_hook_free, free)

void fuzz_reset_alloc_counters(void) {
    atomic_store(&g_allocs, 0);
    atomic_store(&g_frees, 0);
}

__attribute__((destructor)) static void fuzz_report_leaks(void) {
    fprintf(stderr, "NET_ALLOCS=%ld\n", atomic_load(&g_allocs) - atomic_load(&g_frees));
}
"#;
    let c_path = dir.join("fuzz_alloc_hook.c");
    let dylib_path = dir.join("libfuzz_alloc_hook.dylib");
    fs::write(&c_path, hook_src).unwrap();
    let out = Command::new("clang")
        .args(["-shared", "-fPIC", "-install_name"])
        .arg(&dylib_path)
        .arg(&c_path)
        .arg("-o")
        .arg(&dylib_path)
        .output()
        .expect("failed to invoke clang for alloc hook");
    assert!(
        out.status.success(),
        "clang dylib build failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    dylib_path
}

fn verify_drop_counts(stdout: &str, iter: usize, seed: u64, src: &str) {
    let mut created: HashMap<i64, usize> = HashMap::new();
    let mut dropped: HashMap<i64, usize> = HashMap::new();

    for line in stdout.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("FUZZ_NEW ") {
            let id: i64 = rest.trim().parse().unwrap_or_else(|_| {
                panic!("Bad FUZZ_NEW line: {t}");
            });
            *created.entry(id).or_insert(0) += 1;
        } else if let Some(rest) = t.strip_prefix("FUZZ_DROP ") {
            let id: i64 = rest.trim().parse().unwrap_or_else(|_| {
                panic!("Bad FUZZ_DROP line: {t}");
            });
            *dropped.entry(id).or_insert(0) += 1;
        }
    }

    for (id, &c_cnt) in &created {
        let d_cnt = dropped.get(id).copied().unwrap_or(0);
        assert_eq!(
            c_cnt, d_cnt,
            "Tier 4 DROP MISMATCH at iter={iter} for DropTracker id={id}: created={c_cnt}, dropped={d_cnt}!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier4\nSource:\n{src}\nSTDOUT:\n{stdout}"
        );
    }
    for (id, &d_cnt) in &dropped {
        let c_cnt = created.get(id).copied().unwrap_or(0);
        assert_eq!(
            c_cnt, d_cnt,
            "Tier 4 PHANTOM/EXTRA DROP at iter={iter} for DropTracker id={id}: created={c_cnt}, dropped={d_cnt}!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier4\nSource:\n{src}\nSTDOUT:\n{stdout}"
        );
    }
}

#[test]
fn fuzz_tier4_runtime_oracles_drop_canary_and_zero_leak() {
    let (mut rng, seed) = Rng::from_env_or_default();
    let id_dir = FUZZ_BIN_COUNTER.fetch_add(1, Ordering::SeqCst);
    let temp_dir = std::env::temp_dir().join(format!("gdrs_fuzz_t4_{}_{id_dir}", std::process::id()));
    fs::create_dir_all(&temp_dir).unwrap();

    #[cfg(target_os = "macos")]
    let hook_dylib = build_alloc_hook_dylib(&temp_dir);

    for iter in 0..20 {
        let sub_seed = rng.next_u64();
        let sub_rng = Rng { state: sub_seed };
        let mut smith = GdrsSmith::new(sub_rng, true, cfg!(target_os = "macos"));
        let src = smith.generate_program();

        let (typed_prog, struct_layouts, source_map) = check_source_in_memory(&src)
            .unwrap_or_else(|e| {
                panic!("Tier 4 sanal failure at iter={iter} (seed=0x{seed:016x}): {e}\nSource:\n{src}");
            });

        let bin_path = temp_dir.join(format!("fuzz_prog_{iter}"));
        let bin_str = bin_path.to_string_lossy().to_string();
        #[cfg(target_os = "macos")]
        let lib_paths = vec![temp_dir.to_string_lossy().to_string()];
        #[cfg(not(target_os = "macos"))]
        let lib_paths: Vec<String> = Vec::new();
        #[cfg(target_os = "macos")]
        let libs = vec!["fuzz_alloc_hook".to_string()];
        #[cfg(not(target_os = "macos"))]
        let libs: Vec<String> = Vec::new();
        codegen::object::compile_program_to_binary(
            &typed_prog,
            &struct_layouts,
            &bin_str,
            &lib_paths,
            &libs,
            &source_map,
        )
        .unwrap_or_else(|e| {
            panic!("Tier 4 build failure at iter={iter} (seed=0x{seed:016x}): {e}\nSource:\n{src}");
        });

        let mut cmd = Command::new(&bin_path);
        #[cfg(target_os = "macos")]
        cmd.env("DYLD_LIBRARY_PATH", &temp_dir)
            .env("DYLD_INSERT_LIBRARIES", &hook_dylib);

        let run_out = cmd.output().expect("failed to run Tier 4 binary");
        let _ = fs::remove_file(&bin_path);

        let stdout = String::from_utf8_lossy(&run_out.stdout);
        let stderr = String::from_utf8_lossy(&run_out.stderr);

        assert!(
            run_out.status.success(),
            "Tier 4 RUNTIME CRASH / ASSERTION FAILURE at iter={iter} (exit={:?})!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier4\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}\nSource:\n{src}",
            run_out.status.code()
        );

        verify_drop_counts(&stdout, iter, seed, &src);

        #[cfg(target_os = "macos")]
        {
            let net_allocs = stderr
                .lines()
                .find_map(|line| line.strip_prefix("NET_ALLOCS="))
                .and_then(|v| v.trim().parse::<i64>().ok())
                .unwrap_or_else(|| {
                    panic!("Missing NET_ALLOCS in stderr at iter={iter}:\n{stderr}");
                });
            assert_eq!(
                net_allocs, 0,
                "Tier 4 MEMORY LEAK DETECTED at iter={iter}: NET_ALLOCS={net_allocs}!\nReproduce with: GDRS_FUZZ_SEED=0x{seed:016x} cargo test --test fuzz_tests fuzz_tier4\nSTDERR:\n{stderr}\nSource:\n{src}"
            );
        }
    }

    let _ = fs::remove_dir_all(&temp_dir);
}
