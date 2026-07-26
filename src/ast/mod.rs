use logos::Logos;

// ==========================================
// 1. LEXER (Logos)
// ==========================================
#[derive(Logos, Debug, PartialEq, Eq, Hash, Clone)]
#[logos(skip r"[ \t]+")] // Automatically skip spaces and tabs inline
#[logos(skip(r"//[^\r\n]*", allow_greedy = true))]
pub enum Token {
    #[token("#")]
    Hash,
    #[token("let")]
    Let,
    #[token("mut")]
    Mut,
    #[token("=")]
    Assign,
    #[token("+")]
    Plus,
    #[token("..")]
    DotDot,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("+=")]
    PlusEqual,
    #[token("-=")]
    MinusEqual,
    #[token("*=")]
    StarEqual,
    #[token("/=")]
    SlashEqual,
    #[token("%")]
    Percent,
    #[token(">")]
    GreaterThan,
    #[token("<")]
    LessThan,
    #[token(">=")]
    GreaterEqual,
    #[token("<=")]
    LessEqual,
    #[token("==")]
    Equal,
    #[token("!=")]
    NotEqual,
    #[token("!")]
    Exclamation,
    #[token("?")]
    Question,
    #[token("not")]
    Not,
    #[token("&&")]
    #[token("and")]
    And,
    #[token("||")]
    #[token("or")]
    Or,

    #[token("|")]
    Pipe,
    #[token("&")]
    Ampersand,
    #[token("^")]
    Caret,
    #[token("<<")]
    Shl,
    #[token(">>")]
    Shr,

    #[token("->")]
    Arrow,
    #[token("return")]
    Return,
    #[token("else")]
    Else,

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().parse::<f64>().unwrap().to_bits())]
    Float(u64),
    #[regex(r"0[xX][0-9a-fA-F]+", |lex| i64::from_str_radix(&lex.slice()[2..], 16).unwrap_or_else(|_| u64::from_str_radix(&lex.slice()[2..], 16).map(|u| u as i64).unwrap_or(0)))]
    #[regex("[0-9]+", |lex| lex.slice().parse::<i64>().unwrap())]
    Int(i64),

    // Catch newlines and count the spaces immediately after them
    #[regex(r"\r?\n[ \t]*", |lex| {
        lex.slice().chars().filter(|c| *c == ' ' || *c == '\t').count()
    })]
    NewlineWithIndent(usize),

    // Virtual tokens we will inject (Logos never matches these directly)
    Indent,
    Dedent,
    Newline,

    #[token("fn")]
    Fn,
    #[token("::")]
    ColonColon,
    #[token(":")]
    Colon,

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,

    #[token("true", |_| true)]
    #[token("false", |_| false)]
    Bool(bool),

    #[regex(r#""([^"\\]|\\.)*""#, |lex| lex.slice().to_string())]
    String(String),
    #[token("while")]
    While,
    #[token("if")]
    If,
    #[token(",")]
    Comma,
    #[token("i64")]
    TypeI64,
    #[token("i32")]
    TypeI32,
    #[token("f64")]
    TypeFloat,
    #[token("f32")]
    TypeF32,
    #[token("bool")]
    TypeBool,
    #[token("string")]
    TypeString,
    #[token("str")]
    TypeStr,
    #[token("rc")]
    TypeRc,
    #[token("arc")]
    TypeArc,
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*!", |lex| lex.slice()[..lex.slice().len() - 1].to_string())]
    MacroIdent(String),

    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token(";")]
    Semicolon,

    #[token("obj")]
    Obj,
    #[token("enum")]
    Enum,
    #[token("impl")]
    Impl,
    #[token("mod")]
    Mod,
    #[token("use")]
    Use,
    #[token("trait")]
    Trait,
    #[token("where")]
    Where,
    #[token("type")]
    TypeKw,
    #[token("dyn")]
    Dyn,
    #[token("extern")]
    Extern,
    #[token("unsafe")]
    Unsafe,
    #[token("match")]
    Match,
    #[token("=>")]
    FatArrow,
    #[token("$")]
    Dollar,

    #[token(".")]
    Dot,
}

pub type Span = std::ops::Range<usize>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    I32,
    Float,
    F32,
    Bool,
    Str,
    String,
    Unit,
    Obj(&'static str),
    Enum(&'static str),
    Generic(&'static str),
    DynTrait(&'static str),
    Array(&'static Type, usize),
    Slice(&'static Type),
    Vec(&'static Type),
    Rc(&'static Type),
    Arc(&'static Type),
    Ref(&'static Type),
    MutRef(&'static Type),
}

impl Type {
    pub fn name_or_default(&self) -> &'static str {
        match self {
            Type::Obj(name) => name,
            Type::Enum(name) => name,
            Type::Generic(name) => name,
            Type::DynTrait(name) => name,
            _ => "unknown",
        }
    }
}

pub fn intern_type(ty: Type) -> &'static Type {
    Box::leak(Box::new(ty))
}

pub fn intern_str(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

#[derive(Debug, Clone)]
pub struct Attribute {
    pub name: String,
    pub args: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: String,
    pub ty: Type,
    pub attributes: Vec<Attribute>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub attributes: Vec<Attribute>,
    pub where_clause: Option<WhereClause>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EnumVariantDecl {
    pub name: String,
    pub payload_types: Vec<Type>,
    pub attributes: Vec<Attribute>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EnumDecl {
    pub name: String,
    pub variants: Vec<EnumVariantDecl>,
    pub attributes: Vec<Attribute>,
    pub where_clause: Option<WhereClause>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ImplDecl {
    pub trait_name: Option<String>,
    pub target_type: String,
    pub methods: Vec<FuncDecl>,
    pub where_clause: Option<WhereClause>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub is_mutable: bool,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(i64, Span),
    Float(f64, Span),
    Ident(String, Span),
    Bool(bool, Span),

    Add(Box<Expr>, Box<Expr>, Span),
    Sub(Box<Expr>, Box<Expr>, Span),
    Mul(Box<Expr>, Box<Expr>, Span),
    Div(Box<Expr>, Box<Expr>, Span),
    Mod(Box<Expr>, Box<Expr>, Span),
    Neg(Box<Expr>, Span),
    Not(Box<Expr>, Span),

    GreaterThan(Box<Expr>, Box<Expr>, Span),
    LessThan(Box<Expr>, Box<Expr>, Span),
    GreaterEqual(Box<Expr>, Box<Expr>, Span),
    LessEqual(Box<Expr>, Box<Expr>, Span),
    Equal(Box<Expr>, Box<Expr>, Span),
    NotEqual(Box<Expr>, Box<Expr>, Span),
    And(Box<Expr>, Box<Expr>, Span),
    Or(Box<Expr>, Box<Expr>, Span),

    String(String, Span),

    Let(String, Option<Type>, bool, Box<Expr>, Span),
    Block(Vec<Expr>, Span),
    Unsafe(Vec<Expr>, Span),
    Assign(String, Box<Expr>, Span),
    While(Box<Expr>, Box<Expr>, Span),
    If(Box<Expr>, Box<Expr>, Span),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>, Span),
    Return(Option<Box<Expr>>, Span),
    MacroCall(String, Vec<Expr>, Span),
    Call(String, Vec<Expr>, Span),
    Try(Box<Expr>, Span),

    ObjInit(String, Vec<(String, Expr)>, Span),
    FieldAccess(Box<Expr>, String, Span),
    FieldAssign(Box<Expr>, String, Box<Expr>, Span),

    ArrayInit(Vec<Expr>, Span),
    IndexAccess(Box<Expr>, Box<Expr>, Span),
    IndexAssign(Box<Expr>, Box<Expr>, Box<Expr>, Span),

    Pipe(Box<Expr>, Box<Expr>, Span),
    Ampersand(Box<Expr>, Box<Expr>, Span),
    Caret(Box<Expr>, Box<Expr>, Span),
    Shl(Box<Expr>, Box<Expr>, Span),
    Shr(Box<Expr>, Box<Expr>, Span),

    EnumConstruct(String, String, Vec<Expr>, Span),
    Match(Box<Expr>, Vec<MatchArm>, Span),
    Ref(Box<Expr>, bool, Span),
    Deref(Box<Expr>, Span),
    DerefAssign(Box<Expr>, Box<Expr>, Span),
    Closure(Vec<String>, Box<Expr>, Span),
    Range(Box<Expr>, Box<Expr>, Span),
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub variant_name: String,
    pub bindings: Vec<String>,
    pub body: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedMatchArm {
    pub variant_name: String,
    pub tag: i64,
    pub bindings: Vec<(String, Type)>,
    pub body: Vec<TypedExpr>,
    pub span: Span,
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Int(_, s) => s.clone(),
            Expr::Float(_, s) => s.clone(),
            Expr::Ident(_, s) => s.clone(),
            Expr::Bool(_, s) => s.clone(),
            Expr::String(_, s) => s.clone(),
            Expr::Add(_, _, s)
            | Expr::Sub(_, _, s)
            | Expr::Mul(_, _, s)
            | Expr::Div(_, _, s)
            | Expr::Mod(_, _, s)
            | Expr::GreaterThan(_, _, s)
            | Expr::LessThan(_, _, s)
            | Expr::GreaterEqual(_, _, s)
            | Expr::LessEqual(_, _, s)
            | Expr::Equal(_, _, s)
            | Expr::NotEqual(_, _, s)
            | Expr::And(_, _, s)
            | Expr::Or(_, _, s) => s.clone(),
            Expr::Pipe(_, _, s) => s.clone(),
            Expr::Ampersand(_, _, s) => s.clone(),
            Expr::Caret(_, _, s) => s.clone(),
            Expr::Shl(_, _, s) => s.clone(),
            Expr::Shr(_, _, s) => s.clone(),
            Expr::Neg(_, s) | Expr::Not(_, s) => s.clone(),
            Expr::Let(_, _, _, _, s) => s.clone(),
            Expr::Block(_, s) => s.clone(),
            Expr::Unsafe(_, s) => s.clone(),
            Expr::Assign(_, _, s) => s.clone(),
            Expr::While(_, _, s) => s.clone(),
            Expr::If(_, _, s) => s.clone(),
            Expr::IfElse(_, _, _, s) => s.clone(),
            Expr::Return(_, s) => s.clone(),
            Expr::MacroCall(_, _, s) => s.clone(),
            Expr::Call(_, _, s) => s.clone(),
            Expr::ObjInit(_, _, s) => s.clone(),
            Expr::FieldAccess(_, _, s) => s.clone(),
            Expr::FieldAssign(_, _, _, s) => s.clone(),
            Expr::ArrayInit(_, s) => s.clone(),
            Expr::IndexAccess(_, _, s) => s.clone(),
            Expr::IndexAssign(_, _, _, s) => s.clone(),
            Expr::EnumConstruct(_, _, _, s) => s.clone(),
            Expr::Match(_, _, s) => s.clone(),
            Expr::Ref(_, _, s) => s.clone(),
            Expr::Deref(_, s) => s.clone(),
            Expr::DerefAssign(_, _, s) => s.clone(),
            Expr::Closure(_, _, s) => s.clone(),
            Expr::Range(_, _, s) => s.clone(),
            Expr::Try(_, s) => s.clone(),
        }
    }
}

// ==========================================
// 2. TYPED AST (Produced by sanal Type Checker)
// ==========================================
#[derive(Debug, Clone)]
pub enum TypedExpr {
    Int(i64, Span),
    Float(f64, Span),
    Ident(String, Type, Span),
    Bool(bool, Span),
    String(String, Span),

    // mul
    Add(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Sub(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Mul(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Div(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Mod(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Neg(Box<TypedExpr>, Type, Span),
    Not(Box<TypedExpr>, Span),

    // cmp
    GreaterThan(Box<TypedExpr>, Box<TypedExpr>, Span),
    LessThan(Box<TypedExpr>, Box<TypedExpr>, Span),
    GreaterEqual(Box<TypedExpr>, Box<TypedExpr>, Span),
    LessEqual(Box<TypedExpr>, Box<TypedExpr>, Span),
    Equal(Box<TypedExpr>, Box<TypedExpr>, Span),
    NotEqual(Box<TypedExpr>, Box<TypedExpr>, Span),
    And(Box<TypedExpr>, Box<TypedExpr>, Span),
    Or(Box<TypedExpr>, Box<TypedExpr>, Span),

    // Bitwise
    Pipe(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Ampersand(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Caret(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Shl(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Shr(Box<TypedExpr>, Box<TypedExpr>, Type, Span),

    Let(String, bool, Box<TypedExpr>, Type, Span),
    Block(Vec<TypedExpr>, Type, Span),
    Unsafe(Vec<TypedExpr>, Type, Span),
    Assign(String, Box<TypedExpr>, Span),
    While(Box<TypedExpr>, Box<TypedExpr>, Span),
    If(Box<TypedExpr>, Box<TypedExpr>, Span),
    IfElse(Box<TypedExpr>, Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    Return(Option<Box<TypedExpr>>, Span),
    MacroCall(String, Vec<TypedExpr>, Type, Span),
    Call(String, Vec<TypedExpr>, Type, Span),

    ObjInit(String, Vec<(String, TypedExpr)>, Type, Span),
    FieldAccess(Box<TypedExpr>, String, Type, Span),
    FieldAssign(Box<TypedExpr>, String, Box<TypedExpr>, Span),

    ArrayInit(Vec<TypedExpr>, Type, Span),
    IndexAccess(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
    IndexAssign(Box<TypedExpr>, Box<TypedExpr>, Box<TypedExpr>, Span),

    EnumConstruct(String, String, usize, Vec<TypedExpr>, Type, Span),
    CoerceToDyn(Box<TypedExpr>, &'static str, Span),
    DynCall(Box<TypedExpr>, String, Vec<TypedExpr>, Type, Span),
    Match(Box<TypedExpr>, Vec<TypedMatchArm>, Type, Span),
    CastF32(Box<TypedExpr>, Span),
    CastI32(Box<TypedExpr>, Span),
    Ref(Box<TypedExpr>, bool, Type, Span),
    Deref(Box<TypedExpr>, Type, Span),
    DerefAssign(Box<TypedExpr>, Box<TypedExpr>, Span),
    Closure(String, Vec<(String, Type)>, Box<TypedExpr>, Type, Span),
    Range(Box<TypedExpr>, Box<TypedExpr>, Type, Span),
}

impl TypedExpr {
    pub fn ty(&self) -> Type {
        match self {
            TypedExpr::Int(..) => Type::Int,
            TypedExpr::Float(..) => Type::Float,
            TypedExpr::Add(_, _, ty, _)
            | TypedExpr::Sub(_, _, ty, _)
            | TypedExpr::Mul(_, _, ty, _)
            | TypedExpr::Div(_, _, ty, _)
            | TypedExpr::Mod(_, _, ty, _)
            | TypedExpr::Pipe(_, _, ty, _)
            | TypedExpr::Ampersand(_, _, ty, _)
            | TypedExpr::Caret(_, _, ty, _)
            | TypedExpr::Shl(_, _, ty, _)
            | TypedExpr::Shr(_, _, ty, _)
            | TypedExpr::Neg(_, ty, _) => *ty,

            TypedExpr::Bool(..)
            | TypedExpr::Not(..)
            | TypedExpr::GreaterThan(..)
            | TypedExpr::LessThan(..)
            | TypedExpr::GreaterEqual(..)
            | TypedExpr::LessEqual(..)
            | TypedExpr::Equal(..)
            | TypedExpr::NotEqual(..)
            | TypedExpr::And(..)
            | TypedExpr::Or(..) => Type::Bool,

            TypedExpr::String(..) => Type::Str,
            TypedExpr::Ident(_, ty, _)
            | TypedExpr::Let(_, _, _, ty, _)
            | TypedExpr::Block(_, ty, _)
            | TypedExpr::Unsafe(_, ty, _)
            | TypedExpr::IfElse(_, _, _, ty, _)
            | TypedExpr::MacroCall(_, _, ty, _)
            | TypedExpr::Call(_, _, ty, _)
            | TypedExpr::ObjInit(_, _, ty, _)
            | TypedExpr::FieldAccess(_, _, ty, _)
            | TypedExpr::ArrayInit(_, ty, _)
            | TypedExpr::IndexAccess(_, _, ty, _)
            | TypedExpr::EnumConstruct(_, _, _, _, ty, _)
            | TypedExpr::Match(_, _, ty, _)
            | TypedExpr::Ref(_, _, ty, _)
            | TypedExpr::Deref(_, ty, _)
            | TypedExpr::Closure(_, _, _, ty, _)
            | TypedExpr::Range(_, _, ty, _) => *ty,
            | TypedExpr::DynCall(_, _, _, ty, _) => *ty,
            TypedExpr::CoerceToDyn(_, trait_name, _) => Type::DynTrait(trait_name),
            TypedExpr::CastF32(..) => Type::F32,
            TypedExpr::CastI32(..) => Type::I32,
            TypedExpr::Assign(..)
            | TypedExpr::While(..)
            | TypedExpr::If(..)
            | TypedExpr::Return(..)
            | TypedExpr::FieldAssign(..)
            | TypedExpr::IndexAssign(..)
            | TypedExpr::DerefAssign(..) => Type::Unit,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            TypedExpr::Int(_, s) => s.clone(),
            TypedExpr::Float(_, s) => s.clone(),
            TypedExpr::Ident(_, _, s) => s.clone(),
            TypedExpr::Bool(_, s) => s.clone(),
            TypedExpr::String(_, s) => s.clone(),
            TypedExpr::Add(_, _, _, s)
            | TypedExpr::Sub(_, _, _, s)
            | TypedExpr::Mul(_, _, _, s)
            | TypedExpr::Div(_, _, _, s)
            | TypedExpr::Mod(_, _, _, s)
            | TypedExpr::Ampersand(_, _, _, s)
            | TypedExpr::Pipe(_, _, _, s)
            | TypedExpr::Caret(_, _, _, s)
            | TypedExpr::Shl(_, _, _, s)
            | TypedExpr::Shr(_, _, _, s)
            | TypedExpr::GreaterThan(_, _, s)
            | TypedExpr::LessThan(_, _, s)
            | TypedExpr::GreaterEqual(_, _, s)
            | TypedExpr::LessEqual(_, _, s)
            | TypedExpr::Equal(_, _, s)
            | TypedExpr::NotEqual(_, _, s)
            | TypedExpr::And(_, _, s)
            | TypedExpr::Or(_, _, s) => s.clone(),
            TypedExpr::Neg(_, _, s) | TypedExpr::Not(_, s) => s.clone(),
            TypedExpr::Let(_, _, _, _, s) => s.clone(),
            TypedExpr::Block(_, _, s) => s.clone(),
            TypedExpr::Unsafe(_, _, s) => s.clone(),
            TypedExpr::Assign(_, _, s) => s.clone(),
            TypedExpr::While(_, _, s) => s.clone(),
            TypedExpr::If(_, _, s) => s.clone(),
            TypedExpr::IfElse(_, _, _, _, s) => s.clone(),
            TypedExpr::Return(_, s) => s.clone(),
            TypedExpr::MacroCall(_, _, _, s) => s.clone(),
            TypedExpr::Call(_, _, _, s) => s.clone(),
            TypedExpr::ObjInit(_, _, _, s) => s.clone(),
            TypedExpr::CoerceToDyn(_, _, s) => s.clone(),
            TypedExpr::DynCall(_, _, _, _, s) => s.clone(),
            TypedExpr::FieldAccess(_, _, _, s) => s.clone(),
            TypedExpr::FieldAssign(_, _, _, s) => s.clone(),
            TypedExpr::ArrayInit(_, _, s) => s.clone(),
            TypedExpr::IndexAccess(_, _, _, s) => s.clone(),
            TypedExpr::IndexAssign(_, _, _, s) => s.clone(),
            TypedExpr::EnumConstruct(_, _, _, _, _, s) => s.clone(),
            TypedExpr::Match(_, _, _, s) => s.clone(),
            TypedExpr::CastF32(_, s) | TypedExpr::CastI32(_, s) => s.clone(),
            TypedExpr::Ref(_, _, _, s) => s.clone(),
            TypedExpr::Deref(_, _, s) => s.clone(),
            TypedExpr::DerefAssign(_, _, s) => s.clone(),
            TypedExpr::Closure(_, _, _, _, s) => s.clone(),
            TypedExpr::Range(_, _, _, s) => s.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ModDecl {
    pub path: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct UseDecl {
    pub path: Vec<String>,
    pub alias: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TraitDecl {
    pub name: String,
    pub methods: Vec<FuncDecl>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TraitAliasDecl {
    pub name: String,
    pub traits: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct WhereClause {
    pub target_param: String,
    pub bounds: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ExternFnDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ExternDecl {
    pub abi: String,
    pub functions: Vec<ExternFnDecl>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Program {
    pub mods: Vec<ModDecl>,
    pub uses: Vec<UseDecl>,
    pub traits: Vec<TraitDecl>,
    pub trait_aliases: Vec<TraitAliasDecl>,
    pub externs: Vec<ExternDecl>,
    pub structs: Vec<StructDecl>,
    pub enums: Vec<EnumDecl>,
    pub impls: Vec<ImplDecl>,
    pub functions: Vec<FuncDecl>,
}

#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub where_clause: Option<WhereClause>,
    pub body: Vec<Expr>, // The indented block of code
}

#[derive(Debug)]
pub struct TypedProgram {
    pub traits: Vec<TraitDecl>,
    pub trait_aliases: Vec<TraitAliasDecl>,
    pub externs: Vec<ExternDecl>,
    pub structs: Vec<StructDecl>,
    pub enums: Vec<EnumDecl>,
    pub impls: Vec<ImplDecl>,
    pub functions: Vec<TypedFuncDecl>,
}

#[derive(Debug, Clone)]
pub struct TypedFuncDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub where_clause: Option<WhereClause>,
    pub body: Vec<TypedExpr>,
}
