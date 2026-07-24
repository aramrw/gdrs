use logos::Logos;

// ==========================================
// 1. LEXER (Logos)
// ==========================================
#[derive(Logos, Debug, PartialEq, Eq, Hash, Clone)]
#[logos(skip r"[ \t]+")] // Automatically skip spaces and tabs inline
pub enum Token {
    #[token("let")]
    Let,
    #[token("mut")]
    Mut,
    #[token("=")]
    Assign,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token(">")]
    GreaterThan,
    #[token("<")]
    LessThan,
    #[token("==")]
    Equal,

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
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
    #[token(":")]
    Colon,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

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
    TypeInt,
    #[token("bool")]
    TypeBool,
    #[token("string")]
    TypeString,
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*!", |lex| lex.slice()[..lex.slice().len() - 1].to_string())]
    MacroIdent(String),
}

pub type Span = std::ops::Range<usize>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    String,
    Unit,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug)]
pub enum Expr {
    Int(i64, Span),
    Ident(String, Span),
    Bool(bool, Span),

    Add(Box<Expr>, Box<Expr>, Span),
    Sub(Box<Expr>, Box<Expr>, Span),
    GreaterThan(Box<Expr>, Box<Expr>, Span),
    LessThan(Box<Expr>, Box<Expr>, Span),
    Equal(Box<Expr>, Box<Expr>, Span),

    String(String, Span),

    Let(String, bool, Box<Expr>, Span),
    Block(Vec<Expr>, Span),
    Assign(String, Box<Expr>, Span),
    While(Box<Expr>, Box<Expr>, Span),
    If(Box<Expr>, Box<Expr>, Span),
    MacroCall(String, Vec<Expr>, Span),
    Call(String, Vec<Expr>, Span),
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Int(_, s) => s.clone(),
            Expr::Ident(_, s) => s.clone(),
            Expr::Bool(_, s) => s.clone(),
            Expr::String(_, s) => s.clone(),
            Expr::Add(_, _, s) => s.clone(),
            Expr::Sub(_, _, s) => s.clone(),
            Expr::GreaterThan(_, _, s) => s.clone(),
            Expr::LessThan(_, _, s) => s.clone(),
            Expr::Equal(_, _, s) => s.clone(),
            Expr::Let(_, _, _, s) => s.clone(),
            Expr::Block(_, s) => s.clone(),
            Expr::Assign(_, _, s) => s.clone(),
            Expr::While(_, _, s) => s.clone(),
            Expr::If(_, _, s) => s.clone(),
            Expr::MacroCall(_, _, s) => s.clone(),
            Expr::Call(_, _, s) => s.clone(),
        }
    }
}

// ==========================================
// 2. TYPED AST (Produced by sanal Type Checker)
// ==========================================
#[derive(Debug, Clone)]
pub enum TypedExpr {
    Int(i64, Span),
    Ident(String, Type, Span),
    Bool(bool, Span),
    String(String, Span),

    Add(Box<TypedExpr>, Box<TypedExpr>, Span),
    Sub(Box<TypedExpr>, Box<TypedExpr>, Span),
    GreaterThan(Box<TypedExpr>, Box<TypedExpr>, Span),
    LessThan(Box<TypedExpr>, Box<TypedExpr>, Span),
    Equal(Box<TypedExpr>, Box<TypedExpr>, Span),

    Let(String, bool, Box<TypedExpr>, Type, Span),
    Block(Vec<TypedExpr>, Type, Span),
    Assign(String, Box<TypedExpr>, Span),
    While(Box<TypedExpr>, Box<TypedExpr>, Span),
    If(Box<TypedExpr>, Box<TypedExpr>, Span),
    MacroCall(String, Vec<TypedExpr>, Span),
    Call(String, Vec<TypedExpr>, Type, Span),
}

impl TypedExpr {
    pub fn ty(&self) -> Type {
        match self {
            TypedExpr::Int(..) | TypedExpr::Add(..) | TypedExpr::Sub(..) => Type::Int,
            TypedExpr::Bool(..)
            | TypedExpr::GreaterThan(..)
            | TypedExpr::LessThan(..)
            | TypedExpr::Equal(..) => Type::Bool,
            TypedExpr::String(..) => Type::String,
            TypedExpr::Ident(_, ty, _)
            | TypedExpr::Let(_, _, _, ty, _)
            | TypedExpr::Block(_, ty, _)
            | TypedExpr::Call(_, _, ty, _) => *ty,
            TypedExpr::Assign(..)
            | TypedExpr::While(..)
            | TypedExpr::If(..)
            | TypedExpr::MacroCall(..) => Type::Unit,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            TypedExpr::Int(_, s) => s.clone(),
            TypedExpr::Ident(_, _, s) => s.clone(),
            TypedExpr::Bool(_, s) => s.clone(),
            TypedExpr::String(_, s) => s.clone(),
            TypedExpr::Add(_, _, s) => s.clone(),
            TypedExpr::Sub(_, _, s) => s.clone(),
            TypedExpr::GreaterThan(_, _, s) => s.clone(),
            TypedExpr::LessThan(_, _, s) => s.clone(),
            TypedExpr::Equal(_, _, s) => s.clone(),
            TypedExpr::Let(_, _, _, _, s) => s.clone(),
            TypedExpr::Block(_, _, s) => s.clone(),
            TypedExpr::Assign(_, _, s) => s.clone(),
            TypedExpr::While(_, _, s) => s.clone(),
            TypedExpr::If(_, _, s) => s.clone(),
            TypedExpr::MacroCall(_, _, s) => s.clone(),
            TypedExpr::Call(_, _, _, s) => s.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<FuncDecl>,
}

#[derive(Debug)]
pub struct FuncDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub body: Vec<Expr>, // The indented block of code
}

#[derive(Debug)]
pub struct TypedProgram {
    pub functions: Vec<TypedFuncDecl>,
}

#[derive(Debug, Clone)]
pub struct TypedFuncDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub body: Vec<TypedExpr>,
}
