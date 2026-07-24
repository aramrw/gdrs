#![feature(type_alias_impl_trait)]

pub mod math;
pub mod stmt;

use crate::ast::*;
use chumsky::prelude::*;
use math::{math_parser};
use stmt::{stmt_parser};

// Types
// impl Parser<Token, Expr, Error = Simple<Token>> + Clone + 'a;

// ==========================================
// 4. PARSER (Chumsky)
// ==========================================
pub fn parser() -> impl Parser<Token, Program, Error = Simple<Token>> {
    let type_parser = recursive(|type_parser| {
        let array_type = just(Token::LBracket)
            .ignore_then(type_parser)
            .then_ignore(just(Token::RBracket))
            .map(|t| Type::Array(intern_type(t), 0));

        select! {
            Token::TypeInt => Type::Int,
            Token::TypeFloat => Type::Float,
            Token::TypeBool => Type::Bool,
            Token::TypeString => Type::String,
            Token::Ident(s) => Type::Obj(intern_str(&s)),
        }
        .or(array_type)
    });

    // 3. Math Expression parser with operator precedence hierarchy
    let math = math_parser();

    // 4. Recursive statement and block parser
    let stmt = stmt_parser(math);

    let param = select! { Token::Ident(name) => name }
        .then_ignore(just(Token::Colon))
        .then(type_parser.clone())
        .map_with_span(|(name, ty), span| Param { name, ty, span });

    // Function signature: fn name(params) -> return_type:
    let function = just(Token::Fn)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser.clone()).or_not())
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            stmt.repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map(|(((name, params), opt_ret), body)| FuncDecl {
            name,
            params,
            return_type: opt_ret.unwrap_or(Type::Unit),
            body,
        });

    let field_decl = select! { Token::Ident(name) => name }
        .then_ignore(just(Token::Colon))
        .then(type_parser)
        .map_with_span(|(name, ty), span| FieldDecl { name, ty, span })
        .then_ignore(just(Token::Newline).or_not());

    let obj_decl = just(Token::Obj)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            field_decl
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(|(name, fields), span| StructDecl { name, fields, span });

    let item = function
        .map(Either::Left)
        .or(obj_decl.map(Either::Right));

    item.repeated().then_ignore(end()).map(|items| {
        let mut structs = Vec::new();
        let mut functions = Vec::new();
        for item in items {
            match item {
                Either::Left(f) => functions.push(f),
                Either::Right(s) => structs.push(s),
            }
        }
        Program { structs, functions }
    })
}

enum Either<L, R> {
    Left(L),
    Right(R),
}
