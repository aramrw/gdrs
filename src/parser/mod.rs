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
        .then(type_parser.clone())
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

    let enum_variant = select! { Token::Ident(name) => name }
        .then(
            type_parser
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .or_not(),
        )
        .map_with_span(|(name, payload), span| EnumVariantDecl {
            name,
            payload_types: payload.unwrap_or_default(),
            span,
        })
        .then_ignore(just(Token::Newline).or_not());

    let enum_decl = just(Token::Enum)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            enum_variant
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(|(name, variants), span| EnumDecl { name, variants, span });

    let item = function
        .map(Item::Func)
        .or(obj_decl.map(Item::Struct))
        .or(enum_decl.map(Item::Enum));

    item.repeated().then_ignore(end()).map(|items| {
        let mut structs = Vec::new();
        let mut enums = Vec::new();
        let mut functions = Vec::new();
        for item in items {
            match item {
                Item::Func(f) => functions.push(f),
                Item::Struct(s) => structs.push(s),
                Item::Enum(e) => enums.push(e),
            }
        }
        Program {
            structs,
            enums,
            functions,
        }
    })
}

enum Item {
    Func(FuncDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
}
