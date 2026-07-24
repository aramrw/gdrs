use crate::ast::*;
use chumsky::prelude::*;

// ==========================================
// 4. PARSER (Chumsky)
// ==========================================
pub fn parser() -> impl Parser<Token, Program, Error = Simple<Token>> {
    // 1. Individual base literal & identifier parsers
    let int = select! { Token::Int(n) => n }.map_with_span(|n, span| Expr::Int(n, span));
    let boolean = select! { Token::Bool(b) => b }.map_with_span(|b, span| Expr::Bool(b, span));
    let ident = select! { Token::Ident(s) => s }.map_with_span(|s, span| Expr::Ident(s, span));
    let string = select! { Token::String(s) => s }.map_with_span(|s, span| Expr::String(s, span));

    // 2. Binary Operators (+ and -)
    let op = just::<_, _, Simple<Token>>(Token::Plus)
        .to(Expr::Add as fn(_, _, _) -> _)
        .or(just::<_, _, Simple<Token>>(Token::Minus).to(Expr::Sub as fn(_, _, _) -> _))
        .or(just::<_, _, Simple<Token>>(Token::GreaterThan).to(Expr::GreaterThan as fn(_, _, _) -> _))
        .or(just::<_, _, Simple<Token>>(Token::LessThan).to(Expr::LessThan as fn(_, _, _) -> _))
        .or(just::<_, _, Simple<Token>>(Token::Equal).to(Expr::Equal as fn(_, _, _) -> _))
    ;

    // 3. Expression parser with infinite chaining (.foldl) and parenthesized grouping ( ... )
    let math = recursive(|math| {
        let atom = int
            .or(boolean)
            .or(ident)
            .or(string)
            .or(math.delimited_by(just(Token::LParen), just(Token::RParen)));

        atom.clone()
            .then(op.then(atom).repeated())
            .foldl(|lhs, (make_expr, rhs)| {
                let span = lhs.span().start..rhs.span().end;
                make_expr(Box::new(lhs), Box::new(rhs), span)
            })
    });

    // 4. Recursive statement and block parser
    let stmt = recursive(|stmt| {
        let let_stmt = just(Token::Let)
            .ignore_then(just(Token::Mut).or_not())
            .then(select! { Token::Ident(s) => s })
            .then_ignore(just(Token::Assign))
            .then(math.clone())
            .map_with_span(|((is_mut, name), expr), span| {
                Expr::Let(name, is_mut.is_some(), Box::new(expr), span)
            })
            .then_ignore(just(Token::Newline).or_not());

        let assign_stmt = select! { Token::Ident(s) => s }
            .then_ignore(just(Token::Assign))
            .then(math.clone())
            .map_with_span(|(name, expr), span| Expr::Assign(name, Box::new(expr), span))
            .then_ignore(just(Token::Newline).or_not());

        let block = stmt
            .repeated()
            .at_least(1)
            .delimited_by(just(Token::Indent), just(Token::Dedent))
            .map_with_span(|stmts, span| Expr::Block(stmts, span));

        let while_stmt = just(Token::While)
            .ignore_then(math.clone())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(block.clone())
            .map_with_span(|(cond, body), span| Expr::While(Box::new(cond), Box::new(body), span));

        let if_stmt = just(Token::If)
            .ignore_then(math.clone())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(block.clone())
            .map_with_span(|(cond, body), span| Expr::If(Box::new(cond), Box::new(body), span));

        let macro_call = select! { Token::MacroIdent(name) => name }
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|(name, args), span| Expr::MacroCall(name, args, span))
            .then_ignore(just(Token::Newline).or_not());

        let call_stmt = select! { Token::Ident(name) => name }
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|(name, args), span| Expr::Call(name, args, span))
            .then_ignore(just(Token::Newline).or_not());

        let_stmt
            .or(assign_stmt)
            .or(if_stmt)
            .or(while_stmt)
            .or(macro_call)
            .or(call_stmt)
            .or(block)
    });

    let type_parser = select! {
        Token::TypeInt => Type::Int,
        Token::TypeBool => Type::Bool,
        Token::TypeString => Type::String,
    };

    let param = select! { Token::Ident(name) => name }
        .then_ignore(just(Token::Colon))
        .then(type_parser)
        .map_with_span(|(name, ty), span| Param { name, ty, span });

    // Function definition
    let function = just(Token::Fn)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            stmt.repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map(|((name, params), body)| FuncDecl { name, params, body });

    function
        .repeated()
        .then_ignore(end())
        .map(|functions| Program { functions })
}
