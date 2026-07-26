use crate::ast::{Expr, Span, Token};
use chumsky::prelude::*;

pub fn math_parser<'a>() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone + 'a {
    // 1. Individual base literal & identifier parsers
    let int = select! { Token::Int(n) => n }.map_with_span(|n, span| Expr::Int(n, span));
    let float_lit = select! { Token::Float(bits) => f64::from_bits(bits) }
        .map_with_span(|f, span| Expr::Float(f, span));
    let boolean = select! { Token::Bool(b) => b }.map_with_span(|b, span| Expr::Bool(b, span));
    let string = select! { Token::String(s) => s }.map_with_span(|s, span| Expr::String(s, span));

    let shift_op = just::<_, _, Simple<Token>>(Token::Shl)
        .to(Expr::Shl as fn(_, _, _) -> _)
        .or(just(Token::Shr).to(Expr::Shr as fn(_, _, _) -> _));

    let bitwise_op = just::<_, _, Simple<Token>>(Token::Ampersand)
        .to(Expr::Ampersand as fn(_, _, _) -> _)
        .or(just(Token::Caret).to(Expr::Caret as fn(_, _, _) -> _))
        .or(just(Token::Pipe).to(Expr::Pipe as fn(_, _, _) -> _));

    // 2. Operators by Precedence
    let mul_op = just::<_, _, Simple<Token>>(Token::Star)
        .to(Expr::Mul as fn(_, _, _) -> _)
        .or(just(Token::Slash).to(Expr::Div as fn(_, _, _) -> _))
        .or(just(Token::Percent).to(Expr::Mod as fn(_, _, _) -> _));

    let add_op = just::<_, _, Simple<Token>>(Token::Plus)
        .to(Expr::Add as fn(_, _, _) -> _)
        .or(just(Token::Minus).to(Expr::Sub as fn(_, _, _) -> _));

    let comp_op = just::<_, _, Simple<Token>>(Token::Equal)
        .to(Expr::Equal as fn(_, _, _) -> _)
        .or(just(Token::NotEqual).to(Expr::NotEqual as fn(_, _, _) -> _))
        .or(just(Token::GreaterEqual).to(Expr::GreaterEqual as fn(_, _, _) -> _))
        .or(just(Token::LessEqual).to(Expr::LessEqual as fn(_, _, _) -> _))
        .or(just(Token::GreaterThan).to(Expr::GreaterThan as fn(_, _, _) -> _))
        .or(just(Token::LessThan).to(Expr::LessThan as fn(_, _, _) -> _));

    let logic_op = just::<_, _, Simple<Token>>(Token::And)
        .to(Expr::And as fn(_, _, _) -> _)
        .or(just(Token::Or).to(Expr::Or as fn(_, _, _) -> _));

    // The recursive core
    recursive(|math| {
        let field_init = select! { Token::Ident(s) => s }
            .then_ignore(just(Token::Colon))
            .then(math.clone());

        let path_segment = select! {
            Token::Ident(s) => s,
            Token::TypeRc => "rc".to_string(),
            Token::TypeArc => "arc".to_string(),
        };

        let path = path_segment
            .separated_by(just(Token::ColonColon))
            .at_least(1)
            .map(|parts| parts.join("::"));

        let struct_init = path
            .clone()
            .then(
                field_init
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LBrace), just(Token::RBrace)),
            )
            .map_with_span(|(name, fields), span| Expr::ObjInit(name, fields, span));

        let call_expr = path
            .clone()
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|(name, args), span| Expr::Call(name, args, span));

        let array_init = math
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map_with_span(|elems, span| Expr::ArrayInit(elems, span));

        let macro_call = select! { Token::MacroIdent(name) => name }
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|(name, args), span| Expr::MacroCall(name, args, span));

        let ident = path.map_with_span(|name, span| Expr::Ident(name, span));

        let closure_params = select! { Token::Ident(s) => s }
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::Pipe), just(Token::Pipe))
            .or(just(Token::Pipe).then(just(Token::Pipe)).to(Vec::new()));

        let closure_block = closure_params
            .clone()
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(
                math.clone()
                    .delimited_by(just(Token::Indent), just(Token::Dedent))
                    .or(math.clone()),
            )
            .map_with_span(|(params, body), span| Expr::Closure(params, Box::new(body), span));

        let closure_expr = closure_params
            .then(math.clone())
            .map_with_span(|(params, body), span| Expr::Closure(params, Box::new(body), span));

        let atom = closure_block
            .or(closure_expr)
            .or(string)
            .or(float_lit)
            .or(int)
            .or(boolean)
            .or(macro_call)
            .or(struct_init)
            .or(call_expr)
            .or(array_init)
            .or(ident)
            .or(math
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)));

        #[derive(Clone)]
        enum Postfix {
            DotCall(String, Vec<Expr>, Span),
            Dot(String, Span),
            Index(Expr, Span),
            Try(Span),
        }

        let dot_call_post = just(Token::Dot)
            .ignore_then(select! { Token::Ident(s) => s })
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|(method, args), span: Span| Postfix::DotCall(method, args, span));

        let dot_post = just(Token::Dot)
            .ignore_then(select! { Token::Ident(s) => s })
            .map_with_span(|field, span: Span| Postfix::Dot(field, span));

        let index_post = math
            .clone()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map_with_span(|idx, span: Span| Postfix::Index(idx, span));

        let try_post = just(Token::Question)
            .map_with_span(|_, span: Span| Postfix::Try(span));

        let postfix_atom = atom
            .then(dot_call_post.or(dot_post).or(index_post).or(try_post).repeated())
            .foldl(|target, post| match post {
                Postfix::DotCall(method, args, method_span) => {
                    let span = target.span().start..method_span.end;
                    let mut call_args = vec![target];
                    call_args.extend(args);
                    Expr::Call(method, call_args, span)
                }
                Postfix::Dot(field, field_span) => {
                    let span = target.span().start..field_span.end;
                    Expr::FieldAccess(Box::new(target), field, span)
                }
                Postfix::Index(idx, idx_span) => {
                    let span = target.span().start..idx_span.end;
                    Expr::IndexAccess(Box::new(target), Box::new(idx), span)
                }
                Postfix::Try(try_span) => {
                    let span = target.span().start..try_span.end;
                    Expr::Try(Box::new(target), span)
                }
            });

        let neg = just(Token::Minus)
            .ignore_then(postfix_atom.clone())
            .map_with_span(|expr, span| Expr::Neg(Box::new(expr), span));

        let not = just(Token::Exclamation)
            .or(just(Token::Not))
            .ignore_then(postfix_atom.clone())
            .map_with_span(|expr, span| Expr::Not(Box::new(expr), span));

        let deref = just(Token::Star)
            .ignore_then(postfix_atom.clone())
            .map_with_span(|expr, span| Expr::Deref(Box::new(expr), span));

        let reference = just(Token::Ampersand)
            .then(just(Token::Mut).or_not())
            .then(postfix_atom.clone())
            .map_with_span(|((_, opt_mut), expr), span| {
                Expr::Ref(Box::new(expr), opt_mut.is_some(), span)
            });

        let unary = neg.or(not).or(deref).or(reference).or(postfix_atom);

        let factor =
            unary
                .clone()
                .then(mul_op.then(unary).repeated())
                .foldl(|lhs, (make_expr, rhs)| {
                    let span = lhs.span().start..rhs.span().end;
                    make_expr(Box::new(lhs), Box::new(rhs), span)
                });

        let term =
            factor
                .clone()
                .then(add_op.then(factor).repeated())
                .foldl(|lhs, (make_expr, rhs)| {
                    let span = lhs.span().start..rhs.span().end;
                    make_expr(Box::new(lhs), Box::new(rhs), span)
                });

        let range_term = term
            .clone()
            .then(just(Token::DotDot).then(term.clone()).or_not())
            .map(|(lhs, opt_rhs)| match opt_rhs {
                Some((_, rhs)) => {
                    let span = lhs.span().start..rhs.span().end;
                    Expr::Range(Box::new(lhs), Box::new(rhs), span)
                }
                None => lhs,
            });

        // 1. Shift operations (<<, >>) - Binds looser than +, - but tighter than comparisons
        let shift_term =
            range_term.clone()
                .then(shift_op.then(range_term).repeated())
                .foldl(|lhs, (make_expr, rhs)| {
                    let span = lhs.span().start..rhs.span().end;
                    make_expr(Box::new(lhs), Box::new(rhs), span)
                }).boxed();

        // 2. Bitwise operations (&, ^, |) - Binds looser than shifts but tighter than comparisons
        let bitwise_term = shift_term
            .clone()
            .then(bitwise_op.then(shift_term).repeated())
            .foldl(|lhs, (make_expr, rhs)| {
                let span = lhs.span().start..rhs.span().end;
                make_expr(Box::new(lhs), Box::new(rhs), span)
            }).boxed();

        // 3. Comparisons (<, >, ==, etc.) - Updated to use `bitwise_term`
        let comp = bitwise_term
            .clone()
            .then(comp_op.then(bitwise_term).repeated())
            .foldl(|lhs, (make_expr, rhs)| {
                let span = lhs.span().start..rhs.span().end;
                make_expr(Box::new(lhs), Box::new(rhs), span)
            });

        comp.clone()
            .then(logic_op.then(comp).repeated())
            .foldl(|lhs, (make_expr, rhs)| {
                let span = lhs.span().start..rhs.span().end;
                make_expr(Box::new(lhs), Box::new(rhs), span)
            })
    })
}
