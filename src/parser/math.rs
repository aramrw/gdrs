use crate::ast::{Expr, Span, Token};
use chumsky::prelude::*;

/// Lowers a `for item in iter_expr:` / `iter_expr.for_each(|item|: ...)` loop cleanly.
/// Static/inline `start..end` ranges lower to a native register counter `while` loop
/// with zero heap allocation; all other iterables use `into_iter()` + `next()`.
pub fn lower_for_loop(
    item_name: String,
    iter_expr: Expr,
    body_stmts: Vec<Expr>,
    span: Span,
) -> Expr {
    static LOOP_COUNTER: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);
    let loop_id = LOOP_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);

    if let Expr::Range(start, end, range_span) = iter_expr {
        let idx_var = format!("__range_idx_{loop_id}");
        let end_var = format!("__range_end_{loop_id}");

        let mut while_body = Vec::with_capacity(body_stmts.len() + 2);
        if item_name != "_" {
            while_body.push(Expr::Let(
                item_name,
                None,
                false,
                Box::new(Expr::Ident(idx_var.clone(), range_span.clone())),
                range_span.clone(),
            ));
        }
        while_body.push(Expr::Assign(
            idx_var.clone(),
            Box::new(Expr::Add(
                Box::new(Expr::Ident(idx_var.clone(), range_span.clone())),
                Box::new(Expr::Int(1, range_span.clone())),
                range_span.clone(),
            )),
            range_span.clone(),
        ));
        while_body.extend(body_stmts);

        return Expr::Block(
            vec![
                Expr::Let(idx_var.clone(), None, true, start, range_span.clone()),
                Expr::Let(end_var.clone(), None, false, end, range_span.clone()),
                Expr::While(
                    Box::new(Expr::LessThan(
                        Box::new(Expr::Ident(idx_var, range_span.clone())),
                        Box::new(Expr::Ident(end_var, range_span.clone())),
                        range_span.clone(),
                    )),
                    Box::new(Expr::Block(while_body, span.clone())),
                    span.clone(),
                ),
            ],
            span,
        );
    }

    let iter_var = format!("__iter_{loop_id}");
    let mut arm_body = body_stmts;
    arm_body.push(Expr::Bool(true, span.clone()));

    let match_cond = Expr::Match(
        Box::new(Expr::Call(
            ".next".to_string(),
            vec![Expr::Ident(iter_var.clone(), span.clone())],
            span.clone(),
        )),
        vec![
            crate::ast::MatchArm {
                variant_name: "Some".to_string(),
                bindings: vec![item_name],
                body: arm_body,
                span: span.clone(),
            },
            crate::ast::MatchArm {
                variant_name: "_".to_string(),
                bindings: vec![],
                body: vec![Expr::Bool(false, span.clone())],
                span: span.clone(),
            },
        ],
        span.clone(),
    );

    let init_iter = match &iter_expr {
        Expr::Call(name, _, _)
            if {
                let s = name.strip_prefix('.').unwrap_or(name);
                s == "into_iter" || s.ends_with("_iter")
            } =>
        {
            iter_expr
        }
        _ => Expr::Call(".into_iter".to_string(), vec![iter_expr], span.clone()),
    };

    Expr::Block(
        vec![
            Expr::Let(iter_var, None, true, Box::new(init_iter), span.clone()),
            Expr::While(
                Box::new(match_cond),
                Box::new(Expr::Block(vec![], span.clone())),
                span.clone(),
            ),
        ],
        span,
    )
}

/// Parses `.ident`, `.0`, or `.0.1` (lexed as Float after `.`) into field name segments.
pub(crate) fn dot_field_segments_parser<'a>(
) -> impl Parser<Token, Vec<String>, Error = Simple<Token>> + Clone + 'a {
    just(Token::Dot).ignore_then(select! {
        Token::Ident(s) => vec![s],
        Token::Int(n) if n >= 0 => vec![n.to_string()],
        Token::Float(raw) => raw.split('.').map(|s| s.to_string()).collect(),
    })
}

pub fn math_parser<'a>(
    type_parser: impl Parser<Token, crate::ast::Type, Error = Simple<Token>> + Clone + 'a,
) -> BoxedParser<'a, Token, Expr, Simple<Token>> {
    // 1. Individual base literal & identifier parsers
    let int = select! { Token::Int(n) => n }.map_with_span(|n, span| Expr::Int(n, span));
    let float_lit = select! { Token::Float(raw) => raw.parse::<f64>().unwrap() }
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

        let layout_junk = just(Token::Newline)
            .or(just(Token::Indent))
            .or(just(Token::Dedent))
            .repeated();

        let struct_init = path
            .clone()
            .then(
                layout_junk.clone().ignore_then(
                    field_init
                        .padded_by(layout_junk.clone())
                        .separated_by(just(Token::Comma).then_ignore(layout_junk.clone()))
                        .allow_trailing(),
                )
                .then_ignore(layout_junk.clone())
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
            )
            .map_with_span(|(name, fields), span| Expr::ObjInit(name, fields, span));

        let parenthesized_args = layout_junk.clone()
            .ignore_then(
                math.clone()
                    .padded_by(layout_junk.clone())
                    .separated_by(just(Token::Comma).then_ignore(layout_junk.clone()))
                    .allow_trailing(),
            )
            .then_ignore(layout_junk.clone())
            .delimited_by(just(Token::LParen), just(Token::RParen));

        let bracketed_args = layout_junk.clone()
            .ignore_then(
                math.clone()
                    .padded_by(layout_junk.clone())
                    .separated_by(just(Token::Comma).then_ignore(layout_junk.clone()))
                    .allow_trailing(),
            )
            .then_ignore(layout_junk.clone())
            .delimited_by(just(Token::LBracket), just(Token::RBracket));

        let call_expr = path
            .clone()
            .then(parenthesized_args.clone())
            .map_with_span(|(name, args), span| Expr::Call(name, args, span));

        let array_init = bracketed_args
            .clone()
            .map_with_span(|elems, span| Expr::ArrayInit(elems, span));

        let macro_args = parenthesized_args.clone().or(bracketed_args.clone());

        let macro_call = select! { Token::MacroIdent(name) => name }
            .then(macro_args)
            .map_with_span(|(name, args), span| Expr::MacroCall(name, args, span));

        let ident = path.clone().map_with_span(|name, span| Expr::Ident(name, span));

        let closure_params = select! { Token::Ident(s) => s }
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::Pipe), just(Token::Pipe))
            .or(just(Token::Pipe).then(just(Token::Pipe).then(just(Token::Colon))).to(Vec::new()));

        type ExprOp = fn(Box<Expr>, Box<Expr>, Span) -> Expr;

        let assign_op = just(Token::Assign)
            .to(None)
            .or(just(Token::PlusEqual).to(Some(Expr::Add as ExprOp)))
            .or(just(Token::MinusEqual).to(Some(Expr::Sub as ExprOp)))
            .or(just(Token::StarEqual).to(Some(Expr::Mul as ExprOp)))
            .or(just(Token::SlashEqual).to(Some(Expr::Div as ExprOp)));

        let simple_assign_stmt = select! { Token::Ident(s) => s }
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|((name, op), rhs), span: Span| {
                let final_rhs = match op {
                    Some(make_expr) => {
                        let lhs = Expr::Ident(name.clone(), span.clone());
                        make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                    }
                    None => rhs,
                };
                Expr::Assign(name, Box::new(final_rhs), span)
            });

        enum AccessPost {
            Field(String, Span),
            Index(Expr, Span),
        }

        let field_post = just(Token::Dot)
            .ignore_then(select! { Token::Ident(f) => f })
            .map_with_span(|f, span| AccessPost::Field(f, span));

        let index_post = math
            .clone()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map_with_span(|idx, span| AccessPost::Index(idx, span));

        let assign_target_expr = path
            .clone()
            .map_with_span(|name, span| Expr::Ident(name, span))
            .then(field_post.or(index_post).repeated())
            .foldl(|target, post| match post {
                AccessPost::Field(field, span) => Expr::FieldAccess(Box::new(target), field, span),
                AccessPost::Index(idx, span) => Expr::IndexAccess(Box::new(target), Box::new(idx), span),
            });

        let target_expr = path
            .clone()
            .map_with_span(|name, span: Span| Expr::Ident(name, span))
            .then(
                just(Token::Dot)
                    .ignore_then(select! { Token::Ident(f) => f })
                    .repeated()
                    .at_least(1),
            )
            .foldl(|target, field| {
                let span = target.span().clone();
                Expr::FieldAccess(Box::new(target), field, span)
            });

        let index_assign_stmt = assign_target_expr
            .clone()
            .try_map(|expr, span| match expr {
                Expr::IndexAccess(target, idx, _) => Ok((target, idx)),
                _ => Err(Simple::custom(span, "expected index access as assignment target")),
            })
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|(((target, idx), op), rhs), span: Span| {
                let final_rhs = match op {
                    Some(make_expr) => {
                        let lhs = Expr::IndexAccess(
                            target.clone(),
                            idx.clone(),
                            span.clone(),
                        );
                        make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                    }
                    None => rhs,
                };
                Expr::IndexAssign(target, idx, Box::new(final_rhs), span)
            });

        let field_assign_stmt = target_expr
            .clone()
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|((target, op), rhs), span: Span| {
                if let Expr::FieldAccess(inner_target, field, _) = target {
                    let final_rhs = match op {
                        Some(make_expr) => {
                            let lhs = Expr::FieldAccess(
                                inner_target.clone(),
                                field.clone(),
                                span.clone(),
                            );
                            make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                        }
                        None => rhs,
                    };
                    Expr::FieldAssign(inner_target, field, Box::new(final_rhs), span)
                } else {
                    unreachable!()
                }
            });

        let let_stmt = just(Token::Let)
            .ignore_then(just(Token::Mut).or_not())
            .then(select! { Token::Ident(s) => s })
            .then_ignore(just(Token::Assign))
            .then(math.clone())
            .map_with_span(|((is_mut, name), rhs), span: Span| {
                Expr::Let(name, None, is_mut.is_some(), Box::new(rhs), span)
            });

        let closure_stmt = let_stmt
            .or(index_assign_stmt)
            .or(field_assign_stmt)
            .or(simple_assign_stmt)
            .or(math.clone());

        let closure_block_body = closure_stmt
            .then_ignore(just(Token::Newline).repeated())
            .repeated()
            .at_least(1)
            .delimited_by(just(Token::Indent), just(Token::Dedent))
            .map_with_span(|exprs, span: Span| {
                if exprs.len() == 1 {
                    exprs.into_iter().next().unwrap()
                } else {
                    Expr::Block(exprs, span)
                }
            })
            .or(math.clone());

        let closure_block = closure_params
            .clone()
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(closure_block_body)
            .map_with_span(|(params, body), span| Expr::Closure(params, Box::new(body), span));

        let closure_expr = closure_params
            .then(math.clone())
            .map_with_span(|(params, body), span| Expr::Closure(params, Box::new(body), span));

        let paren_or_tuple = just(Token::LParen)
            .ignore_then(
                math.clone()
                    .then(
                        just(Token::Comma)
                            .ignore_then(
                                math.clone()
                                    .separated_by(just(Token::Comma))
                                    .allow_trailing(),
                            )
                            .or_not(),
                    )
                    .or_not(),
            )
            .then_ignore(just(Token::RParen))
            .map_with_span(|opt, span| match opt {
                None => Expr::TupleInit(Vec::new(), span),
                Some((first, None)) => first,
                Some((first, Some(rest))) => {
                    let mut elems = Vec::with_capacity(1 + rest.len());
                    elems.push(first);
                    elems.extend(rest);
                    Expr::TupleInit(elems, span)
                }
            });

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
            .or(paren_or_tuple)
            .boxed();

        #[derive(Clone)]
        enum Postfix {
            DotCall(String, Vec<Expr>, Span),
            Dot(Vec<String>, Span),
            Index(Expr, Span),
            Try(Span),
        }

        let dot_call_post = just(Token::Dot)
            .ignore_then(select! { Token::Ident(s) => s })
            .then(parenthesized_args.clone())
            .map_with_span(|(method, args), span: Span| Postfix::DotCall(method, args, span));

        let dot_post = dot_field_segments_parser()
            .map_with_span(|fields, span: Span| Postfix::Dot(fields, span));

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
                    if method == "for_each" && args.len() == 1 {
                        if let Expr::Closure(params, closure_body, _) = &args[0] {
                            let item_name =
                                params.first().cloned().unwrap_or_else(|| "_".to_string());
                            let body_stmts = match closure_body.as_ref() {
                                Expr::Block(stmts, _) => stmts.clone(),
                                single => vec![single.clone()],
                            };
                            lower_for_loop(item_name, target, body_stmts, span)
                        } else {
                            let mut call_args = vec![target];
                            call_args.extend(args);
                            Expr::Call(format!(".{method}"), call_args, span)
                        }
                    } else {
                        let mut call_args = vec![target];
                        call_args.extend(args);
                        Expr::Call(format!(".{method}"), call_args, span)
                    }
                }
                Postfix::Dot(fields, field_span) => {
                    let mut cur = target;
                    for field in fields {
                        let span = cur.span().start..field_span.end;
                        cur = Expr::FieldAccess(Box::new(cur), field, span);
                    }
                    cur
                }
                Postfix::Index(idx, idx_span) => {
                    let span = target.span().start..idx_span.end;
                    Expr::IndexAccess(Box::new(target), Box::new(idx), span)
                }
                Postfix::Try(try_span) => {
                    let span = target.span().start..try_span.end;
                    Expr::Try(Box::new(target), span)
                }
            })
            .boxed();

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

        let unary = neg.or(not).or(deref).or(reference).or(postfix_atom).boxed();

        let cast = unary
            .then(
                just(Token::As)
                    .ignore_then(type_parser.clone())
                    .repeated(),
            )
            .foldl(|expr, target_ty| {
                let span = expr.span();
                Expr::Cast(Box::new(expr), target_ty, span)
            })
            .boxed();

        let factor =
            cast.clone()
                .then(mul_op.then(cast).repeated())
                .foldl(|lhs, (make_expr, rhs)| {
                    let span = lhs.span().start..rhs.span().end;
                    make_expr(Box::new(lhs), Box::new(rhs), span)
                })
                .boxed();

        let term =
            factor
                .clone()
                .then(add_op.then(factor).repeated())
                .foldl(|lhs, (make_expr, rhs)| {
                    let span = lhs.span().start..rhs.span().end;
                    make_expr(Box::new(lhs), Box::new(rhs), span)
                })
                .boxed();

        let range_term = term
            .clone()
            .then(just(Token::DotDot).then(term.clone()).or_not())
            .map(|(lhs, opt_rhs)| match opt_rhs {
                Some((_, rhs)) => {
                    let span = lhs.span().start..rhs.span().end;
                    Expr::Range(Box::new(lhs), Box::new(rhs), span)
                }
                None => lhs,
            })
            .boxed();

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
            })
            .boxed();

        comp.clone()
            .then(logic_op.then(comp).repeated())
            .foldl(|lhs, (make_expr, rhs)| {
                let span = lhs.span().start..rhs.span().end;
                make_expr(Box::new(lhs), Box::new(rhs), span)
            })
    })
    .boxed()
}
