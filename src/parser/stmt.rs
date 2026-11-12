use crate::ast::{Expr, Span, Token, TuplePattern, Type};
use crate::parser::math::dot_field_segments_parser;
use chumsky::prelude::*;

// Helper type alias for your math AST variant constructors
type ExprOp = fn(Box<Expr>, Box<Expr>, Span) -> Expr;

pub fn stmt_parser<'a>(
    math: impl Parser<Token, Expr, Error = Simple<Token>> + Clone + 'a,
    type_parser: impl Parser<Token, Type, Error = Simple<Token>> + Clone + 'a,
) -> BoxedParser<'a, Token, Expr, Simple<Token>> {
    let tuple_pattern = recursive(|pat| {
        let ident_pat = just(Token::Mut)
            .or_not()
            .then(select! { Token::Ident(s) => s })
            .map_with_span(|(m, name), span| TuplePattern::Ident {
                name,
                is_mutable: m.is_some(),
                span,
            });
        let tup_pat = pat
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with_span(|items, span| TuplePattern::Tuple(items, span));
        tup_pat.or(ident_pat)
    });

    let stmt = recursive(|stmt| {
        let let_tuple_stmt = just(Token::Let)
            .ignore_then(
                tuple_pattern
                    .clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .map_with_span(|items, span| TuplePattern::Tuple(items, span)),
            )
            .then(just(Token::Colon).ignore_then(type_parser.clone()).or_not())
            .then_ignore(just(Token::Assign))
            .then(math.clone())
            .map_with_span(|((pat, ty), expr), span| {
                Expr::LetTuple(pat, ty, Box::new(expr), span)
            })
            .then_ignore(just(Token::Newline).or_not());

        let let_stmt = just(Token::Let)
            .ignore_then(just(Token::Mut).or_not())
            .then(select! { Token::Ident(s) => s })
            .then(just(Token::Colon).ignore_then(type_parser.clone()).or_not())
            .then_ignore(just(Token::Assign))
            .then(math.clone())
            .map_with_span(|(((is_mut, name), ty), expr), span| {
                Expr::Let(name, ty, is_mut.is_some(), Box::new(expr), span)
            })
            .then_ignore(just(Token::Newline).or_not())
            .or(let_tuple_stmt);

        let path = select! { Token::Ident(s) => s }
            .separated_by(just(Token::ColonColon))
            .at_least(1)
            .map(|parts| parts.join("::"));

        // Parses `=`, `+=`, `-=`, `*=`, `/=`
        let assign_op = just(Token::Assign)
            .to(None)
            .or(just(Token::PlusEqual).to(Some(Expr::Add as ExprOp)))
            .or(just(Token::MinusEqual).to(Some(Expr::Sub as ExprOp)))
            .or(just(Token::StarEqual).to(Some(Expr::Mul as ExprOp)))
            .or(just(Token::SlashEqual).to(Some(Expr::Div as ExprOp)));

        let field_target_expr = path
            .clone()
            .map_with_span(|name, span| Expr::Ident(name, span))
            .then(dot_field_segments_parser().repeated().at_least(1))
            .foldl(|target, fields| {
                let mut cur = target;
                for field in fields {
                    let span = cur.span().clone();
                    cur = Expr::FieldAccess(Box::new(cur), field, span);
                }
                cur
            });

        // Field assignment statement: p.x = 42 or p.pos.x += 10
        let field_assign_stmt = field_target_expr
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|((target_expr, op), rhs), span| {
                if let Expr::FieldAccess(inner_target, field, _) = target_expr {
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
            })
            .then_ignore(just(Token::Newline).or_not());

        enum AccessPost {
            Fields(Vec<String>, Span),
            Index(Expr, Span),
        }

        let field_post = dot_field_segments_parser()
            .map_with_span(|fs, span| AccessPost::Fields(fs, span));

        let index_post = math
            .clone()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map_with_span(|idx, span| AccessPost::Index(idx, span));

        let assign_target_expr = path
            .clone()
            .map_with_span(|name, span| Expr::Ident(name, span))
            .then(field_post.or(index_post).repeated())
            .foldl(|target, post| match post {
                AccessPost::Fields(fields, span) => {
                    let mut cur = target;
                    for field in fields {
                        cur = Expr::FieldAccess(Box::new(cur), field, span.clone());
                    }
                    cur
                }
                AccessPost::Index(idx, span) => Expr::IndexAccess(Box::new(target), Box::new(idx), span),
            });

        // Index assignment statement: arr[0] = 42, self.keys[slot] = key, or arr[i][j] = val
        // assign_target_expr greedily consumes all postfix accesses including the
        // final [index], so we decompose the resulting IndexAccess here.
        let index_assign_stmt = assign_target_expr
            .clone()
            .try_map(|expr, span| match expr {
                Expr::IndexAccess(target, idx, _) => Ok((target, idx)),
                _ => Err(Simple::custom(span, "expected index access as assignment target")),
            })
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|(((target_expr, idx), op), rhs), span| {
                let final_rhs = match op {
                    Some(make_expr) => {
                        let lhs = Expr::IndexAccess(
                            target_expr.clone(),
                            idx.clone(),
                            span.clone(),
                        );
                        make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                    }
                    None => rhs,
                };
                Expr::IndexAssign(
                    target_expr,
                    idx,
                    Box::new(final_rhs),
                    span,
                )
            })
            .then_ignore(just(Token::Newline).or_not());

        // Standard variable assignment: x = 10 or x += 5
        let assign_stmt = select! { Token::Ident(s) => s }
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|((name, op), rhs), span| {
                let final_rhs = match op {
                    Some(make_expr) => {
                        let lhs = Expr::Ident(name.clone(), span.clone());
                        make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                    }
                    None => rhs,
                };
                Expr::Assign(name, Box::new(final_rhs), span)
            })
            .then_ignore(just(Token::Newline).or_not());

        let block = stmt
            .repeated()
            .at_least(1)
            .delimited_by(just(Token::Indent), just(Token::Dedent))
            .map_with_span(|stmts, span| Expr::Block(stmts, span))
            .boxed();

        let while_stmt = just(Token::While)
            .ignore_then(math.clone())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(block.clone())
            .map_with_span(|(cond, body), span| Expr::While(Box::new(cond), Box::new(body), span));

        let for_stmt = just(Token::For)
            .ignore_then(tuple_pattern.clone())
            .then_ignore(just(Token::In))
            .then(math.clone())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(block.clone())
            .map_with_span(|((pat, iter_expr), body_block), span| {
                let body_stmts = match body_block {
                    Expr::Block(stmts, _) => stmts,
                    single => vec![single],
                };
                match pat {
                    TuplePattern::Ident {
                        name,
                        is_mutable: false,
                        ..
                    } => crate::parser::math::lower_for_loop(name, iter_expr, body_stmts, span),
                    other_pat => {
                        let tmp = "__for_item".to_string();
                        let mut wrapped = Vec::with_capacity(body_stmts.len() + 1);
                        wrapped.push(Expr::LetTuple(
                            other_pat,
                            None,
                            Box::new(Expr::Ident(tmp.clone(), span.clone())),
                            span.clone(),
                        ));
                        wrapped.extend(body_stmts);
                        crate::parser::math::lower_for_loop(tmp, iter_expr, wrapped, span)
                    }
                }
            })
            .boxed();

        let if_stmt = recursive(|if_s| {
            let else_if_branch = just(Token::Else).ignore_then(if_s);
            let else_block_branch = just(Token::Else)
                .ignore_then(just(Token::Colon))
                .ignore_then(just(Token::Newline).or_not())
                .ignore_then(block.clone());

            just(Token::If)
                .ignore_then(math.clone())
                .then_ignore(just(Token::Colon))
                .then_ignore(just(Token::Newline).or_not())
                .then(block.clone())
                .then(else_if_branch.or(else_block_branch).or_not())
                .map_with_span(|((cond, then_b), else_b), span| match else_b {
                    Some(else_body) => {
                        Expr::IfElse(Box::new(cond), Box::new(then_b), Box::new(else_body), span)
                    }
                    None => Expr::If(Box::new(cond), Box::new(then_b), span),
                })
        })
        .boxed();

        let return_stmt = just(Token::Return)
            .ignore_then(math.clone().or_not())
            .map_with_span(|opt_expr, span| Expr::Return(opt_expr.map(Box::new), span))
            .then_ignore(just(Token::Newline).or_not());

        let break_stmt = just(Token::Break)
            .map_with_span(|_, span| Expr::Break(span))
            .then_ignore(just(Token::Newline).or_not());

        let continue_stmt = just(Token::Continue)
            .map_with_span(|_, span| Expr::Continue(span))
            .then_ignore(just(Token::Newline).or_not());

        let macro_call = select! { Token::MacroIdent(name) => name }
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|(name, args), span| Expr::MacroCall(name, args, span))
            .then_ignore(just(Token::Newline).or_not());

        let unsafe_stmt = just(Token::Unsafe)
            .ignore_then(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(block.clone())
            .map_with_span(|(_, body_expr), span| match body_expr {
                Expr::Block(stmts, _) => Expr::Unsafe(stmts, span),
                other => Expr::Unsafe(vec![other], span),
            });

        let arm_pattern = select! { Token::Ident(s) if s == "_" => s }
            .then(empty().to(Vec::new()))
            .or(path.clone().then(
                select! { Token::Ident(s) => s }
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not()
                    .map(|opt| opt.unwrap_or_default()),
            ));

        let match_arm = arm_pattern
            .then_ignore(just(Token::FatArrow))
            .then_ignore(just(Token::Newline).or_not())
            .then(math.clone().or(block.clone()))
            .map_with_span(|((variant_name, bindings), body_expr), span| {
                let body = match body_expr {
                    Expr::Block(stmts, _) => stmts,
                    other => vec![other],
                };
                crate::ast::MatchArm {
                    variant_name,
                    bindings,
                    body,
                    span,
                }
            })
            .then_ignore(just(Token::Newline).repeated());

        let match_stmt = just(Token::Match)
            .ignore_then(math.clone())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline).or_not())
            .then(
                match_arm
                    .repeated()
                    .at_least(1)
                    .delimited_by(just(Token::Indent), just(Token::Dedent)),
            )
            .map_with_span(|(target, arms), span| Expr::Match(Box::new(target), arms, span))
            .boxed();

        let deref_assign_stmt = just(Token::Star)
            .ignore_then(math.clone())
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|((ptr, op), rhs), span| {
                let final_rhs = match op {
                    Some(make_expr) => {
                        let lhs = Expr::Deref(Box::new(ptr.clone()), span.clone());
                        make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                    }
                    None => rhs,
                };
                Expr::DerefAssign(Box::new(ptr), Box::new(final_rhs), span)
            })
            .then_ignore(just(Token::Newline).or_not());

        let math_stmt = math.clone().then_ignore(just(Token::Newline).or_not());

        just(Token::Newline)
            .repeated()
            .ignore_then(
                deref_assign_stmt
                    .or(let_stmt)
                    .or(index_assign_stmt)
                    .or(field_assign_stmt)
                    .or(assign_stmt)
                    .or(return_stmt)
                    .or(break_stmt)
                    .or(continue_stmt)
                    .or(unsafe_stmt)
                    .or(match_stmt)
                    .or(if_stmt)
                    .or(while_stmt)
                    .or(for_stmt)
                    .or(macro_call)
                    .or(math_stmt)
                    .or(block),
            )
            .then_ignore(just(Token::Newline).repeated())
    });

    stmt.boxed()
}
