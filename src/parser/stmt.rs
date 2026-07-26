use crate::ast::{Expr, Span, Token, Type};
use chumsky::prelude::*;

// Helper type alias for your math AST variant constructors
type ExprOp = fn(Box<Expr>, Box<Expr>, Span) -> Expr;

pub fn stmt_parser<'a>(
    math: impl Parser<Token, Expr, Error = Simple<Token>> + Clone + 'a,
    type_parser: impl Parser<Token, Type, Error = Simple<Token>> + Clone + 'a,
) -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone + 'a {
    let stmt = recursive(|stmt| {
        let let_stmt = just(Token::Let)
            .ignore_then(just(Token::Mut).or_not())
            .then(select! { Token::Ident(s) => s })
            .then(just(Token::Colon).ignore_then(type_parser.clone()).or_not())
            .then_ignore(just(Token::Assign))
            .then(math.clone())
            .map_with_span(|(((is_mut, name), ty), expr), span| {
                Expr::Let(name, ty, is_mut.is_some(), Box::new(expr), span)
            })
            .then_ignore(just(Token::Newline).or_not());

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

        // Field assignment statement: p.x = 42 or p.x += 10
        let field_assign_stmt = select! { Token::Ident(target) => target }
            .then_ignore(just(Token::Dot))
            .then(select! { Token::Ident(field) => field })
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|(((target, field), op), rhs), span| {
                let target_ident = Expr::Ident(target.clone(), span.clone());
                let final_rhs = match op {
                    Some(make_expr) => {
                        let lhs = Expr::FieldAccess(
                            Box::new(target_ident.clone()),
                            field.clone(),
                            span.clone(),
                        );
                        make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                    }
                    None => rhs,
                };
                Expr::FieldAssign(Box::new(target_ident), field, Box::new(final_rhs), span)
            })
            .then_ignore(just(Token::Newline).or_not());

        let assign_target_expr = path
            .clone()
            .map_with_span(|name, span| Expr::Ident(name, span))
            .then(
                just(Token::Dot)
                    .ignore_then(select! { Token::Ident(f) => f })
                    .repeated(),
            )
            .foldl(|target, field| {
                let span = target.span().clone();
                Expr::FieldAccess(Box::new(target), field, span)
            });

        // Index assignment statement: arr[0] = 42 or self.keys[slot] = key
        let index_assign_stmt = assign_target_expr
            .clone()
            .then_ignore(just(Token::LBracket))
            .then(math.clone())
            .then_ignore(just(Token::RBracket))
            .then(assign_op.clone())
            .then(math.clone())
            .map_with_span(|(((target_expr, idx), op), rhs), span| {
                let final_rhs = match op {
                    Some(make_expr) => {
                        let lhs = Expr::IndexAccess(
                            Box::new(target_expr.clone()),
                            Box::new(idx.clone()),
                            span.clone(),
                        );
                        make_expr(Box::new(lhs), Box::new(rhs), span.clone())
                    }
                    None => rhs,
                };
                Expr::IndexAssign(
                    Box::new(target_expr),
                    Box::new(idx),
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
            .then(
                just(Token::Else)
                    .ignore_then(just(Token::Colon))
                    .then_ignore(just(Token::Newline).or_not())
                    .ignore_then(block.clone())
                    .or_not(),
            )
            .map_with_span(|((cond, then_b), else_b), span| match else_b {
                Some(else_body) => {
                    Expr::IfElse(Box::new(cond), Box::new(then_b), Box::new(else_body), span)
                }
                None => Expr::If(Box::new(cond), Box::new(then_b), span),
            });

        let return_stmt = just(Token::Return)
            .ignore_then(math.clone().or_not())
            .map_with_span(|opt_expr, span| Expr::Return(opt_expr.map(Box::new), span))
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

        let method_call_stmt = select! { Token::Ident(target) => target }
            .then_ignore(just(Token::Dot))
            .then(select! { Token::Ident(method) => method })
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|((target, method), args), span| {
                let mut call_args = vec![Expr::Ident(target, span.clone())];
                call_args.extend(args);
                Expr::Call(method, call_args, span)
            })
            .then_ignore(just(Token::Newline).or_not());

        let call_stmt = path
            .clone()
            .then(
                math.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with_span(|(name, args), span| Expr::Call(name, args, span))
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
            .map_with_span(|(target, arms), span| Expr::Match(Box::new(target), arms, span));

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
                    .or(unsafe_stmt)
                    .or(match_stmt)
                    .or(if_stmt)
                    .or(while_stmt)
                    .or(macro_call)
                    .or(method_call_stmt)
                    .or(call_stmt)
                    .or(math_stmt)
                    .or(block),
            )
            .then_ignore(just(Token::Newline).repeated())
    });

    stmt
}
