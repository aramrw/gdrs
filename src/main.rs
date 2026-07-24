mod ast;
mod cli;
mod codegen;
mod compiler;
mod diagnostics;
mod parser;
mod sanal;

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::Parser; // Stream is imported directly below
use clap::Parser as ClapParser;
use logos::Logos;
use std::fs::read_to_string;

use crate::{
    ast::{Span, Token},
    cli::Cli,
};

// 1. UPDATE: Accept and return tuples of (Token, Span)
pub fn inject_indentation(tokens: Vec<(Token, Span)>) -> Vec<(Token, Span)> {
    let mut processed = Vec::new();
    let mut indent_stack = vec![0];

    let mut iter = tokens.into_iter().peekable();

    while let Some((token, span)) = iter.next() {
        if let Token::NewlineWithIndent(spaces) = token {
            // Ignore blank lines (lines with only whitespace before another newline or EOF)
            if matches!(iter.peek(), Some((Token::NewlineWithIndent(_), _)) | None) {
                continue;
            }

            let current_indent = *indent_stack.last().unwrap();

            // Avoid duplicate newlines
            if let Some((last_tok, _)) = processed.last() {
                if !matches!(last_tok, Token::Newline | Token::Indent | Token::Dedent) {
                    processed.push((Token::Newline, span.clone()));
                }
            }

            if spaces > current_indent {
                indent_stack.push(spaces);
                processed.push((Token::Indent, span.clone()));
            } else if spaces < current_indent {
                while *indent_stack.last().unwrap() > spaces {
                    indent_stack.pop();
                    processed.push((Token::Dedent, span.clone()));
                }
            }
        } else {
            processed.push((token, span));
        }
    }

    let eof_span = processed.last().map(|(_, s)| s.clone()).unwrap_or(0..0);
    while indent_stack.len() > 1 {
        indent_stack.pop();
        processed.push((Token::Dedent, eof_span.clone()));
    }

    processed
}

fn main() {
    let cli = Cli::parse();

    // compile loop
    for src in cli.srcs {
        let fstring = read_to_string(&src).unwrap();

        // Step 1: Lex raw tokens
        let raw_tokens: Vec<(Token, Span)> = Token::lexer(&fstring)
            .spanned()
            .filter_map(|(res, span)| match res {
                Ok(token) => Some((token, span)),
                Err(_) => None,
            })
            .collect();

        // Step 2: Inject Indent/Dedent logic
        let processed_tokens = inject_indentation(raw_tokens);

        // Step 3: Run the parser
        let eof_span = fstring.len()..fstring.len();
        let stream = chumsky::Stream::from_iter(eof_span, processed_tokens.into_iter());
        let ast = crate::parser::parser().parse(stream);

        // Step 4: Analyze, Type Check, and Codegen
        match ast {
            Ok(tree) => match crate::sanal::check_semantics(&tree) {
                Ok(typed_tree) => {
                    // Step 5: JIT Code Generation & Execution on Typed AST
                    let mut jit = crate::codegen::JitCompiler::new();
                    jit.compile_and_run(&typed_tree);
                }
                Err(errors) => {
                    crate::diagnostics::print_semantic_errors(&src, &fstring, errors);
                }
            },
            Err(parse_errors) => {
                crate::diagnostics::print_syntax_errors(&src, &fstring, parse_errors);
            }
        }
    }
}
