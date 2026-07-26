use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::error::Simple;
use std::path::PathBuf;

use crate::ast::Token;
use crate::sanal::SemanticError;

pub fn print_syntax_errors(src: &PathBuf, source_code: &str, errors: Vec<Simple<Token>>) {
    let file_name = src.to_string_lossy().to_string();

    for err in errors {
        let span = err.span();
        let found_str = match err.found() {
            Some(tok) => format!("unexpected token `{tok:?}`"),
            None => "unexpected end of input".to_string(),
        };

        let expected_toks: Vec<String> = err
            .expected()
            .map(|tok| match tok {
                Some(t) => format!("`{t:?}`"),
                None => "end of input".to_string(),
            })
            .collect();

        let message = if expected_toks.is_empty() {
            format!("Syntax error: {}", found_str)
        } else if expected_toks.len() == 1 {
            format!("Syntax error: {}, expected {}", found_str, expected_toks[0])
        } else {
            format!(
                "Syntax error: {}, expected one of: {}",
                found_str,
                expected_toks.join(", ")
            )
        };

        let mut label = Label::new((file_name.clone(), span.clone()))
            .with_message(found_str)
            .with_color(Color::Red);

        if !expected_toks.is_empty() {
            label = label.with_message(format!("expected {}", expected_toks.join(" or ")));
        }

        Report::build(ReportKind::Error, (file_name.clone(), span))
            .with_code("E0001")
            .with_message(message)
            .with_label(label)
            .finish()
            .print((file_name.clone(), Source::from(source_code)))
            .unwrap();
    }
}

pub fn print_semantic_errors(src: &PathBuf, source_code: &str, errors: Vec<SemanticError>) {
    let file_name = src.to_string_lossy().to_string();

    for err in errors {
        let span = if err.span.is_empty() { 0..1 } else { err.span.clone() };
        let mut report = Report::build(ReportKind::Error, (file_name.clone(), span.clone()))
            .with_code(err.code)
            .with_message(&err.message)
            .with_label(
                Label::new((file_name.clone(), span))
                    .with_message(&err.label)
                    .with_color(Color::Red),
            );

        if let Some((sec_span, sec_msg)) = &err.secondary_label {
            let s_span = if sec_span.is_empty() { 0..1 } else { sec_span.clone() };
            report = report.with_label(
                Label::new((file_name.clone(), s_span))
                    .with_message(sec_msg)
                    .with_color(Color::Yellow),
            );
        }

        if let Some(help) = &err.help {
            report = report.with_help(help);
        }

        report
            .finish()
            .print((file_name.clone(), Source::from(source_code)))
            .unwrap();
    }
}
