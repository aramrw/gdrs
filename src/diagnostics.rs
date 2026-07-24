use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::error::Simple;
use std::path::PathBuf;

use crate::ast::Token;
use crate::sanal::SemanticError;

pub fn print_syntax_errors(src: &PathBuf, source_code: &str, errors: Vec<Simple<Token>>) {
    let file_name = src.to_string_lossy().to_string();

    for err in errors {
        let span = err.span();

        Report::build(ReportKind::Error, (file_name.clone(), span.clone()))
            .with_code("SYNTAX")
            .with_message("Invalid syntax")
            .with_label(
                Label::new((file_name.clone(), span))
                    .with_message("Unknown Token")
                    .with_color(Color::Red),
            )
            .finish()
            .print((file_name.clone(), Source::from(source_code)))
            .unwrap();
    }
}

pub fn print_semantic_errors(src: &PathBuf, source_code: &str, errors: Vec<SemanticError>) {
    let file_name = src.to_string_lossy().to_string();

    for err in errors {
        let mut report = Report::build(ReportKind::Error, (file_name.clone(), err.span.clone()))
            .with_code("E001")
            .with_message(&err.message)
            .with_label(
                Label::new((file_name.clone(), err.span.clone()))
                    .with_message(&err.label)
                    .with_color(Color::Red),
            );

        if let Some(help) = &err.help {
            report = report.with_help(help);
        }

        report
            .finish()
            .print((file_name.clone(), Source::from(source_code)))
            .unwrap();
    }
}
