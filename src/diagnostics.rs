use ariadne::{sources, Color, Label, Report, ReportKind, Source};
use chumsky::error::Simple;
use std::path::PathBuf;

use crate::ast::Token;
use crate::loader::SourceMap;
use crate::sanal::SemanticError;

pub fn print_syntax_errors(
    src: &PathBuf,
    source_code: &str,
    base_offset: usize,
    errors: Vec<Simple<Token>>,
) {
    let file_name = src.to_string_lossy().to_string();

    for err in errors {
        let raw_span = err.span();
        let local_start = raw_span.start.saturating_sub(base_offset).min(source_code.len());
        let local_end = raw_span.end.saturating_sub(base_offset).min(source_code.len()).max(local_start);
        let span = local_start..local_end;
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

pub fn print_semantic_errors(source_map: &SourceMap, errors: Vec<SemanticError>) {
    let cache_entries: Vec<(String, String)> = source_map
        .files
        .iter()
        .map(|f| (f.path.to_string_lossy().to_string(), f.source.clone()))
        .collect();

    for err in errors {
        let (file_name, span) = source_map.resolve(&err.span);
        let span = if span.is_empty() {
            span.start..(span.start + 1)
        } else {
            span
        };

        let mut report = Report::build(ReportKind::Error, (file_name.clone(), span.clone()))
            .with_code(err.code)
            .with_message(&err.message)
            .with_label(
                Label::new((file_name, span))
                    .with_message(&err.label)
                    .with_color(Color::Red),
            );

        if let Some((sec_span, sec_msg)) = &err.secondary_label {
            let (sec_file, s_span) = source_map.resolve(sec_span);
            let s_span = if s_span.is_empty() {
                s_span.start..(s_span.start + 1)
            } else {
                s_span
            };
            report = report.with_label(
                Label::new((sec_file, s_span))
                    .with_message(sec_msg)
                    .with_color(Color::Yellow),
            );
        }

        if let Some(help) = &err.help {
            report = report.with_help(help);
        }

        let cache = sources(
            cache_entries
                .iter()
                .map(|(p, s)| (p.clone(), s.as_str())),
        );
        report.finish().print(cache).unwrap();
    }
}
