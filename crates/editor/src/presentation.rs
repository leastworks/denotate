//! Thin checked-finding → LSP adapter. Positions use the finding's immutable
//! snapshot, never a newer buffer. Publication freshness is the caller's gate.
use denotate_ir::{SemanticKeys, SourceSpan, Sources};
use denotate_presentation::{Diagnostic as Finding, Severity};
use lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, NumberOrString, Range,
    Url,
};

pub fn location(sources: &Sources, span: SourceSpan) -> Result<Location, String> {
    sources.text(span).map_err(|e| e.to_string())?;
    let snapshot = sources
        .snapshot(span.snapshot())
        .map_err(|e| e.to_string())?;
    let lines = crate::document::line_starts(&snapshot.text);
    let position = |offset| crate::document::position(&snapshot.text, &lines, offset);
    Ok(Location::new(
        Url::parse(&snapshot.uri).map_err(|e| e.to_string())?,
        Range::new(
            position(span.byte_range().start),
            position(span.byte_range().end),
        ),
    ))
}
pub fn diagnostic(
    finding: &Finding,
    sources: &Sources,
    keys: &SemanticKeys,
) -> Result<(Url, Diagnostic), String> {
    let primary = location(sources, finding.primary)?;
    let mut message = finding.message.clone();
    for note in &finding.notes {
        message.push('\n');
        message.push_str(note);
    }
    Ok((
        primary.uri,
        Diagnostic {
            range: primary.range,
            severity: Some(match finding.kind.severity() {
                Severity::Error => DiagnosticSeverity::ERROR,
                Severity::Warning => DiagnosticSeverity::WARNING,
                Severity::Information => DiagnosticSeverity::INFORMATION,
            }),
            code: Some(NumberOrString::String(finding.kind.code().into())),
            source: Some("denotate".into()),
            message,
            related_information: Some(
                finding
                    .related
                    .iter()
                    .map(|r| {
                        Ok(DiagnosticRelatedInformation {
                            location: location(sources, r.span)?,
                            message: r.label.clone(),
                        })
                    })
                    .collect::<Result<_, String>>()?,
            ),
            data: Some(finding.data(keys).map_err(|e| e.to_string())?),
            ..Diagnostic::default()
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::Position;
    #[test]
    fn immutable_unicode_crlf_and_cr_positions() {
        let mut sources = Sources::new();
        let old = sources
            .add("file:///x.den", 1, "denotate", "α😀\r\nβ\rγ")
            .unwrap();
        sources
            .add("file:///x.den", 2, "denotate", "changed")
            .unwrap();
        let at = |range| {
            location(&sources, sources.span(old, range).unwrap())
                .unwrap()
                .range
        };
        assert_eq!(
            at(2..6),
            Range::new(Position::new(0, 1), Position::new(0, 3))
        );
        assert_eq!(
            at(8..10),
            Range::new(Position::new(1, 0), Position::new(1, 1))
        );
        assert_eq!(
            at(11..13),
            Range::new(Position::new(2, 0), Position::new(2, 1))
        );
    }
}
