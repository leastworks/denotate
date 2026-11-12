//! Thin checked-finding → LSP adapter. Positions use the finding's immutable
//! snapshot, never a newer buffer. Publication freshness is the caller's gate.
use denotate_ir::{SemanticKeys, SnapshotId, SourceSpan, Sources};
use denotate_presentation::{Diagnostic as Finding, Severity};
use lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, NumberOrString, Range,
    Url,
};
use std::collections::BTreeMap;

pub fn location(sources: &Sources, span: SourceSpan) -> Result<Location, String> {
    Locations::new(sources).location(span)
}

/// Per-presentation immutable snapshot indexes, shared across all diagnostics.
pub struct Locations<'a> {
    sources: &'a Sources,
    lines: BTreeMap<SnapshotId, Vec<usize>>,
}
impl<'a> Locations<'a> {
    pub fn new(sources: &'a Sources) -> Self {
        Self {
            sources,
            lines: BTreeMap::new(),
        }
    }
    pub fn location(&mut self, span: SourceSpan) -> Result<Location, String> {
        self.sources.text(span).map_err(|e| e.to_string())?;
        let snapshot = self
            .sources
            .snapshot(span.snapshot())
            .map_err(|e| e.to_string())?;
        let lines = self
            .lines
            .entry(span.snapshot())
            .or_insert_with(|| crate::document::line_starts(&snapshot.text));
        let position = |offset| crate::document::position(&snapshot.text, lines, offset);
        Ok(Location::new(
            Url::parse(&snapshot.uri).map_err(|e| e.to_string())?,
            Range::new(
                position(span.byte_range().start),
                position(span.byte_range().end),
            ),
        ))
    }
    pub fn diagnostic(
        &mut self,
        finding: &Finding,
        keys: &SemanticKeys,
    ) -> Result<(Url, Diagnostic), String> {
        diagnostic_with_locations(finding, self, keys)
    }
}
pub fn diagnostic(
    finding: &Finding,
    sources: &Sources,
    keys: &SemanticKeys,
) -> Result<(Url, Diagnostic), String> {
    Locations::new(sources).diagnostic(finding, keys)
}
fn diagnostic_with_locations(
    finding: &Finding,
    locations: &mut Locations<'_>,
    keys: &SemanticKeys,
) -> Result<(Url, Diagnostic), String> {
    let primary = locations.location(finding.primary)?;
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
                            location: locations.location(r.span)?,
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
    fn cached_locations_match_original_conversion_including_long_lines_and_old_revisions() {
        let mut sources = Sources::new();
        for (version, text) in [
            "α😀\r\nβ\rγ\n".to_owned(),
            "α😀".repeat(30_000),
            String::new(),
        ]
        .iter()
        .enumerate()
        {
            sources
                .add(
                    "file:///same.den",
                    version as u64,
                    "denotate",
                    text.as_str(),
                )
                .unwrap();
        }
        let mut locations = Locations::new(&sources);
        for source in sources.snapshots().collect::<Vec<_>>().into_iter().rev() {
            let offsets: Vec<_> = if source.text.len() < 100 {
                source
                    .text
                    .char_indices()
                    .map(|(i, _)| i)
                    .chain([source.text.len()])
                    .collect()
            } else {
                vec![0, 2, 6, 60_000, source.text.len()]
            };
            for byte in offsets {
                let span = sources.span(source.id, byte..source.text.len()).unwrap();
                let actual = locations.location(span).unwrap();
                // The original adapter rebuilt this index for every location.
                let lines = crate::document::line_starts(&source.text);
                assert_eq!(
                    actual.range,
                    Range::new(
                        crate::document::position(&source.text, &lines, byte),
                        crate::document::position(&source.text, &lines, source.text.len())
                    )
                );
            }
        }
        assert_eq!(locations.lines.len(), 3);
    }
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
