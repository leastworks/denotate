//! Snapshot-owned frontend/checker bridge. No LSP I/O or scheduling here.
use crate::attribution::SourceView;
use crate::{lowering::*, presentation, syntax, warnings};
use denotate_check::*;
use denotate_editor::Document;
use denotate_ir::{SnapshotId, SourceSpan, Sources};
use lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, NumberOrString, Range,
    Url,
};
use std::sync::Arc;

pub struct Prepared {
    pub fast: Vec<Diagnostic>,
    pub program: Option<Program>,
}
pub struct Program {
    pub document: Arc<Document>,
    pub sources: Sources,
    pub snapshot: SnapshotId,
    pub uri: Url,
    pub lowered: LoweredProgram,
}
pub struct Output {
    pub key_computation: std::time::Duration,
    pub results: Accounted<ScopedResults>,
    pub diagnostics: Vec<Diagnostic>,
    pub creator_warnings: Vec<String>,
}
#[derive(Debug)]
pub enum Failure {
    Cancelled,
    Deadline,
    Creator(String),
}
impl From<CheckError> for Failure {
    fn from(error: CheckError) -> Self {
        match error {
            CheckError::Cancelled => Self::Cancelled,
            CheckError::Deadline { .. } => Self::Deadline,
            other => Self::Creator(other.to_string()),
        }
    }
}

pub fn diagnostic(
    range: Range,
    code: &str,
    message: String,
    severity: DiagnosticSeverity,
) -> Diagnostic {
    Diagnostic {
        range,
        code: Some(NumberOrString::String(code.into())),
        source: Some("InputMapping".into()),
        message,
        severity: Some(severity),
        ..Default::default()
    }
}
fn range(document: &Document, span: SourceSpan) -> Range {
    let bytes = span.byte_range();
    Range::new(document.position(bytes.start), document.position(bytes.end))
}
pub fn creator_failure() -> Diagnostic {
    diagnostic(Range::default(), "creator-failure", "Semantic checking failed inside the DSL implementation; see the server log. This is not an error in a mapping.".into(), DiagnosticSeverity::INFORMATION)
}

/// An editor-only operational notice, never a checker finding or cached result.
pub fn deadline_notice() -> Diagnostic {
    diagnostic(
        Range::default(),
        "deadline",
        "Semantic checking stopped at its deadline; results are incomplete.".into(),
        DiagnosticSeverity::INFORMATION,
    )
}

fn paused() -> Diagnostic {
    diagnostic(
        Range::default(),
        "paused",
        "Semantic checks paused until errors are fixed.".into(),
        DiagnosticSeverity::INFORMATION,
    )
}

pub fn prepare(
    uri: &Url,
    revision: u64,
    document: Arc<Document>,
    lowering: &mut incremental::Session,
) -> Result<Prepared, String> {
    let mut sources = Sources::new();
    let snapshot = sources
        .add(
            uri.as_str(),
            revision,
            SourceView::TestDsl.as_str(),
            document.text.as_str(),
        )
        .map_err(|e| e.to_string())?;
    let ast = match syntax::project(&document, &sources, snapshot).map_err(|e| e.to_string())? {
        syntax::ParseOutcome::Parsed(ast) => ast,
        syntax::ParseOutcome::SyntaxErrors(errors) => {
            let mut fast: Vec<_> = errors
                .into_iter()
                .map(|e| {
                    diagnostic(
                        range(&document, e.span),
                        "syntax",
                        e.message,
                        DiagnosticSeverity::ERROR,
                    )
                })
                .collect();
            fast.push(paused());
            return Ok(Prepared {
                fast,
                program: None,
            });
        }
    };
    match lowering.lower(&ast, &sources).map_err(|e| e.to_string())? {
        LoweringOutcome::Lowered(lowered) => Ok(Prepared {
            fast: vec![],
            program: Some(Program {
                document,
                sources,
                snapshot,
                uri: uri.clone(),
                lowered,
            }),
        }),
        LoweringOutcome::UserErrors(errors) => {
            let mut fast = Vec::new();
            for error in errors {
                let code = if matches!(error.kind, DiagnosticKind::InvalidInteger) {
                    "literal"
                } else {
                    "name"
                };
                let message = match error.kind {
                    DiagnosticKind::InvalidInteger => {
                        "Expected a signed 64-bit decimal integer.".into()
                    }
                    DiagnosticKind::UnknownName { name, expected } => {
                        format!("Unknown {expected:?} '{name}'.")
                    }
                    DiagnosticKind::WrongKind {
                        name,
                        expected,
                        found,
                    } => format!(
                        "'{name}' is a {found:?}, but this position requires a {expected:?}."
                    ),
                    DiagnosticKind::DuplicateDeclaration { name, kind } => {
                        format!("Duplicate {kind:?} declaration '{name}'.")
                    }
                };
                let mut d = diagnostic(
                    range(&document, error.span),
                    code,
                    message,
                    DiagnosticSeverity::ERROR,
                );
                d.related_information = Some(
                    error
                        .related
                        .into_iter()
                        .map(|span| DiagnosticRelatedInformation {
                            location: Location::new(uri.clone(), range(&document, span)),
                            message: "Declaration here.".into(),
                        })
                        .collect(),
                );
                fast.push(d);
            }
            fast.push(paused());
            Ok(Prepared {
                fast,
                program: None,
            })
        }
    }
}

impl Program {
    fn location(&self, span: SourceSpan) -> Result<Location, Failure> {
        if span.snapshot() != self.snapshot {
            return Err(Failure::Creator(
                "Diagnostic refers to a different source snapshot.".into(),
            ));
        }
        self.sources
            .text(span)
            .map_err(|e| Failure::Creator(e.to_string()))?;
        Ok(Location::new(self.uri.clone(), range(&self.document, span)))
    }

    pub fn check(&self, limits: &Limits, after_prepare: impl FnOnce()) -> Result<Output, Failure> {
        limits.cancellation.check()?;
        let request = self.lowered.request(limits)?;
        let operations = OperationalLimits::from(limits);
        let ground = match request.prepare(&self.lowered.corpus, &self.lowered.keys, &operations)? {
            RequestPreparation::Complete(p) => p,
            RequestPreparation::Inconclusive { reason, receipts } => {
                return Ok(inconclusive(
                    "preparation",
                    Accounted {
                        value: request.exhausted(reason),
                        receipts,
                    },
                    self.lowered.key_computation,
                ));
            }
        };
        after_prepare();
        limits.cancellation.check()?;
        let ground = ground.admit(&operations)?;
        let report = match ground.verify(&operations)? {
            CheckOutcome::Complete(r) => r,
            CheckOutcome::Inconclusive {
                stage,
                reason,
                receipts,
            } => {
                return Ok(inconclusive(
                    stage.label(),
                    Accounted {
                        value: request.exhausted(reason),
                        receipts,
                    },
                    self.lowered.key_computation + ground.key_computation(),
                ));
            }
        };
        limits.cancellation.check()?;
        let findings = presentation::present(
            &self.lowered,
            &report.verification,
            &self.sources,
            SourceView::TestDsl.as_str(),
        )
        .map_err(|e| Failure::Creator(e.to_string()))?;
        let rewrites = warnings::present_rewrites(
            &self.lowered,
            ground.program(),
            &self.sources,
            SourceView::TestDsl.as_str(),
        )
        .map_err(|e| Failure::Creator(e.to_string()))?;
        let mut output = Output {
            results: report.results,
            key_computation: self.lowered.key_computation + ground.key_computation(),
            diagnostics: vec![],
            creator_warnings: vec![],
        };
        for finding in findings {
            let severity = match finding.kind.severity() {
                presentation::DiagnosticSeverity::Error => DiagnosticSeverity::ERROR,
                presentation::DiagnosticSeverity::Warning => DiagnosticSeverity::WARNING,
                presentation::DiagnosticSeverity::Information => DiagnosticSeverity::INFORMATION,
            };
            let mut message = finding.message;
            for note in finding.notes {
                message.push('\n');
                message.push_str(&note);
            }
            let mut d = diagnostic(
                self.location(finding.primary)?.range,
                &format!("{:?}", finding.kind),
                message,
                severity,
            );
            d.related_information = Some(
                finding
                    .related
                    .into_iter()
                    .map(|o| {
                        Ok(DiagnosticRelatedInformation {
                            location: self.location(o.span)?,
                            message: o.label,
                        })
                    })
                    .collect::<Result<_, Failure>>()?,
            );
            output.diagnostics.push(d);
        }
        for warning in rewrites {
            if warning.owner == warnings::Contribution::Library {
                output.creator_warnings.push(warning.message);
                continue;
            }
            let span = warning
                .primary
                .ok_or_else(|| Failure::Creator("User warning has no source origin.".into()))?;
            let mut d = diagnostic(
                self.location(span)?.range,
                "redundant",
                warning.message,
                DiagnosticSeverity::WARNING,
            );
            d.related_information = Some(
                warning
                    .related
                    .into_iter()
                    .map(|o| {
                        Ok(DiagnosticRelatedInformation {
                            location: self.location(o.span)?,
                            message: o.label,
                        })
                    })
                    .collect::<Result<_, Failure>>()?,
            );
            output.diagnostics.push(d);
        }
        for warning in warnings::covered_masks(&self.lowered, &self.sources)
            .map_err(|e| Failure::Creator(e.to_string()))?
        {
            let mut d = diagnostic(
                self.location(warning.primary)?.range,
                "redundant-mask",
                warning.message,
                DiagnosticSeverity::WARNING,
            );
            d.related_information = Some(
                warning
                    .related
                    .into_iter()
                    .map(|o| {
                        Ok(DiagnosticRelatedInformation {
                            location: self.location(o.span)?,
                            message: o.label,
                        })
                    })
                    .collect::<Result<_, Failure>>()?,
            );
            output.diagnostics.push(d);
        }
        limits.cancellation.check()?;
        Ok(output)
    }
}

fn inconclusive(
    phase: &str,
    results: Accounted<ScopedResults>,
    key_computation: std::time::Duration,
) -> Output {
    Output {
        results,
        key_computation,
        diagnostics: vec![diagnostic(
            Range::default(),
            "inconclusive",
            format!("Semantic checks inconclusive: {phase} exhausted its budget."),
            DiagnosticSeverity::INFORMATION,
        )],
        creator_warnings: vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attribution_failure_is_for_the_creator_not_a_user_finding() {
        let text = include_str!("../fixtures/overlapping-mappings.txt");
        let doc = Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            text.into(),
            1,
            true,
        ));
        let mut p = prepare(
            &Url::parse("file:///example.inputmapping").unwrap(),
            1,
            doc,
            &mut incremental::Session::default(),
        )
        .unwrap()
        .program
        .unwrap();
        p.lowered.attribution.provenance = denotate_ir::Provenance::new();
        let Err(Failure::Creator(message)) = p.check(&Limits::default(), || {}) else {
            panic!("expected creator failure");
        };
        assert!(!message.is_empty());
        let notice = super::creator_failure();
        assert_eq!(notice.range, Range::default());
        assert_eq!(notice.severity, Some(DiagnosticSeverity::INFORMATION));
        assert!(notice.message.contains("DSL implementation"));
    }

    #[test]
    fn top_level_limit_is_inconclusive_but_cancellation_returns_no_diagnostics() {
        let doc = Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            "input i; slot a; a <- i;".into(),
            1,
            true,
        ));
        let p = prepare(
            &Url::parse("file:///example.inputmapping").unwrap(),
            1,
            doc,
            &mut incremental::Session::default(),
        )
        .unwrap()
        .program
        .unwrap();
        let limits = Limits {
            max_work: 0,
            ..Limits::default()
        };
        let result = p.check(&limits, || {}).unwrap();
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(
            result.diagnostics[0].code,
            Some(NumberOrString::String("inconclusive".into()))
        );
        limits.cancellation.cancel();
        assert!(matches!(p.check(&limits, || {}), Err(Failure::Cancelled)));
    }
}
