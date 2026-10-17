//! Snapshot-owned frontend/checker bridge. No LSP I/O or scheduling here.
use denotate_check::*;
use denotate_editor::Document;
use denotate_ir::{SnapshotId, SourceSpan, Sources};
use denotate_test_dsl::{lowering::*, presentation, syntax, warnings};
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
    pub diagnostics: Vec<Diagnostic>,
    pub creator_warnings: Vec<String>,
}
#[derive(Debug)]
pub enum Failure {
    Cancelled,
    Creator(String),
}
impl From<CheckError> for Failure {
    fn from(error: CheckError) -> Self {
        match error {
            CheckError::Cancelled => Self::Cancelled,
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
fn paused() -> Diagnostic {
    diagnostic(
        Range::default(),
        "paused",
        "Semantic checks paused until errors are fixed.".into(),
        DiagnosticSeverity::INFORMATION,
    )
}

pub fn prepare(uri: &Url, revision: u64, document: Arc<Document>) -> Result<Prepared, String> {
    let mut sources = Sources::new();
    let snapshot = sources
        .add(uri.as_str(), revision, "test-dsl", document.text.as_str())
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
    match lower(&ast, &sources).map_err(|e| e.to_string())? {
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
                let message = match error.kind {
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
                    "name",
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
        let domains = self
            .lowered
            .corpus
            .sorts()
            .map(|sort| {
                (
                    sort.id,
                    self.lowered
                        .corpus
                        .constants()
                        .filter(|c| c.sort == sort.id)
                        .map(|c| c.id)
                        .collect(),
                )
            })
            .collect();
        let AnalysisOutcome::Complete(ground) =
            GroundProgram::prepare_checked(&self.lowered.corpus, &domains, limits)?
        else {
            return Ok(inconclusive("preparation"));
        };
        after_prepare();
        limits.cancellation.check()?;
        let ground = ground.admit(limits)?;
        let AnalysisOutcome::Complete(meaning) = ground.symbolic_checked(limits)? else {
            return Ok(inconclusive("symbolic evaluation"));
        };
        let AnalysisOutcome::Complete(report) = meaning.verify_checked(limits)? else {
            return Ok(inconclusive("verification"));
        };
        limits.cancellation.check()?;
        let findings = presentation::present(&self.lowered, &report, &self.sources, "test-dsl")
            .map_err(|e| Failure::Creator(e.to_string()))?;
        let rewrites =
            warnings::present_rewrites(&self.lowered, &ground, &self.sources, "test-dsl")
                .map_err(|e| Failure::Creator(e.to_string()))?;
        let mut output = Output {
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
                            message: o.role,
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
                            message: o.role,
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

fn inconclusive(phase: &str) -> Output {
    Output {
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
        let text = include_str!("../../fixtures/overlapping-mappings.txt");
        let doc = Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            text.into(),
            1,
            true,
        ));
        let mut p = prepare(&Url::parse("file:///example.inputmapping").unwrap(), 1, doc)
            .unwrap()
            .program
            .unwrap();
        p.lowered.provenance = denotate_ir::Provenance::new();
        assert!(matches!(
            p.check(&Limits::default(), || {}),
            Err(Failure::Creator(_))
        ));
        let notice = super::super::creator_failure();
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
        let p = prepare(&Url::parse("file:///example.inputmapping").unwrap(), 1, doc)
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
