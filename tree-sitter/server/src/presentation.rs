//! Checked-result adapter, ready for the stage-4 publication gate. No scheduler
//! or edits are implied by converting a snapshot-owned report.
use denotate_check::CheckedReport;
use denotate_ir_text::LoadedProgram;
use lsp_types::{Diagnostic, Url};
use serde_json::Value;
use std::collections::BTreeMap;

#[allow(dead_code)] // Stage 4 installs the worker and freshness/publication gate.
pub struct Publication {
    pub diagnostics: BTreeMap<Url, Vec<Diagnostic>>,
    pub status: Value,
}
#[allow(dead_code)]
pub fn present(program: &LoadedProgram, report: &CheckedReport<'_>) -> Result<Publication, String> {
    let output =
        denotate_ir_text::presentation::present(program, report).map_err(|e| e.to_string())?;
    let mut diagnostics = BTreeMap::<_, Vec<_>>::new();
    for finding in output.diagnostics {
        let (uri, diagnostic) =
            denotate_editor::presentation::diagnostic(&finding, &program.sources, &program.keys)?;
        diagnostics.entry(uri).or_default().push(diagnostic);
    }
    Ok(Publication {
        diagnostics,
        status: output.status,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use denotate_check::*;
    use denotate_ir_text::{load, ProgramMembership, SourceFile};
    #[test]
    fn converts_checked_identity_locations_and_summary_without_publishing() {
        let doc = SourceFile::new("file:///unicode.den", 7, "// 😀\nsort S; const a,b: S; relation p(x:S); p(a); p(b); obligation unique: at_most_one(p, group_by: ());");
        let program = load(
            &ProgramMembership::single("file:///den.root", [doc.uri.clone()]),
            &[doc],
        )
        .unwrap();
        let limits = Limits::default();
        let ops = OperationalLimits::from(&limits);
        let request = program.request(&limits, BackendIdentity::bdd()).unwrap();
        let RequestPreparation::Complete(prepared) = request
            .prepare(&program.corpus, &program.keys, &ops)
            .unwrap()
        else {
            panic!()
        };
        let prepared = prepared.admit(&ops).unwrap();
        let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
            panic!()
        };
        let out = present(&program, &report).unwrap();
        let diagnostics = &out.diagnostics[&Url::parse("file:///unicode.den").unwrap()];
        assert_eq!(diagnostics.len(), 2);
        for d in diagnostics {
            assert_eq!(d.range.start.line, 1);
            assert_eq!(d.data.as_ref().unwrap()["program"], "file:///den.root");
            assert_eq!(d.data.as_ref().unwrap()["kind"], "counterexample");
            assert_eq!(
                d.data.as_ref().unwrap()["evidence"]["tuples"]
                    .as_array()
                    .unwrap()
                    .len(),
                2
            );
        }
        assert_eq!(out.status["state"], "findings");
    }
}
