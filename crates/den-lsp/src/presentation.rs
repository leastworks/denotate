//! Checked-result adapter. No scheduler
//! or edits are implied by converting a snapshot-owned report.
use denotate_check::CheckedReport;
use denotate_ir_text::LoadedProgram;
use lsp_types::{Diagnostic, Url};
use serde_json::Value;
use std::collections::BTreeMap;

pub struct Publication {
    pub diagnostics: BTreeMap<Url, Vec<Diagnostic>>,
    pub status: Value,
}
pub fn present(program: &LoadedProgram, report: &CheckedReport<'_>) -> Result<Publication, String> {
    let output =
        denotate_ir_text::presentation::present(program, report).map_err(|e| e.to_string())?;
    let mut diagnostics = BTreeMap::<_, Vec<_>>::new();
    for finding in output.diagnostics {
        let (uri, mut diagnostic) =
            denotate_editor::presentation::diagnostic(&finding, &program.sources, &program.keys)?;
        let span_data = |span: denotate_ir::SourceSpan| -> Result<Value, String> {
            let snapshot = program
                .sources
                .snapshot(span.snapshot())
                .map_err(|e| e.to_string())?;
            let range = span.byte_range();
            Ok(
                serde_json::json!({"uri":snapshot.uri,"view":snapshot.view,"hash":denotate_ir_text::origins::content_hash(&snapshot.text),"bytes":[range.start,range.end]}),
            )
        };
        diagnostic.data.as_mut().unwrap()["locations"] = serde_json::json!({
            "primary":span_data(finding.primary)?,
            "related":finding.related.iter().map(|r|span_data(r.span)).collect::<Result<Vec<_>,_>>()?,
        });
        diagnostics.entry(uri).or_default().push(diagnostic);
    }
    Ok(Publication {
        diagnostics,
        status: output.status,
    })
}

/// Selection is configuration, independent of semantic checking or its budgets.
pub fn configuration(program: &LoadedProgram) -> Result<Publication, String> {
    use denotate_ir::{Namespace, OccurrenceId};
    use lsp_types::{DiagnosticSeverity, NumberOrString};
    use serde_json::json;
    use std::collections::BTreeSet;
    let name = |id: OccurrenceId, text: &str| {
        denotate_ir_text::index::Name {
            namespace: Some(
                program
                    .corpus
                    .namespace(id)
                    .cloned()
                    .unwrap_or_else(Namespace::default),
            ),
            text: text.into(),
            generated: false,
        }
        .spelling()
    };
    let mut declarations = program.corpus.verifications().collect::<Vec<_>>();
    declarations.sort_by_key(|v| program.keys.verification(v.id).unwrap());
    let selected = declarations
        .iter()
        .flat_map(|v| v.obligations.iter().copied())
        .collect::<BTreeSet<_>>();
    let verifications = declarations.iter().map(|v| json!({
        "verification": name(v.id.into(), &v.name),
        "assumptions": v.assumptions.iter().map(|id| name((*id).into(), &program.corpus.assumption(*id).unwrap().name)).collect::<Vec<_>>(),
        "mode": if v.obligations.is_empty() { "consistency-only" } else { "normal" },
        "consistency": "consistent", "checking": "pending", "summary": null,
    })).collect::<Vec<_>>();
    let mut unchecked = vec![];
    let mut diagnostics = BTreeMap::<_, Vec<_>>::new();
    for obligation in program
        .corpus
        .obligations()
        .filter(|o| !selected.contains(&o.id))
    {
        let spelling = name(obligation.id.into(), &obligation.name);
        unchecked.push(spelling.clone());
        let key = &program
            .keys
            .obligation(obligation.id)
            .map_err(|e| e.to_string())?
            .0;
        let uri = &program.owners[&obligation.id.into()];
        let fallback = program
            .documents
            .iter()
            .find(|d| &d.uri == uri)
            .unwrap()
            .ownership
            == "library";
        let message = format!(
            "Obligation {spelling} is not checked by any verification in program {}.",
            program.root
        );
        // The declaration is the sole notice site, including the labeled library fallback.
        if let Some(origin) = program.provenance.origins(obligation.id).first() {
            let location = denotate_editor::presentation::location(&program.sources, origin.span)?;
            diagnostics.entry(location.uri).or_default().push(Diagnostic {
                range: location.range,
                severity: Some(DiagnosticSeverity::INFORMATION),
                code: Some(NumberOrString::String("unchecked-obligation".into())),
                source: Some("denotate".into()),
                message: if fallback { format!("in {}: {message}", program.root) } else { message },
                data: Some(json!({"program": program.root, "finding": {"uncheckedObligation": [key.namespace.as_ref(), key.name.as_ref()]}, "kind": "unchecked-obligation", "fallback": fallback})),
                ..Default::default()
            });
        }
    }
    unchecked.sort();
    Ok(Publication {
        diagnostics,
        status: json!({
            "state": if verifications.is_empty() { "unconfigured" } else { "incomplete" },
            "checking": if verifications.is_empty() { "unconfigured" } else { "pending" },
            "verifications": verifications, "uncheckedObligations": unchecked, "findings": [],
        }),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use denotate_check::*;
    use denotate_ir_text::{load, ProgramMembership, SourceFile};
    #[test]
    fn converts_checked_identity_locations_and_summary_without_publishing() {
        let doc = SourceFile::new("file:///unicode.den", 7, "// 😀\nsort S; const a,b: S; relation p(x:S); p(a); p(b); obligation unique: at_most_one(p, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }");
        let program = load(
            &ProgramMembership::single("file:///den.root", [doc.uri.clone()]),
            &[doc],
        )
        .unwrap();
        let limits = Limits::default();
        let ops = OperationalLimits::from(&limits);
        let request = program
            .verification_requests(&limits, BackendIdentity::bdd())
            .unwrap()
            .remove(0)
            .1;
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
