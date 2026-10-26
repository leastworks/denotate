//! `.den` source-placement adapter. Checking/publication scheduling is the
//! editor's responsibility; loading alone never runs the checker.
use crate::LoadedProgram;
use denotate_check::CheckedReport;
use denotate_presentation::{Diagnostic, Kind, Placement, Result, interpret, rewrites, summary};
use serde_json::{Value, json};

pub struct Presentation {
    pub diagnostics: Vec<Diagnostic>,
    pub status: Value,
}
pub fn present(program: &LoadedProgram, report: &CheckedReport<'_>) -> Result<Presentation> {
    let user_files = program
        .documents
        .iter()
        .filter(|d| d.ownership == "user")
        .map(|d| d.uri.clone())
        .collect();
    let placement = Placement {
        program: &program.root,
        verification: report.results.value.context.verification.as_ref(),
        user_files: &user_files,
        sources: &program.sources,
        current: &program.provenance,
        upstream: &program.embedded.provenance,
    };
    let findings = interpret(
        &program.corpus,
        &report.verification,
        Some((&program.keys, &report.results.value)),
    )?;
    let mut diagnostics = Vec::new();
    let mut inventory = Vec::new();
    for finding in findings {
        let mut placed = placement.finding(&finding)?;
        let evidence = denotate_presentation::evidence_data(&finding, &program.keys)?;
        for d in &mut placed {
            d.evidence = evidence.clone();
            d.notes.extend(denotate_presentation::generic_details(
                &program.corpus,
                &finding,
            )?);
        }
        inventory.push(json!({"identity":finding.identity.data_in(&program.keys, report.results.value.context.verification.as_ref())?,"kind":finding.kind.code(),
            "message":finding.message,"fallback":placed.iter().any(|d|d.fallback),"located":!placed.is_empty()}));
        diagnostics.extend(placed);
    }
    for rewrite in rewrites(&program.corpus, report.verification.program())? {
        let mut placed = placement.place(
            &rewrite.identity(),
            Kind::Rewrite,
            rewrite.message,
            &[],
            &rewrite.contributions(),
        )?;
        for d in &mut placed {
            d.evidence =
                json!({"kind":"rewrite-proof","coversAllInstances":rewrite.covers_all_instances});
        }
        inventory.push(json!({"identity":rewrite.identity().data_in(&program.keys, report.results.value.context.verification.as_ref())?,"kind":Kind::Rewrite.code(),
            "message":rewrite.message,"fallback":placed.iter().any(|d|d.fallback),"located":!placed.is_empty()}));
        diagnostics.extend(placed);
    }
    let mut status = summary(&report.results.value);
    status["program"] = json!(program.root);
    status["findings"] = json!(inventory);
    Ok(Presentation {
        diagnostics,
        status,
    })
}
