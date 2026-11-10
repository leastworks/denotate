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
/// Declaration validity is program-scoped, including without verifications.
pub fn present_assumption_validation(
    program: &LoadedProgram,
    validation: &denotate_check::AssumptionValidation,
) -> Result<Presentation> {
    let user_files = program
        .documents
        .iter()
        .filter(|d| d.ownership == "user")
        .map(|d| d.uri.clone())
        .collect();
    let placement = Placement {
        program: &program.root,
        verification: None,
        user_files: &user_files,
        sources: &program.sources,
        current: &program.provenance,
        upstream: &program.embedded.provenance,
    };
    let mut diagnostics = Vec::new();
    let mut inventory = Vec::new();
    for (finding, evidence) in denotate_presentation::assumption_validation_findings(
        &program.corpus,
        &program.keys,
        validation,
        &diagnostic_names(&program.corpus),
    )? {
        let mut placed = placement.place(
            &finding.identity,
            finding.kind,
            &finding.message,
            &finding.notes,
            &finding.contributions,
        )?;
        for d in &mut placed {
            d.evidence = evidence.clone();
        }
        inventory.push(json!({"identity":finding.identity.data_in(&program.keys,None)?,"kind":finding.kind.code(),"message":finding.message,"fallback":placed.iter().any(|d|d.fallback),"located":!placed.is_empty()}));
        diagnostics.extend(placed);
    }
    let mut status = denotate_presentation::assumption_validation_summary(validation);
    status["findings"] = json!(inventory);
    Ok(Presentation {
        diagnostics,
        status,
    })
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
    let names = diagnostic_names(&program.corpus);
    let findings = interpret(&program.corpus, &report.verification, &names)?;
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
                &names,
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
    for finding in denotate_presentation::context_findings(&program.corpus, &program.keys, report)?
    {
        let mut placed = placement.place(
            &finding.identity,
            finding.kind,
            &finding.message,
            &finding.notes,
            &finding.contributions,
        )?;
        for d in &mut placed {
            d.evidence = match &finding.identity {
                denotate_presentation::Identity::Notice(id) => {
                    denotate_presentation::notice_evidence_data(
                        &report.results.value.notices[program.keys.notice(*id)?],
                    )
                }
                _ => json!({"kind":finding.kind.code()}),
            };
        }
        inventory.push(json!({"identity":finding.identity.data_in(&program.keys, report.results.value.context.verification.as_ref())?,"kind":finding.kind.code(),"message":finding.message,"fallback":placed.iter().any(|d|d.fallback),"located":!placed.is_empty()}));
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

/// Canonical, qualified `.den` names for the relations and constants in tuple
/// diagnostics. Generated relations use the exporter's allocated labels, keeping
/// `$helper` distinct from an authored `'$helper'`. The shared presenter receives
/// this callback and remains independent of text syntax.
///
/// The callback accepts only relation and constant declarations in this corpus.
pub fn diagnostic_names(
    corpus: &denotate_ir::Corpus,
) -> impl Fn(denotate_ir::OccurrenceId) -> String {
    use crate::{NameKind, spelling};
    use denotate_ir::OccurrenceId;
    let qualify = |id: OccurrenceId, text: String| {
        corpus
            .namespace(id)
            .into_iter()
            .flat_map(|ns| ns.segments())
            .map(|part| spelling(part, NameKind::Identifier))
            .chain(std::iter::once(text))
            .collect::<Vec<_>>()
            .join("::")
    };
    let mut names = std::collections::BTreeMap::<OccurrenceId, String>::new();
    for (id, text) in crate::print::relation_names(corpus) {
        names.insert(id.into(), qualify(id.into(), text));
    }
    for constant in corpus.constants() {
        names.insert(
            constant.id.into(),
            qualify(
                constant.id.into(),
                spelling(&constant.name, NameKind::Constant),
            ),
        );
    }
    move |id| {
        names
            .get(&id)
            .expect("diagnostic relation or constant belongs to corpus")
            .clone()
    }
}
