//! `.den` source-placement adapter. Checking/publication scheduling is the
//! editor's responsibility; loading alone never runs the checker.
use crate::LoadedProgram;
use denotate_check::CheckedReport;
pub use denotate_presentation::RewriteDetail;
use denotate_presentation::{Diagnostic, Placement, Result, interpret, rewrites, summary};
use serde_json::{Value, json};

pub struct Presentation {
    pub diagnostics: Vec<Diagnostic>,
    pub status: Value,
}
impl Presentation {
    /// Optional view filter. Use the rewritten rule's ownership, not its primary
    /// location: a library proof may be placed on a consumer occurrence. Keep the
    /// complete per-verification finding inventory and outcome in the summary.
    pub fn hide_library_rewrites(&mut self, program: &LoadedProgram) {
        let library_files: std::collections::BTreeSet<_> = program
            .documents
            .iter()
            .filter(|d| d.ownership == "library")
            .map(|d| &d.uri)
            .collect();
        let mut hidden = std::collections::BTreeSet::new();
        self.diagnostics.retain(|d| {
            let denotate_presentation::Identity::Rewrite { rule, .. } = &d.identity else {
                return true;
            };
            let library = program
                .owners
                .get(&(*rule).into())
                .is_some_and(|uri| library_files.contains(uri));
            if library {
                hidden.insert(d.identity.clone());
            }
            !library
        });
        let previous = self.status["hiddenLibraryRewrites"].as_u64().unwrap_or(0);
        self.status["hiddenLibraryRewrites"] = json!(previous + hidden.len() as u64);
    }
}
/// Declaration validity is program-scoped, including without verifications.
pub fn present_assumption_validation(
    program: &LoadedProgram,
    validation: &denotate_check::AssumptionValidation,
) -> Result<Presentation> {
    present_assumptions(
        program,
        validation,
        program.corpus.assumptions().map(|a| a.id),
    )
}

/// An explicit stable audit can omit declarations checked only by completion.
pub fn present_assumption_audit(
    program: &LoadedProgram,
    validation: &denotate_check::AssumptionValidation,
) -> Result<Presentation> {
    let mut selected = Vec::new();
    for a in program.corpus.assumptions() {
        if validation
            .assumptions
            .contains_key(program.keys.assumption(a.id)?)
        {
            selected.push(a.id);
        }
    }
    present_assumptions(program, validation, selected)
}

fn present_assumptions(
    program: &LoadedProgram,
    validation: &denotate_check::AssumptionValidation,
    selected: impl IntoIterator<Item = denotate_ir::AssumptionId>,
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
    for (finding, evidence) in denotate_presentation::assumption_validation_findings_for(
        &program.corpus,
        &program.keys,
        validation,
        &diagnostic_names(&program.corpus),
        selected,
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
    present_with_rewrite_detail(
        program,
        report,
        denotate_presentation::RewriteDetail::Direct,
    )
}

pub fn present_with_rewrite_detail(
    program: &LoadedProgram,
    report: &CheckedReport<'_>,
    detail: denotate_presentation::RewriteDetail,
) -> Result<Presentation> {
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
        let placed = placement.rewrite(&rewrite, &program.corpus, &names, detail)?;
        inventory.push(json!({"identity":rewrite.identity().data_in(&program.keys, report.results.value.context.verification.as_ref())?,"kind":rewrite.kind().code(),
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
                denotate_presentation::Identity::DownstreamWork => {
                    let r = report.results.value.downstream_incomplete.as_ref().unwrap();
                    denotate_presentation::with_limit_details(
                        json!({"kind":finding.kind.code(),"phase":r.phase,"resource":r.resource}),
                        r.details,
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
) -> impl Fn(denotate_ir::OccurrenceId) -> String + Send + Sync + use<> {
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
    for assumption in corpus.assumptions() {
        names.insert(
            assumption.id.into(),
            qualify(
                assumption.id.into(),
                spelling(&assumption.name, NameKind::Identifier),
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

/// Opt-in CLI adapter. Editors still use the ordinary checked-report path.
pub fn present_stable(
    program: &LoadedProgram,
    report: &denotate_check::stable_query::Report,
) -> Result<Presentation> {
    let own = program
        .documents
        .iter()
        .filter(|d| d.ownership == "user")
        .map(|d| d.uri.clone())
        .collect();
    let key = program.keys.verification(report.verification)?;
    let placement = Placement {
        program: &program.root,
        verification: Some(key),
        user_files: &own,
        sources: &program.sources,
        current: &program.provenance,
        upstream: &program.embedded.provenance,
    };
    let names = diagnostic_names(&program.corpus);
    let findings = denotate_presentation::stable_findings(&program.corpus, report, &names)?;
    let mut status = denotate_presentation::stable_summary(&program.corpus, &program.keys, report)?;
    let mut diagnostics = Vec::new();
    let mut inventory = Vec::new();
    for f in findings {
        let evidence = denotate_presentation::evidence_data(&f, &program.keys)?;
        let mut placed = placement.finding(&f)?;
        for d in &mut placed {
            d.evidence = evidence.clone();
            d.notes.extend(denotate_presentation::generic_details(
                &program.corpus,
                &f,
                &names,
            )?);
        }
        inventory.push(json!({"identity":f.identity.data_in(&program.keys,Some(key))?,"kind":f.kind.code(),"message":f.message,"evidence":evidence}));
        diagnostics.extend(placed);
    }
    let syntactic_notices = report
        .subsumed_producers
        .iter()
        .filter(|n| n.syntactic)
        .map(|n| n.rule)
        .collect::<std::collections::BTreeSet<_>>();
    for finding in denotate_presentation::stable_producer_notices(report, &program.corpus, &names)?
    {
        let mut placed = placement.place(
            &finding.identity,
            finding.kind,
            &finding.message,
            &finding.notes,
            &finding.contributions,
        )?;
        for d in &mut placed {
            let syntactic = matches!(finding.identity, denotate_presentation::Identity::SubsumedProducer(rule) if syntactic_notices.contains(&rule));
            d.evidence =
                json!({"kind":if syntactic {"syntactic-subsumption"} else {"settled-producer"}});
        }
        inventory.push(json!({"identity":finding.identity.data_in(&program.keys,Some(key))?,"kind":finding.kind.code(),"message":finding.message}));
        diagnostics.extend(placed);
    }
    status["findings"] = json!(inventory);
    Ok(Presentation {
        diagnostics,
        status,
    })
}

/// Completion evidence uses the same source placement and fallback policy, without
/// manufacturing a stable derivation or asking presentation to solve equations.
pub fn present_completion(
    program: &LoadedProgram,
    report: &denotate_check::completion_query::Report,
) -> Result<Presentation> {
    present_completion_with_options(program, report, Default::default())
}

pub fn present_completion_with_options(
    program: &LoadedProgram,
    report: &denotate_check::completion_query::Report,
    options: denotate_presentation::CompletionEvidenceOptions,
) -> Result<Presentation> {
    let (findings, summary) = denotate_presentation::completion_presentation(
        &program.corpus,
        &program.keys,
        report,
        &diagnostic_names(&program.corpus),
        options,
    )?;
    place_completion_findings(program, report.verification, findings, summary)
}

pub fn completion_input_domain_failure(
    program: &LoadedProgram,
    verification: denotate_ir::VerificationId,
    issues: &[denotate_check::completion_query::InputDomainIssue],
) -> Result<Presentation> {
    completion_input_domain_failure_with_options(program, verification, issues, Default::default())
}
pub fn completion_input_domain_failure_with_options(
    program: &LoadedProgram,
    verification: denotate_ir::VerificationId,
    issues: &[denotate_check::completion_query::InputDomainIssue],
    options: denotate_presentation::CompletionEvidenceOptions,
) -> Result<Presentation> {
    use denotate_check::completion_query::InputDomainFailure;
    let (findings, data, models) = denotate_presentation::completion_input_domain_presentation(
        &program.corpus,
        &program.keys,
        issues,
        &diagnostic_names(&program.corpus),
        options,
    )?;
    let status = json!({"backend":{"backend":"sat"},"semantics":"completion","state":"incomplete","incomplete":true,
        "hasFailures":issues.iter().any(|i|matches!(i.failure,InputDomainFailure::Ambiguous(_)|InputDomainFailure::NoMeaning)),
        "inputDomains":data,"completionEvidence":models,"meaning":{"state":"not-analysed"}});
    place_completion_findings(program, verification, findings, status)
}

fn place_completion_findings(
    program: &LoadedProgram,
    verification: denotate_ir::VerificationId,
    findings: Vec<denotate_presentation::CompletionFinding>,
    mut status: Value,
) -> Result<Presentation> {
    let own = program
        .documents
        .iter()
        .filter(|d| d.ownership == "user")
        .map(|d| d.uri.clone())
        .collect();
    let key = program.keys.verification(verification)?;
    let placement = Placement {
        program: &program.root,
        verification: Some(key),
        user_files: &own,
        sources: &program.sources,
        current: &program.provenance,
        upstream: &program.embedded.provenance,
    };
    let mut diagnostics = Vec::new();
    let mut inventory = Vec::new();
    for item in findings {
        let f = item.finding;
        let mut placed =
            placement.place(&f.identity, f.kind, &f.message, &f.notes, &f.contributions)?;
        for d in &mut placed {
            d.evidence = item.evidence.clone();
        }
        inventory.push(json!({"identity":f.identity.data_in(&program.keys,Some(key))?,"kind":f.kind.code(),"message":f.message,"evidence":item.evidence,"fallback":placed.iter().any(|d|d.fallback),"located":!placed.is_empty()}));
        diagnostics.extend(placed);
    }
    status["findings"] = json!(inventory);
    Ok(Presentation {
        diagnostics,
        status,
    })
}

pub fn completion_preparation_failure(
    program: &LoadedProgram,
    verification: denotate_ir::VerificationId,
    exhausted: Option<denotate_check::Inconclusive>,
    reason: &str,
) -> Result<Presentation> {
    use denotate_presentation::{Contribution, Identity, Kind, Role};
    let users = program
        .documents
        .iter()
        .filter(|d| d.ownership == "user")
        .map(|d| d.uri.clone())
        .collect();
    let key = program.keys.verification(verification)?;
    let placement = Placement {
        program: &program.root,
        verification: Some(key),
        user_files: &users,
        sources: &program.sources,
        current: &program.provenance,
        upstream: &program.embedded.provenance,
    };
    let contributions = vec![Contribution {
        occurrence: verification.into(),
        role: Role::Declaration,
    }];
    let mut evidence = json!({"kind":"unsupported-semantics"});
    let (identity, kind) = if let Some(c) = exhausted {
        evidence = denotate_presentation::with_limit_details(
            json!({"kind":"incomplete","phase":c.phase,"resource":c.resource}),
            c.details,
        );
        (
            Identity::CompletionMeaning("preparation"),
            Kind::Inconclusive,
        )
    } else {
        (Identity::UnsupportedSemantics, Kind::UnsupportedSemantics)
    };
    let mut diagnostics = placement.place(&identity, kind, reason, &[], &contributions)?;
    for d in &mut diagnostics {
        d.evidence = evidence.clone();
    }
    let status = json!({"backend":{"backend":"sat","configuration":"original-completion-v1"},"semantics":"completion","state":"incomplete","incomplete":true,"hasFailures":false,"reason":reason,"findings":[{"identity":identity.data_in(&program.keys,Some(key))?,"kind":kind.code(),"message":reason,"evidence":evidence,"fallback":diagnostics.iter().any(|d|d.fallback),"located":!diagnostics.is_empty()}]});
    Ok(Presentation {
        diagnostics,
        status,
    })
}

/// Capability refusal is shared by CLI and editor; it is not a semantic verdict.
pub fn unsupported_semantics(
    program: &LoadedProgram,
    verification: denotate_ir::VerificationId,
    reason: &str,
) -> Result<Presentation> {
    use denotate_presentation::{Contribution, Identity, Kind, Role};
    let v = program.corpus.verification(verification).ok_or(
        denotate_presentation::Error::InvalidFinding("unknown verification"),
    )?;
    let key = program.keys.verification(verification)?;
    let users = program
        .documents
        .iter()
        .filter(|d| d.ownership == "user")
        .map(|d| d.uri.clone())
        .collect();
    let placement = Placement {
        program: &program.root,
        verification: Some(key),
        user_files: &users,
        sources: &program.sources,
        current: &program.provenance,
        upstream: &program.embedded.provenance,
    };
    let identity = Identity::UnsupportedSemantics;
    let kind = Kind::UnsupportedSemantics;
    let mut contributions = vec![Contribution {
        occurrence: verification.into(),
        role: Role::Declaration,
    }];
    if let Some(h) = v.options.hypothesis {
        contributions.push(Contribution {
            occurrence: h.into(),
            role: Role::Condition,
        });
    }
    let mut diagnostics = placement.place(&identity, kind, reason, &[], &contributions)?;
    for diagnostic in &mut diagnostics {
        diagnostic.evidence = json!({"kind":kind.code()});
    }
    let status = json!({"state":"incomplete", "consistency":"unknown", "reason":reason,
        "findings":[{"identity":identity.data_in(&program.keys,Some(key))?,"kind":kind.code(),"message":reason,
            "fallback":diagnostics.iter().any(|d|d.fallback),"located":!diagnostics.is_empty()}]});
    Ok(Presentation {
        diagnostics,
        status,
    })
}
