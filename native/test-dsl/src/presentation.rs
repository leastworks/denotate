//! InputMapping wording and source-view selection. The checker knows neither
//! this vocabulary nor these attribution roles; a different DSL supplies its own
//! presenter. Missing attribution is a creator failure, never a user error.

use crate::lowering::LoweredProgram;
use denotate_check::*;
use denotate_ir::*;
use std::{collections::BTreeSet, fmt};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticKind {
    OverlappingMappings,
    UnsupportedCycle,
    NoMeaning,
    UnsupportedGroup,
    Inconclusive,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Information,
}
impl DiagnosticKind {
    pub fn severity(self) -> DiagnosticSeverity {
        match self {
            Self::OverlappingMappings | Self::NoMeaning => DiagnosticSeverity::Error,
            Self::UnsupportedCycle => DiagnosticSeverity::Warning,
            Self::UnsupportedGroup | Self::Inconclusive => DiagnosticSeverity::Information,
        }
    }
}
#[derive(Debug)]
pub struct Diagnostic {
    pub kind: DiagnosticKind,
    pub message: String,
    pub primary: SourceSpan,
    pub related: Vec<Origin>,
    pub notes: Vec<String>,
    /// Every original rule on the reported/blocking cycles, even library rules with no
    /// location in this source view. Ground instances remain in Verification.
    pub cycle_rules: Vec<RuleId>,
}

#[derive(Debug)]
pub enum PresentationError {
    Provenance(ProvenanceError),
    MissingOrigin {
        occurrence: OccurrenceId,
        role: &'static str,
        view: String,
    },
    InvalidFinding(&'static str),
}
impl From<ProvenanceError> for PresentationError {
    fn from(e: ProvenanceError) -> Self {
        Self::Provenance(e)
    }
}
impl fmt::Display for PresentationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Creator-facing presentation failure: {self:?}")
    }
}
impl std::error::Error for PresentationError {}
type Result<T> = std::result::Result<T, PresentationError>;

/// Call only after successful checking. Returns no partial diagnostic list on
/// missing/foreign provenance. `view` selects e.g. "test-dsl" or "denotate";
/// locations always belong to the immutable source snapshots supplied here.
pub fn present(
    lowered: &LoweredProgram,
    report: &Verification<'_>,
    sources: &Sources,
    view: &str,
) -> Result<Vec<Diagnostic>> {
    let origins = |id: OccurrenceId| -> Result<Vec<Origin>> {
        if !lowered.corpus.contains_occurrence(id) {
            return Err(PresentationError::InvalidFinding(
                "finding belongs to another corpus",
            ));
        }
        Ok(lowered
            .provenance
            .in_view(id, sources, view)?
            .into_iter()
            .cloned()
            .collect())
    };
    let required = |id: OccurrenceId, role: &'static str| -> Result<Vec<Origin>> {
        let values: Vec<_> = origins(id)?
            .into_iter()
            .filter(|o| o.role == role)
            .collect();
        if values.is_empty() {
            Err(PresentationError::MissingOrigin {
                occurrence: id,
                role,
                view: view.into(),
            })
        } else {
            Ok(values)
        }
    };
    let name = |id| -> Result<&str> {
        lowered
            .corpus
            .constant(id)
            .map(|c| c.name.as_str())
            .ok_or(PresentationError::InvalidFinding("unknown constant"))
    };
    let mut diagnostics = Vec::new();
    for group in &report.groups {
        if matches!(group.outcome, VerifiedOutcome::Proved) {
            continue;
        }
        if group.group.obligation != lowered.library.unique_input || group.group.key.len() != 1 {
            return Err(PresentationError::InvalidFinding(
                "unexpected InputMapping obligation",
            ));
        }
        let slot = group.group.key[0];
        if matches!(
            group.outcome,
            VerifiedOutcome::Unsupported | VerifiedOutcome::Inconclusive(_)
        ) {
            // A skipped check has no counterexample derivation to follow. Attribute the
            // skipped check to every possible mapping producer in this group,
            // not to dependency mappings for other slots in the same cone.
            let mut mappings = BTreeSet::new();
            for tuple in &group.group.tuples {
                if tuple.relation != lowered.library.supplies
                    || tuple.arguments.len() != 2
                    || tuple.arguments[1] != slot
                {
                    return Err(PresentationError::InvalidFinding(
                        "unexpected blocked tuple",
                    ));
                }
                mappings.insert(GroundAtom::new(
                    lowered.library.mapped_to,
                    tuple.arguments.clone(),
                ));
            }
            let mut targets = BTreeSet::new();
            for rule in report.program().rules() {
                if !mappings.contains(&rule.head.atom) {
                    continue;
                }
                let [_, target] = rule.head.arguments.as_slice() else {
                    return Err(PresentationError::InvalidFinding(
                        "unexpected mapping arity",
                    ));
                };
                targets.extend(required(*target, "target")?.into_iter().map(|o| o.span));
            }
            if targets.is_empty()
                || (group.cone.blocked_by.is_empty()
                    && matches!(group.outcome, VerifiedOutcome::Unsupported))
            {
                return Err(PresentationError::InvalidFinding(
                    "unsupported group has no mappings or blocking cycles",
                ));
            }
            let mut related = Vec::new();
            let mut cycle_rules = BTreeSet::new();
            let mut has_no_meaning = false;
            for component in &group.cone.blocked_by {
                let region = report
                    .unresolved
                    .iter()
                    .find(|r| r.component == *component)
                    .ok_or(PresentationError::InvalidFinding("missing blocking cycle"))?;
                let (cycle_targets, _) = cycle_locations(region, &origins, view)?;
                let proven_failure = matches!(region.completion, CompletionOutcome::NoMeaning(_));
                has_no_meaning |= proven_failure;
                related.extend(cycle_targets.into_iter().map(|span| {
                    Origin::new(
                        span,
                        if proven_failure {
                            "blocking no-meaning finding"
                        } else {
                            "blocking unsupported cycle"
                        },
                    )
                }));
                cycle_rules.extend(region.rules.iter().map(|r| r.source));
            }
            let cause = if has_no_meaning {
                "a region with a no-consistent-result finding"
            } else if group.cone.blocked_by.len() == 1 {
                "an unsupported cycle"
            } else {
                "unsupported cycles"
            };
            let mut message = format!(
                "Overlap check for slot {} was skipped: it depends on {cause}. See related locations.",
                name(slot)?
            );
            let kind = if let VerifiedOutcome::Inconclusive(cause) = group.outcome {
                message = format!(
                    "Overlap check for slot {} is inconclusive: {} exhausted its {} budget.",
                    name(slot)?,
                    cause.phase,
                    cause.resource
                );
                DiagnosticKind::Inconclusive
            } else {
                DiagnosticKind::UnsupportedGroup
            };
            for primary in targets {
                diagnostics.push(Diagnostic {
                    kind,
                    message: message.clone(),
                    primary,
                    related: unique_origins(related.iter().cloned()),
                    notes: vec!["No proof or counterexample is available for this slot.".into()],
                    cycle_rules: cycle_rules.iter().copied().collect(),
                });
            }
            continue;
        }
        let VerifiedOutcome::Counterexample(example) = &group.outcome else {
            return Err(PresentationError::InvalidFinding(
                "unexpected group outcome",
            ));
        };
        let mut targets = BTreeSet::new();
        let mut related = Vec::new();
        let mut guards = BTreeSet::new();
        let mut inputs = BTreeSet::new();
        for tuple in &example.tuples {
            if tuple.relation != lowered.library.supplies
                || tuple.arguments.len() != 2
                || tuple.arguments[1] != slot
            {
                return Err(PresentationError::InvalidFinding(
                    "unexpected conflicting tuple",
                ));
            }
            inputs.insert(name(tuple.arguments[0])?);
            let mapping = GroundAtom::new(lowered.library.mapped_to, tuple.arguments.clone());
            let Some(EvidenceStep {
                evidence: GroundEvidence::Derived { rule, .. },
                ..
            }) = example.evidence.get(&mapping)
            else {
                return Err(PresentationError::InvalidFinding(
                    "missing mapping evidence",
                ));
            };
            let [input_occurrence, target_occurrence] = rule.head.arguments.as_slice() else {
                return Err(PresentationError::InvalidFinding(
                    "unexpected mapping evidence arity",
                ));
            };
            for origin in required(*target_occurrence, "target")? {
                targets.insert(origin.span);
                related.push(Origin::new(origin.span, "conflicting mapping target"));
            }
            related.extend(required(*input_occurrence, "input")?);
            let rule_guards = if rule.body.is_empty() {
                vec![]
            } else {
                required(rule.source.into(), "guard")?
            };
            for origin in rule_guards {
                guards.insert(sources.text(origin.span)?.to_owned());
                related.push(origin);
            }
        }
        let template = &lowered
            .corpus
            .obligation(group.group.obligation)
            .ok_or(PresentationError::InvalidFinding("unknown obligation"))?
            .message_template;
        let mut message = template.replace("{slot}", name(slot)?).replace(
            "{inputs}",
            &inputs.into_iter().collect::<Vec<_>>().join(", "),
        );
        if !guards.is_empty() {
            message.push_str(&format!(
                " Mapping conditions: {}.",
                guards
                    .into_iter()
                    .map(|g| format!("`{g}`"))
                    .collect::<Vec<_>>()
                    .join("; ")
            ));
        }
        let mut notes = vec![match example.replay_scope {
            ReplayScope::WholeProgram if !report.whole_program_admitted() => "Counterexample replayed on the whole program for this observation only; whole-program admissibility across all inputs remains incomplete.".into(),
            ReplayScope::WholeProgram => "Counterexample replayed on the whole program.".into(),
            ReplayScope::ConeOnly => "Counterexample replayed on this obligation's dependency cone only; whole-program admissibility is incomplete.".into(),
        }];
        match &example.certification {
            Some(CertificationOutcome::NotCertified) => notes.push("Whole-program replay was not certified for the attempted observations. Failure to certify alone is not proof of no meaning.".into()),
            Some(CertificationOutcome::Inconclusive(cause)) => notes.push(format!("Whole-program replay certification is inconclusive: {} exhausted its {} budget. The cone counterexample is unchanged.", cause.phase, cause.resource)),
            _ => {}
        }
        for component in &example.confined_to_no_meaning {
            let region = report
                .unresolved
                .iter()
                .find(|r| r.component == *component)
                .filter(|r| matches!(r.completion, CompletionOutcome::NoMeaning(_)))
                .ok_or(PresentationError::InvalidFinding(
                    "missing no-meaning implication target",
                ))?;
            let (locations, _) = cycle_locations(region, &origins, view)?;
            related.extend(
                locations
                    .into_iter()
                    .map(|span| Origin::new(span, "conflict confined to no-meaning region")),
            );
        }
        if !example.confined_to_no_meaning.is_empty() {
            notes.push("This conflict only occurs in observations where the rules at the related no-meaning locations have no consistent result. It remains a cone-only conflict, not a whole-program execution.".into());
        }
        notes.push(
            "Locations follow the retained grounded derivation for each conflicting tuple.".into(),
        );
        for primary in targets {
            diagnostics.push(Diagnostic {
                kind: DiagnosticKind::OverlappingMappings,
                primary,
                message: message.clone(),
                related: unique_origins(related.iter().filter(|o| o.span != primary).cloned()),
                notes: notes.clone(),
                cycle_rules: vec![],
            });
        }
    }
    for region in &report.unresolved {
        let (targets, mut related) = cycle_locations(region, &origins, view)?;
        let mut rules = region
            .rules
            .iter()
            .map(|r| r.source)
            .collect::<BTreeSet<_>>();
        let mut notes = vec!["This is not a proof that the program has no meaning. Independent obligation results remain available.".into()];
        let (kind, message) = match &region.completion {
            CompletionOutcome::NoMeaning(finding) => {
                rules = finding.rules.iter().map(|r|r.source).collect();
                for rule in &finding.rules { related.extend(origins(rule.source.into())?); }
                notes = vec![
                    observation_note(lowered, &finding.observation)?,
                    "Other observations remain unsupported unless separately certified; a consistent equation solution does not establish meaning.".into(),
                    "Independent obligation results remain available.".into(),
                ];
                (DiagnosticKind::NoMeaning, no_meaning_message(lowered, report.program(), &finding.bad_input)?)
            }
            CompletionOutcome::Inconclusive(cause) => (DiagnosticKind::Inconclusive, format!("Consistency checking for this dependency cycle is inconclusive: {} exhausted its {} budget.",cause.phase,cause.resource)),
            CompletionOutcome::Deferred { blocked_by } => {
                for id in blocked_by {
                    if let Some(upstream) = report.unresolved.iter().find(|r|r.component==*id) {
                        let (locations, _) = cycle_locations(upstream, &origins, view)?;
                        related.extend(locations.into_iter().map(|span| Origin::new(span,
                            if matches!(upstream.completion,CompletionOutcome::NoMeaning(_)) { "upstream no-meaning finding" }
                            else { "unsettled upstream component" })));
                    }
                }
                (DiagnosticKind::UnsupportedCycle, "Consistency checking for this cycle was deferred: an upstream component is not settled. See related locations.".into())
            }
            CompletionOutcome::NoContradiction => match region.outcome {
                RegionOutcome::Unsupported => (DiagnosticKind::UnsupportedCycle, "This dependency cycle contains negation and is unsupported by the current checker. Its equations have a solution for every input observation, but that does not establish meaning.".into()),
                RegionOutcome::Inconclusive(cause) => (DiagnosticKind::Inconclusive, format!("Admission of this dependency cycle is inconclusive: {} exhausted its {} budget.", cause.phase, cause.resource)),
            },
        };
        if kind == DiagnosticKind::NoMeaning {
            if let RegionOutcome::Inconclusive(cause) = region.outcome {
                notes.push(format!("Admission remains inconclusive: {} exhausted its {} budget. The separate consistency check established this failure.",cause.phase,cause.resource));
            }
        }
        for primary in targets {
            diagnostics.push(Diagnostic {
                kind,
                message: message.clone(),
                primary,
                related: unique_origins(related.iter().filter(|o| o.span != primary).cloned()),
                notes: notes.clone(),
                cycle_rules: rules.iter().copied().collect(),
            });
        }
    }
    Ok(diagnostics)
}

fn no_meaning_message(
    lowered: &LoweredProgram,
    program: &GroundProgram,
    condition: &Condition,
) -> Result<String> {
    let literals = match program.input_conjunction(condition, &Limits::default()) {
        Ok(Some(literals)) => literals,
        // Wording is optional: a summary budget must not suppress a finding.
        Ok(None) | Err(CheckError::LimitExceeded { .. }) => {
            return Ok(
                "These rules have no consistent result in the example input observation.".into(),
            );
        }
        Err(_) => {
            return Err(PresentationError::InvalidFinding(
                "invalid failure condition",
            ));
        }
    };
    if literals.is_empty() {
        return Ok("These rules have no consistent result for any input observation.".into());
    }
    let mut clauses = Vec::new();
    for (atom, value) in literals {
        if atom.relation != lowered.library.present || atom.arguments.len() != 1 {
            return Err(PresentationError::InvalidFinding(
                "unexpected InputMapping input",
            ));
        }
        let input = lowered
            .corpus
            .constant(atom.arguments[0])
            .ok_or(PresentationError::InvalidFinding("unknown input value"))?;
        clauses.push(format!(
            "{} is {}",
            input.name,
            if value { "present" } else { "absent" }
        ));
    }
    Ok(format!(
        "These rules have no consistent result whenever {}.",
        clauses.join(" and ")
    ))
}

fn observation_note(lowered: &LoweredProgram, observation: &Observation) -> Result<String> {
    let show = |facts: &BTreeSet<GroundAtom>| -> Result<String> {
        facts
            .iter()
            .map(|a| {
                let relation = lowered
                    .corpus
                    .relation(a.relation)
                    .ok_or(PresentationError::InvalidFinding("unknown input relation"))?;
                let values = a
                    .arguments
                    .iter()
                    .map(|id| {
                        lowered
                            .corpus
                            .constant(*id)
                            .map(|c| c.name.as_str())
                            .ok_or(PresentationError::InvalidFinding("unknown input value"))
                    })
                    .collect::<Result<Vec<_>>>()?
                    .join(", ");
                Ok(if a.relation == lowered.library.present {
                    values
                } else {
                    format!("{}({values})", relation.name)
                })
            })
            .collect::<Result<Vec<_>>>()
            .map(|v| {
                if v.is_empty() {
                    "(none)".into()
                } else {
                    v.join(", ")
                }
            })
    };
    Ok(format!(
        "Example observation - inputs present: {}; inputs absent: {}.",
        show(&observation.present)?,
        show(&observation.absent)?
    ))
}

fn cycle_locations(
    region: &UnresolvedRegion,
    origins: &impl Fn(OccurrenceId) -> Result<Vec<Origin>>,
    view: &str,
) -> Result<(BTreeSet<SourceSpan>, Vec<Origin>)> {
    let mut related = Vec::new();
    let mut targets = BTreeSet::new();
    let mut rule_locations = BTreeSet::new();
    for rule in &region.rules {
        let locations = origins(rule.source.into())?;
        rule_locations.extend(locations.iter().map(|o| o.span));
        related.extend(locations);
    }
    for edge in &region.cycle.edges {
        let locations = origins(edge.premise)?;
        if edge.polarity == Polarity::Negative {
            let preferred: Vec<_> = locations.iter().filter(|o| o.role == "not").collect();
            if preferred.is_empty() {
                targets.extend(locations.iter().map(|o| o.span));
            } else {
                targets.extend(preferred.into_iter().map(|o| o.span));
            }
        }
        related.extend(locations);
    }
    // A library can introduce the negative edge without a location in the
    // user's source view. Point to participating authored rules instead; this
    // does not turn the unsupported cycle into a proven user error.
    if targets.is_empty() {
        targets = rule_locations;
    }
    if targets.is_empty() {
        // Term-only provenance is useful too. Fail only when the whole reported
        // cycle has no location in this view, not merely an unlocated negation.
        for rule in &region.rules {
            for occurrence in std::iter::once(rule.head.occurrence)
                .chain(rule.head.arguments.iter().copied())
                .chain(rule.body.iter().flat_map(|literal| {
                    std::iter::once(literal.term.occurrence)
                        .chain(literal.term.arguments.iter().copied())
                }))
            {
                related.extend(origins(occurrence)?);
            }
        }
        targets.extend(related.iter().map(|o| o.span));
    }
    if targets.is_empty() {
        return Err(PresentationError::MissingOrigin {
            occurrence: region
                .cycle
                .edges
                .first()
                .ok_or(PresentationError::InvalidFinding("empty reported cycle"))?
                .premise,
            role: "cycle location",
            view: view.into(),
        });
    }
    Ok((targets, related))
}

fn unique_origins(origins: impl IntoIterator<Item = Origin>) -> Vec<Origin> {
    let mut result = Vec::new();
    for origin in origins {
        if !result.contains(&origin) {
            result.push(origin);
        }
    }
    result
}
