//! InputMapping wording and source-view selection. The checker knows neither
//! this vocabulary nor the source-selection policy; a different DSL supplies its own
//! presenter. Missing attribution is a creator failure, never a user error.

use crate::{
    attribution::{AttributionError, RelatedLocation, SourceView},
    lowering::LoweredProgram,
};
use denotate_check::*;
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

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
    pub related: Vec<RelatedLocation>,
    pub notes: Vec<String>,
    /// Every original rule on the reported/blocking cycles, even library rules with no
    /// location in this source view. Ground instances remain in Verification.
    pub cycle_rules: Vec<RuleId>,
}

#[derive(Debug)]
pub enum PresentationError {
    Provenance(ProvenanceError),
    Attribution(AttributionError),
    MissingOrigin {
        occurrence: OccurrenceId,
        view: SourceView,
    },
    InvalidFinding(&'static str),
}
impl From<AttributionError> for PresentationError {
    fn from(error: AttributionError) -> Self {
        Self::Attribution(error)
    }
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
/// missing/foreign provenance. `view` selects DSL or Denotate attribution;
/// locations always belong to the immutable source snapshots supplied here.
pub fn present(
    lowered: &LoweredProgram,
    report: &Verification<'_>,
    sources: &Sources,
    view: &str,
) -> Result<Vec<Diagnostic>> {
    let view = SourceView::try_from(view)?;
    lowered.attribution.validate(&lowered.corpus, sources)?;
    let origins = |id: OccurrenceId| -> Result<Vec<RelatedLocation>> {
        if !lowered.corpus.contains_occurrence(id) {
            return Err(PresentationError::InvalidFinding(
                "finding belongs to another corpus",
            ));
        }
        Ok(lowered
            .attribution
            .origin(id, sources, view)?
            .into_iter()
            .map(|span| RelatedLocation::new(span, "cycle contributor"))
            .collect())
    };
    let required = |id: OccurrenceId| -> Result<SourceSpan> {
        if !lowered.corpus.contains_occurrence(id) {
            return Err(PresentationError::InvalidFinding(
                "finding belongs to another corpus",
            ));
        }
        lowered
            .attribution
            .origin(id, sources, view)?
            .ok_or(PresentationError::MissingOrigin {
                occurrence: id,
                view,
            })
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
                targets.insert(required(*target)?);
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
                let (cycle_targets, _) =
                    cycle_locations(lowered, report.program(), region, &origins, view)?;
                let proven_failure = matches!(region.completion, CompletionOutcome::NoMeaning(_));
                has_no_meaning |= proven_failure;
                related.extend(cycle_targets.into_iter().map(|span| {
                    RelatedLocation::new(
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
                    related: unique_locations(related.iter().cloned()),
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
            let target = required(*target_occurrence)?;
            targets.insert(target);
            related.push(RelatedLocation::new(target, "conflicting mapping target"));
            related.push(RelatedLocation::new(
                required(*input_occurrence)?,
                "conflicting Input",
            ));
            if !rule.body.is_empty() {
                let guard = *lowered.attribution.guards.get(&(rule.source, view)).ok_or(
                    PresentationError::MissingOrigin {
                        occurrence: rule.source.into(),
                        view,
                    },
                )?;
                guards.insert(sources.text(guard)?.to_owned());
                related.push(RelatedLocation::new(guard, "mapping condition"));
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
        if lowered.has_value_tests() {
            notes.push(observation_note(lowered, &example.observation)?);
        }
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
            let (locations, _) =
                cycle_locations(lowered, report.program(), region, &origins, view)?;
            related.extend(
                locations.into_iter().map(|span| {
                    RelatedLocation::new(span, "conflict confined to no-meaning region")
                }),
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
                related: unique_locations(related.iter().filter(|o| o.span != primary).cloned()),
                notes: notes.clone(),
                cycle_rules: vec![],
            });
        }
    }
    for region in &report.unresolved {
        let (targets, mut related) =
            cycle_locations(lowered, report.program(), region, &origins, view)?;
        let masks = mask_cycle(lowered, region, view);
        let slots = masks
            .iter()
            .map(|m| name(m.target))
            .collect::<Result<BTreeSet<_>>>()?
            .into_iter()
            .collect::<Vec<_>>();
        let mut authored_negation = false;
        for edge in &region.cycle.edges {
            if edge.polarity == Polarity::Negative && !origins(edge.premise)?.is_empty() {
                authored_negation = true;
            }
        }
        let mask_dependency = match slots.as_slice() {
            [] => None,
            _ if authored_negation => Some(
                "This dependency cycle involves masking and an authored negated condition".into(),
            ),
            [slot] => Some(format!(
                "Masking Slot {} depends on its own availability",
                slot
            )),
            _ => Some(format!(
                "Masking Slots {} depends cyclically on their availability",
                slots.join(" and ")
            )),
        };
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
                let message = no_meaning_message(lowered, report.program(), &finding.bad_input, mask_dependency.as_deref())?;
                (DiagnosticKind::NoMeaning, message)
            }
            CompletionOutcome::Inconclusive(cause) => (DiagnosticKind::Inconclusive, format!("Consistency checking for this dependency cycle is inconclusive: {} exhausted its {} budget.",cause.phase,cause.resource)),
            CompletionOutcome::Deferred { blocked_by } => {
                for id in blocked_by {
                    if let Some(upstream) = report.unresolved.iter().find(|r|r.component==*id) {
                        let (locations, _) = cycle_locations(lowered, report.program(), upstream, &origins, view)?;
                        related.extend(locations.into_iter().map(|span| RelatedLocation::new(span,
                            if matches!(upstream.completion,CompletionOutcome::NoMeaning(_)) { "upstream no-meaning finding" }
                            else { "unsettled upstream component" })));
                    }
                }
                (DiagnosticKind::UnsupportedCycle, "Consistency checking for this cycle was deferred: an upstream component is not settled. See related locations.".into())
            }
            CompletionOutcome::NoContradiction => match region.outcome {
                RegionOutcome::Unsupported => (DiagnosticKind::UnsupportedCycle, mask_dependency.as_ref().map(|d| format!("{d}. The checker could not establish a single result.")).unwrap_or_else(|| "This dependency cycle contains negation and is unsupported by the current checker. Its equations have a solution for every input observation, but that does not establish meaning.".into())),
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
                related: unique_locations(related.iter().filter(|o| o.span != primary).cloned()),
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
    mask_dependency: Option<&str>,
) -> Result<String> {
    let subject = mask_dependency
        .map(|d| format!("{d}; no consistent result exists"))
        .unwrap_or_else(|| "These rules have no consistent result".into());
    let literals = match program.input_conjunction(condition, &Limits::default()) {
        Ok(Some(literals)) => literals,
        // Wording is optional: a summary budget must not suppress a finding.
        Ok(None) | Err(CheckError::LimitExceeded { .. }) => {
            return Ok(format!("{subject} in the example input observation."));
        }
        Err(_) => {
            return Err(PresentationError::InvalidFinding(
                "invalid failure condition",
            ));
        }
    };
    if literals.is_empty() {
        return Ok(format!("{subject} for any input observation."));
    }
    let mut clauses = Vec::new();
    for (atom, value) in literals {
        let (input, value_case) = input_case(lowered, &atom)?;
        let phrase = if !lowered.has_value_tests() {
            if value {
                "present".into()
            } else {
                "absent".into()
            }
        } else if value_case == lowered.library.other {
            if value {
                "an integer outside the tested literals".into()
            } else {
                "absent or a tested integer".into()
            }
        } else {
            let number = lowered
                .corpus
                .constant(value_case)
                .ok_or(PresentationError::InvalidFinding("unknown integer"))?;
            if value {
                number.name.clone()
            } else {
                format!("not {} (including absence)", number.name)
            }
        };
        clauses.push(format!(
            "{}{} is {}",
            if mask_dependency.is_some() {
                "Input "
            } else {
                ""
            },
            input.name,
            phrase
        ));
    }
    Ok(format!(
        "{subject} {} {}.",
        if mask_dependency.is_some() {
            "when"
        } else {
            "whenever"
        },
        clauses.join(" and ")
    ))
}

fn input_case<'a>(
    lowered: &'a LoweredProgram,
    atom: &GroundAtom,
) -> Result<(&'a denotate_ir::Constant, ConstantId)> {
    if atom.relation != lowered.library.value || atom.arguments.len() != 2 {
        return Err(PresentationError::InvalidFinding(
            "unexpected InputMapping input",
        ));
    }
    let input = lowered
        .corpus
        .constant(atom.arguments[0])
        .filter(|c| c.sort == lowered.library.input)
        .ok_or(PresentationError::InvalidFinding("unknown input"))?;
    let value = lowered
        .corpus
        .constant(atom.arguments[1])
        .filter(|c| c.sort == lowered.library.integer)
        .ok_or(PresentationError::InvalidFinding("unknown integer case"))?;
    Ok((input, value.id))
}

/// Decode an observation into concrete integers. `other` uses one integer outside
/// K; equality and copying cannot distinguish which outside integer is chosen.
pub fn decode_observation(
    lowered: &LoweredProgram,
    observation: &Observation,
) -> Result<BTreeMap<ConstantId, Option<i64>>> {
    let tested: BTreeSet<i64> = lowered
        .corpus
        .constants()
        .filter(|c| c.sort == lowered.library.integer && c.id != lowered.library.other)
        .map(|c| {
            c.name
                .parse()
                .map_err(|_| PresentationError::InvalidFinding("invalid integer case"))
        })
        .collect::<Result<_>>()?;
    let mut other = 0i64;
    while tested.contains(&other) {
        other = other
            .checked_add(1)
            .ok_or(PresentationError::InvalidFinding("no other integer"))?;
    }
    let mut decoded = BTreeMap::new();
    for atom in observation.present.iter().chain(&observation.absent) {
        let (input, _) = input_case(lowered, atom)?;
        decoded.entry(input.id).or_insert(None);
    }
    for atom in &observation.present {
        let (input, value) = input_case(lowered, atom)?;
        if observation.absent.contains(atom) {
            return Err(PresentationError::InvalidFinding(
                "contradictory observation",
            ));
        }
        let number = if value == lowered.library.other {
            other
        } else {
            lowered
                .corpus
                .constant(value)
                .unwrap()
                .name
                .parse()
                .map_err(|_| PresentationError::InvalidFinding("invalid integer case"))?
        };
        if decoded.insert(input.id, Some(number)).flatten().is_some() {
            return Err(PresentationError::InvalidFinding("multiple input values"));
        }
    }
    Ok(decoded)
}

fn observation_note(lowered: &LoweredProgram, observation: &Observation) -> Result<String> {
    let decoded = decode_observation(lowered, observation)?;
    if !lowered.has_value_tests() {
        let show = |present| {
            let names = decoded
                .iter()
                .filter(|(_, v)| v.is_some() == present)
                .map(|(id, _)| lowered.corpus.constant(*id).unwrap().name.as_str())
                .collect::<Vec<_>>();
            if names.is_empty() {
                "(none)".into()
            } else {
                names.join(", ")
            }
        };
        return Ok(format!(
            "Example observation - inputs present: {}; inputs absent: {}.",
            show(true),
            show(false)
        ));
    }
    let mut cases = Vec::new();
    for (id, value) in decoded {
        let name = &lowered.corpus.constant(id).unwrap().name;
        let outside = observation.present.contains(&GroundAtom::new(
            lowered.library.value,
            [id, lowered.library.other],
        ));
        let value = match value {
            None => "absent".into(),
            Some(n) if outside => format!("other integer (e.g. {n})"),
            Some(n) => n.to_string(),
        };
        cases.push(format!("{name}: {value}"));
    }
    Ok(format!("Example observation - {}.", cases.join("; ")))
}

fn mask_cycle<'a>(
    lowered: &'a LoweredProgram,
    region: &UnresolvedRegion,
    view: SourceView,
) -> Vec<&'a crate::attribution::MaskAttribution> {
    if view != SourceView::TestDsl
        || !region.rules.iter().any(|r| {
            r.body.iter().any(|l| {
                l.polarity == Polarity::Negative && l.term.atom.relation == lowered.library.masked
            })
        })
    {
        return vec![];
    }
    region
        .rules
        .iter()
        .filter_map(|r| lowered.attribution.masks.get(&r.source))
        .collect()
}

fn cycle_locations(
    lowered: &LoweredProgram,
    program: &GroundProgram,
    region: &UnresolvedRegion,
    origins: &impl Fn(OccurrenceId) -> Result<Vec<RelatedLocation>>,
    view: SourceView,
) -> Result<(BTreeSet<SourceSpan>, Vec<RelatedLocation>)> {
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
            targets.extend(locations.iter().map(|o| o.span));
        }
        related.extend(locations);
    }
    // Library negation has no authored `not`. Attribute the finding to the
    // participating mask conditions, retaining any authored negations too.
    // Supporting mappings stay related only.
    let masks = mask_cycle(lowered, region, view);
    if !masks.is_empty() {
        let mask_targets: BTreeSet<_> = masks
            .iter()
            .map(|m| m.condition.unwrap_or(m.statement))
            .collect();
        related.extend(
            mask_targets
                .iter()
                .map(|s| RelatedLocation::new(*s, "mask condition")),
        );
        targets.extend(mask_targets);
        // Mapping facts can be settled outside the SCC while supplying its
        // Slots. These are related dependencies, not additional error sites.
        let mapping_facts: BTreeSet<_> = region
            .rules
            .iter()
            .flat_map(|r| r.body.iter())
            .filter(|l| {
                l.polarity == Polarity::Positive
                    && l.term.atom.relation == lowered.library.mapped_to
            })
            .map(|l| &l.term.atom)
            .collect();
        let cycle_rules: BTreeSet<_> = region.rules.iter().map(|r| r.source).collect();
        for rule in program
            .original_rules()
            .filter(|r| mapping_facts.contains(&r.head.atom) && !cycle_rules.contains(&r.source))
        {
            related.extend(
                origins(rule.source.into())?
                    .into_iter()
                    .map(|o| RelatedLocation::new(o.span, "supporting InputMapping")),
            );
        }
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
            view,
        });
    }
    Ok((targets, related))
}

fn unique_locations(origins: impl IntoIterator<Item = RelatedLocation>) -> Vec<RelatedLocation> {
    let mut result: Vec<RelatedLocation> = Vec::new();
    for origin in origins {
        if let Some(existing) = result.iter_mut().find(|item| item.span == origin.span) {
            // Keep traversal order, but prefer a specific display label over
            // the generic cycle label when both describe the same location.
            if existing.label == "cycle contributor" && origin.label != "cycle contributor" {
                *existing = origin;
            }
        } else {
            result.push(origin);
        }
    }
    result
}
