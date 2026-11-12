use crate::exhaustion_text;
use crate::{Error, Identity, Result};
use denotate_check::*;
use denotate_ir::*;
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    InvalidAssumption,
    UnvalidatedAssumption,
    InconsistentAssumptions,
    AssumedConclusion,
    ImpossibleCondition,
    AlwaysTrueCondition,
    UnanalysedCondition,
    EmptyGroupingDomain,
    Counterexample,
    NoMeaning,
    UnsupportedGroup,
    UnsupportedRegion,
    Inconclusive,
    Rewrite,
}
impl Kind {
    pub fn code(self) -> &'static str {
        match self {
            Self::InvalidAssumption => "invalid-assumption",
            Self::UnvalidatedAssumption => "unvalidated-assumption",
            Self::InconsistentAssumptions => "inconsistent-assumptions",
            Self::AssumedConclusion => "assumed-conclusion",
            Self::ImpossibleCondition => "impossible-condition",
            Self::AlwaysTrueCondition => "always-true-condition",
            Self::UnanalysedCondition => "unanalysed-condition",
            Self::Counterexample => "counterexample",
            Self::EmptyGroupingDomain => "empty-grouping-domain",
            Self::NoMeaning => "no-meaning",
            Self::UnsupportedGroup => "unsupported-group",
            Self::UnsupportedRegion => "unsupported-region",
            Self::Inconclusive => "inconclusive",
            Self::Rewrite => "redundant",
        }
    }
    pub fn severity(self) -> Severity {
        match self {
            Self::InvalidAssumption
            | Self::Counterexample
            | Self::NoMeaning
            | Self::InconsistentAssumptions => Severity::Error,
            Self::UnsupportedRegion
            | Self::Rewrite
            | Self::AssumedConclusion
            | Self::ImpossibleCondition => Severity::Warning,
            Self::UnvalidatedAssumption
            | Self::UnsupportedGroup
            | Self::Inconclusive
            | Self::EmptyGroupingDomain
            | Self::AlwaysTrueCondition
            | Self::UnanalysedCondition => Severity::Information,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Information,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Role {
    Producer,
    Contributor,
    Declaration,
    Obligation,
    RelatedOnly,
    Condition,
    EnclosingScope,
    BlockingCycle,
    AdmissionAttempt,
}
impl Role {
    pub fn label(self) -> &'static str {
        match self {
            Self::Producer => "producing rule",
            Self::Contributor => "contributing occurrence",
            Self::Declaration => "participating declaration",
            Self::Obligation => "checked obligation",
            Self::RelatedOnly => "supporting rewrite proof",
            Self::Condition => "condition being inspected",
            Self::EnclosingScope => "complete enclosing scope",
            Self::BlockingCycle => "blocking dependency cycle",
            Self::AdmissionAttempt => "skipped admission proof attempt",
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Contribution {
    pub occurrence: OccurrenceId,
    pub role: Role,
}
#[derive(Debug)]
pub enum Evidence<'a> {
    Emptiness(&'a EmptinessReport),
    Coverage(&'a CoverageReport),
    Group(&'a VerifiedGroup),
    Region(&'a UnresolvedRegion),
}
/// Borrow the retained proof; placement never reconstructs a derivation.
#[derive(Debug)]
pub struct PlacementDerivation<'a> {
    pub tuple: &'a GroundAtom,
    pub steps: &'a std::collections::BTreeMap<GroundAtom, EvidenceStep>,
}
/// Independently placed evidence sharing a finding identity. Keeping these
/// groups separate preserves an example's fallback when another is locatable.
#[derive(Debug)]
pub struct PlacementGroup<'a> {
    pub derivation: Option<PlacementDerivation<'a>>,
    pub contributions: Vec<Contribution>,
    pub notes: Vec<String>,
}
#[derive(Debug)]
pub struct Finding<'a> {
    pub identity: Identity,
    pub kind: Kind,
    pub message: String,
    pub notes: Vec<String>,
    pub contributions: Vec<Contribution>,
    pub placement_groups: Vec<PlacementGroup<'a>>,
    pub cycle_rules: Vec<RuleId>,
    /// Original checked evidence, for optional frontend wording and attribution.
    pub evidence: Evidence<'a>,
}

pub fn rule_contributions(rule: &GroundRule, out: &mut Vec<Contribution>) {
    out.push(Contribution {
        occurrence: rule.source.into(),
        role: Role::Producer,
    });
    for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(|l| &l.term)) {
        for occurrence in std::iter::once(atom.occurrence).chain(atom.arguments.iter().copied()) {
            out.push(Contribution {
                occurrence,
                role: Role::Contributor,
            });
        }
        atom_contributions(&atom.atom, out);
    }
}
fn atom_contributions(atom: &GroundAtom, out: &mut Vec<Contribution>) {
    out.push(Contribution {
        occurrence: atom.relation.into(),
        role: Role::Declaration,
    });
    out.extend(atom.arguments.iter().map(|id| Contribution {
        occurrence: (*id).into(),
        role: Role::Declaration,
    }));
}
/// Use the same retained derivation for emptiness and uniqueness placement.
fn derivation_contributions(
    evidence: &std::collections::BTreeMap<GroundAtom, EvidenceStep>,
    contributions: &mut Vec<Contribution>,
) {
    for (atom, step) in evidence {
        step_contributions(atom, step, contributions);
    }
}
pub(crate) fn step_contributions(
    atom: &GroundAtom,
    step: &EvidenceStep,
    contributions: &mut Vec<Contribution>,
) {
    atom_contributions(atom, contributions);
    if let GroundEvidence::Derived { rule, premises } = &step.evidence {
        rule_contributions(rule, contributions);
        for premise in premises {
            let occurrence = match premise {
                PremiseEvidence::Positive { occurrence, .. }
                | PremiseEvidence::Absent { occurrence, .. } => *occurrence,
                PremiseEvidence::Discharged {
                    literal_occurrence, ..
                } => *literal_occurrence,
            };
            contributions.push(Contribution {
                occurrence,
                role: Role::Contributor,
            });
        }
    }
}

fn region_contributions(region: &UnresolvedRegion, out: &mut Vec<Contribution>) {
    for rule in &region.rules {
        rule_contributions(rule, out);
    }
    if let CompletionOutcome::NoMeaning(n) = &region.completion {
        for rule in &n.rules {
            rule_contributions(rule, out);
        }
    }
}
fn linked_region<'a>(
    report: &'a Verification<'_>,
    id: ComponentId,
) -> Result<&'a UnresolvedRegion> {
    report
        .unresolved
        .iter()
        .find(|r| r.component == id)
        .ok_or(Error::InvalidFinding("missing related region"))
}

/// Interpret outcomes once. Frontends may replace wording/choose highlights, but
/// retain each finding's identity, classification and checked evidence.
/// `names` spells relation and constant declarations for the caller's text format.
/// It is used only for visible notes, never finding identity or structured evidence.
pub fn interpret<'a>(
    corpus: &Corpus,
    report: &'a Verification<'_>,
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<Finding<'a>>> {
    let mut findings = Vec::new();
    for group in &report.groups {
        let obligation = corpus
            .obligation(group.group.obligation)
            .ok_or(Error::InvalidFinding("foreign obligation"))?;
        let combined = obligation.requirement.kind() == denotate_ir::Cardinality::ExactlyOne;
        let identity = if combined {
            Identity::Uniqueness {
                obligation: group.group.obligation,
                tuple: group.group.key.clone(),
            }
        } else {
            Identity::Group {
                obligation: group.group.obligation,
                tuple: group.group.key.clone(),
            }
        };
        let subject = format!(
            "Obligation {}{}",
            obligation.name,
            if combined { " (uniqueness)" } else { "" }
        );
        let mut contributions = vec![Contribution {
            occurrence: obligation.id.into(),
            role: Role::Obligation,
        }];
        let mut notes = Vec::new();
        let mut cycle_rules = BTreeSet::new();
        let (kind, message) = match &group.outcome {
            VerifiedOutcome::Proved => continue,
            VerifiedOutcome::Counterexample(example) => {
                if example.tuples.len() < 2
                    || !example
                        .tuples
                        .iter()
                        .all(|t| group.group.tuples.contains(t) && example.evidence.contains_key(t))
                {
                    return Err(Error::InvalidFinding("invalid replayed tuples"));
                }
                derivation_contributions(&example.evidence, &mut contributions);
                notes.push(match example.replay_scope {
                    ReplayScope::WholeProgram if !report.whole_program_admitted() => "Counterexample replayed on the whole program for this observation only; whole-program admissibility across all inputs remains incomplete.",
                    ReplayScope::WholeProgram => "Counterexample replayed on the whole program.",
                    ReplayScope::ConeOnly => "Counterexample replayed on this obligation's dependency cone only; whole-program admissibility is incomplete.",
                }.into());
                match &example.certification {
                    Some(CertificationOutcome::NotCertified) => notes.push("Whole-program replay was not certified for the attempted observations. Failure to certify alone is not proof of no meaning.".into()),
                    Some(CertificationOutcome::Inconclusive(c)) => notes.push(format!("Whole-program replay certification is inconclusive: {}. The cone counterexample is unchanged.", exhaustion_text(c.phase, c.resource, c.details))),
                    _ => {}
                }
                for id in &example.confined_to_no_meaning {
                    let region = linked_region(report, *id)?;
                    if !matches!(region.completion, CompletionOutcome::NoMeaning(_)) {
                        return Err(Error::InvalidFinding("unproved no-meaning implication"));
                    }
                    region_contributions(region, &mut contributions);
                }
                if !example.confined_to_no_meaning.is_empty() {
                    notes.push("This conflict only occurs in observations where the rules at the related no-meaning locations have no consistent result. It remains a cone-only conflict, not a whole-program execution.".into());
                }
                notes.push(
                    "Locations follow the retained grounded derivation for each conflicting tuple."
                        .into(),
                );
                (
                    Kind::Counterexample,
                    format!(
                        "{subject} is violated: {} distinct tuples hold in the replayed observation.",
                        example.tuples.len()
                    ),
                )
            }
            VerifiedOutcome::Unsupported | VerifiedOutcome::Inconclusive(_) => {
                // Potential producers in the checked dependency cone, not arbitrary
                // rules sharing the same source file or namespace.
                let atoms: BTreeSet<_> = group
                    .cone
                    .components
                    .iter()
                    .filter_map(|id| report.program().component(*id))
                    .flat_map(|c| c.atoms.iter())
                    .collect();
                for rule in report
                    .program()
                    .original_rules()
                    .filter(|r| atoms.contains(&r.head.atom))
                {
                    rule_contributions(rule, &mut contributions);
                }
                for tuple in &group.group.tuples {
                    atom_contributions(tuple, &mut contributions);
                }
                for id in &group.cone.blocked_by {
                    let region = linked_region(report, *id)?;
                    region_contributions(region, &mut contributions);
                    cycle_rules.extend(region.rules.iter().map(|r| r.source));
                }
                notes.push("No proof or counterexample is available for this group.".into());
                match &group.outcome {
                    VerifiedOutcome::Inconclusive(c) => (
                        Kind::Inconclusive,
                        format!(
                            "{subject} is inconclusive: {}.",
                            exhaustion_text(c.phase, c.resource, c.details)
                        ),
                    ),
                    _ => (
                        Kind::UnsupportedGroup,
                        format!(
                            "{subject} is unsupported by the selected checker or depends on unsettled regions."
                        ),
                    ),
                }
            }
        };
        findings.push(Finding {
            identity,
            kind,
            message,
            notes,
            contributions,
            placement_groups: vec![],
            cycle_rules: cycle_rules.into_iter().collect(),
            evidence: Evidence::Group(group),
        });
    }
    for (id, emptiness) in &report.emptiness {
        if emptiness.proved() {
            continue;
        }
        let obligation = corpus
            .obligation(*id)
            .ok_or(Error::InvalidFinding("foreign emptiness obligation"))?;
        let message = if emptiness.present > 0 {
            format!(
                "Obligation {}: relation is not empty; {}{} distinct tuples can be present; showing {} examples{}",
                obligation.name,
                if emptiness.complete() {
                    ""
                } else {
                    "at least "
                },
                emptiness.present,
                emptiness.examples.len(),
                if emptiness.complete() {
                    "."
                } else {
                    "; checking incomplete."
                }
            )
        } else {
            format!(
                "Obligation {}: emptiness checking incomplete{}.",
                obligation.name,
                emptiness
                    .inconclusive
                    .map(|c| format!(" ({})", exhaustion_text(c.phase, c.resource, c.details)))
                    .unwrap_or_else(|| " (unresolved permitted worlds)".into())
            )
        };
        let mut contributions = vec![Contribution {
            occurrence: (*id).into(),
            role: Role::Obligation,
        }];
        let notes = Vec::new();
        let mut placement_groups = Vec::new();
        for example in &emptiness.examples {
            let mut group = PlacementGroup {
                derivation: None,
                contributions: vec![Contribution {
                    occurrence: (*id).into(),
                    role: Role::Obligation,
                }],
                notes: vec![presence_note(corpus, names, example)?],
            };
            match &example.attribution {
                Some(Attribution::Complete(evidence)) => {
                    group.derivation = Some(PlacementDerivation {
                        tuple: &example.tuple,
                        steps: evidence,
                    });
                    derivation_contributions(evidence, &mut group.contributions);
                }
                Some(Attribution::Incomplete(c)) => group.notes.push(format!(
                    "Source attribution for {} is incomplete ({}); its counterexample is unchanged. Locations fall back to the obligation.",
                    atom_name(corpus, names, &example.tuple)?, exhaustion_text(c.phase, c.resource, c.details),
                )),
                None => {}
            }
            contributions.extend(group.contributions.iter().copied());
            placement_groups.push(group);
        }
        findings.push(Finding {
            identity: Identity::Emptiness(*id),
            kind: if emptiness.present > 0 {
                Kind::Counterexample
            } else {
                Kind::Inconclusive
            },
            message,
            notes,
            contributions,
            placement_groups,
            cycle_rules: vec![],
            evidence: Evidence::Emptiness(emptiness),
        });
    }
    for (id, coverage) in &report.coverage {
        let obligation = corpus
            .obligation(*id)
            .ok_or(Error::InvalidFinding("foreign coverage obligation"))?;
        let subject = format!(
            "Obligation {}{}",
            obligation.name,
            if obligation.requirement.kind() == denotate_ir::Cardinality::ExactlyOne {
                " (coverage)"
            } else {
                ""
            }
        );
        let (kind, message) = if coverage.missing > 0 {
            (
                Kind::Counterexample,
                format!(
                    "{subject}: {}{} {} coverage{}",
                    if coverage.complete() { "" } else { "at least " },
                    coverage.missing,
                    if coverage.missing == 1 {
                        "group fails"
                    } else {
                        "groups fail"
                    },
                    if coverage.complete() {
                        "."
                    } else {
                        "; checking incomplete."
                    }
                ),
            )
        } else if coverage.no_groups {
            (
                Kind::EmptyGroupingDomain,
                format!("{subject}: no groups: the grouping domain is empty"),
            )
        } else if let Some(cause) = coverage.inconclusive {
            (
                Kind::Inconclusive,
                format!(
                    "{subject}: coverage checking incomplete ({}).",
                    exhaustion_text(cause.phase, cause.resource, cause.details)
                ),
            )
        } else if coverage.unsupported > 0 {
            (
                Kind::UnsupportedGroup,
                format!("{subject}: coverage is unsupported in some permitted worlds."),
            )
        } else {
            continue;
        };
        let obligation_contribution = Contribution {
            occurrence: (*id).into(),
            role: Role::Obligation,
        };
        let mut contributions = vec![obligation_contribution];
        let mut placement_groups = Vec::new();
        for example in &coverage.examples {
            let mut group = PlacementGroup {
                derivation: None,
                contributions: vec![obligation_contribution],
                notes: vec![coverage_note(corpus, names, example)?],
            };
            group
                .contributions
                .extend(example.group.iter().map(|id| Contribution {
                    occurrence: (*id).into(),
                    role: Role::Declaration,
                }));
            contributions.extend(group.contributions.iter().copied());
            placement_groups.push(group);
        }
        findings.push(Finding {
            identity: Identity::Coverage(*id),
            kind,
            message,
            notes: vec![],
            contributions,
            placement_groups,
            cycle_rules: vec![],
            evidence: Evidence::Coverage(coverage),
        });
    }
    for region in &report.unresolved {
        let component = report
            .program()
            .component(region.component)
            .ok_or(Error::InvalidFinding("foreign component"))?;
        let mut contributions = Vec::new();
        region_contributions(region, &mut contributions);
        let mut rules: BTreeSet<_> = region.rules.iter().map(|r| r.source).collect();
        let mut notes = vec!["This is not a proof that the program has no meaning. Independent obligation results remain available.".into()];
        let (kind, message) = match &region.completion {
            CompletionOutcome::NoMeaning(n) => {
                rules = n.rules.iter().map(|r| r.source).collect();
                notes = vec!["Other observations remain unsupported unless separately certified; a consistent equation solution does not establish meaning.".into(), "Independent obligation results remain available.".into()];
                if let RegionOutcome::Inconclusive(c) = region.outcome {
                    notes.push(format!("Admission remains inconclusive: {}. The separate consistency check established this failure.", exhaustion_text(c.phase, c.resource, c.details)));
                }
                (Kind::NoMeaning, "These rules have no consistent result in the example input observation.".into())
            }
            CompletionOutcome::Inconclusive(c) => (Kind::Inconclusive, format!("Consistency checking for this dependency cycle is inconclusive: {}.", exhaustion_text(c.phase, c.resource, c.details))),
            CompletionOutcome::Deferred { blocked_by } => {
                for id in blocked_by { region_contributions(linked_region(report, *id)?, &mut contributions); }
                (Kind::UnsupportedRegion, "Consistency checking for this cycle was deferred: an upstream component is not settled. See related locations.".into())
            }
            CompletionOutcome::NoContradiction => match region.outcome {
                RegionOutcome::Unsupported => (Kind::UnsupportedRegion, "This dependency cycle contains negation and is unsupported by the current checker. Its equations have a solution for every input observation, but that does not establish meaning.".into()),
                RegionOutcome::Inconclusive(c) => (Kind::Inconclusive, format!("Admission of this dependency cycle is inconclusive: {}.", exhaustion_text(c.phase, c.resource, c.details))),
            },
        };
        for skip in &region.admission_skips {
            notes.push(format!(
                "Admission skipped a {} proof for {}: {}. Other proof attempts continued.",
                skip.kind.label(),
                atom_name(corpus, names, &skip.head)?,
                exhaustion_text(skip.reason.phase, skip.reason.resource, skip.reason.details)
            ));
            if let Some(rule) = skip.rule.and_then(|id| report.program().original_rule(id)) {
                contributions.push(Contribution {
                    occurrence: rule.source.into(),
                    role: Role::AdmissionAttempt,
                });
            }
            if let Some(occurrence) = skip.occurrence {
                contributions.push(Contribution {
                    occurrence,
                    role: Role::AdmissionAttempt,
                });
            }
        }
        findings.push(Finding {
            identity: Identity::Region(component.atoms.iter().cloned().collect()),
            kind,
            message,
            notes,
            contributions,
            placement_groups: vec![],
            cycle_rules: rules.into_iter().collect(),
            evidence: Evidence::Region(region),
        });
    }
    for finding in &mut findings {
        for c in &finding.contributions {
            if !corpus.contains_occurrence(c.occurrence) {
                return Err(Error::InvalidFinding("evidence belongs to another corpus"));
            }
        }
    }
    Ok(findings)
}

/// Default IR vocabulary. A DSL can instead decode the same observation into
/// its own value model without replacing the shared interpretation above.
pub fn generic_details(
    corpus: &Corpus,
    finding: &Finding<'_>,
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<String>> {
    let show = |atoms| world_atoms(corpus, names, atoms);
    let mut details = Vec::new();
    let observation = match &finding.evidence {
        // Tuple/world notes are attached only to that example's locations.
        Evidence::Emptiness(_) => None,
        // Missing-group notes are attached only to that group's locations.
        Evidence::Coverage(_) => None,
        Evidence::Group(g) => match &g.outcome {
            VerifiedOutcome::Counterexample(c) => {
                details.push(format!("Replayed tuples: {}.", show(&c.tuples)?));
                let note = input_note(
                    corpus,
                    names,
                    &c.observation,
                    c.replay_scope,
                    c.dependency_inputs.as_ref(),
                )?;
                if !note.is_empty() {
                    details.push(note.trim_start().into());
                }
                None
            }
            _ => None,
        },
        Evidence::Region(r) => {
            details.push(crate::cycles::ground_cycle_note(corpus, names, &r.cycle)?);
            match &r.completion {
                CompletionOutcome::NoMeaning(n) => Some(&n.observation),
                _ => None,
            }
        }
    };
    if let Some(o) = observation {
        details.push(format!(
            "Example input observation — present: {}; absent: {}.",
            show(&o.present)?,
            show(&o.absent)?
        ));
    }
    Ok(details)
}

pub(crate) fn atom_name(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    a: &GroundAtom,
) -> Result<String> {
    corpus
        .relation(a.relation)
        .ok_or(Error::InvalidFinding("unknown witness relation"))?;
    let args = a
        .arguments
        .iter()
        .map(|id| {
            corpus
                .constant(*id)
                .ok_or(Error::InvalidFinding("unknown witness constant"))?;
            Ok(names((*id).into()))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(format!("{}({})", names(a.relation.into()), args.join(", ")))
}
fn world_atoms(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    atoms: &BTreeSet<GroundAtom>,
) -> Result<String> {
    let atom = |a| atom_name(corpus, names, a);
    let names = atoms.iter().map(&atom).collect::<Result<BTreeSet<_>>>()?;
    Ok(if names.is_empty() {
        "(none)".into()
    } else {
        names.into_iter().collect::<Vec<_>>().join(", ")
    })
}

/// Restrict the displayed world to the checker-supplied structural input scope.
/// The complete replay witness remains in structured evidence.
fn presence_note(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    example: &PresenceExample<
        GroundAtom,
        Observation,
        std::collections::BTreeMap<GroundAtom, EvidenceStep>,
    >,
) -> Result<String> {
    let mut note = format!(
        "Replayed present tuple: {}.",
        atom_name(corpus, names, &example.tuple)?
    );
    note.push_str(&input_note(
        corpus,
        names,
        &example.observation,
        example.replay_scope,
        example.dependency_inputs.as_ref(),
    )?);
    Ok(note)
}

fn input_note(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    observation: &Observation,
    replay_scope: ReplayScope,
    dependency_inputs: Option<&Attribution<BTreeSet<GroundAtom>>>,
) -> Result<String> {
    let mut note = String::new();
    let (present, absent, label) = match dependency_inputs {
        Some(Attribution::Complete(inputs)) => {
            if inputs.is_empty() {
                return Ok(note);
            }
            (
                observation.present.intersection(inputs).cloned().collect(),
                observation.absent.intersection(inputs).cloned().collect(),
                "Inputs in dependency cone",
            )
        }
        scope => {
            note.push_str(" Dependency-cone inputs unavailable");
            if let Some(Attribution::Incomplete(c)) = scope {
                note.push_str(&format!(
                    " ({})",
                    exhaustion_text(c.phase, c.resource, c.details)
                ));
            }
            note.push_str("; showing the full observation.");
            (
                observation.present.clone(),
                observation.absent.clone(),
                "Example input observation",
            )
        }
    };
    note.push_str(&format!(
        " {label} — present: {}; absent: {}. Scope: {}.",
        world_atoms(corpus, names, &present)?,
        world_atoms(corpus, names, &absent)?,
        match replay_scope {
            ReplayScope::WholeProgram => "whole-program",
            ReplayScope::ConeOnly => "cone-only",
        },
    ));
    Ok(note)
}

fn coverage_note(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    example: &CoverageExample,
) -> Result<String> {
    let group = example
        .group
        .iter()
        .map(|id| {
            corpus
                .constant(*id)
                .ok_or(Error::InvalidFinding("unknown grouping constant"))?;
            Ok(names((*id).into()))
        })
        .collect::<Result<Vec<_>>>()?
        .join(", ");
    let mut note = format!("Missing group ({group}).");
    note.push_str(&input_note(
        corpus,
        names,
        &example.observation,
        example.replay_scope,
        example.dependency_inputs.as_ref(),
    )?);
    Ok(note)
}

/// Context diagnostics concern the selection, not a witness or checked group.
pub struct ContextFinding {
    pub identity: Identity,
    pub kind: Kind,
    pub message: String,
    pub notes: Vec<String>,
    pub contributions: Vec<Contribution>,
}
pub fn context_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    report: &CheckedReport<'_>,
) -> Result<Vec<ContextFinding>> {
    let Some(key) = &report.results.value.context.verification else {
        return Ok(vec![]);
    };
    let v = corpus
        .verifications()
        .find(|v| keys.verification(v.id).is_ok_and(|k| k == key))
        .ok_or(Error::InvalidFinding("unknown verification"))?;
    let primary = Contribution {
        occurrence: v.id.into(),
        role: Role::Declaration,
    };
    let mut findings = Vec::new();
    if report.results.value.inconsistent_assumptions {
        let mut contributions = vec![primary];
        contributions.extend(v.assumptions.iter().map(|a| Contribution {
            occurrence: (*a).into(),
            role: Role::RelatedOnly,
        }));
        findings.push(ContextFinding {
            identity: Identity::InconsistentAssumptions,
            kind: Kind::InconsistentAssumptions,
            message: "Selected assumptions permit no input world; obligations were not checked."
                .into(),
            notes: vec![],
            contributions,
        });
    }
    for (key, result) in &report.results.value.notices {
        let (kind, explanation) = match result.state {
            NoticeState::Impossible => (
                Kind::ImpossibleCondition,
                "Condition is impossible in this scope.".to_owned(),
            ),
            NoticeState::AlwaysTrue => (
                Kind::AlwaysTrueCondition,
                "Condition is always true in this scope.".to_owned(),
            ),
            NoticeState::Unknown(NoticeUnknown::Unsupported) => (
                Kind::UnanalysedCondition,
                "Condition could not be analysed: it depends on an unsupported cycle.".into(),
            ),
            NoticeState::Unknown(NoticeUnknown::Inconclusive(c)) => (
                Kind::UnanalysedCondition,
                format!(
                    "Condition could not be analysed: {}.",
                    exhaustion_text(c.phase, c.resource, c.details)
                ),
            ),
            NoticeState::Unknown(NoticeUnknown::Deadline { phase, details }) => (
                Kind::UnanalysedCondition,
                format!(
                    "Condition could not be analysed: {}.",
                    exhaustion_text(phase, "deadline", details)
                ),
            ),
            _ => continue,
        };
        let n = corpus
            .notices()
            .find(|n| keys.notice(n.id).is_ok_and(|k| k == key))
            .ok_or(Error::InvalidFinding("unknown notice"))?;
        let mut contributions = vec![
            Contribution {
                occurrence: n.id.into(),
                role: Role::Declaration,
            },
            Contribution {
                occurrence: n.condition.into(),
                role: Role::Condition,
            },
        ];
        if let Some(parent) = n.within {
            contributions.push(Contribution {
                occurrence: parent.into(),
                role: Role::EnclosingScope,
            });
        }
        let blocking_rules = result.blockers.values().flatten().collect::<BTreeSet<_>>();
        for key in blocking_rules {
            let rule = corpus
                .rules()
                .find(|r| keys.rule(r.id).is_ok_and(|k| k == key))
                .ok_or(Error::InvalidFinding("unknown notice blocking rule"))?;
            contributions.push(Contribution {
                occurrence: rule.id.into(),
                role: Role::BlockingCycle,
            });
        }
        findings.push(ContextFinding {
            identity: Identity::Notice(n.id),
            kind,
            message: if n.message.is_empty() {
                explanation.into()
            } else {
                format!("{}: {explanation}", n.message)
            },
            notes: vec![],
            contributions,
        });
    }
    for (a, o) in corpus.assumption_conclusions(v.id) {
        findings.push(ContextFinding {identity:Identity::AssumedConclusion(a,o),kind:Kind::AssumedConclusion, notes:vec![],
            message:format!("Assumption {} constrains the conclusion of obligation {} (directly or through its dependencies).", corpus.assumption(a).unwrap().name,corpus.obligation(o).unwrap().name),
            contributions:vec![Contribution {occurrence:v.id.into(),role:Role::Declaration},Contribution {occurrence:a.into(),role:Role::RelatedOnly},Contribution {occurrence:o.into(),role:Role::RelatedOnly}] });
    }
    Ok(findings)
}
