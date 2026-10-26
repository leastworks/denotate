use crate::{Error, Identity, Result};
use denotate_check::*;
use denotate_ir::*;
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
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
            Self::Counterexample | Self::NoMeaning => Severity::Error,
            Self::UnsupportedRegion | Self::Rewrite => Severity::Warning,
            Self::UnsupportedGroup | Self::Inconclusive | Self::EmptyGroupingDomain => {
                Severity::Information
            }
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
}
impl Role {
    pub fn label(self) -> &'static str {
        match self {
            Self::Producer => "producing rule",
            Self::Contributor => "contributing occurrence",
            Self::Declaration => "participating declaration",
            Self::Obligation => "checked obligation",
            Self::RelatedOnly => "supporting rewrite proof",
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
    Coverage(&'a CoverageReport),
    Group(&'a VerifiedGroup),
    Region(&'a UnresolvedRegion),
}
#[derive(Debug)]
pub struct Finding<'a> {
    pub identity: Identity,
    pub kind: Kind,
    pub message: String,
    pub notes: Vec<String>,
    pub contributions: Vec<Contribution>,
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
pub fn interpret<'a>(corpus: &Corpus, report: &'a Verification<'_>) -> Result<Vec<Finding<'a>>> {
    let mut findings = Vec::new();
    for group in &report.groups {
        let obligation = corpus
            .obligation(group.group.obligation)
            .ok_or(Error::InvalidFinding("foreign obligation"))?;
        let identity = Identity::Group {
            obligation: group.group.obligation,
            tuple: group.group.key.clone(),
        };
        let subject = format!("Obligation {}", obligation.name);
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
                for (atom, step) in &example.evidence {
                    atom_contributions(atom, &mut contributions);
                    if let GroundEvidence::Derived { rule, premises } = &step.evidence {
                        rule_contributions(rule, &mut contributions);
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
                notes.push(match example.replay_scope {
                    ReplayScope::WholeProgram if !report.whole_program_admitted() => "Counterexample replayed on the whole program for this observation only; whole-program admissibility across all inputs remains incomplete.",
                    ReplayScope::WholeProgram => "Counterexample replayed on the whole program.",
                    ReplayScope::ConeOnly => "Counterexample replayed on this obligation's dependency cone only; whole-program admissibility is incomplete.",
                }.into());
                match &example.certification {
                    Some(CertificationOutcome::NotCertified) => notes.push("Whole-program replay was not certified for the attempted observations. Failure to certify alone is not proof of no meaning.".into()),
                    Some(CertificationOutcome::Inconclusive(c)) => notes.push(format!("Whole-program replay certification is inconclusive: {} exhausted its {} budget. The cone counterexample is unchanged.", c.phase, c.resource)),
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
                            "{subject} is inconclusive: {} exhausted its {} budget.",
                            c.phase, c.resource
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
            cycle_rules: cycle_rules.into_iter().collect(),
            evidence: Evidence::Group(group),
        });
    }
    for (id, coverage) in &report.coverage {
        let obligation = corpus
            .obligation(*id)
            .ok_or(Error::InvalidFinding("foreign coverage obligation"))?;
        let subject = format!("Obligation {}", obligation.name);
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
                    "{subject}: coverage checking incomplete ({}: {}).",
                    cause.phase, cause.resource
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
        let notes = Vec::new();
        findings.push(Finding {
            identity: Identity::Coverage(*id),
            kind,
            message,
            notes,
            contributions: vec![Contribution {
                occurrence: (*id).into(),
                role: Role::Obligation,
            }],
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
                    notes.push(format!("Admission remains inconclusive: {} exhausted its {} budget. The separate consistency check established this failure.", c.phase, c.resource));
                }
                (Kind::NoMeaning, "These rules have no consistent result in the example input observation.".into())
            }
            CompletionOutcome::Inconclusive(c) => (Kind::Inconclusive, format!("Consistency checking for this dependency cycle is inconclusive: {} exhausted its {} budget.",c.phase,c.resource)),
            CompletionOutcome::Deferred { blocked_by } => {
                for id in blocked_by { region_contributions(linked_region(report, *id)?, &mut contributions); }
                (Kind::UnsupportedRegion, "Consistency checking for this cycle was deferred: an upstream component is not settled. See related locations.".into())
            }
            CompletionOutcome::NoContradiction => match region.outcome {
                RegionOutcome::Unsupported => (Kind::UnsupportedRegion, "This dependency cycle contains negation and is unsupported by the current checker. Its equations have a solution for every input observation, but that does not establish meaning.".into()),
                RegionOutcome::Inconclusive(c) => (Kind::Inconclusive, format!("Admission of this dependency cycle is inconclusive: {} exhausted its {} budget.",c.phase,c.resource)),
            },
        };
        findings.push(Finding {
            identity: Identity::Region(component.atoms.iter().cloned().collect()),
            kind,
            message,
            notes,
            contributions,
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
pub fn generic_details(corpus: &Corpus, finding: &Finding<'_>) -> Result<Vec<String>> {
    let name = |id: OccurrenceId, name: &str| {
        let spelling = |name: &str| {
            if !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                name.to_owned()
            } else {
                format!("{name:?}")
            }
        };
        corpus
            .namespace(id)
            .into_iter()
            .flat_map(|n| n.segments())
            .map(|s| spelling(s))
            .chain(std::iter::once(spelling(name)))
            .collect::<Vec<_>>()
            .join("::")
    };
    let atom = |a: &GroundAtom| -> Result<String> {
        let relation = corpus
            .relation(a.relation)
            .ok_or(Error::InvalidFinding("unknown witness relation"))?;
        let args = a
            .arguments
            .iter()
            .map(|id| {
                let c = corpus
                    .constant(*id)
                    .ok_or(Error::InvalidFinding("unknown witness constant"))?;
                Ok(name((*id).into(), &c.name))
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(format!(
            "{}({})",
            name(a.relation.into(), &relation.name),
            args.join(", ")
        ))
    };
    let show = |atoms: &BTreeSet<GroundAtom>| -> Result<String> {
        let names = atoms.iter().map(&atom).collect::<Result<BTreeSet<_>>>()?;
        Ok(if names.is_empty() {
            "(none)".into()
        } else {
            names.into_iter().collect::<Vec<_>>().join(", ")
        })
    };
    let mut details = Vec::new();
    let observation = match &finding.evidence {
        Evidence::Coverage(c) => {
            for e in &c.examples {
                let group = e
                    .group
                    .iter()
                    .map(|id| {
                        let c = corpus
                            .constant(*id)
                            .ok_or(Error::InvalidFinding("unknown grouping constant"))?;
                        Ok(name((*id).into(), &c.name))
                    })
                    .collect::<Result<Vec<_>>>()?
                    .join(", ");
                details.push(format!(
                    "Missing group ({group}). Example input observation — present: {}; absent: {}.",
                    show(&e.observation.present)?,
                    show(&e.observation.absent)?
                ));
            }
            None
        }
        Evidence::Group(g) => match &g.outcome {
            VerifiedOutcome::Counterexample(c) => {
                details.push(format!("Replayed tuples: {}.", show(&c.tuples)?));
                Some(&c.observation)
            }
            _ => None,
        },
        Evidence::Region(r) => match &r.completion {
            CompletionOutcome::NoMeaning(n) => Some(&n.observation),
            _ => None,
        },
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
