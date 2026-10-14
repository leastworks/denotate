use crate::{
    limits::{Budget, Result},
    *,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplayScope {
    WholeProgram,
    ConeOnly,
}

/// A finite grounded proof DAG. Positive premises name earlier steps; negative
/// premises only reference a completed provider and its confirmed absence.
#[derive(Debug, Clone)]
pub enum GroundEvidence {
    Input,
    Derived {
        rule: GroundRule,
        premises: Vec<PremiseEvidence>,
    },
}
#[derive(Debug, Clone)]
pub struct EvidenceStep {
    pub order: usize,
    pub evidence: GroundEvidence,
}
#[derive(Debug)]
pub struct Counterexample {
    pub observation: Observation,
    pub replay_scope: ReplayScope,
    /// Every distinct group tuple true in the selected observation, not duplicate
    /// derivations of one tuple. At least two, confirmed by concrete replay.
    pub tuples: BTreeSet<GroundAtom>,
    pub evidence: BTreeMap<GroundAtom, EvidenceStep>,
}
#[derive(Debug)]
pub enum VerifiedOutcome {
    Proved,
    Counterexample(Counterexample),
    Unsupported,
}
#[derive(Debug)]
pub struct VerifiedGroup {
    pub group: AtMostOneGroup,
    pub cone: DependencyCone,
    pub outcome: VerifiedOutcome,
}

/// One reported closed cycle, with every ground rule and premise on that path.
/// This does not purport to enumerate every cycle in the component.
#[derive(Debug)]
pub struct UnresolvedRegion {
    pub component: ComponentId,
    pub cycle: Cycle,
    pub rules: Vec<GroundRule>,
}
#[derive(Debug, Default)]
pub struct FindingMetrics {
    pub witness: Duration,
    pub replay: Duration,
    pub evidence: Duration,
}
#[derive(Debug)]
pub struct Verification<'p> {
    program: &'p GroundProgram,
    pub groups: Vec<VerifiedGroup>,
    pub unresolved: Vec<UnresolvedRegion>,
    pub property_metrics: SymbolicMetrics,
    pub finding_metrics: FindingMetrics,
}
impl Verification<'_> {
    pub fn program(&self) -> &GroundProgram {
        self.program
    }
    pub fn whole_program_admitted(&self) -> bool {
        self.program.is_admitted()
    }
    /// Includes trivially discharged groups (zero/one possible tuple). A blocked
    /// program is never a global pass, even if its independent groups are proved.
    pub fn all_obligations_proved(&self) -> bool {
        self.whole_program_admitted()
            && self
                .groups
                .iter()
                .all(|g| matches!(g.outcome, VerifiedOutcome::Proved))
    }
}

impl<'p> SymbolicMeaning<'p> {
    /// Synchronous checked findings. No partial successful report escapes a limit
    /// or replay failure. Use check_at_most_one for raw, unreplayed conditions.
    pub fn verify_at_most_one(&self, limits: &Limits) -> Result<Verification<'p>> {
        let report = self.check_at_most_one(limits)?;
        let mut budget = Budget::new(limits);
        let mut metrics = FindingMetrics::default();
        let mut groups = Vec::new();
        for check in report.groups {
            budget.tick("findings")?;
            let outcome = match check.outcome {
                GroupOutcome::Proved => VerifiedOutcome::Proved,
                GroupOutcome::Unsupported => VerifiedOutcome::Unsupported,
                GroupOutcome::Overlap(condition) => {
                    let start = Instant::now();
                    let observation = self
                        .context
                        .witness_with_budget(&condition, &mut budget)?
                        .ok_or(CheckError::Internal("overlap has no witness"))?;
                    metrics.witness += start.elapsed();
                    let start = Instant::now();
                    let selected = (!self.program.is_admitted()).then_some(&check.cone.components);
                    let replay = self.program.evaluate_selected(
                        observation.present.iter().cloned(),
                        selected,
                        &mut budget,
                    )?;
                    let replay_scope = if replay.is_complete() {
                        ReplayScope::WholeProgram
                    } else {
                        ReplayScope::ConeOnly
                    };
                    let mut tuples = BTreeSet::new();
                    for tuple in &check.group.tuples {
                        budget.tick("replay confirmation")?;
                        match replay.fact(tuple)? {
                            FactState::Settled(true) => {
                                tuples.insert(tuple.clone());
                            }
                            FactState::Settled(false) => {}
                            FactState::Blocked(_) => {
                                return Err(CheckError::Internal("overlap replay is blocked"));
                            }
                        }
                    }
                    if tuples.len() < 2 {
                        return Err(CheckError::Internal("symbolic overlap did not replay"));
                    }
                    metrics.replay += start.elapsed();
                    let start = Instant::now();
                    let evidence = collect_evidence(&replay, &tuples, &mut budget)?;
                    metrics.evidence += start.elapsed();
                    VerifiedOutcome::Counterexample(Counterexample {
                        observation,
                        replay_scope,
                        tuples,
                        evidence,
                    })
                }
            };
            groups.push(VerifiedGroup {
                group: check.group,
                cone: check.cone,
                outcome,
            });
        }
        let mut unresolved = Vec::new();
        for id in report.unresolved_components {
            budget.tick("cycle evidence")?;
            let component = self
                .program
                .component(id)
                .ok_or(CheckError::Internal("missing component"))?;
            let cycle = component
                .cycle
                .as_ref()
                .ok_or(CheckError::Internal("missing cycle"))?;
            let mut rules = Vec::new();
            let mut seen = BTreeSet::new();
            for edge in &cycle.edges {
                budget.tick("cycle evidence")?;
                if seen.insert(edge.rule) {
                    let rule = self
                        .program
                        .rule(edge.rule)
                        .ok_or(CheckError::Internal("missing cycle rule"))?;
                    budget.charge(rule.body.len(), "cycle evidence")?;
                    rules.push(rule.clone());
                }
            }
            unresolved.push(UnresolvedRegion {
                component: id,
                cycle: cycle.clone(),
                rules,
            });
        }
        Ok(Verification {
            program: self.program,
            groups,
            unresolved,
            property_metrics: report.metrics,
            finding_metrics: metrics,
        })
    }
}

fn collect_evidence(
    replay: &Replay<'_>,
    roots: &BTreeSet<GroundAtom>,
    budget: &mut Budget<'_>,
) -> Result<BTreeMap<GroundAtom, EvidenceStep>> {
    let mut result = BTreeMap::new();
    let mut pending: Vec<_> = roots.iter().cloned().collect();
    while let Some(fact) = pending.pop() {
        budget.tick("evidence")?;
        if result.contains_key(&fact) {
            continue;
        }
        let derivation = replay
            .derivation(&fact)
            .ok_or(CheckError::Internal("missing positive evidence"))?;
        let evidence = match &derivation.evidence {
            Evidence::Input => GroundEvidence::Input,
            Evidence::Derived { rule, premises } => {
                let rule = replay
                    .program()
                    .rule(*rule)
                    .ok_or(CheckError::Internal("missing evidence rule"))?;
                for premise in premises {
                    budget.tick("evidence")?;
                    match premise {
                        PremiseEvidence::Positive { fact, .. } => {
                            let support = replay
                                .derivation(fact)
                                .ok_or(CheckError::Internal("missing support"))?;
                            if support.order >= derivation.order {
                                return Err(CheckError::Internal("ungrounded evidence"));
                            }
                            pending.push(fact.clone());
                        }
                        PremiseEvidence::Absent { fact, provider, .. } => {
                            if replay.absence_provider(fact)?.as_ref() != Some(provider) {
                                return Err(CheckError::Internal("absence did not replay"));
                            }
                        }
                    }
                }
                GroundEvidence::Derived {
                    rule: rule.clone(),
                    premises: premises.clone(),
                }
            }
        };
        result.insert(
            fact,
            EvidenceStep {
                order: derivation.order,
                evidence,
            },
        );
    }
    Ok(result)
}
