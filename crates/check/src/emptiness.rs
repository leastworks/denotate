//! Ungrouped absence obligations. Presence is evidence only after concrete replay;
//! unresolved facts never prove emptiness. Retain one example, independently of
//! the amount of unresolved analysis in the rest of the relation.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::{ObligationId, RelationId};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PresenceExample<A, W> {
    pub tuple: A,
    pub observation: W,
    pub replay_scope: ReplayScope,
}
/// Optional source attribution, separate from semantic completeness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Attribution<E> {
    Complete(E),
    Incomplete(Inconclusive),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmptinessSummary<A, W, E> {
    pub example: Option<PresenceExample<A, W>>,
    /// None when there is no example (or before the post-check attribution pass).
    pub attribution: Option<Attribution<E>>,
    /// Some permitted worlds could not be settled or certified.
    pub unresolved: bool,
    pub inconclusive: Option<Inconclusive>,
}
pub type EmptinessReport =
    EmptinessSummary<GroundAtom, Observation, BTreeMap<GroundAtom, EvidenceStep>>;
pub type EmptinessResult = EmptinessSummary<AtomKey, Candidate, EvidenceKeys>;
impl<A, W, E> Default for EmptinessSummary<A, W, E> {
    fn default() -> Self {
        Self {
            example: None,
            attribution: None,
            unresolved: false,
            inconclusive: None,
        }
    }
}
impl<A, W, E> EmptinessSummary<A, W, E> {
    pub fn complete(&self) -> bool {
        !self.unresolved && self.inconclusive.is_none()
    }
    pub fn proved(&self) -> bool {
        self.complete() && self.example.is_none()
    }
}
impl SymbolicMeaning<'_> {
    pub(crate) fn check_emptiness(
        &self,
        limits: &Limits,
        mut queries: Option<&mut QueryRun<'_>>,
    ) -> Result<BTreeMap<ObligationId, EmptinessReport>> {
        let mut ordered = self.program.emptiness.iter().collect::<Vec<_>>();
        if let Some(q) = queries.as_ref() {
            ordered.sort_by_key(|(id, _)| q.keys.obligation(**id).unwrap());
        }
        let mut reports = BTreeMap::new();
        for (id, relation) in ordered {
            let mut budget = Budget::tracked(limits);
            let mut report = EmptinessReport::default();
            if let Err(error) = self.empty_relation(*relation, &mut budget, &mut report) {
                budget.failure(&error);
                report.inconclusive = Some(Inconclusive::from_error(error)?);
            }
            if let Some(q) = queries.as_mut() {
                let dependency = if q.receipts.get(&QueryKey::CoverageMeaning).is_some() {
                    QueryKey::CoverageMeaning
                } else {
                    QueryKey::Symbolic
                };
                budget.record(
                    q.receipts,
                    QueryKey::Emptiness(q.keys.obligation(*id).map_err(CheckError::Keys)?.clone()),
                    [dependency],
                )?;
            }
            reports.insert(*id, report);
        }
        Ok(reports)
    }
    fn empty_relation(
        &self,
        relation: RelationId,
        budget: &mut Budget<'_>,
        report: &mut EmptinessReport,
    ) -> Result<()> {
        use biodivine_lib_bdd::op_function;
        let context = &self.context;
        budget.check("emptiness")?;
        for atom in self.program.atoms().filter(|a| a.relation == relation) {
            budget.tick("emptiness conditions")?;
            let (mut remaining, blocked) = match self.fact(atom)? {
                SymbolicFact::Settled(c) => (
                    context.apply(&context.permitted_worlds(), &c, op_function::and, budget)?,
                    false,
                ),
                SymbolicFact::Blocked(_) => (context.permitted_worlds(), true),
                SymbolicFact::Inconclusive(c) => {
                    report.inconclusive = Some(c);
                    continue;
                }
            };
            loop {
                budget.tick("emptiness search")?;
                let Some(observation) = context.witness_with_budget(&remaining, budget)? else {
                    break;
                };
                let replay = self.program.evaluate_selected(
                    observation.present.iter().cloned(),
                    None,
                    budget,
                )?;
                let scope = if replay.is_complete() {
                    ReplayScope::WholeProgram
                } else {
                    ReplayScope::ConeOnly
                };
                let (present, scope) = match replay.fact(atom)? {
                    FactState::Settled(value) => (value, scope),
                    FactState::Blocked(_) => match self
                        .program
                        .certify_with_budget(observation.present.iter().cloned(), budget)?
                    {
                        CertificationOutcome::Certified(c) => {
                            (c.facts.contains(atom), ReplayScope::WholeProgram)
                        }
                        CertificationOutcome::NotCertified => {
                            report.unresolved = true;
                            (false, scope)
                        }
                        CertificationOutcome::Inconclusive(c) => {
                            return Err(CheckError::LimitExceeded {
                                phase: c.phase,
                                resource: c.resource,
                            });
                        }
                    },
                };
                if present && report.example.is_none() {
                    budget.charge(atom.arguments.len() + 1, "emptiness evidence")?;
                    report.example = Some(PresenceExample {
                        tuple: atom.clone(),
                        observation: observation.clone(),
                        replay_scope: scope,
                    });
                }
                if !blocked {
                    // A settled symbolic presence must agree with replay.
                    if !present {
                        return Err(CheckError::Internal(
                            "emptiness replay disagrees with symbolic presence",
                        ));
                    }
                    break;
                }
                // Certification can vary by world. Keep unresolved worlds visible,
                // and continue looking for a replayed presence under the same budget.
                let mut world = context.true_condition();
                for input in context.inputs() {
                    let mut literal = context.input_with_budget(input, budget)?;
                    if !observation.present.contains(input) {
                        literal = context.apply(
                            &context.true_condition(),
                            &literal,
                            |_, b| b.map(|v| !v),
                            budget,
                        )?;
                    }
                    world = context.apply(&world, &literal, op_function::and, budget)?;
                }
                remaining = context.apply(
                    &remaining,
                    &world,
                    |a, b| op_function::and(a, b.map(|v| !v)),
                    budget,
                )?;
            }
        }
        Ok(())
    }
}

impl GroundProgram {
    /// Run only after semantic checking, with a fresh allowance per example.
    /// Attribution exhaustion never consumes a semantic query's budget or alters
    /// its completeness. Cancellation and invalid evidence remain hard errors.
    pub(crate) fn attribute_emptiness(
        &self,
        reports: &mut BTreeMap<ObligationId, EmptinessReport>,
        limits: &Limits,
    ) -> Result<()> {
        for report in reports.values_mut() {
            let Some(example) = &report.example else {
                continue;
            };
            let mut budget = Budget::new(limits);
            let result = self.presence_evidence(example, &mut budget);
            report.attribution = Some(match result {
                Ok(evidence) => Attribution::Complete(evidence),
                Err(error) => Attribution::Incomplete(Inconclusive::from_error(error)?),
            });
        }
        Ok(())
    }

    fn presence_evidence(
        &self,
        example: &PresenceExample<GroundAtom, Observation>,
        budget: &mut Budget<'_>,
    ) -> Result<BTreeMap<GroundAtom, EvidenceStep>> {
        let replay =
            self.evaluate_selected(example.observation.present.iter().cloned(), None, budget)?;
        let roots = BTreeSet::from([example.tuple.clone()]);
        match replay.fact(&example.tuple)? {
            FactState::Settled(true) => crate::findings::collect_evidence(&replay, &roots, budget),
            FactState::Blocked(_) => match self
                .certify_with_budget(example.observation.present.iter().cloned(), budget)?
            {
                CertificationOutcome::Certified(certified)
                    if certified.facts.contains(&example.tuple) =>
                {
                    crate::certification::certified_evidence(&certified, &roots, budget)
                }
                CertificationOutcome::Inconclusive(c) => Err(CheckError::LimitExceeded {
                    phase: c.phase,
                    resource: c.resource,
                }),
                _ => Err(CheckError::Internal("presence attribution did not certify")),
            },
            FactState::Settled(false) => {
                Err(CheckError::Internal("presence attribution did not replay"))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use denotate_ir::*;

    #[test]
    fn optional_attribution_limits_do_not_change_presence_or_completeness() {
        for unresolved in [false, true] {
            let mut c = Corpus::new();
            let s = c.declare_sort("S").unwrap();
            let a = c.declare_constant("a", s).unwrap();
            let b = c.declare_constant("b", s).unwrap();
            let r = c
                .declare_relation("r", RelationRole::Derived, [Parameter::new("x", s)])
                .unwrap();
            let fact = c.atom(r, [Term::Constant(a)]).unwrap();
            c.add_fact(fact).unwrap();
            if unresolved {
                let head = c.atom(r, [Term::Constant(b)]).unwrap();
                let body = c.atom(r, [Term::Constant(b)]).unwrap();
                c.add_rule(head, [Literal::Negative(body)]).unwrap();
            }
            c.empty("none", r, "").unwrap();
            let limits = Limits::default();
            let program =
                GroundProgram::prepare(&c, &Domains::from([(s, vec![a, b])]), &limits).unwrap();
            let meaning = program.symbolic(&limits).unwrap();
            let original = meaning.check_emptiness(&limits, None).unwrap();
            assert!(original.values().all(|r| r.example.is_some()));
            assert_eq!(original.values().next().unwrap().complete(), !unresolved);
            for max_work in [0, limits.max_work] {
                let mut attributed = original.clone();
                program
                    .attribute_emptiness(
                        &mut attributed,
                        &Limits {
                            max_work,
                            ..limits.clone()
                        },
                    )
                    .unwrap();
                for (id, report) in &mut attributed {
                    match report.attribution.take().unwrap() {
                        Attribution::Incomplete(_) => assert_eq!(max_work, 0),
                        Attribution::Complete(steps) => assert!(!steps.is_empty()),
                    }
                    assert_eq!(report, &original[id]);
                }
            }
            let mut attributed = original;
            let cancelled = Limits::default();
            cancelled.cancellation.cancel();
            assert_eq!(
                program.attribute_emptiness(&mut attributed, &cancelled),
                Err(CheckError::Cancelled)
            );
        }
    }
}
