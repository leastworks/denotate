//! Ungrouped absence obligations. Presence is evidence only after concrete replay;
//! unresolved facts never prove emptiness. Retain one example, independently of
//! the amount of unresolved analysis in the rest of the relation.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::{ObligationId, RelationId};
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PresenceExample<A, W> {
    pub tuple: A,
    pub observation: W,
    pub replay_scope: ReplayScope,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmptinessSummary<A, W> {
    pub example: Option<PresenceExample<A, W>>,
    /// Some permitted worlds could not be settled or certified.
    pub unresolved: bool,
    pub inconclusive: Option<Inconclusive>,
}
pub type EmptinessReport = EmptinessSummary<GroundAtom, Observation>;
pub type EmptinessResult = EmptinessSummary<AtomKey, Candidate>;
impl<A, W> Default for EmptinessSummary<A, W> {
    fn default() -> Self {
        Self {
            example: None,
            unresolved: false,
            inconclusive: None,
        }
    }
}
impl<A, W> EmptinessSummary<A, W> {
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
