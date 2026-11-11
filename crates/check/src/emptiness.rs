//! Ungrouped absence obligations. Presence is evidence only after concrete replay;
//! unresolved facts never prove emptiness. Retain a bounded, keyed sample without
//! changing semantic enumeration or its allowance.
use crate::{
    certification::CertificationDependencies,
    limits::{Budget, Result},
    *,
};
use denotate_ir::{ObligationId, RelationId};
use std::collections::{BTreeMap, BTreeSet};

pub const EMPTINESS_EXAMPLE_LIMIT: usize = 3;

/// Diagnostic retention only: every candidate is checked regardless of this
/// choice. `All` retains every confirmed tuple, not every possible input world.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmptinessExamples {
    Limited(std::num::NonZeroUsize),
    All,
}
impl Default for EmptinessExamples {
    fn default() -> Self {
        Self::Limited(std::num::NonZeroUsize::new(EMPTINESS_EXAMPLE_LIMIT).unwrap())
    }
}
impl EmptinessExamples {
    pub(crate) fn limit(self) -> usize {
        match self {
            Self::Limited(n) => n.get(),
            Self::All => usize::MAX,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PresenceExample<A, W, E> {
    pub tuple: A,
    pub observation: W,
    pub replay_scope: ReplayScope,
    /// Structural dependency-cone inputs, collected after checking under a
    /// separate allowance. Incomplete is distinct from a cone with no inputs.
    pub dependency_inputs: Option<Attribution<BTreeSet<A>>>,
    /// Populated by the separate post-check attribution pass.
    pub attribution: Option<Attribution<E>>,
}
/// Optional diagnostic evidence, separate from semantic completeness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Attribution<E> {
    Complete(E),
    Incomplete(Inconclusive),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmptinessSummary<A, W, E> {
    /// Distinct tuples confirmed present in at least one permitted world.
    /// Exact when complete(); otherwise a lower bound, not a simultaneous count.
    pub present: usize,
    pub examples: Vec<PresenceExample<A, W, E>>,
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
            present: 0,
            examples: vec![],
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
        self.complete() && self.present == 0
    }
}
impl SymbolicMeaning<'_> {
    pub(crate) fn check_emptiness(
        &self,
        limits: &Limits,
        examples: EmptinessExamples,
        mut queries: Option<&mut QueryRun<'_>>,
    ) -> Result<BTreeMap<ObligationId, EmptinessReport>> {
        let mut ordered = self.program.emptiness.iter().collect::<Vec<_>>();
        if let Some(q) = queries.as_ref() {
            ordered.sort_by_key(|(id, _)| q.keys.obligation(**id).unwrap());
        }
        let mut reports = BTreeMap::new();
        for (id, relation) in ordered {
            let _stage =
                limits
                    .progress
                    .scope("emptiness", Some(CheckingTarget::Obligation(*id)), true);
            let mut budget = Budget::tracked(limits);
            let mut report = EmptinessReport::default();
            if let Err(error) = self.empty_relation(
                *relation,
                queries.as_ref().map(|q| q.keys),
                examples.limit(),
                &mut budget,
                &mut report,
            ) {
                budget.failure(&error);
                report.inconclusive = Some(Inconclusive::from_error(error)?);
            }
            // For an unbounded sample, append during checking and sort once
            // afterwards. Re-sorting each insertion would make retention quadratic.
            if examples.limit() == usize::MAX {
                if let Some(q) = &queries {
                    let mut keyed = report
                        .examples
                        .drain(..)
                        .map(|example| {
                            AtomKey::from_atom(q.keys, &example.tuple)
                                .map(|key| (key, example))
                                .map_err(CheckError::Keys)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    keyed.sort_by(|(a, _), (b, _)| a.cmp(b));
                    report.examples = keyed.into_iter().map(|(_, example)| example).collect();
                } else {
                    report.examples.sort_by(|a, b| a.tuple.cmp(&b.tuple));
                }
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
        keys: Option<&denotate_ir::SemanticKeys>,
        example_limit: usize,
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
            let mut counted = false;
            let mut dependencies = None;
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
                            return Err(CheckError::from(c));
                        }
                    },
                };
                if present && !counted {
                    // Preserve the historical first-witness charge exactly. Extra
                    // sample retention does not spend the semantic allowance.
                    if report.present == 0 {
                        budget.charge(atom.arguments.len() + 1, "emptiness evidence")?;
                    }
                    report.present += 1;
                    counted = true;
                    retain_example(report, atom, &observation, scope, keys, example_limit)?;
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
                if dependencies.is_none() {
                    dependencies = Some(CertificationDependencies::new(
                        self.program,
                        [atom.clone()],
                        budget,
                    )?);
                }
                remaining = dependencies.as_ref().unwrap().exclude(
                    context,
                    &remaining,
                    &observation,
                    budget,
                )?;
            }
        }
        Ok(())
    }
}

// A bounded top-k sample, independent of semantic traversal order. In particular,
// sorting all candidates before checking would change resource-limited outcomes.
// Keyless low-level callers use preparation-local atom order, as coverage does.
fn retain_example(
    report: &mut EmptinessReport,
    atom: &GroundAtom,
    observation: &Observation,
    replay_scope: ReplayScope,
    keys: Option<&denotate_ir::SemanticKeys>,
    limit: usize,
) -> Result<()> {
    if limit == usize::MAX {
        report.examples.push(PresenceExample {
            tuple: atom.clone(),
            observation: observation.clone(),
            replay_scope,
            dependency_inputs: None,
            attribution: None,
        });
        return Ok(());
    }
    let mut index = 0;
    let key = keys
        .map(|keys| AtomKey::from_atom(keys, atom))
        .transpose()
        .map_err(CheckError::Keys)?;
    for existing in &report.examples {
        let before = if let (Some(keys), Some(key)) = (keys, &key) {
            key < &AtomKey::from_atom(keys, &existing.tuple).map_err(CheckError::Keys)?
        } else {
            atom < &existing.tuple
        };
        if before {
            break;
        }
        index += 1;
    }
    if index < limit {
        if report.examples.len() == limit {
            report.examples.pop();
        }
        report.examples.insert(
            index,
            PresenceExample {
                tuple: atom.clone(),
                observation: observation.clone(),
                replay_scope,
                dependency_inputs: None,
                attribution: None,
            },
        );
    }
    Ok(())
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
        for (id, report) in reports.iter_mut() {
            let _stage = limits
                .progress
                .advisory("attribution", CheckingTarget::Obligation(*id));
            for example in &mut report.examples {
                let mut budget = Budget::new(limits);
                let result = self.presence_evidence(example, &mut budget);
                example.attribution = Some(match result {
                    Ok(evidence) => Attribution::Complete(evidence),
                    Err(error) => {
                        limits.progress.failure(&error);
                        Attribution::Incomplete(Inconclusive::from_error(error)?)
                    }
                });
                // Display scope must include negative dependencies and alternative
                // producers, not only the selected positive proof. Its own budget
                // cannot change attribution or checking completeness.
                let mut budget = Budget::new(limits);
                let result =
                    self.dependency_inputs_with_budget([example.tuple.clone()], &mut budget);
                example.dependency_inputs = Some(match result {
                    Ok(inputs) => Attribution::Complete(inputs),
                    Err(error) => {
                        limits.progress.failure(&error);
                        Attribution::Incomplete(Inconclusive::from_error(error)?)
                    }
                });
            }
        }
        Ok(())
    }

    fn presence_evidence(
        &self,
        example: &PresenceExample<GroundAtom, Observation, BTreeMap<GroundAtom, EvidenceStep>>,
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
                CertificationOutcome::Inconclusive(c) => Err(CheckError::from(c)),
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
            let original = meaning
                .check_emptiness(&limits, EmptinessExamples::default(), None)
                .unwrap();
            assert!(original.values().all(|r| r.present > 0));
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
                    for example in &mut report.examples {
                        match example.dependency_inputs.take().unwrap() {
                            Attribution::Incomplete(_) => assert_eq!(max_work, 0),
                            Attribution::Complete(inputs) => assert!(inputs.is_empty()),
                        }
                        match example.attribution.take().unwrap() {
                            Attribution::Incomplete(_) => assert_eq!(max_work, 0),
                            Attribution::Complete(steps) => assert!(!steps.is_empty()),
                        }
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
    #[test]
    fn retaining_more_examples_preserves_bounded_semantic_outcomes() {
        let mut c = Corpus::new();
        let s = c.declare_sort("S").unwrap();
        let r = c
            .declare_relation("r", RelationRole::Derived, [Parameter::new("x", s)])
            .unwrap();
        let mut constants = vec![];
        for name in ["a", "b", "c", "d", "e"] {
            let value = c.declare_constant(name, s).unwrap();
            let fact = c.atom(r, [Term::Constant(value)]).unwrap();
            c.add_fact(fact).unwrap();
            constants.push(value);
        }
        c.empty("none", r, "").unwrap();
        let limits = Limits::default();
        let program =
            GroundProgram::prepare(&c, &Domains::from([(s, constants)]), &limits).unwrap();
        let meaning = program.symbolic(&limits).unwrap();
        let mut saw_partial = false;
        let mut saw_complete = false;
        for max_work in 0..2000 {
            let limited = Limits {
                max_work,
                ..limits.clone()
            };
            let check = |cap| {
                let mut report = EmptinessReport::default();
                if let Err(error) =
                    meaning.empty_relation(r, None, cap, &mut Budget::new(&limited), &mut report)
                {
                    report.inconclusive = Some(Inconclusive::from_error(error).unwrap());
                }
                report
            };
            let one = check(1);
            let several = check(EMPTINESS_EXAMPLE_LIMIT);
            let all = check(usize::MAX);
            assert_eq!(
                (one.present, one.unresolved, one.inconclusive, one.proved()),
                (all.present, all.unresolved, all.inconclusive, all.proved())
            );
            assert_eq!(
                (one.present, one.unresolved, one.inconclusive, one.proved()),
                (
                    several.present,
                    several.unresolved,
                    several.inconclusive,
                    several.proved()
                )
            );
            saw_partial |= several.present > 0 && !several.complete();
            if several.complete() {
                assert_eq!(several.present, 5);
                assert_eq!(several.examples.len(), EMPTINESS_EXAMPLE_LIMIT);
                assert_eq!(all.examples.len(), 5);
                saw_complete = true;
                break;
            }
        }
        assert!(saw_partial && saw_complete);
    }

    #[test]
    fn one_tuples_attribution_exhaustion_does_not_spend_anothers_allowance() {
        let mut c = Corpus::new();
        let s = c.declare_sort("S").unwrap();
        let a = c.declare_constant("a", s).unwrap();
        let b = c.declare_constant("b", s).unwrap();
        let r = c
            .declare_relation("r", RelationRole::Derived, [Parameter::new("x", s)])
            .unwrap();
        let mut prior = c
            .declare_relation("seed", RelationRole::Derived, [])
            .unwrap();
        let fact = c.atom(prior, []).unwrap();
        c.add_fact(fact).unwrap();
        for i in 0..12 {
            let next = c
                .declare_relation(format!("step{i}"), RelationRole::Derived, [])
                .unwrap();
            let head = c.atom(next, []).unwrap();
            let body = c.atom(prior, []).unwrap();
            c.add_rule(head, [Literal::Positive(body)]).unwrap();
            prior = next;
        }
        let head = c.atom(r, [Term::Constant(a)]).unwrap();
        let body = c.atom(prior, []).unwrap();
        c.add_rule(head, [Literal::Positive(body)]).unwrap();
        let fact = c.atom(r, [Term::Constant(b)]).unwrap();
        c.add_fact(fact).unwrap();
        c.empty("none", r, "").unwrap();
        let limits = Limits::default();
        let program =
            GroundProgram::prepare(&c, &Domains::from([(s, vec![a, b])]), &limits).unwrap();
        let meaning = program.symbolic(&limits).unwrap();
        let original = meaning
            .check_emptiness(&limits, EmptinessExamples::default(), None)
            .unwrap();
        let mut saw_independent = false;
        for max_work in 0..5000 {
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
            let report = attributed.values_mut().next().unwrap();
            let states = report
                .examples
                .iter()
                .map(|e| matches!(e.attribution, Some(Attribution::Complete(_))))
                .collect::<Vec<_>>();
            if states == [false, true] {
                for e in &mut report.examples {
                    e.attribution = None;
                    e.dependency_inputs = None;
                }
                assert_eq!(&attributed, &original);
                saw_independent = true;
                break;
            }
        }
        assert!(
            saw_independent,
            "a long derivation must not consume the next tuple's attribution allowance"
        );
    }
}
