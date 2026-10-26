//! Coverage ranges over resolved grouping domains, never just producing tuples.
//! Results retain bounded examples; enumeration and replay share a work allowance.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::{ConstantId, ConstantKey, ObligationId, RelationId, SemanticKeys};
use std::collections::BTreeMap;

pub const COVERAGE_EXAMPLE_LIMIT: usize = 3;
#[derive(Debug, Clone)]
pub(crate) struct CoverageShape {
    pub relation: RelationId,
    pub columns: Vec<usize>,
    pub domains: Vec<Vec<ConstantId>>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoverageExample<T = ConstantId, W = Observation> {
    pub group: Vec<T>,
    pub observation: W,
    pub replay_scope: ReplayScope,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoverageSummary<T, W> {
    pub examined: usize,
    pub missing: usize,
    pub unsupported: usize,
    pub inconclusive: Option<Inconclusive>,
    pub no_groups: bool,
    pub examples: Vec<CoverageExample<T, W>>,
}
pub type CoverageReport = CoverageSummary<ConstantId, Observation>;
pub type CoverageResult = CoverageSummary<ConstantKey, Candidate>;
impl<T, W> Default for CoverageSummary<T, W> {
    fn default() -> Self {
        Self {
            examined: 0,
            missing: 0,
            unsupported: 0,
            inconclusive: None,
            no_groups: false,
            examples: vec![],
        }
    }
}
impl<T, W> CoverageSummary<T, W> {
    pub fn complete(&self) -> bool {
        self.unsupported == 0 && self.inconclusive.is_none()
    }
    pub fn proved(&self) -> bool {
        self.complete() && self.missing == 0
    }
}

impl SymbolicMeaning<'_> {
    pub(crate) fn check_coverage(
        &self,
        limits: &Limits,
        mut queries: Option<&mut QueryRun<'_>>,
    ) -> Result<BTreeMap<ObligationId, CoverageReport>> {
        let mut ordered = self.program.coverage.iter().collect::<Vec<_>>();
        if let Some(q) = queries.as_ref() {
            ordered.sort_by_key(|(id, _)| q.keys.obligation(**id).unwrap());
        }
        let mut reports = BTreeMap::new();
        for (id, shape) in ordered {
            let mut budget = Budget::tracked(limits);
            let mut report = CoverageReport::default();
            let result = self.coverage_obligation(
                shape,
                queries.as_ref().map(|q| q.keys),
                &mut budget,
                &mut report,
            );
            if let Err(error) = result {
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
                    QueryKey::Coverage(q.keys.obligation(*id).map_err(CheckError::Keys)?.clone()),
                    [dependency],
                )?;
            }
            reports.insert(*id, report);
        }
        Ok(reports)
    }
    fn coverage_obligation(
        &self,
        shape: &CoverageShape,
        keys: Option<&SemanticKeys>,
        budget: &mut Budget<'_>,
        report: &mut CoverageReport,
    ) -> Result<()> {
        budget.check("coverage enumeration")?;
        if shape.domains.iter().any(Vec::is_empty) {
            report.no_groups = true;
            return Ok(());
        }
        // Allocate only the domain factors and one cursor, not their product.
        for domain in &shape.domains {
            budget.charge(domain.len(), "coverage domains")?;
        }
        let mut domains = shape.domains.clone();
        if let Some(keys) = keys {
            for domain in &mut domains {
                domain.sort_by_key(|id| keys.constant(*id).unwrap());
            }
        }
        budget.charge(domains.len(), "coverage enumeration")?;
        let mut positions = vec![0; domains.len()];
        let mut members: BTreeMap<Vec<ConstantId>, Vec<GroundAtom>> = BTreeMap::new();
        for atom in self
            .program
            .atoms()
            .filter(|a| a.relation == shape.relation)
        {
            budget.charge(
                1 + shape.columns.len() + atom.arguments.len(),
                "coverage members",
            )?;
            members
                .entry(shape.columns.iter().map(|c| atom.arguments[*c]).collect())
                .or_default()
                .push(atom.clone());
        }
        loop {
            budget.charge(1 + positions.len(), "coverage enumeration")?;
            let group = positions
                .iter()
                .enumerate()
                .map(|(i, p)| domains[i][*p])
                .collect::<Vec<_>>();
            let tuples = members.get(&group).map_or(&[][..], Vec::as_slice);
            let (example, unresolved) = self.coverage_group(tuples, budget)?;
            report.examined = increment(report.examined)?;
            if unresolved {
                report.unsupported = increment(report.unsupported)?;
            }
            if let Some((observation, replay_scope)) = example {
                report.missing = increment(report.missing)?;
                if report.examples.len() < COVERAGE_EXAMPLE_LIMIT {
                    report.examples.push(CoverageExample {
                        group,
                        observation,
                        replay_scope,
                    });
                }
            }
            // Mixed-radix successor, including exactly one empty grouping tuple.
            let mut advanced = false;
            for i in (0..positions.len()).rev() {
                positions[i] += 1;
                if positions[i] < domains[i].len() {
                    advanced = true;
                    break;
                }
                positions[i] = 0;
            }
            if !advanced {
                break;
            }
        }
        Ok(())
    }
    fn coverage_group(
        &self,
        tuples: &[GroundAtom],
        budget: &mut Budget<'_>,
    ) -> Result<(Option<(Observation, ReplayScope)>, bool)> {
        use biodivine_lib_bdd::op_function;
        let context = &self.context;
        let mut covered = context.false_condition();
        let mut incomplete = None;
        for atom in tuples {
            budget.tick("coverage conditions")?;
            match self.fact(atom)? {
                SymbolicFact::Settled(c) => {
                    covered = context.apply(&covered, &c, op_function::or, budget)?
                }
                SymbolicFact::Blocked(_) => {}
                SymbolicFact::Inconclusive(c) => incomplete = Some(c),
            }
        }
        let mut remaining = context.apply(
            &context.permitted_worlds(),
            &covered,
            |w, c| op_function::and(w, c.map(|v| !v)),
            budget,
        )?;
        let mut unresolved = false;
        loop {
            budget.tick("coverage search")?;
            let observation = context.witness_with_budget(&remaining, budget)?;
            let Some(observation) = observation else {
                return Ok((None, unresolved));
            };
            if let Some(c) = incomplete {
                return Err(CheckError::LimitExceeded {
                    phase: c.phase,
                    resource: c.resource,
                });
            }
            let replay = self.program.evaluate_selected(
                observation.present.iter().cloned(),
                None,
                budget,
            )?;
            let mut present = false;
            let mut blocked = false;
            for atom in tuples {
                budget.tick("coverage replay")?;
                match replay.fact(atom)? {
                    FactState::Settled(true) => present = true,
                    FactState::Settled(false) => {}
                    FactState::Blocked(_) => blocked = true,
                }
            }
            if !present && !blocked {
                let scope = if replay.is_complete() {
                    ReplayScope::WholeProgram
                } else {
                    ReplayScope::ConeOnly
                };
                return Ok((Some((observation, scope)), unresolved));
            }
            if !present {
                match self
                    .program
                    .certify_with_budget(observation.present.iter().cloned(), budget)?
                {
                    CertificationOutcome::Certified(c) => {
                        if tuples.iter().all(|a| !c.facts.contains(a)) {
                            return Ok((
                                Some((observation, ReplayScope::WholeProgram)),
                                unresolved,
                            ));
                        }
                    }
                    CertificationOutcome::NotCertified => unresolved = true,
                    CertificationOutcome::Inconclusive(c) => {
                        return Err(CheckError::LimitExceeded {
                            phase: c.phase,
                            resource: c.resource,
                        });
                    }
                }
            }
            // An unresolved world is not absence. Keep searching for a settled
            // counterexample; bounded exhaustion preserves incompleteness.
            let mut world = context.true_condition();
            for atom in context.inputs() {
                let mut literal = context.input_with_budget(atom, budget)?;
                if !observation.present.contains(atom) {
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
}

fn increment(n: usize) -> Result<usize> {
    n.checked_add(1).ok_or(CheckError::LimitExceeded {
        phase: "coverage counting",
        resource: "cardinality",
    })
}
