//! Failed proof attempts, local to one admission run. Retry dependencies use
//! ground atoms/rules stable across that run's graph rebuilds, never SCC handles.
use crate::{
    admission_progress::AdmissionReporter,
    limits::{Budget, Result},
    *,
};
use denotate_ir::OccurrenceId;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdmissionAttemptKind {
    Coverage,
    Removal,
    UpperBounds,
    Discharge,
}
impl AdmissionAttemptKind {
    pub fn label(self) -> &'static str {
        match self {
            Self::Coverage => "producer-coverage",
            Self::Removal => "producer-removal",
            Self::UpperBounds => "upper-bounds",
            Self::Discharge => "negation-discharge",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionSkip {
    pub kind: AdmissionAttemptKind,
    pub head: GroundAtom,
    pub rule: Option<GroundRuleId>,
    pub occurrence: Option<OccurrenceId>,
    pub reason: Inconclusive,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Attempt {
    Coverage(GroundAtom),
    Removal(GroundRuleId),
    UpperBounds(GroundAtom),
    Discharge(GroundRuleId, OccurrenceId),
}
impl Attempt {
    fn record(&self, head: &GroundAtom, reason: Inconclusive) -> AdmissionSkip {
        let (kind, rule, occurrence) = match self {
            Self::Coverage(_) => (AdmissionAttemptKind::Coverage, None, None),
            Self::Removal(rule) => (AdmissionAttemptKind::Removal, Some(*rule), None),
            Self::UpperBounds(_) => (AdmissionAttemptKind::UpperBounds, None, None),
            Self::Discharge(rule, occurrence) => (
                AdmissionAttemptKind::Discharge,
                Some(*rule),
                Some(*occurrence),
            ),
        };
        AdmissionSkip {
            kind,
            head: head.clone(),
            rule,
            occurrence,
            reason,
        }
    }
}

#[derive(Default)]
pub(crate) struct Attempts {
    skipped: BTreeMap<Attempt, AdmissionSkip>,
    pub count: usize,
}
pub(crate) struct RetryChanges {
    all: BTreeSet<GroundAtom>,
    settled: BTreeSet<GroundAtom>,
}

impl Attempts {
    pub fn run<T>(
        &mut self,
        attempt: Attempt,
        head: &GroundAtom,
        program: &GroundProgram,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
        run: impl FnOnce(&mut usize, &mut Budget<'_>) -> Result<T>,
    ) -> Result<Option<T>> {
        if self.skipped.contains_key(&attempt) {
            return Ok(None);
        }
        let before = *retained;
        match run(retained, budget) {
            Ok(value) => Ok(Some(value)),
            Err(
                error @ CheckError::LimitExceeded {
                    phase: "BDD operation" | "BDD preflight",
                    resource: "BDD tasks" | "BDD nodes",
                    ..
                },
            ) => {
                // The closure's partial values have dropped. Undo only retained
                // storage; work and failed-operation charges remain consumed.
                *retained = before;
                let reason = Inconclusive::from_error(error.clone())?;
                let record = attempt.record(head, reason);
                self.count += 1;
                progress.skipped(program, &record, self.count);
                budget.record_failure(&error);
                self.skipped.insert(attempt, record);
                Ok(None)
            }
            Err(error) => Err(error),
        }
    }

    /// Compute before committing: removed edges must still carry invalidation.
    /// Bounds/discharge use every changed reader. Coverage/removal only read
    /// settled conditions, whose unrestricted meanings can change when a rewrite
    /// touches an already settled head (equivalence is only guaranteed under W).
    pub fn changed_readers(
        &self,
        program: &GroundProgram,
        batch: &[RewriteProof],
        budget: &mut Budget<'_>,
    ) -> Result<RetryChanges> {
        let mut all = BTreeSet::new();
        let mut settled = BTreeSet::new();
        if self.skipped.is_empty() {
            return Ok(RetryChanges { all, settled });
        }
        budget.charge(self.skipped.len(), "admission retry dependencies")?;
        let conservative = self
            .skipped
            .keys()
            .any(|a| matches!(a, Attempt::UpperBounds(_) | Attempt::Discharge(..)));
        let precise = self
            .skipped
            .keys()
            .any(|a| matches!(a, Attempt::Coverage(_) | Attempt::Removal(_)));
        for proof in batch {
            budget.tick("admission retry dependencies")?;
            let head = &proof.candidate().head.atom;
            if conservative {
                all.insert(head.clone());
            }
            if precise && is_settled(program, head) {
                settled.insert(head.clone());
            }
        }
        if all.is_empty() && settled.is_empty() {
            return Ok(RetryChanges { all, settled });
        }
        let mut readers = BTreeMap::<_, Vec<_>>::new();
        for edge in &program.dependencies {
            budget.tick("admission retry dependencies")?;
            readers
                .entry(&edge.provider)
                .or_default()
                .push(&edge.consumer);
        }
        for changed in [&mut all, &mut settled] {
            let mut pending: Vec<_> = changed.iter().cloned().collect();
            while let Some(atom) = pending.pop() {
                budget.tick("admission retry dependencies")?;
                for reader in readers.get(&atom).into_iter().flatten() {
                    budget.tick("admission retry dependencies")?;
                    if changed.insert((*reader).clone()) {
                        pending.push((*reader).clone());
                    }
                }
            }
        }
        Ok(RetryChanges { all, settled })
    }

    /// Compare cheap summary inputs after the tentative rebuild, before commit.
    /// No BDDs or per-attempt copies of the wide producer set are retained.
    pub fn invalidated(
        &self,
        before: &GroundProgram,
        after: &GroundProgram,
        changed: &RetryChanges,
        budget: &mut Budget<'_>,
    ) -> Result<BTreeSet<Attempt>> {
        let mut invalid = BTreeSet::new();
        if self.skipped.is_empty() {
            return Ok(invalid);
        }
        budget.charge(
            before.inputs.len() + after.inputs.len(),
            "admission retry inputs",
        )?;
        // Admission currently preserves these exactly. If a future rebuild
        // changes the universe/order, every BDD attempt must be tried again.
        if before.inputs != after.inputs || before.input_order != after.input_order {
            budget.charge(self.skipped.len(), "admission retry inputs")?;
            return Ok(self.skipped.keys().cloned().collect());
        }
        // One scan per commit, shared by coverage and all removal attempts for
        // the same head, rather than one scan of its producers per failed rule.
        let mut coverage = BTreeMap::<_, bool>::new();
        let mut candidates = BTreeSet::new();
        for (attempt, skip) in &self.skipped {
            budget.tick("admission retry inputs")?;
            if matches!(attempt, Attempt::Coverage(_) | Attempt::Removal(_)) {
                coverage.insert(&skip.head, false);
            }
        }
        if !coverage.is_empty() {
            for rule in &before.rules {
                budget.tick("admission retry inputs")?;
                let Some(changed_coverage) = coverage.get_mut(&rule.head.atom) else {
                    continue;
                };
                if before.rewrites.dropped.contains(&rule.id) {
                    continue;
                }
                let next = after.rule(rule.id);
                let was_exact = exact(before, rule, budget)?;
                let now_exact = match next {
                    Some(rule) => exact(after, rule, budget)?,
                    None => false,
                };
                if next.is_some() && !now_exact {
                    candidates.insert(&rule.head.atom);
                }
                if was_exact != now_exact
                    || (was_exact
                        && summary_changed(before, after, rule, next, &changed.settled, budget)?)
                {
                    *changed_coverage = true;
                }
            }
        }
        for (attempt, skip) in &self.skipped {
            budget.tick("admission retry inputs")?;
            let retry = match attempt {
                Attempt::Coverage(_) => coverage[&skip.head] || !candidates.contains(&skip.head),
                Attempt::Removal(id) => {
                    coverage[&skip.head]
                        || match before.rule(*id) {
                            Some(rule) => summary_changed(
                                before,
                                after,
                                rule,
                                after.rule(*id),
                                &changed.settled,
                                budget,
                            )?,
                            None => true,
                        }
                }
                Attempt::UpperBounds(_) | Attempt::Discharge(..) => {
                    changed.all.contains(&skip.head)
                }
            };
            if retry {
                invalid.insert(attempt.clone());
            }
        }
        Ok(invalid)
    }
    pub fn invalidate(&mut self, invalid: &BTreeSet<Attempt>) {
        self.skipped.retain(|attempt, _| !invalid.contains(attempt));
    }
    pub fn records(self) -> BTreeMap<GroundAtom, Vec<AdmissionSkip>> {
        let mut records = BTreeMap::<_, Vec<_>>::new();
        for skip in self.skipped.into_values() {
            records.entry(skip.head.clone()).or_default().push(skip);
        }
        records
    }
}

// Symbolic admission is all-or-nothing: a represented, unblocked atom is
// settled, as are fixed boundaries and legal atoms with no possible producer.
fn is_settled(program: &GroundProgram, atom: &GroundAtom) -> bool {
    program.atom_index.get(atom).is_none_or(|index| {
        program.components[program.atom_components[*index].index]
            .blocked_by
            .is_empty()
    })
}
fn exact(program: &GroundProgram, rule: &GroundRule, budget: &mut Budget<'_>) -> Result<bool> {
    for literal in &rule.body {
        budget.tick("admission retry inputs")?;
        if !is_settled(program, &literal.term.atom) {
            return Ok(false);
        }
    }
    Ok(true)
}
fn summary_changed(
    before: &GroundProgram,
    after: &GroundProgram,
    rule: &GroundRule,
    next: Option<&GroundRule>,
    changed_settled: &BTreeSet<GroundAtom>,
    budget: &mut Budget<'_>,
) -> Result<bool> {
    let Some(next) = next else { return Ok(true) };
    budget.charge(rule.body.len() + next.body.len(), "admission retry inputs")?;
    let mut left = rule
        .body
        .iter()
        .filter(|l| is_settled(before, &l.term.atom));
    let mut right = next.body.iter().filter(|l| is_settled(after, &l.term.atom));
    loop {
        match (left.next(), right.next()) {
            (None, None) => return Ok(false),
            (Some(a), Some(b)) if a == b && !changed_settled.contains(&a.term.atom) => {}
            _ => return Ok(true),
        }
    }
}

impl GroundProgram {
    pub fn admission_skips(&self) -> impl Iterator<Item = &AdmissionSkip> {
        self.rewrites.skips.values().flatten()
    }
    pub fn admission_skips_for<'a>(
        &'a self,
        component: &'a Component,
    ) -> impl Iterator<Item = &'a AdmissionSkip> {
        component
            .atoms
            .iter()
            .flat_map(|a| self.rewrites.skips.get(a).into_iter().flatten())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel, rule};

    #[test]
    fn admission_retry_invalidates_all_if_a_future_rebuild_changes_input_order() {
        let mut c = denotate_ir::Corpus::new();
        let a = rel(&mut c, "a", true);
        let _b = rel(&mut c, "b", true);
        let out = rel(&mut c, "out", false);
        let u = rel(&mut c, "u", false);
        let v = rel(&mut c, "v", false);
        rule(&mut c, u, &[(v, true)]);
        rule(&mut c, v, &[(u, true)]);
        rule(&mut c, out, &[(a, false)]);
        rule(&mut c, out, &[(u, false)]);
        let limits = Limits::default();
        let before = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let attempt = Attempt::Coverage(atom(out));
        let reason =
            Inconclusive::from_error(CheckError::limit("BDD operation", "BDD nodes", 1, Some(2)))
                .unwrap();
        let attempts = Attempts {
            skipped: BTreeMap::from([(attempt.clone(), attempt.record(&atom(out), reason))]),
            count: 1,
        };
        let changes = RetryChanges {
            all: BTreeSet::new(),
            settled: BTreeSet::new(),
        };
        assert!(
            attempts
                .invalidated(&before, &before, &changes, &mut Budget::new(&limits))
                .unwrap()
                .is_empty()
        );
        let mut after = before.clone();
        after.input_order = Some(before.ordered_inputs().into_iter().rev().cloned().collect());
        assert_eq!(
            attempts
                .invalidated(&before, &after, &changes, &mut Budget::new(&limits))
                .unwrap(),
            BTreeSet::from([attempt])
        );
    }
}
