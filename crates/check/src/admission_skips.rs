//! Completed negative and failed attempts, local to one admission run. Dependencies use
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
    GuaranteedBounds,
    BoundRemoval,
    ImpliedGuard,
    GuardedPreprocessing,
    GuardedBounds,
    GuardedSettlement,
    Discharge,
}
impl AdmissionAttemptKind {
    pub fn label(self) -> &'static str {
        match self {
            Self::Coverage => "producer-coverage",
            Self::Removal => "producer-removal",
            Self::UpperBounds => "upper-bounds",
            Self::GuaranteedBounds => "guaranteed-bounds",
            Self::BoundRemoval => "bound-removal",
            Self::ImpliedGuard => "implied-guard",
            Self::GuardedPreprocessing => "guarded-preprocessing",
            Self::GuardedBounds => "guarded-bounds",
            Self::GuardedSettlement => "guarded-settlement",
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
    GuaranteedBounds(GroundAtom),
    BoundRemoval(GroundRuleId),
    ImpliedGuard(GroundRuleId),
    GuardedCone(GroundRuleId, OccurrenceId),
    GuardedBounds(GroundRuleId, OccurrenceId),
    GuardedSettlement(GroundRuleId, OccurrenceId),
    Discharge(GroundRuleId, OccurrenceId),
}
impl Attempt {
    pub fn kind(&self) -> AdmissionAttemptKind {
        match self {
            Self::Coverage(_) => AdmissionAttemptKind::Coverage,
            Self::Removal(_) => AdmissionAttemptKind::Removal,
            Self::UpperBounds(_) => AdmissionAttemptKind::UpperBounds,
            Self::GuaranteedBounds(_) => AdmissionAttemptKind::GuaranteedBounds,
            Self::BoundRemoval(_) => AdmissionAttemptKind::BoundRemoval,
            Self::ImpliedGuard(..) => AdmissionAttemptKind::ImpliedGuard,
            Self::GuardedCone(..) => AdmissionAttemptKind::GuardedPreprocessing,
            Self::GuardedBounds(..) => AdmissionAttemptKind::GuardedBounds,
            Self::GuardedSettlement(..) => AdmissionAttemptKind::GuardedSettlement,
            Self::Discharge(..) => AdmissionAttemptKind::Discharge,
        }
    }
    fn local_failure(&self, error: &CheckError) -> bool {
        matches!(
            error,
            CheckError::LimitExceeded {
                phase: "BDD operation" | "BDD preflight",
                resource: "BDD tasks" | "BDD nodes",
                ..
            }
        ) || (matches!(
            self,
            Self::UpperBounds(_)
                | Self::GuaranteedBounds(_)
                | Self::GuardedBounds(..)
                | Self::GuardedCone(..)
                | Self::ImpliedGuard(..)
        ) && matches!(
            error,
            CheckError::LimitExceeded {
                phase: "symbolic storage",
                resource: "condition nodes",
                ..
            }
        ))
    }
    fn record(&self, head: &GroundAtom, reason: Inconclusive) -> AdmissionSkip {
        let (kind, rule, occurrence) = match self {
            Self::Coverage(_) => (AdmissionAttemptKind::Coverage, None, None),
            Self::Removal(rule) => (AdmissionAttemptKind::Removal, Some(*rule), None),
            Self::UpperBounds(_) => (AdmissionAttemptKind::UpperBounds, None, None),
            Self::GuaranteedBounds(_) => (AdmissionAttemptKind::GuaranteedBounds, None, None),
            Self::BoundRemoval(rule) => (AdmissionAttemptKind::BoundRemoval, Some(*rule), None),
            Self::ImpliedGuard(rule) => (AdmissionAttemptKind::ImpliedGuard, Some(*rule), None),
            Self::GuardedCone(rule, occurrence) => (
                AdmissionAttemptKind::GuardedPreprocessing,
                Some(*rule),
                Some(*occurrence),
            ),
            Self::GuardedBounds(rule, occurrence) => (
                AdmissionAttemptKind::GuardedBounds,
                Some(*rule),
                Some(*occurrence),
            ),
            Self::GuardedSettlement(rule, occurrence) => (
                AdmissionAttemptKind::GuardedSettlement,
                Some(*rule),
                Some(*occurrence),
            ),
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

pub(crate) struct Attempts {
    skipped: BTreeMap<Attempt, AdmissionSkip>,
    negative: BTreeMap<Attempt, GroundAtom>,
    // Bounded metadata, one last outcome/cause per live attempt, never BDDs.
    history: BTreeMap<Attempt, (bool, Option<&'static str>)>,
    reuse_negatives: bool,
    pub count: usize,
}
impl Default for Attempts {
    fn default() -> Self {
        Self {
            skipped: BTreeMap::new(),
            negative: BTreeMap::new(),
            history: BTreeMap::new(),
            reuse_negatives: true,
            count: 0,
        }
    }
}
pub(crate) struct RetryChanges {
    all: BTreeSet<GroundAtom>,
    settled: BTreeSet<GroundAtom>,
}

impl Attempts {
    #[cfg(test)]
    pub fn without_negative_reuse() -> Self {
        Self {
            reuse_negatives: false,
            ..Self::default()
        }
    }
    fn tracked(&self) -> impl Iterator<Item = (&Attempt, &GroundAtom)> {
        self.skipped
            .iter()
            .map(|(a, s)| (a, &s.head))
            .chain(self.negative.iter())
    }
    fn len(&self) -> usize {
        self.skipped.len() + self.negative.len()
    }

    /// Consult before constructing a cover/bounds used only by this consumer.
    pub fn reuse_negative(
        &self,
        attempt: &Attempt,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
    ) -> Result<bool> {
        budget.tick("admission attempt lookup")?;
        let reused = self.reuse_negatives && self.negative.contains_key(attempt);
        if reused {
            progress.reused(attempt.kind(), false);
        }
        Ok(reused)
    }
    pub fn proof<T>(
        &mut self,
        attempt: Attempt,
        head: &GroundAtom,
        program: &GroundProgram,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
        negative: fn(&T) -> bool,
        run: impl FnOnce(&mut usize, &mut Budget<'_>) -> Result<T>,
    ) -> Result<Option<T>> {
        self.run_classified(
            attempt,
            head,
            program,
            retained,
            budget,
            progress,
            Some(negative),
            run,
        )
    }
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
        self.run_classified(
            attempt, head, program, retained, budget, progress, None, run,
        )
    }
    fn run_classified<T>(
        &mut self,
        attempt: Attempt,
        head: &GroundAtom,
        program: &GroundProgram,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
        negative: Option<fn(&T) -> bool>,
        run: impl FnOnce(&mut usize, &mut Budget<'_>) -> Result<T>,
    ) -> Result<Option<T>> {
        if self.skipped.contains_key(&attempt) {
            progress.reused(attempt.kind(), true);
            return Ok(None);
        }
        let before = *retained;
        let previous = self.history.get(&attempt).copied();
        let started = progress.attempt_start(attempt.kind(), previous);
        let result = run(retained, budget);
        let outcome = match &result {
            Ok(value) if negative.is_some_and(|f| f(value)) => "negative",
            Ok(_) => "completed",
            Err(error) if attempt.local_failure(error) => "skipped",
            Err(_) => "failed",
        };
        progress.attempt_end(attempt.kind(), started, outcome);
        match result {
            Ok(value) => {
                if negative.is_some_and(|f| f(&value)) {
                    if self.reuse_negatives {
                        self.negative.insert(attempt.clone(), head.clone());
                    }
                    if progress.enabled() {
                        self.history.insert(attempt, (false, None));
                    }
                } else {
                    self.history.remove(&attempt);
                }
                Ok(Some(value))
            }
            Err(error) if attempt.local_failure(&error) => {
                // The closure's partial values have dropped. Undo only retained
                // storage; work and failed-operation charges remain consumed.
                *retained = before;
                let reason = Inconclusive::from_error(error.clone())?;
                let record = attempt.record(head, reason);
                self.count += 1;
                progress.skipped(program, &record, self.count);
                budget.record_failure(&error);
                if progress.enabled() {
                    self.history.insert(attempt.clone(), (true, None));
                }
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
        if self.len() == 0 {
            return Ok(RetryChanges { all, settled });
        }
        budget.charge(self.len(), "admission retry dependencies")?;
        let conservative = self.tracked().any(|(a, _)| {
            matches!(
                a,
                Attempt::UpperBounds(_)
                    | Attempt::GuaranteedBounds(_)
                    | Attempt::BoundRemoval(_)
                    | Attempt::ImpliedGuard(..)
                    | Attempt::GuardedCone(..)
                    | Attempt::GuardedBounds(..)
                    | Attempt::GuardedSettlement(..)
                    | Attempt::Discharge(..)
            )
        });
        let precise = self
            .tracked()
            .any(|(a, _)| matches!(a, Attempt::Coverage(_) | Attempt::Removal(_)));
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
    ) -> Result<BTreeMap<Attempt, &'static str>> {
        let mut invalid = BTreeMap::new();
        // Replacements add settled dependencies as well as cutting a cycle edge.
        // Start conservatively: clear every live entry transactionally. Ordinary
        // removal/discharge commits keep their existing precise invalidation.
        if after
            .rules
            .iter()
            .zip(&before.rules)
            .any(|(a, b)| a.replacements != b.replacements)
        {
            budget.charge(self.len() + after.rules.len(), "guarded retry invalidation")?;
            return Ok(self
                .tracked()
                .map(|(a, _)| (a.clone(), "guarded-replacement"))
                .collect());
        }
        if self.len() == 0 {
            return Ok(invalid);
        }
        budget.charge(
            before.inputs.len() + after.inputs.len(),
            "admission retry inputs",
        )?;
        // Admission currently preserves these exactly. If a future rebuild
        // changes the universe/order, every BDD attempt must be tried again.
        if before.inputs != after.inputs || before.input_order != after.input_order {
            budget.charge(self.len(), "admission retry inputs")?;
            return Ok(self
                .tracked()
                .map(|(a, _)| (a.clone(), "input-order"))
                .collect());
        }
        // One scan per commit, shared by coverage and all removal attempts for
        // the same head, rather than one scan of its producers per failed rule.
        let mut coverage = BTreeMap::<_, bool>::new();
        let mut candidates = BTreeSet::new();
        for (attempt, head) in self.tracked() {
            budget.tick("admission retry inputs")?;
            if matches!(attempt, Attempt::Coverage(_) | Attempt::Removal(_)) {
                coverage.insert(head, false);
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
        for (attempt, head) in self.tracked() {
            budget.tick("admission retry inputs")?;
            let obsolete = match attempt {
                Attempt::Coverage(_) => !candidates.contains(head),
                Attempt::Removal(id) | Attempt::BoundRemoval(id) => after.rule(*id).is_none(),
                // Discharge and guarded settlement both remove a literal. Use
                // the existing index, not a body scan for every cached literal
                // (which would be quadratic for a rule with many negations).
                Attempt::Discharge(id, occurrence) | Attempt::GuardedSettlement(id, occurrence) => {
                    after.rule(*id).is_none()
                        || after.discharge(*id, *occurrence).is_some()
                        || after.replacement_proof(*id, *occurrence).is_some()
                }
                _ => false,
            };
            if obsolete {
                invalid.insert(attempt.clone(), "obsolete");
                continue;
            }
            let retry = match attempt {
                Attempt::Coverage(_) => coverage[head],
                Attempt::Removal(id) => {
                    coverage[head]
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
                Attempt::UpperBounds(_)
                | Attempt::GuaranteedBounds(_)
                | Attempt::BoundRemoval(_)
                | Attempt::ImpliedGuard(..)
                | Attempt::GuardedCone(..)
                | Attempt::GuardedBounds(..)
                | Attempt::GuardedSettlement(..)
                | Attempt::Discharge(..) => changed.all.contains(head),
            };
            if retry {
                let cause = match attempt {
                    Attempt::Coverage(_) => "exact-cover",
                    Attempt::Removal(_) if coverage[head] => "exact-cover",
                    Attempt::Removal(_) => "settled-summary",
                    _ => "reader-cone",
                };
                invalid.insert(attempt.clone(), cause);
            }
        }
        Ok(invalid)
    }
    pub fn invalidate(&mut self, invalid: &BTreeMap<Attempt, &'static str>) {
        for (attempt, cause) in invalid {
            self.skipped.remove(attempt);
            self.negative.remove(attempt);
            if *cause == "obsolete" {
                self.history.remove(attempt);
            } else if let Some(previous) = self.history.get_mut(attempt) {
                previous.1 = Some(cause);
            }
        }
    }
    pub fn records(self) -> BTreeMap<GroundAtom, Vec<AdmissionSkip>> {
        let mut records = BTreeMap::<_, Vec<_>>::new();
        for skip in self.skipped.into_values() {
            // Optional inference falls back to the original settled guard. Its
            // failure is progress evidence, not an unfinished admission proof.
            if skip.kind == AdmissionAttemptKind::ImpliedGuard {
                continue;
            }
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
    for literal in rule.dependency_literals() {
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
    if rule.replacements != next.replacements {
        return Ok(true);
    }
    for replacement in &rule.replacements {
        for atom in replacement.expression.atoms() {
            budget.tick("admission retry inputs")?;
            if changed_settled.contains(atom) {
                return Ok(true);
            }
        }
    }
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
    fn obsolete_negative_discharge_is_removed_without_becoming_a_skip() {
        let mut c = denotate_ir::Corpus::new();
        let i = rel(&mut c, "i", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        rule(&mut c, a, &[(i, false), (b, true)]);
        rule(&mut c, b, &[(i, true), (a, true)]);
        let limits = Limits::default();
        let before = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let after = before.clone().admit(&limits).unwrap();
        let proof = after.rewrite_proofs().next().unwrap();
        let RewriteKind::Discharge { literal_occurrence } = proof.kind else {
            panic!("discharge")
        };
        let attempt = Attempt::Discharge(proof.candidate().id, literal_occurrence);
        let mut attempts = Attempts::default();
        attempts
            .negative
            .insert(attempt.clone(), proof.candidate().head.atom.clone());
        attempts.history.insert(attempt.clone(), (false, None));
        let changed = RetryChanges {
            all: BTreeSet::new(),
            settled: BTreeSet::new(),
        };
        let invalid = attempts
            .invalidated(&before, &after, &changed, &mut Budget::new(&limits))
            .unwrap();
        assert_eq!(invalid[&attempt], "obsolete");
        attempts.invalidate(&invalid);
        assert!(attempts.negative.is_empty());
        assert!(attempts.history.is_empty());
        assert_eq!(attempts.count, 0);
        assert!(attempts.records().is_empty());
    }

    #[test]
    fn negative_invalidation_covers_producer_edits_settlement_and_scc_splits() {
        let mut c = denotate_ir::Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let u = rel(&mut c, "u", false);
        let v = rel(&mut c, "v", false);
        let h = rel(&mut c, "h", false);
        let base = rule(&mut c, h, &[(i, false)]);
        let candidate = rule(&mut c, h, &[(j, false), (u, false)]);
        rule(&mut c, u, &[(i, false)]);
        let cyclic = rule(&mut c, u, &[(v, false)]);
        let back = rule(&mut c, v, &[(u, true)]);
        let limits = Limits::default();
        let before = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let id = |source| before.rules().find(|r| r.source == source).unwrap().id;
        for edit in [
            "lost-producer",
            "producer-body",
            "candidate-body",
            "settlement",
        ] {
            let attempt = Attempt::Removal(id(candidate));
            let mut attempts = Attempts::default();
            attempts.negative.insert(attempt.clone(), atom(h));
            let mut after = before.clone();
            let mut changed = RetryChanges {
                all: BTreeSet::new(),
                settled: BTreeSet::new(),
            };
            match edit {
                "lost-producer" => {
                    after.rewrites.dropped.insert(id(base));
                }
                "producer-body" => {
                    after.rules[id(base).index].body.clear();
                }
                "candidate-body" => {
                    after.rules[id(candidate).index].body.remove(0);
                }
                "settlement" => {
                    after.rewrites.dropped.insert(id(back));
                    changed.all.extend([atom(v), atom(u), atom(h)]);
                }
                _ => unreachable!(),
            }
            crate::graph::analyze(&mut after, &mut Budget::new(&limits)).unwrap();
            let invalid = attempts
                .invalidated(&before, &after, &changed, &mut Budget::new(&limits))
                .unwrap();
            assert!(invalid.contains_key(&attempt), "{edit}");
            attempts.invalidate(&invalid);
            assert!(attempts.negative.is_empty());
            assert!(attempts.records().is_empty());
        }
        let mut attempts = Attempts::default();
        let bound = Attempt::BoundRemoval(id(cyclic));
        attempts.negative.insert(bound.clone(), atom(u));
        let mut after = before.clone();
        after.rewrites.dropped.insert(id(back));
        crate::graph::analyze(&mut after, &mut Budget::new(&limits)).unwrap();
        assert!(before.component_for(&atom(u)).unwrap().cycle.is_some());
        assert!(after.component_for(&atom(u)).unwrap().cycle.is_none());
        let changed = RetryChanges {
            all: BTreeSet::from([atom(v), atom(u), atom(h)]),
            settled: BTreeSet::new(),
        };
        let invalid = attempts
            .invalidated(&before, &after, &changed, &mut Budget::new(&limits))
            .unwrap();
        assert_eq!(invalid[&bound], "reader-cone");
    }

    #[test]
    fn bound_attempts_retry_tighter_bounds_while_the_component_stays_blocked() {
        for negative in [false, true] {
            let mut c = denotate_ir::Corpus::new();
            let i = rel(&mut c, "i", true);
            let a = rel(&mut c, "a", false);
            let b = rel(&mut c, "b", false);
            let s = rel(&mut c, "s", false);
            let v = rel(&mut c, "v", false);
            let sr = rule(&mut c, s, &[(i, false), (v, true)]);
            let vr = rule(&mut c, v, &[(i, true), (s, true)]);
            rule(&mut c, a, &[(i, false)]);
            let candidate = rule(&mut c, a, &[(b, false)]);
            rule(&mut c, b, &[(s, false), (a, true)]);
            // Discharging the independent s/v cycle settles s=i. a/b still form a
            // negative SCC, but b's bound tightens from !i to i & !i = false.
            // a's exact cover and its candidate's settled summary are unchanged.
            let limits = Limits::default();
            let before = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
            let completed = before.clone().admit(&limits).unwrap();
            let batch: Vec<_> = completed
                .rewrite_proofs()
                .filter(|p| {
                    [sr, vr].contains(&p.candidate().source)
                        && matches!(p.kind, RewriteKind::Discharge { .. })
                })
                .cloned()
                .collect();
            assert_eq!(batch.len(), 2);
            let id = before.rules().find(|r| r.source == candidate).unwrap().id;
            let bound = Attempt::GuaranteedBounds(atom(a));
            let removal = Attempt::BoundRemoval(id);
            let cheap = Attempt::Removal(id);
            let reason =
                Inconclusive::from_error(CheckError::limit("BDD operation", "BDD tasks", 1, None))
                    .unwrap();
            let mut attempts = Attempts::default();
            for attempt in [bound.clone(), removal.clone(), cheap.clone()] {
                // Inject completed negatives or local failures without a resource golden.
                // Retry uses production graph traversal and invalidation below.
                if negative && !matches!(attempt, Attempt::GuaranteedBounds(_)) {
                    attempts.negative.insert(attempt.clone(), atom(a));
                } else {
                    attempts
                        .skipped
                        .insert(attempt.clone(), attempt.record(&atom(a), reason));
                }
            }
            let changed = attempts
                .changed_readers(&before, &batch, &mut Budget::new(&limits))
                .unwrap();
            let mut after = before.clone();
            for proof in &batch {
                let RewriteKind::Discharge { literal_occurrence } = proof.kind else {
                    unreachable!()
                };
                after.rules[proof.candidate().id.index]
                    .body
                    .retain(|l| l.term.occurrence != literal_occurrence);
            }
            crate::graph::analyze(&mut after, &mut Budget::new(&limits)).unwrap();
            for (p, false_bound) in [(&before, false), (&after, true)] {
                let component = p.component_for(&atom(a)).unwrap();
                assert!(!component.blocked_by.is_empty());
                let meaning = p.symbolic(&limits).unwrap();
                let ctx = meaning.context();
                let mut summaries = BTreeMap::new();
                for rule in p.rules() {
                    let mut condition = ctx.true_condition();
                    let mut settled = Vec::new();
                    let mut exact = true;
                    for literal in &rule.body {
                        match meaning.fact(&literal.term.atom).unwrap() {
                            SymbolicFact::Settled(mut value) => {
                                if literal.polarity == Polarity::Negative {
                                    value = ctx.not(&value, &limits).unwrap();
                                }
                                condition = ctx.and(&condition, &value, &limits).unwrap();
                                settled.push(SettledPremise {
                                    literal: literal.clone(),
                                    condition: value,
                                });
                            }
                            SymbolicFact::Blocked(_) => exact = false,
                            SymbolicFact::Inconclusive(_) => panic!(),
                        }
                    }
                    summaries.insert(
                        rule.id,
                        ProducerSummary {
                            rule: rule.clone(),
                            settled,
                            condition,
                            exact,
                        },
                    );
                }
                let bounds = crate::upper_bounds::compute_with_guarantees(
                    p,
                    component,
                    &summaries,
                    ctx,
                    &mut 0,
                    &mut Budget::new(&limits),
                    None,
                    true,
                )
                .unwrap();
                assert_eq!(bounds.conditions[&atom(b)].is_false(), false_bound);
                assert_eq!(
                    ctx.evaluate(&bounds.conditions[&atom(b)], [], &limits)
                        .unwrap(),
                    !false_bound
                );
            }
            let invalid = attempts
                .invalidated(&before, &after, &changed, &mut Budget::new(&limits))
                .unwrap();
            assert_eq!(
                invalid.keys().cloned().collect::<BTreeSet<_>>(),
                BTreeSet::from([bound, removal])
            );
            attempts.invalidate(&invalid);
            assert_eq!(
                attempts
                    .tracked()
                    .map(|(a, _)| a.clone())
                    .collect::<Vec<_>>(),
                vec![cheap]
            );
        }
    }

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
            ..Attempts::default()
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
                .unwrap()
                .into_keys()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([attempt])
        );
    }
}
