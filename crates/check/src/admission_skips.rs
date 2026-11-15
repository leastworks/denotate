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
    pub prepared: BTreeMap<Attempt, crate::guarded_preparation::PreparedCone>,
    // Complete producer dependencies, including deadness and inferred guards.
    dependencies: BTreeMap<Attempt, std::sync::Arc<BTreeSet<GroundRuleId>>>,
    pub reuse_prepared: bool,
    #[cfg(test)]
    pub batch_guarded: bool,
}
impl Default for Attempts {
    fn default() -> Self {
        Self {
            skipped: BTreeMap::new(),
            negative: BTreeMap::new(),
            history: BTreeMap::new(),
            reuse_negatives: true,
            count: 0,
            prepared: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            reuse_prepared: true,
            #[cfg(test)]
            batch_guarded: true,
        }
    }
}
pub(crate) struct RetryChanges {
    all: BTreeSet<GroundAtom>,
    settled: BTreeSet<GroundAtom>,
}

impl Attempts {
    pub fn nodes(&self) -> usize {
        self.prepared.values().map(|p| p.nodes()).sum::<usize>()
            + self
                .dependencies
                .values()
                .map(|d| d.len() + 1)
                .sum::<usize>()
    }
    pub fn prune_dependencies(&mut self) -> usize {
        let before = self.nodes();
        self.dependencies.retain(|a, _| {
            self.prepared.contains_key(a)
                || self.skipped.contains_key(a)
                || self.negative.contains_key(a)
        });
        before - self.nodes()
    }
    pub fn clear_prepared(&mut self) -> usize {
        let before = self.nodes();
        self.prepared.clear();
        self.dependencies
            .retain(|a, _| self.skipped.contains_key(a) || self.negative.contains_key(a));
        before - self.nodes()
    }
    pub fn remember_dependencies(
        &mut self,
        rule: GroundRuleId,
        occurrence: OccurrenceId,
        dependencies: BTreeSet<GroundRuleId>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        let keys = [
            Attempt::GuardedCone(rule, occurrence),
            Attempt::GuardedBounds(rule, occurrence),
            Attempt::GuardedSettlement(rule, occurrence),
        ];
        budget.charge(dependencies.len(), "guarded retry footprint")?;
        let old: usize = keys
            .iter()
            .filter_map(|k| self.dependencies.remove(k))
            .map(|d| d.len() + 1)
            .sum();
        *retained -= old;
        let nodes = keys.len() * (dependencies.len() + 1);
        if retained.saturating_add(nodes) <= budget.limits.max_condition_nodes {
            *retained = crate::symbolic::retain(*retained, 0, nodes, budget)?;
            let dependencies = std::sync::Arc::new(dependencies);
            for key in keys {
                self.dependencies.insert(key, dependencies.clone());
            }
        } else if let Some(old) = self.prepared.remove(&keys[0]) {
            *retained -= old.nodes();
        }
        Ok(())
    }
    pub fn keep_prepared(
        &mut self,
        key: Attempt,
        cone: crate::guarded_preparation::PreparedCone,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        // Without a complete footprint, retry conservatively and do not retain a cone.
        if !self.reuse_prepared || !self.dependencies.contains_key(&key) {
            return Ok(());
        }
        if let Some(old) = self.prepared.remove(&key) {
            *retained -= old.nodes();
        }
        let nodes = cone.nodes();
        budget.charge(nodes, "guarded preparation retention")?;
        if retained.saturating_add(nodes) <= budget.limits.max_condition_nodes {
            *retained = crate::symbolic::retain(*retained, 0, nodes, budget)?;
            self.prepared.insert(key, cone);
        }
        Ok(())
    }
    pub fn reason(&self, attempt: &Attempt) -> Option<Inconclusive> {
        self.skipped.get(attempt).map(|s| s.reason)
    }
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
            .chain(self.prepared.iter().map(|(a, p)| (a, &p.head)))
    }
    fn len(&self) -> usize {
        self.skipped.len() + self.negative.len() + self.prepared.len()
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
            .any(|(a, _)| matches!(a, Attempt::Coverage(_) | Attempt::Removal(_)))
            || !self.dependencies.is_empty();
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
                Attempt::Discharge(id, occurrence)
                | Attempt::GuardedSettlement(id, occurrence)
                | Attempt::GuardedCone(id, occurrence)
                | Attempt::GuardedBounds(id, occurrence) => {
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
            let retry = if let Some(dependencies) = self.dependencies.get(attempt) {
                dependency_changes(before, after, head, dependencies, &changed.settled, budget)?
            } else {
                match attempt {
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
                }
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
            self.prepared.remove(attempt);
            self.dependencies.remove(attempt);
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

/// Compare complete inputs on both sides of an atomic commit. SCC IDs themselves
/// change on every rebuild; only membership relative to the reading head matters.
fn dependency_changes(
    before: &GroundProgram,
    after: &GroundProgram,
    head: &GroundAtom,
    dependencies: &BTreeSet<GroundRuleId>,
    changed_settled: &BTreeSet<GroundAtom>,
    budget: &mut Budget<'_>,
) -> Result<bool> {
    let old_component = before.component_for(head)?.id;
    let new_component = after.component_for(head)?.id;
    for id in dependencies {
        budget.tick("guarded retry inputs")?;
        let (Some(old), Some(new)) = (before.rule(*id), after.rule(*id)) else {
            return Ok(true);
        };
        if old != new || summary_changed(before, after, old, Some(new), changed_settled, budget)? {
            return Ok(true);
        }
        for atom in std::iter::once(old.head.atom.clone())
            .chain(old.dependency_literals().map(|l| l.term.atom))
        {
            budget.tick("guarded retry membership")?;
            let inside = |p: &GroundProgram, component| {
                p.atom_index
                    .get(&atom)
                    .is_some_and(|i| p.atom_components[*i] == component)
            };
            if inside(before, old_component) != inside(after, new_component) {
                return Ok(true);
            }
        }
    }
    Ok(false)
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
    fn prepared_cones_rebind_across_unrelated_rewrites_and_invalidate_every_source() {
        let (mut c, claim) = crate::tests::guarded_settlement::fixture(0);
        let x = rel(&mut c, "x", true);
        let y = rel(&mut c, "y", false);
        let unrelated = rule(&mut c, y, &[(x, true)]);
        let l = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        let m = raw.symbolic(&l).unwrap();
        let summaries = crate::test_support::rewrites::summaries(&raw, &m, &l);
        let candidate = summaries
            .values()
            .find(|s| s.rule.head.atom == atom(claim))
            .unwrap();
        let mut attempts = Attempts::default();
        let mut retained = 0;
        raw.guarded_settlements(
            &m,
            &summaries,
            &BTreeSet::from([candidate.rule.id]),
            &mut retained,
            &mut Budget::new(&l),
            &AdmissionReporter::new(None),
            &mut attempts,
        )
        .unwrap();
        // Select the unresolved occurrence, not the settled guard literal.
        let key = attempts
            .prepared
            .keys()
            .find(|a| matches!(a, Attempt::GuardedCone(id, _) if *id == candidate.rule.id))
            .unwrap()
            .clone();
        let old = &attempts.prepared[&key];
        let dependencies = attempts.dependencies[&key].clone();
        let unrelated_id = raw.rules().find(|r| r.source == unrelated).unwrap().id;
        let mut after = raw.clone();
        after.rules[unrelated_id.index].body.clear();
        crate::graph::analyze(&mut after, &mut Budget::new(&l)).unwrap();
        let changed = RetryChanges {
            all: BTreeSet::from([atom(y)]),
            settled: BTreeSet::from([atom(y)]),
        };
        assert!(
            !attempts
                .invalidated(&raw, &after, &changed, &mut Budget::new(&l))
                .unwrap()
                .contains_key(&key)
        );
        let next_meaning = after.symbolic(&l).unwrap();
        let next_summaries = crate::test_support::rewrites::summaries(&after, &next_meaning, &l);
        let rebound = old
            .bind(
                &after,
                &next_summaries[&candidate.rule.id].condition,
                &next_meaning.context().permitted_worlds(),
                &next_summaries,
                &mut 0,
                &mut Budget::new(&l),
            )
            .unwrap()
            .unwrap();
        assert_eq!(rebound.snapshot, after.graph_revision);
        assert_eq!(
            rebound.component,
            after.component_for(&atom(claim)).unwrap().id
        );
        assert_ne!(
            rebound.component,
            raw.component_for(&atom(claim)).unwrap().id
        );
        // Rebuilding the same cone from scratch agrees, including pruning reasons.
        let index = next_summaries
            .values()
            .fold(BTreeMap::<_, Vec<_>>::new(), |mut index, s| {
                index.entry(&s.rule.head.atom).or_default().push(s.rule.id);
                index
            });
        let Attempt::GuardedCone(id, occurrence) = key else {
            panic!()
        };
        let literal = candidate
            .rule
            .body
            .iter()
            .find(|l| l.term.occurrence == occurrence)
            .unwrap();
        let fresh = crate::guarded_bounds::prepare(
            &after,
            after.component_for(&atom(claim)).unwrap(),
            &next_summaries[&id],
            &literal.term.atom,
            &next_summaries,
            &index,
            next_meaning.context(),
            &mut 0,
            &mut Budget::new(&l),
            &mut crate::guarded_bounds::Preparation::default(),
        )
        .unwrap();
        assert!(
            rebound
                .same_computation(&fresh, &mut Budget::new(&l))
                .unwrap()
        );
        assert!(
            old.bind(
                &after,
                &next_meaning.context().false_condition(),
                &next_meaning.context().permitted_worlds(),
                &next_summaries,
                &mut 0,
                &mut Budget::new(&l)
            )
            .unwrap()
            .is_none()
        );
        for source in dependencies.iter() {
            let mut edited = raw.clone();
            edited.rules[source.index].body.clear();
            crate::graph::analyze(&mut edited, &mut Budget::new(&l)).unwrap();
            assert!(
                attempts
                    .invalidated(
                        &raw,
                        &edited,
                        &RetryChanges {
                            all: BTreeSet::new(),
                            settled: BTreeSet::new()
                        },
                        &mut Budget::new(&l)
                    )
                    .unwrap()
                    .contains_key(&Attempt::GuardedCone(id, occurrence)),
                "source {source:?}"
            );
        }
    }

    #[test]
    fn replacement_retries_its_component_bounds_but_keeps_unrelated_failures() {
        let (mut c, claim) = crate::tests::guarded_settlement::fixture(0);
        let x = rel(&mut c, "x", false);
        let y = rel(&mut c, "y", false);
        rule(&mut c, x, &[(y, true)]);
        rule(&mut c, y, &[(x, true)]);
        let l = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        let admitted = raw.clone().admit(&l).unwrap();
        let proof = admitted
            .rewrite_proofs()
            .find(|p| p.guarded_settlement().is_some())
            .unwrap();
        let mut attempts = Attempts::default();
        let own = Attempt::GuaranteedBounds(atom(claim));
        let other = Attempt::GuaranteedBounds(atom(x));
        let reason =
            Inconclusive::from_error(CheckError::limit("BDD operation", "BDD nodes", 1, None))
                .unwrap();
        for (key, head) in [(&own, atom(claim)), (&other, atom(x))] {
            attempts
                .skipped
                .insert(key.clone(), key.record(&head, reason));
        }
        let changes = attempts
            .changed_readers(&raw, std::slice::from_ref(proof), &mut Budget::new(&l))
            .unwrap();
        let mut after = raw.clone();
        let p = proof.guarded_settlement().unwrap();
        let rule = &mut after.rules[proof.candidate().id.index];
        rule.body.retain(|l| l.term.occurrence != p.occurrence);
        rule.replacements.push(SettledReplacement {
            occurrence: p.occurrence,
            expression: p.replacement.clone(),
        });
        crate::graph::analyze(&mut after, &mut Budget::new(&l)).unwrap();
        let invalid = attempts
            .invalidated(&raw, &after, &changes, &mut Budget::new(&l))
            .unwrap();
        assert!(invalid.contains_key(&own));
        assert!(!invalid.contains_key(&other));
        attempts.invalidate(&invalid);
        assert!(
            attempts
                .run(
                    other,
                    &atom(x),
                    &after,
                    &mut 0,
                    &mut Budget::new(&l),
                    &AdmissionReporter::new(None),
                    |_, _| -> Result<()> { panic!("unchanged bound must not rerun") }
                )
                .unwrap()
                .is_none()
        );
        assert!(
            attempts
                .run(
                    own,
                    &atom(claim),
                    &after,
                    &mut 0,
                    &mut Budget::new(&l),
                    &AdmissionReporter::new(None),
                    |_, _| Ok(())
                )
                .unwrap()
                .is_some()
        );
    }

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
