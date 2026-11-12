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
    /// This conservative closure includes both signs and every producer. It
    /// reaches all old SCC members, and external changes affecting their bounds.
    pub fn changed_readers(
        &self,
        program: &GroundProgram,
        batch: &[RewriteProof],
        budget: &mut Budget<'_>,
    ) -> Result<BTreeSet<GroundAtom>> {
        if self.skipped.is_empty() {
            return Ok(BTreeSet::new());
        }
        let mut readers = BTreeMap::<_, Vec<_>>::new();
        for edge in &program.dependencies {
            budget.tick("admission retry dependencies")?;
            readers
                .entry(&edge.provider)
                .or_default()
                .push(&edge.consumer);
        }
        let mut changed: BTreeSet<_> = batch
            .iter()
            .map(|p| p.candidate().head.atom.clone())
            .collect();
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
        Ok(changed)
    }
    pub fn invalidate(&mut self, changed: &BTreeSet<GroundAtom>) {
        self.skipped.retain(|_, skip| !changed.contains(&skip.head));
    }
    pub fn records(self) -> BTreeMap<GroundAtom, Vec<AdmissionSkip>> {
        let mut records = BTreeMap::<_, Vec<_>>::new();
        for skip in self.skipped.into_values() {
            records.entry(skip.head.clone()).or_default().push(skip);
        }
        records
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
