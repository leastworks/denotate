//! Observations of admission, never semantic inputs or retained query values.
use crate::*;
use denotate_ir::RuleId;
use std::{
    cell::RefCell,
    collections::BTreeMap,
    time::{Duration, Instant},
};

/// Per-round observations, never part of a proof, receipt, or cache identity.
#[derive(Debug, Clone, Default)]
pub struct AdmissionAttempts {
    pub new: usize,
    pub rerun_negative: usize,
    pub retried_skip: usize,
    pub reused_negative: usize,
    pub reused_skip: usize,
    pub reused_result: usize,
    pub completed: usize,
    pub negative: usize,
    pub skipped: usize,
    pub failed: usize,
    pub cutoffs: usize,
    pub elapsed: Duration,
    /// A fixed vocabulary of causes, aggregated without storing target lists.
    pub retry_causes: BTreeMap<&'static str, usize>,
}

#[derive(Debug, Clone)]
pub struct AdmissionComponent {
    /// One-based position in this round's ground graph, not a stable identity.
    pub index: usize,
    pub atoms: usize,
    pub rules: usize,
    pub representative: GroundAtom,
    pub source: Option<RuleId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdmissionPhase {
    Relevant,
    Downstream,
}
impl AdmissionPhase {
    pub fn label(self) -> &'static str {
        match self {
            Self::Relevant => "relevant",
            Self::Downstream => "downstream",
        }
    }
}

/// One candidate's restricted bounds work. Timings are observations only.
#[derive(Debug, Clone)]
pub struct GuardedAttempt {
    pub index: usize,
    pub head: GroundAtom,
    pub premise: GroundAtom,
    pub source: RuleId,
    pub cone_atoms: Option<usize>,
    pub cone_rules: Option<usize>,
    pub live_rules: Option<usize>,
    pub preprocessing: Duration,
    pub iteration: Duration,
    pub reused: bool,
    pub state: &'static str,
}

#[derive(Debug, Clone)]
pub struct AdmissionProgress {
    pub phase: AdmissionPhase,
    pub round: usize,
    pub stage: &'static str,
    pub unresolved_components: usize,
    /// Includes atoms in components depending on an unresolved component.
    pub blocked_atoms: usize,
    pub current: Option<AdmissionComponent>,
    /// One-based current rule in summaries/removals/candidates, zero outside scans.
    pub rule: usize,
    pub rules: usize,
    pub iteration: Option<usize>,
    pub removed_rules: usize,
    pub discharged_negations: usize,
    pub skipped_attempts: usize,
    /// Present only on the immediate, recoverable failure event.
    pub skipped: Option<AdmissionSkip>,
    pub failure: Option<Inconclusive>,
    pub attempts: BTreeMap<AdmissionAttemptKind, AdmissionAttempts>,
    pub guarded: Option<GuardedAttempt>,
    pub prerequisites: BTreeMap<&'static str, Duration>,
}
pub type AdmissionObserver<'a> = dyn Fn(&AdmissionProgress) + 'a;

struct State {
    progress: AdmissionProgress,
    current: Option<ComponentId>,
    current_rule: Option<GroundRuleId>,
    last: Option<Instant>,
    round_reported: bool,
}
pub(crate) struct AdmissionReporter<'a> {
    observer: Option<&'a AdmissionObserver<'a>>,
    state: RefCell<State>,
}
impl<'a> AdmissionReporter<'a> {
    pub fn new(observer: Option<&'a AdmissionObserver<'a>>) -> Self {
        Self {
            observer,
            state: RefCell::new(State {
                progress: AdmissionProgress {
                    phase: AdmissionPhase::Relevant,
                    round: 0,
                    stage: "starting",
                    unresolved_components: 0,
                    blocked_atoms: 0,
                    current: None,
                    rule: 0,
                    rules: 0,
                    iteration: None,
                    removed_rules: 0,
                    discharged_negations: 0,
                    skipped_attempts: 0,
                    skipped: None,
                    failure: None,
                    attempts: BTreeMap::new(),
                    prerequisites: BTreeMap::new(),
                    guarded: None,
                },
                current: None,
                current_rule: None,
                last: None,
                round_reported: false,
            }),
        }
    }
    pub fn phase(&self, phase: AdmissionPhase) {
        self.state.borrow_mut().progress.phase = phase;
    }
    pub fn enabled(&self) -> bool {
        self.observer.is_some()
    }
    pub fn reused(&self, kind: AdmissionAttemptKind, skipped: bool) {
        if !self.enabled() {
            return;
        }
        let mut s = self.state.borrow_mut();
        let counts = s.progress.attempts.entry(kind).or_default();
        if skipped {
            counts.reused_skip += 1;
        } else {
            counts.reused_negative += 1;
        }
    }
    pub fn reused_result(&self, kind: AdmissionAttemptKind) {
        if self.enabled() {
            self.state
                .borrow_mut()
                .progress
                .attempts
                .entry(kind)
                .or_default()
                .reused_result += 1;
        }
    }
    pub fn guarded_start(
        &self,
        program: &GroundProgram,
        index: usize,
        rule: &GroundRule,
        premise: &GroundAtom,
    ) {
        if !self.enabled() {
            return;
        }
        self.state.borrow_mut().progress.guarded = Some(GuardedAttempt {
            index,
            head: rule.head.atom.clone(),
            premise: premise.clone(),
            source: rule.source,
            cone_atoms: None,
            cone_rules: None,
            live_rules: None,
            preprocessing: Duration::ZERO,
            iteration: Duration::ZERO,
            reused: false,
            state: "preprocessing",
        });
        self.rule(program, "guarded-preprocessing", rule.id, 0);
    }
    pub fn guarded_prepared(
        &self,
        program: &GroundProgram,
        cone: Option<&GuardedCone>,
        elapsed: Duration,
        state: &'static str,
    ) {
        if !self.enabled() {
            return;
        }
        if let Some(g) = &mut self.state.borrow_mut().progress.guarded {
            g.preprocessing = elapsed;
            g.state = state;
            if let Some(c) = cone {
                g.cone_atoms = Some(c.atoms.len());
                g.cone_rules = Some(c.producers.len());
                g.live_rules = Some(
                    c.producers
                        .iter()
                        .filter(|p| !p.condition.is_false())
                        .count(),
                );
            }
        }
        if state != "iterating" {
            self.emit(program, true);
        }
    }
    pub fn guarded_end(
        &self,
        program: &GroundProgram,
        elapsed: Duration,
        reused: bool,
        state: &'static str,
    ) {
        if !self.enabled() {
            return;
        }
        if let Some(g) = &mut self.state.borrow_mut().progress.guarded {
            g.iteration = elapsed;
            g.reused = reused;
            g.state = state;
        }
        self.emit(program, true);
    }
    pub fn cutoff(&self, kind: AdmissionAttemptKind) {
        if self.enabled() {
            self.state
                .borrow_mut()
                .progress
                .attempts
                .entry(kind)
                .or_default()
                .cutoffs += 1;
        }
    }
    pub fn attempt_start(
        &self,
        kind: AdmissionAttemptKind,
        previous: Option<(bool, Option<&'static str>)>,
    ) -> Option<Instant> {
        if !self.enabled() {
            return None;
        }
        let mut s = self.state.borrow_mut();
        let counts = s.progress.attempts.entry(kind).or_default();
        match previous {
            None => counts.new += 1,
            Some((true, cause)) => {
                counts.retried_skip += 1;
                *counts
                    .retry_causes
                    .entry(cause.unwrap_or("unchanged"))
                    .or_default() += 1;
            }
            Some((false, cause)) => {
                counts.rerun_negative += 1;
                *counts
                    .retry_causes
                    .entry(cause.unwrap_or("unchanged"))
                    .or_default() += 1;
            }
        }
        Some(Instant::now())
    }
    pub fn attempt_end(&self, kind: AdmissionAttemptKind, started: Option<Instant>, outcome: &str) {
        let Some(started) = started else {
            return;
        };
        let mut s = self.state.borrow_mut();
        let counts = s.progress.attempts.entry(kind).or_default();
        counts.elapsed += started.elapsed();
        match outcome {
            "negative" => counts.negative += 1,
            "skipped" => counts.skipped += 1,
            "failed" => counts.failed += 1,
            _ => counts.completed += 1,
        }
    }
    pub fn time(&self, stage: &'static str) -> AdmissionTimer<'_, 'a> {
        AdmissionTimer {
            reporter: self,
            stage,
            started: self.enabled().then(Instant::now),
        }
    }
    pub fn round_end(&self, program: &GroundProgram) {
        if !self.enabled() {
            return;
        }
        let mut s = self.state.borrow_mut();
        if s.round_reported || s.progress.round == 0 {
            return;
        }
        s.round_reported = true;
        let old = s.progress.stage;
        s.progress.stage = "attempt-summary";
        drop(s);
        self.emit(program, true);
        self.state.borrow_mut().progress.stage = old;
    }
    pub fn snapshot(&self, program: &GroundProgram, round: usize, stage: &'static str) {
        if !self.enabled() {
            return;
        }
        if self.state.borrow().progress.round != round {
            self.round_end(program);
            let mut s = self.state.borrow_mut();
            s.progress.attempts.clear();
            s.progress.prerequisites.clear();
            s.round_reported = false;
        }
        {
            let mut s = self.state.borrow_mut();
            s.progress.round = round;
            s.progress.unresolved_components = program
                .components
                .iter()
                .filter(|c| c.cycle.is_some())
                .count();
            s.progress.blocked_atoms = program
                .components
                .iter()
                .filter(|c| !c.blocked_by.is_empty())
                .map(|c| c.atoms.len())
                .sum();
            s.progress.rules = program
                .rules
                .iter()
                .filter(|r| !program.rewrites.dropped.contains(&r.id))
                .count();
            s.progress.removed_rules = program.rewrites.dropped.len();
            s.progress.discharged_negations = program
                .rewrite_proofs()
                .filter(|p| matches!(p.kind, RewriteKind::Discharge { .. }))
                .count();
            s.progress.skipped_attempts = s
                .progress
                .skipped_attempts
                .max(program.rewrites.skipped_attempts);
        }
        self.work(program, stage, None, 0, true);
    }
    pub fn work(
        &self,
        program: &GroundProgram,
        stage: &'static str,
        current: Option<ComponentId>,
        rule: usize,
        force: bool,
    ) {
        if !self.enabled() {
            return;
        }
        let mut s = self.state.borrow_mut();
        let changed = s.progress.stage != stage;
        s.progress.stage = stage;
        if !stage.starts_with("guarded-") {
            s.progress.guarded = None;
        }
        s.progress.rule = rule;
        s.progress.iteration = None;
        s.current = current;
        s.current_rule = None;
        drop(s);
        self.emit(program, force || changed);
    }
    pub fn rule(
        &self,
        program: &GroundProgram,
        stage: &'static str,
        rule: GroundRuleId,
        position: usize,
    ) {
        if !self.enabled() {
            return;
        }
        let mut s = self.state.borrow_mut();
        let changed = s.progress.stage != stage;
        s.progress.stage = stage;
        if !stage.starts_with("guarded-") {
            s.progress.guarded = None;
        }
        s.progress.rule = position;
        s.progress.iteration = None;
        s.current = None;
        s.current_rule = Some(rule);
        drop(s);
        self.emit(program, changed);
    }
    pub fn iteration(&self, program: &GroundProgram, iteration: usize) {
        if !self.enabled() {
            return;
        }
        self.state.borrow_mut().progress.iteration = Some(iteration);
        self.emit(program, false);
    }
    pub fn finish(&self, program: &GroundProgram, stage: &'static str) {
        let round = self.state.borrow().progress.round;
        self.snapshot(program, round, stage);
    }
    pub fn failed(&self, program: &GroundProgram, error: &CheckError) {
        if !self.enabled() {
            return;
        }
        let mut s = self.state.borrow_mut();
        s.progress.failure = match error {
            CheckError::LimitExceeded {
                phase,
                resource,
                details,
            } => Some(Inconclusive {
                phase,
                resource,
                details: *details,
            }),
            CheckError::Deadline { phase, details } => Some(Inconclusive {
                phase,
                resource: "deadline",
                details: *details,
            }),
            _ => None,
        };
        // Preserve the last stage/component on exhaustion so the failing work
        // is identifiable even when its ordinary progress was throttled.
        drop(s);
        self.emit(program, true);
    }
    pub fn skipped(&self, program: &GroundProgram, skip: &AdmissionSkip, count: usize) {
        if !self.enabled() {
            return;
        }
        {
            let mut s = self.state.borrow_mut();
            s.progress.skipped_attempts = count;
            s.progress.skipped = Some(skip.clone());
            s.progress.failure = Some(skip.reason);
        }
        self.emit(program, true);
        let mut s = self.state.borrow_mut();
        s.progress.skipped = None;
        s.progress.failure = None;
    }
    fn emit(&self, program: &GroundProgram, force: bool) {
        let Some(observer) = self.observer else {
            return;
        };
        let mut s = self.state.borrow_mut();
        if !force
            && s.last
                .is_some_and(|t| t.elapsed() < Duration::from_millis(250))
        {
            return;
        }
        s.last = Some(Instant::now());
        // Resolve rule -> component only for delivered updates, not on every
        // rule visited in a large summaries/removals/candidates scan.
        let current = s.current.or_else(|| {
            s.current_rule
                .and_then(|id| program.rule(id))
                .and_then(|r| program.component_for(&r.head.atom).ok())
                .map(|c| c.id)
        });
        s.progress.current = current.and_then(|id| {
            let c = program.component(id)?;
            let first = c.cycle.as_ref().and_then(|c| c.edges.first());
            let rule = first.and_then(|e| program.rule(e.rule)).or_else(|| {
                program.component_rules[id.index]
                    .first()
                    .map(|i| &program.rules[*i])
            });
            Some(AdmissionComponent {
                index: id.index + 1,
                atoms: c.atoms.len(),
                rules: program.component_rules[id.index].len(),
                representative: first
                    .map(|e| &e.consumer)
                    .or_else(|| c.atoms.first())?
                    .clone(),
                source: rule.map(|r| r.source),
            })
        });
        observer(&s.progress);
    }
}

pub(crate) struct AdmissionTimer<'r, 'a> {
    reporter: &'r AdmissionReporter<'a>,
    stage: &'static str,
    started: Option<Instant>,
}
impl Drop for AdmissionTimer<'_, '_> {
    fn drop(&mut self) {
        if let Some(started) = self.started {
            *self
                .reporter
                .state
                .borrow_mut()
                .progress
                .prerequisites
                .entry(self.stage)
                .or_default() += started.elapsed();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limits::Budget;
    use crate::test_support::rewrites::{rel, rule};
    use denotate_ir::Corpus;

    fn program() -> GroundProgram {
        let mut c = Corpus::new();
        let t = rel(&mut c, "t", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        let x = rel(&mut c, "x", false);
        let y = rel(&mut c, "y", false);
        rule(&mut c, a, &[(t, false), (b, true)]);
        rule(&mut c, b, &[(t, true), (a, true)]);
        rule(&mut c, x, &[(a, false), (y, true)]);
        rule(&mut c, y, &[(a, true), (x, true)]);
        GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap()
    }
    fn compare(raw: &GroundProgram, limits: &Limits) -> Vec<AdmissionProgress> {
        let mut quiet = Budget::tracked(limits);
        let expected = raw.clone().admit_with_budget(&mut quiet).unwrap();
        let events = RefCell::new(Vec::new());
        let mut observed = Budget::tracked(limits);
        let actual = raw
            .clone()
            .admit_observed(
                &mut observed,
                Some(&|p| events.borrow_mut().push(p.clone())),
            )
            .unwrap();
        assert_eq!(quiet.snapshot(), observed.snapshot());
        assert_eq!(expected.admission_limit(), actual.admission_limit());
        assert_eq!(expected.is_admitted(), actual.is_admitted());
        assert_eq!(
            expected.rules().collect::<Vec<_>>(),
            actual.rules().collect::<Vec<_>>()
        );
        assert_eq!(
            expected
                .rewrite_proofs()
                .map(|p| (&p.kind, p.candidate().id))
                .collect::<Vec<_>>(),
            actual
                .rewrite_proofs()
                .map(|p| (&p.kind, p.candidate().id))
                .collect::<Vec<_>>()
        );
        events.into_inner()
    }
    #[test]
    fn admission_progress_describes_committed_rounds_without_changing_work() {
        let events = compare(&program(), &Limits::default());
        assert_eq!(events[0].unresolved_components, 2);
        assert_eq!(events[0].blocked_atoms, 4);
        assert!(events.iter().any(|e| {
            e.stage == "upper-bounds"
                && e.current
                    .as_ref()
                    .is_some_and(|c| c.atoms == 2 && c.source.is_some())
        }));
        assert!(
            events
                .iter()
                .any(|e| e.stage == "committed" && e.unresolved_components == 1)
        );
        let last = events.last().unwrap();
        assert_eq!(last.stage, "complete");
        assert_eq!(last.unresolved_components, 0);
        assert_eq!(last.blocked_atoms, 0);
        assert_eq!(last.discharged_negations, 4);
        assert!(last.current.is_none());
    }
    #[test]
    fn temporary_bound_storage_exhaustion_reports_the_component_and_continues() {
        let raw = program();
        let mut covered_upper_bounds = false;
        // Find an exhaustion inside the component analysis without pinning a
        // particular budget, receipt, iteration count or elapsed time.
        for max_condition_nodes in 0..400 {
            let events = compare(
                &raw,
                &Limits {
                    max_condition_nodes,
                    ..Limits::default()
                },
            );
            if let Some((index, event)) = events.iter().enumerate().find(|(_, e)| {
                e.skipped
                    .as_ref()
                    .is_some_and(|s| s.kind == AdmissionAttemptKind::UpperBounds)
            }) {
                assert!(event.current.is_some());
                assert!(event.failure.is_some());
                assert!(event.unresolved_components > 0);
                assert!(
                    events.len() > index + 1,
                    "a local skip must not stop the run"
                );
                covered_upper_bounds = true;
                break;
            }
        }
        assert!(covered_upper_bounds);
    }
}
