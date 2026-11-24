//! Completion equivalence using the common equations. The target head's
//! definition is disabled in every proof. Other equations are unchanged in both
//! programs. No scope is ever computed from these solver-instance rewrites.
use super::*;
mod branch;
mod literals;
pub(super) use branch::{TrialPool, prove, trial};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PruningContext {
    World,
    Hypothesis,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PruningKind {
    Subsumption,
    Coverage,
    ImpliedBodyLiteral,
}
#[derive(Debug, Clone)]
pub struct PruningRecord {
    pub context: PruningContext,
    pub kind: PruningKind,
    pub head: GroundAtom,
    pub rules: Vec<GroundRuleId>,
    pub removed: usize,
    pub removed_literals: usize,
    pub scope_heads: usize,
    pub scope: &'static str,
    pub pins: Vec<(GroundAtom, bool)>,
    pub omitted_pins: usize,
    pub literal: Option<GroundAtom>,
    pub structural: bool,
}
#[derive(Debug, Clone)]
pub struct PruningComponent {
    pub scope: &'static str,
    pub context: PruningContext,
    pub representative: GroundAtom,
    pub atoms: usize,
    pub rules: usize,
    pub kind: &'static str,
    pub discovery_complete: bool,
    pub candidate_heads: usize,
    pub candidate_examples: Vec<GroundAtom>,
    pub candidate_producers: usize,
    pub considered: usize,
    pub proved: usize,
    pub removed: usize,
    pub removed_literals: usize,
    pub last_head: Option<GroundAtom>,
    pub cutoff: Option<Inconclusive>,
    pub elapsed: Duration,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PruningStop {
    Saturated,
    CandidateCutoff,
    OverallCutoff,
}
impl PruningStop {
    pub fn label(self) -> &'static str {
        match self {
            Self::Saturated => "saturated",
            Self::CandidateCutoff => "candidate-cutoff",
            Self::OverallCutoff => "overall-cutoff",
        }
    }
}
#[derive(Debug, Clone)]
pub struct PruningView {
    pub scope: &'static str,
    pub context: PruningContext,
    pub rounds: usize,
    pub attempts: usize,
    pub proved: usize,
    pub removed: usize,
    pub removed_literals: usize,
    pub covered: usize,
    pub stop: PruningStop,
    pub allocated: Duration,
    pub elapsed: Duration,
    pub released: Duration,
    pub priority_attempts: usize,
    pub priority_proved: usize,
}
#[derive(Debug, Clone, Default)]
pub struct PruningReport {
    pub enabled: bool,
    pub views: Vec<PruningView>,
    pub omitted_views: usize,
    pub components: Vec<PruningComponent>,
    pub omitted_components: usize,
    pub elapsed: Duration,
    pub attempts: usize,
    pub removed: usize,
    pub removed_literals: usize,
    pub covered: usize,
    pub records: Vec<PruningRecord>,
    pub omitted: usize,
    pub branch_records: Vec<PruningRecord>,
    pub omitted_branch_records: usize,
    pub incomplete: Vec<Inconclusive>,
    pub trial_attempts: usize,
    pub trial_proved: usize,
    pub trial_elapsed: Duration,
    pub trial_released: Duration,
}
#[derive(Default)]
pub(super) struct Cache {
    views: BTreeMap<ViewKey, Arc<Cone>>,
    pub report: PruningReport,
    reservations: Reservations,
    // Scheduling hints, independent of capped diagnostic records. Invocation-local
    // atom indexes; never reused as proofs or across preparations.
    classification_successes: BTreeSet<usize>,
    pub(super) readonly: bool,
    pub(super) pins: Vec<(usize, bool)>,
    pub(super) trials: Option<Arc<std::sync::Mutex<TrialPool>>>,
}
type Bucket = (&'static str, PruningContext);
#[derive(Default)]
struct Reservation {
    allowance: Duration,
    spent: Duration,
    started: bool,
}
#[derive(Default)]
struct Reservations {
    slots: BTreeMap<Bucket, Reservation>,
    leftover: Duration,
}
impl Reservations {
    fn new(allowance: Duration, classification: bool, properties: bool) -> Self {
        let scopes = std::iter::once("processing")
            .chain(classification.then_some("classification"))
            .chain(properties.then_some("property"));
        let contexts = [PruningContext::World, PruningContext::Hypothesis];
        let mut slots = BTreeMap::new();
        for scope in scopes {
            for &context in &contexts[..if classification { 2 } else { 1 }] {
                slots.insert((scope, context), Reservation::default());
            }
        }
        let share = allowance / slots.len() as u32;
        for slot in slots.values_mut() {
            slot.allowance = share;
        }
        Self {
            slots,
            leftover: Duration::ZERO,
        }
    }
    fn start(&mut self, key: Bucket) -> Duration {
        let slot = self.slots.get_mut(&key).expect("planned pruning scope");
        slot.started = true;
        slot.allowance.saturating_sub(slot.spent)
    }
    fn finish(&mut self, key: Bucket, elapsed: Duration, stop: PruningStop) -> Duration {
        let slot = self.slots.get_mut(&key).unwrap();
        slot.spent += elapsed;
        // Property cones share a bucket. Saturating one is not completion of
        // the others. Root scopes each have one view per context.
        if stop != PruningStop::Saturated || key.0 == "property" {
            return Duration::ZERO;
        }
        let unused = slot.allowance.saturating_sub(slot.spent);
        slot.allowance = slot.spent; // release at most once, including cache hits
        let mut recipients = self
            .slots
            .values_mut()
            .filter(|s| !s.started)
            .collect::<Vec<_>>();
        if recipients.is_empty() {
            self.leftover += unused;
            return Duration::ZERO;
        }
        let share = unused / recipients.len() as u32;
        let mut remaining = unused;
        for recipient in &mut recipients {
            recipient.allowance += share;
            remaining -= share;
        }
        recipients.last_mut().unwrap().allowance += remaining;
        unused
    }
}
#[derive(Default)]
struct Successes {
    heads: BTreeSet<usize>,
    priority_attempts: usize,
    priority_proved: usize,
}
pub(super) type ViewKey = (Vec<usize>, PruningContext, Vec<(usize, bool)>);
pub(super) fn view_key(c: &Cone, context: PruningContext) -> ViewKey {
    (
        c.rules
            .iter()
            .map(|r| r.head)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
        context,
        vec![],
    )
}
impl Cache {
    pub(super) fn merge(&mut self, report: PruningReport) {
        for view in report.views {
            if self.report.views.len() < 64 {
                self.report.views.push(view);
            } else {
                self.report.omitted_views += 1;
            }
        }
        for row in report.components {
            if self.report.components.len() < 64 {
                self.report.components.push(row);
            } else {
                self.report.omitted_components += 1;
            }
        }
        self.report.omitted_components += report.omitted_components;
        self.report.attempts += report.attempts;
        self.report.removed += report.removed;
        self.report.removed_literals += report.removed_literals;
        self.report.covered += report.covered;
        for record in report.records.into_iter().chain(report.branch_records) {
            let conditional = !record.pins.is_empty() || record.omitted_pins > 0;
            let (records, omitted) = if conditional {
                (
                    &mut self.report.branch_records,
                    &mut self.report.omitted_branch_records,
                )
            } else {
                (&mut self.report.records, &mut self.report.omitted)
            };
            if records.len() < 64 {
                records.push(record);
            } else {
                *omitted += 1;
            }
        }
        self.report.omitted_branch_records += report.omitted_branch_records;
        self.report.omitted += report.omitted;
        let room = 64 - self.report.incomplete.len().min(64);
        self.report
            .incomplete
            .extend(report.incomplete.into_iter().take(room));
    }
    pub(super) fn enable_trials(&mut self, e: &Engine) {
        self.trials = Some(Arc::new(std::sync::Mutex::new(TrialPool::new(
            &self.reservations,
            e,
        ))));
    }
    pub(super) fn for_engine(e: &Engine) -> Self {
        let remaining = e.limits.run_deadline.map_or(e.limits.timeout, |d| {
            d.saturating_duration_since(Instant::now())
                .min(e.limits.timeout)
        });
        // Preparation can consume most of the run. Preserve search time even
        // then; independent verification reservations still bound the total.
        let allowance = e
            .limits
            .pruning_allowance
            .unwrap_or(e.limits.timeout / 3)
            .min(remaining / 3);
        Self {
            reservations: Reservations::new(
                allowance,
                e.classification.is_some(),
                !e.selection.is_empty(),
            ),
            ..Self::default()
        }
    }
    pub(super) fn inherited(views: BTreeMap<ViewKey, Arc<Cone>>, pins: Vec<(usize, bool)>) -> Self {
        Self {
            views,
            pins,
            readonly: true,
            ..Self::default()
        }
    }
    pub(super) fn branch_views(&self, e: &Engine) -> Vec<(ViewKey, Arc<Cone>)> {
        let mut keys = BTreeSet::new();
        for c in std::iter::once(&e.cone).chain(e.classification.as_ref().map(|(c, _, _)| c)) {
            for context in [PruningContext::World, PruningContext::Hypothesis] {
                let mut key = view_key(c, context);
                key.2 = self.pins.clone();
                keys.insert(key);
            }
        }
        keys.into_iter()
            .filter_map(|k| self.views.get(&k).map(|v| (k, v.clone())))
            .collect()
    }
}
pub(super) enum View<'a> {
    Original(&'a Cone),
    Pruned(Arc<Cone>),
}
impl View<'_> {
    pub(super) fn label(&self) -> &'static str {
        match self {
            Self::Original(_) => "unpruned",
            Self::Pruned(_) => "pruned",
        }
    }
}
impl std::ops::Deref for View<'_> {
    type Target = Cone;
    fn deref(&self) -> &Cone {
        match self {
            Self::Original(c) => c,
            Self::Pruned(c) => c,
        }
    }
}

pub(super) fn view<'a>(
    engine: &Engine,
    cone: &'a Cone,
    hypothesis: bool,
    remaining: std::time::Duration,
) -> Result<View<'a>> {
    let Some(cache) = &engine.pruning else {
        return Ok(View::Original(cone));
    };
    // All callers supply a frozen scope with every original producer of its
    // heads. The program, domains and W are fixed for this invocation.
    let heads: Vec<_> = cone
        .rules
        .iter()
        .map(|r| r.head)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let context = if hypothesis && engine.classification.is_some() {
        PruningContext::Hypothesis
    } else {
        PruningContext::World
    };
    let key = (heads, context, cache.lock().unwrap().pins.clone());
    {
        let cache = cache.lock().unwrap();
        if let Some(v) = cache.views.get(&key).cloned() {
            return Ok(View::Pruned(v));
        }
        // A branch may reuse only proofs made in its ancestor's exact scope.
        // Computing new pin-relative proofs belongs to the next increment.
        if cache.readonly {
            return Ok(View::Original(cone));
        }
    }
    let classification_heads = engine
        .classification
        .as_ref()
        .map(|(c, _, _)| c.rules.iter().map(|r| r.head).collect::<BTreeSet<_>>());
    let scope = if classification_heads
        .as_ref()
        .is_some_and(|h| h.iter().copied().eq(key.0.iter().copied()))
    {
        "classification"
    } else if engine
        .cone
        .rules
        .iter()
        .map(|r| r.head)
        .collect::<BTreeSet<_>>()
        .iter()
        .copied()
        .eq(key.0.iter().copied())
    {
        "processing"
    } else {
        "property"
    };
    // H views extend the same frozen scope's W-pruned view. No H proof
    // can enter the W cache or a classification query without H.
    let base_started = Instant::now();
    let base = if context == PruningContext::Hypothesis {
        view(engine, cone, false, remaining)?
    } else {
        View::Original(cone)
    };
    let remaining = remaining.saturating_sub(base_started.elapsed());
    let phase = match context {
        PruningContext::World => "completion pruning W",
        PruningContext::Hypothesis => "completion pruning W+H",
    };
    let _progress = engine.limits.progress.diagnostic(phase);
    let mut limits = engine.limits.clone();
    // Reserve independent shares for classification/processing/property, W/H.
    // A W pass cannot consume the later H pass's reservation. The invocation's
    // absolute deadline and this query's remaining time still bound every pass.
    let (available, priority) = {
        let mut c = cache.lock().unwrap();
        let available = c.reservations.start((scope, context));
        let priority = if scope == "processing" {
            c.classification_successes.clone()
        } else {
            BTreeSet::new()
        };
        (available, priority)
    };
    limits.timeout = limits.timeout.min(remaining).min(available);
    let started = Instant::now();
    let mut budget = Budget::new(&limits);
    let mut result = (*base).clone();
    let mut report = PruningReport::default();
    let mut rounds = 0;
    let mut successes = Successes::default();
    let mut round_engine = engine.clone();
    let stop = loop {
        let previous = result.clone();
        let removed = (report.removed, report.removed_literals);
        let first_row = report.components.len();
        let first_cutoff = report.incomplete.len();
        rounds += 1;
        let mut used = QueryLimits {
            max_solves: 0,
            max_solver_polls: 0,
            max_conflicts: 0,
            max_propagations: 0,
        };
        let answer = simplify(
            &round_engine,
            &previous,
            &mut result,
            context,
            scope,
            key.0.len(),
            &mut report,
            &mut budget,
            &mut used,
            &priority,
            &mut successes,
            None,
        );
        round_engine.config.max_solves = round_engine
            .config
            .max_solves
            .saturating_sub(used.max_solves);
        round_engine.config.max_solver_polls = round_engine
            .config
            .max_solver_polls
            .saturating_sub(used.max_solver_polls);
        round_engine.config.max_conflicts = round_engine
            .config
            .max_conflicts
            .saturating_sub(used.max_conflicts);
        round_engine.config.max_propagations = round_engine
            .config
            .max_propagations
            .saturating_sub(used.max_propagations);
        if let Err(error) = answer {
            // Keep every proved prefix. Optimization exhaustion is not a verdict.
            limits.cancellation.check()?;
            report
                .incomplete
                .push(inconclusive(error.in_phase(phase, None))?);
            break PruningStop::OverallCutoff;
        }
        if (report.removed, report.removed_literals) == removed {
            break if report.incomplete.len() != first_cutoff
                || report.components[first_row..]
                    .iter()
                    .any(|c| c.cutoff.is_some() || !c.discovery_complete)
            {
                PruningStop::CandidateCutoff
            } else {
                PruningStop::Saturated
            };
        }
        if report.components.len() > 64 {
            report.omitted_components += report.components.len() - 64;
            report.components.truncate(64);
        }
        if report.incomplete.len() > 64 {
            report.incomplete.truncate(64);
        }
        // A changed equation can make earlier failed proofs succeed and can
        // change the relevant SCCs. Rediscover from the proved prefix.
    };
    let elapsed = started.elapsed();
    let mut cache = cache.lock().unwrap();
    let released = cache.reservations.finish((scope, context), elapsed, stop);
    if let Some(pool) = cache.trials.clone() {
        let leftover = std::mem::take(&mut cache.reservations.leftover);
        pool.lock().unwrap().release(leftover);
    }
    if scope == "classification" && context == PruningContext::World {
        cache.classification_successes.extend(successes.heads);
    }
    report.views.push(PruningView {
        scope,
        context,
        rounds,
        attempts: report.attempts,
        proved: report.records.len() + report.omitted,
        removed: report.removed,
        removed_literals: report.removed_literals,
        covered: report.covered,
        stop,
        allocated: limits.timeout,
        elapsed,
        released,
        priority_attempts: successes.priority_attempts,
        priority_proved: successes.priority_proved,
    });
    let result = Arc::new(result);
    cache.report.elapsed += elapsed;
    cache.merge(report);
    cache.views.insert(key, result.clone());
    Ok(View::Pruned(result))
}

/// Build the reusable views before any question divides its search allowance.
/// The reservation is independent of split mode and bounded across all views.
pub(super) fn prepare(e: &Engine, classification: bool) -> Result<()> {
    if e.pruning.is_none() {
        return Ok(());
    }
    let cone = if classification {
        &*e.classification.as_ref().unwrap().0
    } else {
        &*e.cone
    };
    view(e, cone, e.classification.is_some(), e.limits.timeout)?;
    Ok(())
}

pub(super) fn subtract_query(q: &QueryLimits, used: &QueryLimits) -> QueryLimits {
    QueryLimits {
        max_solves: q.max_solves.saturating_sub(used.max_solves),
        max_solver_polls: q.max_solver_polls.saturating_sub(used.max_solver_polls),
        max_conflicts: q.max_conflicts.saturating_sub(used.max_conflicts),
        max_propagations: q.max_propagations.saturating_sub(used.max_propagations),
    }
}
pub(super) fn add_query(q: &mut QueryLimits, used: QueryLimits) {
    q.max_solves = q.max_solves.saturating_add(used.max_solves);
    q.max_solver_polls = q.max_solver_polls.saturating_add(used.max_solver_polls);
    q.max_conflicts = q.max_conflicts.saturating_add(used.max_conflicts);
    q.max_propagations = q.max_propagations.saturating_add(used.max_propagations);
}
fn simplify(
    engine: &Engine,
    original: &Cone,
    result: &mut Cone,
    context: PruningContext,
    scope: &'static str,
    scope_heads: usize,
    report: &mut PruningReport,
    budget: &mut Budget<'_>,
    used: &mut QueryLimits,
    priority: &BTreeSet<usize>,
    successes: &mut Successes,
    only: Option<&BTreeSet<usize>>,
) -> Result<()> {
    let n = original.fixed.len();
    budget.charge(n + original.rules.len(), "completion pruning index")?;
    let mut producers = vec![Vec::new(); n];
    for (i, r) in original.rules.iter().enumerate() {
        producers[r.head].push(i);
    }
    // One producer can be covered under H too. Skip facts and producer-less
    // heads; constants already have a completion-safe Fitting path.
    let settled = encoding::fitting(original, budget)?;
    let mut discovery_limits = budget.limits.clone();
    discovery_limits.timeout = (budget.remaining_time() / 4).min(Duration::from_millis(500));
    discovery_limits.max_work = budget.limits.max_work.saturating_sub(budget.used()) / 4;
    let mut discovery_budget = Budget::new(&discovery_limits);
    let targets = symbolic::targets::discover(
        engine,
        original,
        &settled,
        scope,
        context,
        report,
        &mut discovery_budget,
        only,
        used,
    );
    budget.charge(
        discovery_budget.used(),
        "completion pruning target discovery",
    )?;
    let targets = match targets {
        Ok(targets) => targets,
        Err(error) => {
            // Discovery has a smaller local allowance than the view. Failure
            // before its first component is still an unresolved discovery attempt,
            // not exhaustion of the aggregate view budget.
            engine.limits.cancellation.check()?;
            report.incomplete.push(inconclusive(error)?);
            return Ok(());
        }
    };
    let candidates = targets.heads.clone();
    if candidates.is_empty() {
        return Ok(());
    }
    if literals::structural(
        original,
        result,
        &targets,
        scope,
        context,
        scope_heads,
        report,
        budget,
        successes,
    )? {
        return Ok(());
    }
    // Fold only consequences independent of ALL candidate definitions. Those
    // constants remain valid whichever single equation the proof disables.
    let mut abstracted = original.clone();
    for h in &candidates {
        abstracted.input[*h] = true;
    }
    abstracted.rules.retain(|r| !abstracted.input[r.head]);
    let fixed = encoding::fitting(&abstracted, budget)?;
    let mut proof_engine = engine.clone();
    proof_engine.config = subtract_query(&engine.config, used);
    let mut run = queries::Run::new(&proof_engine, budget)?;
    run.label(match context {
        PruningContext::World => "completion pruning W",
        PruningContext::Hypothesis => "completion pruning W+H",
    });
    let vars: Vec<_> = (0..n)
        .map(|i| match fixed[i] {
            Some(true) => Ok(run.truth),
            Some(false) => Ok(!run.truth),
            None if original.input[i] => Ok(run.world.vars[i]),
            _ => run.cnf.var(run.budget),
        })
        .collect::<Result<_>>()?;
    let mut logic = encoding::Booleans::new(run.truth);
    let mut bodies = Vec::with_capacity(original.rules.len());
    for r in &original.rules {
        let lits = r
            .body
            .iter()
            .map(|(i, p)| if *p { vars[*i] } else { !vars[*i] })
            .collect::<Vec<_>>();
        bodies.push(logic.and(&lits, &mut run.cnf, run.budget)?);
    }
    let mut gates = Vec::new();
    let mut live_gates = Vec::new();
    let mut current = vec![None; n];
    let mut enabled = vec![true; original.rules.len()];
    for h in 0..n {
        if original.input[h] || fixed[h].is_some() {
            continue;
        }
        let body = logic.or(
            &producers[h].iter().map(|r| bodies[*r]).collect::<Vec<_>>(),
            &mut run.cnf,
            run.budget,
        )?;
        let gate = run.cnf.var(run.budget)?;
        current[h] = Some(gates.len());
        gates.push(gate);
        live_gates.push(true);
        equation(&mut run, gate, vars[h], body)?;
    }
    let source: Vec<_> = original
        .rules
        .iter()
        .map(|r| {
            r.ground
                .ok_or(CheckError::Internal("pruning rule has no ground source"))
        })
        .collect::<Result<_>>()?;
    let mut working = original.clone();
    #[derive(Clone, Copy)]
    enum Attempt {
        Coverage,
        Producer(usize),
        Literal(usize, usize),
    }
    struct Pending {
        head: usize,
        coverage: bool,
        remaining: Vec<usize>,
        candidates: std::collections::VecDeque<usize>,
        literals: std::collections::VecDeque<(usize, usize)>,
    }
    let pending: std::collections::VecDeque<_> = candidates
        .into_iter()
        .map(|head| Pending {
            head,
            coverage: true,
            remaining: producers[head].clone(),
            candidates: targets.rules[&head].clone().into(),
            literals: targets.rules[&head]
                .iter()
                .flat_map(|r| {
                    original.rules[*r]
                        .body
                        .iter()
                        .filter(|(i, p)| {
                            *p && settled[*i].is_none()
                                && targets.components.get(i) == targets.components.get(&head)
                        })
                        .map(move |(i, _)| (*r, *i))
                })
                .collect(),
        })
        .collect();
    let (mut preferred, pending): (std::collections::VecDeque<_>, std::collections::VecDeque<_>) =
        pending
            .into_iter()
            .partition(|p| priority.contains(&p.head));
    let (mut pending, mut deferred): (
        std::collections::VecDeque<_>,
        std::collections::VecDeque<_>,
    ) = pending.into_iter().partition(|p| p.remaining.len() > 1);
    let mut current_row = None;
    let outcome: Result<()> = (|| {
        loop {
            if pending.is_empty() {
                std::mem::swap(&mut pending, &mut deferred);
            }
            let Some(mut item) = preferred.pop_front().or_else(|| pending.pop_front()) else {
                break;
            };
            let head = item.head;
            let row = targets.components[&head];
            current_row = Some(row);
            let attempt = if item.coverage {
                Attempt::Coverage
            } else if let Some((r, lit)) = item.literals.pop_front() {
                if !enabled[r] || !working.rules[r].body.contains(&(lit, true)) {
                    continue;
                }
                Attempt::Literal(r, lit)
            } else {
                let Some(r) = item.candidates.pop_front() else {
                    continue;
                };
                if item.remaining.len() < 2 {
                    continue;
                }
                // Removing this instance must cut at least one unresolved
                // internal edge. Parallel producers can keep an edge alive.
                let cuts = working.rules[r].body.iter().any(|lit| {
                    targets.components.get(&lit.0) == Some(&row)
                        && settled[lit.0].is_none()
                        && item
                            .remaining
                            .iter()
                            .filter(|q| **q != r)
                            .all(|q| !working.rules[*q].body.contains(lit))
                });
                if !cuts {
                    if !item.candidates.is_empty() {
                        if priority.contains(&head) {
                            preferred.push_back(item);
                        } else {
                            pending.push_back(item);
                        }
                    }
                    continue;
                }
                Attempt::Producer(r)
            };
            let candidate = match attempt {
                Attempt::Producer(r) => Some(r),
                _ => None,
            };
            let start = Instant::now();
            report.components[row].last_head = Some(original.atoms[head].clone());
            report.components[row].considered += 1;
            report.attempts += 1;
            successes.priority_attempts += usize::from(priority.contains(&head));
            let _progress =
                engine
                    .limits
                    .progress
                    .sampled("completion targeted pruning", true, || {
                        crate::CheckingTarget::CompletionPruning(report.components[row].clone())
                    });
            let union = logic.or(
                &item
                    .remaining
                    .iter()
                    .filter(|r| Some(**r) != candidate)
                    .map(|r| bodies[*r])
                    .collect::<Vec<_>>(),
                &mut run.cnf,
                run.budget,
            )?;
            let mut pins: Vec<_> = gates
                .iter()
                .enumerate()
                .map(|(i, g)| {
                    if live_gates[i] && Some(i) != current[head] {
                        *g
                    } else {
                        !*g
                    }
                })
                .collect();
            if context == PruningContext::Hypothesis {
                pins.push(vars[engine.classification.as_ref().unwrap().2]);
            }
            if let Attempt::Literal(r, lit) = attempt {
                pins.extend(
                    working.rules[r]
                        .body
                        .iter()
                        .filter(|(i, p)| !(*i == lit && *p))
                        .map(|(i, p)| if *p { vars[*i] } else { !vars[*i] }),
                );
                pins.push(!vars[lit]);
            } else {
                if let Some(r) = candidate {
                    pins.push(bodies[r]);
                }
                pins.push(!union);
            }
            run.budget.charge(pins.len(), "completion pruning pins")?;
            // A hard candidate cannot consume every other head's opportunity.
            // Solver clauses remain valid after an interrupted limited solve.
            let slice = (run.budget.remaining_time()
                / ((preferred.len() + pending.len() + 1).min(16) as u32))
                .min(Duration::from_millis(250));
            let stop = run.cnf.solver.cb_mut();
            let old = stop.timeout;
            stop.timeout = old.min(stop.start.elapsed() + slice);
            let answer = run.raw_solve(&pins);
            run.cnf.solver.cb_mut().timeout = old;
            let proved = match answer {
                Ok(sat) => !sat,
                Err(CheckError::Deadline { .. })
                    if run.budget.check("completion pruning").is_ok() =>
                {
                    let cause =
                        inconclusive(CheckError::deadline("completion pruning candidate", slice))?;
                    // The component retains its latest candidate cutoff.
                    // Keep the bounded view-cutoff list available for later
                    // views instead of filling it with short candidate slices.
                    report.components[row].cutoff = Some(cause);
                    false
                }
                Err(e) => {
                    report.components[row].elapsed += start.elapsed();
                    report.components[row].cutoff = Some(inconclusive(e)?);
                    return Err(report.components[row].cutoff.unwrap().into());
                }
            };
            if proved {
                successes.heads.insert(head);
                successes.priority_proved += usize::from(priority.contains(&head));
                report.components[row].proved += 1;
                if let Attempt::Literal(r, lit) = attempt {
                    literals::record(
                        original,
                        report,
                        row,
                        context,
                        scope,
                        scope_heads,
                        source[r],
                        head,
                        lit,
                        false,
                    );
                    working.rules[r].body.retain(|l| *l != (lit, true));
                    let lits: Vec<_> = working.rules[r]
                        .body
                        .iter()
                        .map(|(i, p)| if *p { vars[*i] } else { !vars[*i] })
                        .collect();
                    bodies[r] = logic.and(&lits, &mut run.cnf, run.budget)?;
                } else {
                    let removed = if candidate.is_some() {
                        1
                    } else {
                        item.remaining.len()
                    };
                    report.components[row].removed += removed;
                    let rs = if let Some(r) = candidate {
                        vec![source[r]]
                    } else {
                        item.remaining.iter().take(32).map(|r| source[*r]).collect()
                    };
                    retain(
                        report,
                        PruningRecord {
                            context,
                            kind: if candidate.is_some() {
                                PruningKind::Subsumption
                            } else {
                                PruningKind::Coverage
                            },
                            head: original.atoms[head].clone(),
                            rules: rs,
                            removed,
                            removed_literals: 0,
                            literal: None,
                            structural: false,
                            scope_heads,
                            scope,
                            pins: vec![],
                            omitted_pins: 0,
                        },
                    );
                    report.removed += removed;
                    if let Some(r) = candidate {
                        enabled[r] = false;
                        item.remaining.retain(|q| *q != r);
                    } else {
                        for r in &item.remaining {
                            enabled[*r] = false;
                        }
                        result.fixed[head] = Some(true);
                        report.covered += 1;
                        item.candidates.clear();
                    }
                }
                let gate = run.cnf.var(run.budget)?;
                if let Some(old) = current[head] {
                    live_gates[old] = false;
                }
                current[head] = Some(gates.len());
                gates.push(gate);
                live_gates.push(true);
                let rhs = match attempt {
                    Attempt::Coverage => run.truth,
                    Attempt::Producer(_) => union,
                    Attempt::Literal(_, _) => logic.or(
                        &item
                            .remaining
                            .iter()
                            .map(|r| bodies[*r])
                            .collect::<Vec<_>>(),
                        &mut run.cnf,
                        run.budget,
                    )?,
                };
                equation(&mut run, gate, vars[head], rhs)?;
            }
            report.components[row].elapsed += start.elapsed();
            // Publish the completed attempt too, including a local cutoff.
            drop(_progress);
            let _progress =
                engine
                    .limits
                    .progress
                    .sampled("completion targeted pruning", true, || {
                        crate::CheckingTarget::CompletionPruning(report.components[row].clone())
                    });
            item.coverage = false;
            if !item.candidates.is_empty() || !item.literals.is_empty() {
                if priority.contains(&head) {
                    preferred.push_back(item);
                } else {
                    pending.push_back(item);
                }
            }
        }
        Ok(())
    })();
    // Pin construction and replacement encoding can also exhaust. Attribute
    // those to the current component, not only failures inside raw_solve.
    if let (Err(error), Some(row)) = (&outcome, current_row) {
        if let Ok(cause) = inconclusive(error.clone()) {
            report.components[row].cutoff = Some(cause);
        }
    }
    add_query(used, run.usage());
    install_result(&working, result, &enabled);
    outcome
}
fn retain(report: &mut PruningReport, record: PruningRecord) {
    if report.records.len() < 64 {
        report.records.push(record);
    } else {
        report.omitted += 1;
    }
}
fn install_result(original: &Cone, result: &mut Cone, enabled: &[bool]) {
    result.rules = original
        .rules
        .iter()
        .zip(enabled)
        .filter(|(_, on)| **on)
        .map(|(r, _)| r.clone())
        .collect();
}
fn equation(run: &mut queries::Run<'_, '_, '_>, gate: Lit, head: Lit, body: Lit) -> Result<()> {
    run.cnf.gate = Some(gate);
    run.cnf.clause(vec![!head, body], run.budget)?;
    run.cnf.clause(vec![head, !body], run.budget)?;
    run.cnf.gate = None;
    Ok(())
}

#[cfg(test)]
mod reservation_tests {
    use super::*;
    #[test]
    fn leftover_is_released_once_only_after_unstarted_roots_have_priority() {
        let cw = ("classification", PruningContext::World);
        let ch = ("classification", PruningContext::Hypothesis);
        let pw = ("processing", PruningContext::World);
        let ph = ("processing", PruningContext::Hypothesis);
        let mut r = Reservations::new(Duration::from_secs(40), true, false);
        r.start(cw);
        assert_eq!(
            r.finish(cw, Duration::from_secs(1), PruningStop::Saturated),
            Duration::from_secs(9)
        );
        assert_eq!(r.leftover, Duration::ZERO);
        assert_eq!(r.start(ch), Duration::from_secs(13));
        assert_eq!(r.start(pw), Duration::from_secs(13));
        assert_eq!(r.start(ph), Duration::from_secs(13));
        r.finish(ph, Duration::from_secs(2), PruningStop::Saturated);
        assert_eq!(std::mem::take(&mut r.leftover), Duration::from_secs(11));
        r.finish(ph, Duration::ZERO, PruningStop::Saturated);
        assert_eq!(r.leftover, Duration::ZERO);
    }
    #[test]
    fn only_saturation_releases_time_fairly_to_unstarted_views() {
        let cw = ("classification", PruningContext::World);
        let ch = ("classification", PruningContext::Hypothesis);
        let pw = ("processing", PruningContext::World);
        let ph = ("processing", PruningContext::Hypothesis);
        let secs = Duration::from_secs;
        for stop in [PruningStop::CandidateCutoff, PruningStop::OverallCutoff] {
            let mut r = Reservations::new(secs(40), true, false);
            assert_eq!(r.start(cw), secs(10));
            assert_eq!(r.finish(cw, secs(1), stop), Duration::ZERO);
            assert_eq!(r.start(pw), secs(10));
            assert_eq!(r.start(ph), secs(10));
        }
        let mut r = Reservations::new(secs(40), true, false);
        assert_eq!(r.start(cw), secs(10));
        // Starting a later view cannot borrow from a view still running.
        assert_eq!(r.start(ch), secs(10));
        assert_eq!(r.finish(cw, secs(2), PruningStop::Saturated), secs(8));
        assert_eq!(r.slots[&ch].allowance, secs(10));
        assert_eq!(r.start(pw), secs(14));
        // A cutoff does not surrender its unused remainder to H.
        assert_eq!(
            r.finish(pw, secs(4), PruningStop::CandidateCutoff),
            Duration::ZERO
        );
        assert_eq!(r.start(ph), secs(14));
        assert_eq!(
            r.finish(cw, Duration::ZERO, PruningStop::Saturated),
            Duration::ZERO
        );
        assert_eq!(
            r.slots.values().map(|s| s.allowance).sum::<Duration>(),
            secs(40)
        );
    }
    #[test]
    fn property_saturation_preserves_other_property_cones_reservation() {
        let mut r = Reservations::new(Duration::from_secs(60), true, true);
        let property = ("property", PruningContext::World);
        assert_eq!(r.start(property), Duration::from_secs(10));
        assert_eq!(
            r.finish(property, Duration::from_secs(1), PruningStop::Saturated),
            Duration::ZERO
        );
        assert_eq!(r.start(property), Duration::from_secs(9));
        assert_eq!(
            r.start(("processing", PruningContext::World)),
            Duration::from_secs(10)
        );
    }
    #[test]
    fn classification_success_hints_survive_the_diagnostic_cap_and_are_reproved() {
        use crate::sat_probe::completion_query::tests::{prepare, verification};
        use crate::test_support::rewrites::{rel, rule};
        let mut c = Corpus::new();
        let h = rel(&mut c, "recognized", false);
        let extra = rel(&mut c, "extra", false);
        rule(&mut c, extra, &[(extra, false)]);
        rule(&mut c, extra, &[(extra, true)]);
        let mut heads = Vec::new();
        for index in 0..70 {
            let i = rel(&mut c, &format!("input{index}"), true);
            let p = rel(&mut c, &format!("accepted{index}"), false);
            let q = rel(&mut c, &format!("profile{index}"), false);
            rule(&mut c, p, &[(i, false)]);
            rule(&mut c, p, &[(q, false)]);
            rule(&mut c, q, &[(i, false), (p, true)]);
            heads.push((p, false));
        }
        rule(&mut c, h, &heads);
        // Extra keeps processing a different original scope: fresh proofs required.
        let v = verification(&mut c, Some(h), &[]);
        let mut e = prepare(&c, v, &Default::default());
        e.config.max_solves = 2048; // exceed the diagnostic cap, not a scale policy test
        e.pruning = Some(Arc::new(std::sync::Mutex::new(Cache::for_engine(&e))));
        view(
            &e,
            &e.classification.as_ref().unwrap().0,
            false,
            e.limits.timeout,
        )
        .unwrap();
        {
            let cache = e.pruning.as_ref().unwrap().lock().unwrap();
            assert_eq!(cache.classification_successes.len(), 70);
            assert!(cache.report.omitted > 0);
            assert_eq!(cache.report.views[0].stop, PruningStop::Saturated);
            assert!(cache.report.views[0].released > Duration::ZERO);
        }
        let attempts = Arc::new(std::sync::Mutex::new(Vec::new()));
        let observed = attempts.clone();
        e.limits.progress = crate::CheckingProgress::new(move |event| {
            if let Some(crate::CheckingTarget::CompletionPruning(row)) = event.target {
                if row.scope == "processing" && row.considered > 0 {
                    if let Some(head) = row.last_head {
                        observed.lock().unwrap().push(head);
                    }
                }
            }
        });
        view(&e, &e.cone, false, e.limits.timeout).unwrap();
        let cache = e.pruning.as_ref().unwrap().lock().unwrap();
        let processing = cache.report.views.last().unwrap();
        assert_eq!(processing.scope, "processing");
        let first = attempts.lock().unwrap()[0].clone();
        assert!(
            cache
                .classification_successes
                .iter()
                .any(|i| e.cone.atoms[*i] == first)
        );
        assert_eq!(processing.priority_proved, 70);
        assert!(processing.priority_attempts > processing.priority_proved);
    }
    #[test]
    fn priority_hints_never_authorize_a_rewrite() {
        use crate::sat_probe::completion_query::tests::{prepare, verification};
        use crate::test_support::rewrites::{rel, rule};
        let mut c = Corpus::new();
        let p = rel(&mut c, "contradiction", false);
        rule(&mut c, p, &[(p, true)]);
        let v = verification(&mut c, None, &[]);
        let mut e = prepare(&c, v, &Default::default());
        let mut cache = Cache::for_engine(&e);
        cache.classification_successes.extend(0..e.cone.atoms.len());
        e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
        let result = view(&e, &e.cone, false, e.limits.timeout).unwrap();
        assert!(*result.rules == *e.cone.rules);
        assert!(result.fixed == e.cone.fixed);
        let cache = e.pruning.as_ref().unwrap().lock().unwrap();
        assert!(cache.report.views[0].priority_attempts > 0);
        assert_eq!(cache.report.views[0].priority_proved, 0);
    }
    #[test]
    fn discovery_setup_cutoff_is_not_reported_as_overall_exhaustion() {
        let mut c = Corpus::new();
        use crate::test_support::rewrites::{rel, rule};
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        rule(&mut c, p, &[(q, true)]);
        rule(&mut c, q, &[(p, false)]);
        let v = crate::sat_probe::completion_query::tests::verification(&mut c, None, &[]);
        let base = crate::sat_probe::completion_query::tests::prepare(&c, v, &Default::default());
        let mut saw_local_cutoff = false;
        for work in (20..500).step_by(10) {
            let mut e = base.clone();
            e.limits.max_work = work;
            e.pruning = Some(Arc::new(std::sync::Mutex::new(Cache::for_engine(&e))));
            view(&e, &e.cone, false, e.limits.timeout).unwrap();
            let cache = e.pruning.as_ref().unwrap().lock().unwrap();
            if cache.report.components.is_empty()
                && cache.report.views[0].stop == PruningStop::CandidateCutoff
            {
                assert!(!cache.report.incomplete.is_empty());
                saw_local_cutoff = true;
            }
        }
        assert!(
            saw_local_cutoff,
            "the sweep exercises discovery before any component record exists"
        );
    }
    #[test]
    fn unresolved_discovery_is_a_candidate_cutoff_not_saturation() {
        let mut c = Corpus::new();
        use crate::test_support::rewrites::{rel, rule};
        let p = rel(&mut c, "p", false);
        rule(&mut c, p, &[(p, false)]);
        let v = crate::sat_probe::completion_query::tests::verification(&mut c, None, &[]);
        let mut e = crate::sat_probe::completion_query::tests::prepare(&c, v, &Default::default());
        e.config.max_solves = 0; // the local uniqueness question cannot finish
        e.pruning = Some(Arc::new(std::sync::Mutex::new(Cache::for_engine(&e))));
        view(&e, &e.cone, false, e.limits.timeout).unwrap();
        let cache = e.pruning.as_ref().unwrap().lock().unwrap();
        assert_eq!(cache.report.views[0].stop, PruningStop::CandidateCutoff);
        assert!(cache.report.records.is_empty());
    }
    #[test]
    fn w_spending_cannot_consume_the_h_reservation() {
        let mut c = Corpus::new();
        use crate::test_support::rewrites::{rel, rule};
        let i = rel(&mut c, "i", true);
        let h = rel(&mut c, "h", false);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        rule(&mut c, p, &[(i, false)]);
        rule(&mut c, p, &[(q, false)]);
        rule(&mut c, q, &[(p, true)]);
        rule(&mut c, h, &[(i, false), (p, false)]);
        let v = crate::sat_probe::completion_query::tests::verification(&mut c, Some(h), &[]);
        let mut e = crate::sat_probe::completion_query::tests::prepare(&c, v, &Default::default());
        let mut cache = Cache::for_engine(&e);
        // A completed W pass used its entire reservation. H must still run.
        let slot = cache
            .reservations
            .slots
            .get_mut(&("classification", PruningContext::World))
            .unwrap();
        slot.spent = slot.allowance;
        e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
        let cone = &*e.classification.as_ref().unwrap().0;
        let w = view(&e, cone, false, e.limits.timeout).unwrap();
        let h = view(&e, cone, true, e.limits.timeout).unwrap();
        assert!(*w.rules == *cone.rules);
        assert!(h.rules.len() < w.rules.len() || h.fixed != w.fixed);
        let cache = e.pruning.as_ref().unwrap().lock().unwrap();
        assert!(
            cache
                .report
                .records
                .iter()
                .any(|r| r.context == PruningContext::Hypothesis)
        );
        assert!(
            cache.classification_successes.is_empty(),
            "H-only proofs are not W hints"
        );
    }
}
