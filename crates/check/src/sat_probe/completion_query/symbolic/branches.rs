//! Invocation-local input partitions. Units share only immutable preparation;
//! their equations, solver, work allowance and results belong to that branch.
use super::*;
mod fitting;
mod forcing;
pub use forcing::ForcingRecord;
mod groups;
mod probe;
mod ranking;
use groups::{Choice, Group};
use ranking::choose;

#[derive(Debug, Clone)]
pub struct SplitAlternative {
    pub split: GroundAtom,
    pub assumption: Option<denotate_ir::AssumptionId>,
    pub children: usize,
    pub guarded_edges: usize,
    pub has_rest: bool,
}
/// A bounded candidate inventory, including untried candidates. Counts are
/// actual live-edge deletions in tentative Fitting children, not influence.
#[derive(Debug, Clone)]
pub struct SplitCandidate {
    pub split: GroundAtom,
    pub assumption: Option<denotate_ir::AssumptionId>,
    pub context: &'static str,
    pub state: &'static str,
    pub children: usize,
    pub guarded_edges: usize,
    pub checked_children: usize,
    pub disabled_edges: usize,
    pub minimum_disabled: usize,
    pub cycles_cut_every_child: usize,
    pub selected: bool,
    pub cutoff: Option<Inconclusive>,
    pub pruning_attempts: usize,
    pub pruning_proved: usize,
    pub derived_guards: Vec<DerivedGuard>,
    pub child_trials: Vec<SplitChild>,
    pub formula: bool,
    pub omitted_derived_guards: usize,
    pub derived_guards_complete: bool,
}
/// Every attempted child has its own outcome; guard sampling shares one cap.
#[derive(Debug, Clone)]
pub struct SplitChild {
    pub forcing: Vec<ForcingRecord>,
    pub child: usize,
    pub context: &'static str,
    pub rest: bool,
    pub pruning_attempts: usize,
    pub pruning_proved: usize,
    pub removed_producers: usize,
    pub removed_producer_examples: Vec<PrunedProducer>,
    pub omitted_producer_examples: usize,
    pub removed_literals: usize,
    pub pruned_heads: Vec<GroundAtom>,
    pub omitted_pruned_heads: usize,
    pub target_atoms: usize,
    pub settled_target_atoms: usize,
    pub disabled_edges: usize,
    /// Witness cycles cut in this child; not a verdict for the residual question.
    pub cycles_cut: usize,
    pub complete: bool,
    pub cutoff: Option<Inconclusive>,
    pub omitted_derived_guards: usize,
    pub derived_guards_complete: bool,
}
/// Bounded original ground bodies identify which self-admitting producer a
/// trial removed, even when the trial is discarded and publishes no finding.
#[derive(Debug, Clone)]
pub struct PrunedProducer {
    pub context: &'static str,
    pub head: GroundAtom,
    pub original_body: Vec<(GroundAtom, bool)>,
    pub omitted_body_literals: usize,
}
#[derive(Debug, Clone)]
pub struct DerivedGuard {
    pub atom: GroundAtom,
    pub child: usize,
    pub acyclic_upstream: bool,
}
#[derive(Debug, Clone, Default)]
pub struct BranchRecord {
    pub forcing: Vec<ForcingRecord>,
    pub id: usize,
    pub parent: Option<usize>,
    pub closed_children: usize,
    pub phase: &'static str,
    pub depth: usize,
    pub state: &'static str,
    pub pins: Vec<(GroundAtom, bool)>,
    pub omitted_pins: usize,
    pub split: Option<GroundAtom>,
    pub runner_up: Option<SplitAlternative>,
    pub candidates: Vec<SplitCandidate>,
    pub omitted_candidates: usize,
    pub children: usize,
    pub split_kind: &'static str,
    pub assumption: Option<denotate_ir::AssumptionId>,
    pub values: Vec<GroundAtom>,
    pub omitted_values: usize,
    pub mapping: Vec<(GroundAtom, GroundAtom)>,
    pub omitted_mapping: usize,
    pub has_rest: bool,
    pub rest: bool,
    pub preparation_work: usize,
    pub search_work: usize,
    /// Structural guard-edge histogram score, not a proof of edge deletion.
    pub guarded_edges: usize,
    pub work: usize,
    pub elapsed: Duration,
    pub cutoff: Option<Inconclusive>,
}
#[derive(Debug, Clone, Default)]
pub struct BranchReport {
    pub enabled: bool,
    pub splits: usize,
    pub leaves: usize,
    pub pending_units: usize,
    pub records: Vec<BranchRecord>,
    pub omitted_records: usize,
}
impl BranchReport {
    fn record(&mut self, e: &Engine, record: BranchRecord) {
        e.limits.progress.completion_branch(&record);
        if self.records.len() < 256 {
            self.records.push(record);
        } else {
            self.omitted_records += 1;
        }
    }
}

struct Unit {
    id: usize,
    parent_id: Option<usize>,
    parent: Option<Arc<fitting::Bundle>>,
    prepared: Option<Arc<fitting::Bundle>>,
    delta: Vec<(usize, bool)>,
    formula: Option<Arc<branch_formula::SettledAtom>>,
    rest: bool,
    pins: BTreeMap<GroundAtom, bool>,
    depth: usize,
    work: usize,
    config: QueryLimits,
    worlds: usize,
    residual_only: Option<Vec<Arc<BTreeSet<usize>>>>,
}
fn divided(q: &QueryLimits, n: usize) -> QueryLimits {
    QueryLimits {
        max_solves: q.max_solves / n,
        max_solver_polls: q.max_solver_polls / n,
        max_conflicts: q.max_conflicts / n as u64,
        max_propagations: q.max_propagations / n as u64,
    }
}

/// Automatic guards survive partitioning; explicitly configured caps have no
/// floor and keep the existing conservative division. No deadline is restarted.
fn guards(e: &mut Engine, options: &mut CheckOptions) {
    if e.limits.completion_exploration {
        return;
    }
    if let Some(g) = &e.limits.search_guards {
        if let Some(v) = g.work {
            e.limits.max_work = e.limits.max_work.max(v);
        }
        if let Some(v) = g.solves {
            e.config.max_solves = e.config.max_solves.max(v);
        }
        if let Some(v) = g.polls {
            e.config.max_solver_polls = e.config.max_solver_polls.max(v);
        }
        if let Some(v) = g.conflicts {
            e.config.max_conflicts = e.config.max_conflicts.max(v);
        }
        if let Some(v) = g.propagations {
            e.config.max_propagations = e.config.max_propagations.max(v);
        }
        if let Some(v) = g.worlds {
            options.max_worlds = options.max_worlds.max(v);
        }
    }
}
struct Root {
    state: Arc<fitting::Bundle>,
    choice: (Choice, Option<Choice>),
    candidates: Vec<SplitCandidate>,
    omitted: usize,
}

/// Rank once, then try the whole question. Only a verified useful partition
/// reserves a second attempt. Explicit logical allowances are never reset.
pub(in crate::sat_probe::completion_query) fn run<T>(
    e: &Engine,
    classification: bool,
    existence: bool,
    options: &CheckOptions,
    shares: usize,
    leaf: impl Fn(&Engine, &CheckOptions) -> Result<Search<T>>,
) -> Result<Search<T>> {
    if options.split_depth == 0 {
        return leaf(e, options);
    }
    if e.limits.completion_exploration {
        e.exploration(
            "completion unsplit attempt",
            "not-started-unbounded",
            0,
            Duration::ZERO,
        );
        return partition_from(e, classification, existence, options, shares, None, leaf);
    }
    // Only classification existence changes ordinary scheduling: its cover
    // follows structural cuts. Processing keeps the established first attempt,
    // so a cheap proof is not delayed by forcing or partitioning.
    if classification && existence {
        return partition_from(e, classification, existence, options, shares, None, leaf);
    }
    pruning::prepare(e, classification)?;
    let mut limits = e.shared_limits(shares);
    if let Err(error) = Budget::new(&limits).check("completion unsplit attempt") {
        return Ok(Search::Inconclusive(inconclusive(error)?));
    }
    let started = Instant::now();
    let end = started + limits.timeout;
    let end = limits.run_deadline.map_or(end, |d| d.min(end));
    // Ranking is optional exploration. Keep time for the actual question even
    // when preparing a shortlist or a local uniqueness trial is expensive.
    let mut ranking_limits = limits.clone();
    ranking_limits.timeout /= 4;
    if let Some(cache) = &e.pruning {
        if let Some(pool) = &cache.lock().unwrap().trials {
            // Even donated time must leave at least half this question for
            // its unsplit/residual search. Unused credit stays in the ledger.
            let extra = pool.lock().unwrap().take_released(ranking_limits.timeout);
            ranking_limits.timeout += extra;
        }
    }
    ranking_limits.max_work /= 4;
    let mut budget = Budget::new(&ranking_limits);
    let mut config = e.config.clone();
    let mut candidates = vec![];
    let mut omitted = 0;
    let ranked: Result<_> = (|| {
        // Preserve the established unsplit attempt. Forcing belongs to the
        // already-funded child trials and to residual branch units, not a new
        // root preflight pass that takes time from the first SAT search.
        let state = Arc::new(fitting::Bundle::new(e, &mut budget)?);
        if options.split_depth == 0 {
            return Ok(None);
        }
        let choice = choose(
            e,
            &state,
            classification,
            existence,
            options.split_branches,
            &mut config,
            &mut candidates,
            &mut omitted,
            &mut budget,
        )?;
        Ok(choice.map(|choice| Root {
            state,
            choice,
            candidates: candidates.clone(),
            omitted,
        }))
    })();
    let root = match ranked {
        Ok(root) => root,
        Err(error) => {
            e.limits.cancellation.check()?;
            inconclusive(error)?; // only optional resource cutoffs are recoverable
            None
        }
    };
    limits.max_work = limits.max_work.saturating_sub(budget.used());
    limits.timeout = end.saturating_duration_since(Instant::now());
    let ranking_work = budget.used();
    let divisor = if root.is_some() { 2 } else { 1 };
    let mut first = e.clone();
    first.limits = limits.clone();
    first.limits.timeout /= divisor;
    first.limits.run_deadline = Some(end.min(Instant::now() + first.limits.timeout));
    first.limits.max_work /= divisor as usize;
    first.config = divided(&config, divisor as usize);
    let sink = crate::CompletionSizes::default();
    first.limits.completion_sizes = Some(sink.clone());
    let mut opts = options.clone();
    opts.split_depth = 0;
    opts.max_worlds /= divisor as usize;
    guards(&mut first, &mut opts);
    let phase = question_phase(e, classification, existence);
    let progress = e
        .limits
        .progress
        .scope("completion unsplit attempt", None, true);
    let result = leaf(&first, &opts)?;
    let searches = sink.snapshot();
    let work = searches
        .searches
        .iter()
        .filter(|s| s.phase == phase)
        .map(|s| s.work.unwrap_or(0))
        .sum();
    let (state, cutoff) = match &result {
        Search::Exists(_) => ("unsplit-counterexample", None),
        Search::None => ("unsplit-proved", None),
        Search::Inconclusive(c) => ("unsplit-inconclusive", Some(*c)),
        Search::NotAnalysed => return Err(CheckError::Internal("unanalysed unsplit attempt")),
    };
    let record = BranchRecord {
        forcing: vec![],
        id: 0,
        parent: None,
        closed_children: 0,
        phase,
        depth: 0,
        state,
        pins: vec![],
        omitted_pins: 0,
        split: None,
        runner_up: None,
        candidates,
        omitted_candidates: omitted,
        children: 0,
        split_kind: "none",
        assumption: None,
        values: vec![],
        omitted_values: 0,
        mapping: vec![],
        omitted_mapping: 0,
        has_rest: false,
        rest: false,
        preparation_work: ranking_work,
        search_work: work,
        guarded_edges: 0,
        work: work.saturating_add(ranking_work),
        elapsed: started.elapsed(),
        cutoff,
    };
    e.limits.progress.completion_branch(&record);
    if let Some(sink) = &e.branches {
        let mut report = sink.lock().unwrap();
        if report.records.len() < 256 {
            report.records.push(record);
        } else {
            report.omitted_records += 1;
        }
    }
    if let Some(out) = &e.limits.completion_sizes {
        for search in searches.searches {
            out.search(search);
        }
    }
    drop(progress);
    if root.is_none() || !matches!(result, Search::Inconclusive(_)) {
        return Ok(result);
    }
    let mut rest = e.clone();
    rest.limits = limits;
    rest.limits.timeout = end.saturating_duration_since(Instant::now());
    rest.limits.run_deadline = Some(end);
    rest.limits.max_work = rest.limits.max_work.saturating_sub(first.limits.max_work);
    rest.config = QueryLimits {
        max_solves: config.max_solves.saturating_sub(first.config.max_solves),
        max_solver_polls: config
            .max_solver_polls
            .saturating_sub(first.config.max_solver_polls),
        max_conflicts: config
            .max_conflicts
            .saturating_sub(first.config.max_conflicts),
        max_propagations: config
            .max_propagations
            .saturating_sub(first.config.max_propagations),
    };
    opts = options.clone();
    opts.max_worlds -= options.max_worlds / 2;
    guards(&mut rest, &mut opts);
    partition_from(&rest, classification, existence, &opts, 1, root, leaf)
}
fn question_phase(e: &Engine, classification: bool, existence: bool) -> &'static str {
    if let Some(phase) = e.branch_phase {
        return phase;
    }
    match (classification, existence) {
        (true, true) => "completion classification existence",
        (true, false) => "completion classification ambiguity",
        (false, true) => "completion processing existence",
        (false, false) => "completion processing ambiguity",
    }
}

#[cfg(test)]
pub(in crate::sat_probe::completion_query) fn partition<T>(
    e: &Engine,
    classification: bool,
    existence: bool,
    options: &CheckOptions,
    shares: usize,
    leaf: impl Fn(&Engine, &CheckOptions) -> Result<Search<T>>,
) -> Result<Search<T>> {
    partition_from(e, classification, existence, options, shares, None, leaf)
}
fn partition_from<T>(
    e: &Engine,
    classification: bool,
    existence: bool,
    options: &CheckOptions,
    shares: usize,
    mut root: Option<Root>,
    leaf: impl Fn(&Engine, &CheckOptions) -> Result<Search<T>>,
) -> Result<Search<T>> {
    if options.split_depth == 0 {
        return leaf(e, options);
    }
    let phase = question_phase(e, classification, existence);
    let limits = e.shared_limits(shares);
    let local_deadline = Instant::now() + limits.timeout;
    let deadline = limits
        .run_deadline
        .map_or(local_deadline, |d| d.min(local_deadline));
    // Prepare both contexts before freezing the branch bundle. H views extend
    // W; leaves select the right view per solver question, including no-H fallbacks.
    if e.pruning.is_some() {
        let mut parent = e.clone();
        parent.limits.run_deadline = Some(deadline);
        let cone = if classification {
            &*e.classification.as_ref().unwrap().0
        } else {
            &*e.cone
        };
        pruning::view(
            &parent,
            cone,
            e.classification.is_some(),
            deadline.saturating_duration_since(Instant::now()),
        )?;
    }
    let mut queue = std::collections::VecDeque::from([Unit {
        id: 1,
        parent_id: None,
        parent: None,
        prepared: None,
        delta: vec![],
        formula: None,
        rest: false,
        pins: BTreeMap::new(),
        depth: 0,
        work: limits.max_work,
        config: e.config.clone(),
        worlds: options.max_worlds,
        residual_only: None,
    }]);
    let mut report = BranchReport::default();
    let usage = e.limits.completion_exploration.then(|| {
        Arc::new(std::sync::Mutex::new(QueryLimits {
            max_solves: 0,
            max_solver_polls: 0,
            max_conflicts: 0,
            max_propagations: 0,
        }))
    });
    let mut remaining_work = limits.max_work;
    let mut next_id = 2;
    let mut unknown = None;
    let mut answer = None;
    while let Some(unit) = queue.pop_front() {
        e.limits.cancellation.check()?;
        if Instant::now() >= deadline {
            let cause = CheckError::deadline(phase, limits.timeout);
            e.limits.progress.failure(&cause);
            unknown.get_or_insert(inconclusive(cause)?);
            report.pending_units += queue.len() + 1;
            break;
        }
        let started = Instant::now();
        let mut record = BranchRecord {
            forcing: vec![],
            id: unit.id,
            parent: unit.parent_id,
            closed_children: 0,
            phase,
            depth: unit.depth,
            state: "preparing",
            pins: {
                let mut pins: Vec<_> = unit.pins.iter().collect();
                pins.sort_by_key(|(a, v)| (!**v, *a));
                pins.into_iter()
                    .take(32)
                    .map(|(a, v)| (a.clone(), *v))
                    .collect()
            },
            omitted_pins: unit.pins.len().saturating_sub(32),
            split: None,
            runner_up: None,
            candidates: vec![],
            omitted_candidates: 0,
            children: 0,
            split_kind: "none",
            assumption: None,
            values: vec![],
            omitted_values: 0,
            mapping: vec![],
            omitted_mapping: 0,
            has_rest: false,
            rest: unit.rest,
            preparation_work: 0,
            search_work: 0,
            guarded_edges: 0,
            work: 0,
            elapsed: Duration::ZERO,
            cutoff: None,
        };
        let _progress = e.limits.progress.scope(
            phase,
            Some(crate::CheckingTarget::CompletionBranch(record.clone())),
            true,
        );
        let sink = crate::CompletionSizes::default();
        let mut local_limits = limits.clone();
        local_limits.completion_sizes = Some(sink.clone());
        local_limits.timeout = deadline.saturating_duration_since(Instant::now())
            / e.limits.completion_share(queue.len() + 1) as u32;
        local_limits.max_work = if e.limits.completion_exploration {
            remaining_work.min(unit.work)
        } else {
            unit.work
        };
        local_limits.run_deadline = Some(deadline.min(Instant::now() + local_limits.timeout));
        let mut allocation = e.clone();
        allocation.limits = local_limits;
        allocation.config = unit.config.clone();
        allocation.exploration_usage = usage.clone();
        if let Some(usage) = &usage {
            let u = usage.lock().unwrap();
            allocation.config.max_solves = allocation
                .config
                .max_solves
                .min(e.config.max_solves.saturating_sub(u.max_solves));
            allocation.config.max_solver_polls = allocation
                .config
                .max_solver_polls
                .min(e.config.max_solver_polls.saturating_sub(u.max_solver_polls));
            allocation.config.max_conflicts = allocation
                .config
                .max_conflicts
                .min(e.config.max_conflicts.saturating_sub(u.max_conflicts));
            allocation.config.max_propagations = allocation
                .config
                .max_propagations
                .min(e.config.max_propagations.saturating_sub(u.max_propagations));
        }
        let mut allocated_options = options.clone();
        allocated_options.max_worlds = unit.worlds;
        guards(&mut allocation, &mut allocated_options);
        let leaf_work = e
            .limits
            .completion_exploration
            .then(|| Arc::new(std::sync::atomic::AtomicUsize::new(0)));
        allocation.exploration_work = leaf_work.clone();
        let unit_engine = e.limits.completion_exploration.then(|| allocation.clone());
        let e = unit_engine.as_ref().unwrap_or(e);
        let local_limits = allocation.limits;
        let mut budget = Budget::new(&local_limits);
        let mut config = allocation.config;
        let mut probe_answer = None;
        let result: Result<Option<Engine>> = (|| {
            if e.limits.completion_exploration && unit.parent.is_none() {
                probe_answer = probe::run(
                    e,
                    &allocated_options,
                    &mut budget,
                    &mut config,
                    unit.id,
                    unit.depth,
                    &leaf,
                )?;
                if probe_answer.is_some() {
                    return Ok(None);
                }
            }
            let preflight = if unit.parent.is_none() {
                root.take()
            } else {
                None
            };
            let state = if let Some(r) = &preflight {
                r.state.clone()
            } else if let Some(prepared) = &unit.prepared {
                prepared.clone()
            } else {
                Arc::new(match &unit.parent {
                    Some(parent) => parent.child_with_formula(
                        &unit.delta,
                        unit.formula.as_ref(),
                        &mut budget,
                    )?,
                    None => fitting::Bundle::new(e, &mut budget)?,
                })
            };
            if e.limits.completion_exploration && unit.parent.is_some() {
                let mut ready = state.engine(e, &mut budget)?;
                ready.branches = e.branches.clone();
                ready.config = config.clone();
                probe_answer = probe::run(
                    &ready,
                    &allocated_options,
                    &mut budget,
                    &mut config,
                    unit.id,
                    unit.depth,
                    &leaf,
                )?;
                if probe_answer.is_some() {
                    return Ok(None);
                }
            }
            let mut settled = (*state).clone();
            settled.settle(e, classification, &mut config, &mut budget)?;
            record.forcing = settled.forcing.clone();
            let state = Arc::new(settled);
            let mut branch = state.engine(e, &mut budget)?;
            branch.limits = local_limits.clone();
            branch.config = config.clone();
            let capacity = options
                .split_branches
                .saturating_sub(report.leaves + queue.len());
            if unit.depth < options.split_depth && capacity > 0 {
                let chosen = if let Some(r) = preflight.filter(|_| !e.forcing) {
                    record.candidates = r.candidates;
                    record.omitted_candidates = r.omitted;
                    Some(r.choice)
                } else {
                    // Optional ranking must leave this sibling time for its
                    // residual question, even when no further split is found.
                    let mut ranking_limits = local_limits.clone();
                    ranking_limits.max_work = budget.remaining() / e.limits.completion_share(4);
                    ranking_limits.timeout =
                        budget.remaining_time() / e.limits.completion_share(4) as u32;
                    let mut ranking = Budget::new(&ranking_limits);
                    let ranking_started = Instant::now();
                    e.exploration("completion split ranking", "started", 0, Duration::ZERO);
                    let answer = ranking::choose_in(
                        &branch,
                        &state,
                        classification,
                        existence,
                        capacity,
                        if e.limits.completion_exploration || (classification && existence) {
                            None
                        } else {
                            unit.residual_only.as_deref()
                        },
                        &mut config,
                        &mut record.candidates,
                        &mut record.omitted_candidates,
                        &mut ranking,
                    );
                    e.exploration(
                        "completion split ranking",
                        if answer.is_ok() && record.candidates.iter().all(|c| c.cutoff.is_none()) {
                            "completed"
                        } else {
                            "cut-off"
                        },
                        ranking.used(),
                        ranking_started.elapsed(),
                    );
                    budget.charge(ranking.used(), "completion child ranking")?;
                    match answer {
                        Ok(choice) => choice,
                        Err(error) => {
                            inconclusive(error)?;
                            None
                        }
                    }
                };
                if let Some((choice, runner_up)) = chosen {
                    let children = choice.children();
                    let n = children.len();
                    if n > 0 {
                        record.runner_up = runner_up.map(|r| SplitAlternative {
                            split: e.cone.atoms[r.selected[0]].clone(),
                            assumption: r.group.assumption,
                            children: r.child_count(),
                            guarded_edges: r.score,
                            has_rest: r.rest,
                        });
                        record.state = "split";
                        record.split = Some(e.cone.atoms[choice.selected[0]].clone());
                        record.children = n;
                        record.guarded_edges = choice.score;
                        record.split_kind = if choice.formula.is_some() {
                            "formula"
                        } else if choice.binary {
                            "binary"
                        } else if choice.group.exact {
                            "exactly-one"
                        } else {
                            "at-most-one"
                        };
                        record.assumption = choice.group.assumption;
                        record.values = choice
                            .selected
                            .iter()
                            .take(32)
                            .map(|i| e.cone.atoms[*i].clone())
                            .collect();
                        record.omitted_values = choice.selected.len().saturating_sub(32);
                        record.has_rest = choice.rest;
                        record.mapping = choice
                            .group
                            .mapping
                            .iter()
                            .take(32)
                            .map(|(a, i)| (e.cone.atoms[*a].clone(), e.cone.atoms[*i].clone()))
                            .collect();
                        record.omitted_mapping = choice.group.mapping.len().saturating_sub(32);
                        report.splits += 1;
                        for (child_index, (delta, rest)) in children.into_iter().enumerate() {
                            let mut pins = unit.pins.clone();
                            for (i, v) in &delta {
                                pins.insert(e.cone.atoms[*i].clone(), *v);
                            }
                            let id = next_id;
                            next_id += 1;
                            let prepared = choice.child_states.get(child_index).map(|s| {
                                let mut child = (**s).clone();
                                child.publish(e);
                                Arc::new(child)
                            });
                            queue.push_back(Unit {
                                id,
                                parent_id: Some(unit.id),
                                parent: Some(state.clone()),
                                prepared,
                                delta,
                                formula: choice.formula.clone(),
                                rest,
                                pins,
                                depth: unit.depth + 1,
                                work: unit.work.saturating_sub(budget.used())
                                    / e.limits.completion_share(n),
                                config: divided(&config, e.limits.completion_share(n)),
                                worlds: unit.worlds / e.limits.completion_share(n),
                                residual_only: Some(choice.residual_only(child_index)),
                            });
                        }
                        return Ok(None);
                    }
                }
            }
            Ok(Some(
                if unit.pins.is_empty() && !e.forcing && !e.limits.completion_exploration {
                    e.clone()
                } else {
                    branch
                },
            ))
        })();
        record.work = budget.used();
        record.preparation_work = budget.used();
        let result = if let Some(answer) = probe_answer {
            report.leaves += 1;
            Ok(answer)
        } else {
            match result {
                Ok(None) => {
                    remaining_work = remaining_work.saturating_sub(record.work);
                    forward(e, &sink, unit.depth);
                    record.elapsed = started.elapsed();
                    report.record(e, record);
                    continue;
                }
                Ok(Some(mut branch)) => {
                    report.leaves += 1;
                    branch.limits = local_limits.clone();
                    branch.limits.timeout = budget.remaining_time();
                    branch.limits.max_work = local_limits.max_work.saturating_sub(budget.used());
                    branch.config = config;
                    let mut opts = options.clone();
                    opts.split_depth = 0;
                    opts.max_worlds = allocated_options.max_worlds;
                    guards(&mut branch, &mut opts);
                    record.state = "searching";
                    let _progress = e.limits.progress.scope(
                        phase,
                        Some(crate::CheckingTarget::CompletionBranch(record.clone())),
                        true,
                    );
                    let value = leaf(&branch, &opts);
                    for search in sink.snapshot().searches {
                        if search.phase == phase {
                            record.search_work =
                                record.search_work.saturating_add(search.work.unwrap_or(0));
                            record.work = record.work.saturating_add(search.work.unwrap_or(0));
                        }
                    }
                    value
                }
                Err(error) => {
                    report.leaves += 1;
                    Ok(Search::Inconclusive(inconclusive(error)?))
                }
            }
        }?;
        remaining_work = remaining_work.saturating_sub(budget.used()).saturating_sub(
            leaf_work
                .as_ref()
                .map_or(0, |w| w.load(std::sync::atomic::Ordering::Relaxed)),
        );
        forward(e, &sink, unit.depth);
        record.elapsed = started.elapsed();
        match result {
            Search::Exists(value) => {
                record.state = "counterexample";
                answer = Some(Search::Exists(value));
            }
            Search::None => {
                record.state = "proved";
                if let Some(parent) = unit.parent_id {
                    if let Some(r) = report.records.iter_mut().find(|r| r.id == parent) {
                        r.closed_children += 1;
                    }
                }
            }
            Search::Inconclusive(cause) => {
                record.state = "inconclusive";
                record.cutoff = Some(cause);
                unknown.get_or_insert(cause);
            }
            Search::NotAnalysed => {
                return Err(CheckError::Internal("unanalysed completion branch"));
            }
        }
        report.record(e, record);
        if answer.is_some() {
            break;
        }
    }
    if let Some(sink) = &e.branches {
        let mut out = sink.lock().unwrap();
        out.splits += report.splits;
        out.leaves += report.leaves;
        out.pending_units += report.pending_units;
        out.omitted_records += report.omitted_records;
        for record in report.records {
            if out.records.len() < 256 {
                out.records.push(record);
            } else {
                out.omitted_records += 1;
            }
        }
    }
    Ok(answer.unwrap_or_else(|| unknown.map_or(Search::None, Search::Inconclusive)))
}

fn forward(e: &Engine, sink: &crate::CompletionSizes, depth: usize) {
    if let Some(out) = &e.limits.completion_sizes {
        for mut search in sink.snapshot().searches {
            search.branch_depth = Some(depth);
            out.search(search);
        }
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
pub(in crate::sat_probe::completion_query) fn test_partition(
    e: &Engine,
    classification: bool,
    existence: bool,
    options: &CheckOptions,
) -> Result<Search<()>> {
    fn erased<T>(s: Search<T>) -> Search<()> {
        match s {
            Search::Exists(_) => Search::Exists(()),
            Search::None => Search::None,
            Search::Inconclusive(c) => Search::Inconclusive(c),
            Search::NotAnalysed => Search::NotAnalysed,
        }
    }
    partition(e, classification, existence, options, 1, |b, o| {
        if existence {
            b.symbolic_no_meaning_in(&BTreeMap::new(), classification, false, o, 1)
                .map(erased)
        } else {
            b.symbolic_pair_in(&BTreeMap::new(), classification, false, o, 1)
                .map(erased)
        }
    })
}

#[cfg(test)]
mod pruning_tests;

#[cfg(test)]
mod formula_tests;

#[cfg(test)]
mod fairness_tests;
