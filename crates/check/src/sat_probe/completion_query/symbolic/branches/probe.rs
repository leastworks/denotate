//! A bounded unsplit attempt before the structural driver: the ordinary search,
//! cover loops and lifting included, under a deterministic work cap. Work includes
//! SAT callback polls, so one difficult solve cannot consume the whole invocation.
//! Only an exhausted cap hands the question to the structural driver; it never
//! counts as a proof, and the consumed work stays charged.
use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

pub(super) fn run<T>(
    e: &Engine,
    options: &CheckOptions,
    budget: &mut Budget<'_>,
    remaining: &mut QueryLimits,
    id: usize,
    depth: usize,
    leaf: &impl Fn(&Engine, &CheckOptions) -> Result<Search<T>>,
) -> Result<Option<Search<T>>> {
    let phase = "completion unsplit probe";
    if e.limits.completion_probe_work == 0 {
        e.exploration(phase, "not-started-disabled", 0, Duration::ZERO);
        return Ok(None);
    }
    let started = Instant::now();
    let mut probe = e.clone();
    probe.probe = true;
    probe.limits.max_work = budget.remaining().min(e.limits.completion_probe_work);
    probe.limits.timeout = budget.remaining_time();
    probe.config = remaining.clone();
    probe.config.max_solver_polls = probe.config.max_solver_polls.min(probe.limits.max_work);
    let work = Arc::new(AtomicUsize::new(0));
    let usage = Arc::new(std::sync::Mutex::new(QueryLimits {
        max_solves: 0,
        max_solver_polls: 0,
        max_conflicts: 0,
        max_propagations: 0,
    }));
    probe.exploration_work = Some(work.clone());
    probe.exploration_usage = Some(usage.clone());
    // Reuse only existing context-correct views; the probe never initiates SAT
    // pruning, forcing or ranking. Search-free Fitting remains charged work.
    if let Some(cache) = &e.pruning {
        let cache = cache.lock().unwrap();
        probe.pruning = Some(Arc::new(std::sync::Mutex::new(cache.frozen())));
    }
    let mut opts = options.clone();
    opts.split_depth = 0;
    opts.force = false;
    e.limits.progress.exploration(
        phase,
        "started",
        "work-limit",
        probe.limits.max_work,
        Duration::ZERO,
    );
    let result = leaf(&probe, &opts);
    let used = usage.lock().unwrap();
    remaining.max_solves = remaining.max_solves.saturating_sub(used.max_solves);
    remaining.max_solver_polls = remaining
        .max_solver_polls
        .saturating_sub(used.max_solver_polls);
    remaining.max_conflicts = remaining.max_conflicts.saturating_sub(used.max_conflicts);
    remaining.max_propagations = remaining
        .max_propagations
        .saturating_sub(used.max_propagations);
    if let Some(total) = &e.exploration_usage {
        let mut total = total.lock().unwrap();
        total.max_solves = total.max_solves.saturating_add(used.max_solves);
        total.max_solver_polls = total.max_solver_polls.saturating_add(used.max_solver_polls);
        total.max_conflicts = total.max_conflicts.saturating_add(used.max_conflicts);
        total.max_propagations = total.max_propagations.saturating_add(used.max_propagations);
    }
    let work = work.load(Ordering::Relaxed);
    let complete = matches!(&result, Ok(Search::None | Search::Exists(_)));
    let cutoff = match &result {
        Ok(Search::Inconclusive(c)) => Some(*c),
        _ => None,
    };
    let record = BranchRecord {
        id,
        depth,
        phase,
        state: if complete { "completed" } else { "cut-off" },
        search_work: work,
        work,
        elapsed: started.elapsed(),
        cutoff,
        split_kind: "none",
        ..Default::default()
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
    e.exploration(
        phase,
        if complete { "completed" } else { "cut-off" },
        work,
        started.elapsed(),
    );
    budget.charge(work, phase)?;
    match result? {
        answer @ (Search::None | Search::Exists(_)) => Ok(Some(answer)),
        Search::Inconclusive(_) => Ok(None),
        Search::NotAnalysed => Err(CheckError::Internal("unanalysed exploration probe")),
    }
}
