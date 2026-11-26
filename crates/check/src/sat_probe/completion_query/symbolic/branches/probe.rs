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
    remaining: &QueryLimits,
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
    // The probe's own scope, inside the question's: its solves debit both.
    let mut probe = e.sub_scope(remaining.clone());
    probe.probe = true;
    probe.limits.max_work = budget.remaining().min(e.limits.completion_probe_work);
    probe.limits.timeout = budget.remaining_time();
    let work = Arc::new(AtomicUsize::new(0));
    probe.exploration_work = Some(work.clone());
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
