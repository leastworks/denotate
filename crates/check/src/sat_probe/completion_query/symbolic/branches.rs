//! Invocation-local input partitions. Units share only immutable preparation;
//! their equations, solver, work allowance and results belong to that branch.
use super::*;

#[derive(Debug, Clone)]
pub struct BranchRecord {
    pub phase: &'static str,
    pub depth: usize,
    pub state: &'static str,
    pub pins: Vec<(GroundAtom, bool)>,
    pub omitted_pins: usize,
    pub split: Option<GroundAtom>,
    pub children: usize,
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

// Only authored input cardinalities and selected input-only exactly-one
// assumptions justify omitting the all-absent and multiple-present branches.
fn groups(e: &Engine, b: &mut Budget<'_>) -> Result<Vec<Vec<usize>>> {
    let mut groups = BTreeSet::new();
    for (kind, atoms) in &e.world.groups {
        b.charge(atoms.len() + 1, "completion split groups")?;
        if *kind == Cardinality::ExactlyOne && atoms.iter().all(|i| e.cone.input[*i]) {
            groups.insert(atoms.clone());
        }
    }
    for a in e.assumptions.iter() {
        if a.kind != Cardinality::ExactlyOne {
            continue;
        }
        for (_, atoms) in &a.groups {
            b.charge(atoms.len() + 1, "completion split groups")?;
            if atoms.iter().all(|i| e.cone.input[*i]) {
                groups.insert(atoms.clone());
            }
        }
    }
    Ok(groups.into_iter().collect())
}

/// Rank the same structural guard/input dependency shape as the odd-component
/// histogram. Scores are candidates; Fitting in each child determines actual cuts.
fn choose(
    e: &Engine,
    classification: bool,
    existence: bool,
    capacity: usize,
    remaining: &mut QueryLimits,
    b: &mut Budget<'_>,
) -> Result<Option<(Vec<usize>, usize)>> {
    let groups = groups(e, b)?;
    if groups.is_empty() {
        return Ok(None);
    }
    let c = if classification {
        &*e.classification.as_ref().unwrap().0
    } else {
        &*e.cone
    };
    let graph = consistency::analyse(c, None, b)?;
    let mut candidates: BTreeSet<_> = graph
        .conflicts
        .iter()
        .map(|(i, _, _)| graph.component[*i])
        .collect();
    if !existence {
        candidates.clear();
        let mut sets = BTreeMap::<usize, BTreeSet<usize>>::new();
        let mut producers = vec![Vec::new(); c.fixed.len()];
        let mut providers = vec![Vec::new(); c.fixed.len()];
        for (r, rule) in c.rules.iter().enumerate() {
            b.charge(rule.body.len() + 1, "completion split components")?;
            if c.fixed[rule.head].is_some()
                || rule
                    .body
                    .iter()
                    .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
            {
                continue;
            }
            producers[rule.head].push(r);
            providers[rule.head].extend(rule.body.iter().map(|(i, _)| *i));
            for (i, _) in &rule.body {
                if !c.input[*i]
                    && c.fixed[*i].is_none()
                    && graph.component[*i] == graph.component[rule.head]
                {
                    sets.entry(graph.component[*i])
                        .or_default()
                        .extend([*i, rule.head]);
                }
            }
        }
        let mut relevant = vec![false; c.fixed.len()];
        let mut pending = c
            .atoms
            .iter()
            .enumerate()
            .filter_map(|(i, a)| e.decision(a).then_some(i))
            .collect::<Vec<_>>();
        while let Some(i) = pending.pop() {
            if relevant[i] {
                continue;
            }
            relevant[i] = true;
            b.charge(providers[i].len() + 1, "completion split components")?;
            pending.extend(providers[i].iter().copied());
        }
        let mut run = queries::Run::local(e, b)?;
        run.label("completion branch local uniqueness");
        for (id, heads) in sets {
            if !heads.iter().any(|i| relevant[*i]) {
                continue;
            }
            let local = existence::component(c, &producers, &heads, run.budget)?;
            let (unique, _, _, _) = run.local_unique(&local, |_, _| {});
            if !unique? {
                candidates.insert(id);
            }
        }
        let used = run.usage();
        remaining.max_solves = remaining.max_solves.saturating_sub(used.max_solves);
        remaining.max_solver_polls = remaining
            .max_solver_polls
            .saturating_sub(used.max_solver_polls);
        remaining.max_conflicts = remaining.max_conflicts.saturating_sub(used.max_conflicts);
        remaining.max_propagations = remaining
            .max_propagations
            .saturating_sub(used.max_propagations);
    }
    if candidates.is_empty() {
        return Ok(None);
    }
    let mut readers = vec![Vec::new(); c.fixed.len()];
    let mut guard_edges = Vec::new();
    for r in &c.rules {
        b.charge(r.body.len() + 1, "completion split index")?;
        if c.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        for (i, _) in &r.body {
            if c.fixed[*i].is_none() {
                readers[*i].push(r.head);
            }
        }
        for (i, p) in &r.body {
            if c.input[*i]
                || c.fixed[*i].is_some()
                || graph.component[*i] != graph.component[r.head]
            {
                continue;
            }
            if !candidates.contains(&graph.component[*i]) {
                continue;
            }
            // The cyclic literal itself is not a guard for its own edge.
            let guards = r
                .body
                .iter()
                .filter_map(|(g, q)| ((*g, *q) != (*i, *p) && c.fixed[*g].is_none()).then_some(*g))
                .collect::<Vec<_>>();
            if !guards.is_empty() {
                guard_edges.push(((r.head, *i, *p), guards));
            }
        }
    }
    if guard_edges.is_empty() {
        return Ok(None);
    }
    let mut best = None;
    for group in groups {
        if group.iter().any(|i| e.cone.fixed[*i] == Some(true)) {
            continue;
        }
        let choices: Vec<_> = group
            .iter()
            .copied()
            .filter(|i| e.cone.fixed[*i].is_none())
            .collect();
        if choices.is_empty() || choices.len() > capacity {
            continue;
        }
        let mut reached = vec![false; c.fixed.len()];
        let mut pending = choices;
        while let Some(i) = pending.pop() {
            if reached[i] {
                continue;
            }
            reached[i] = true;
            b.charge(readers[i].len() + 1, "completion split histogram")?;
            pending.extend(readers[i].iter().copied());
        }
        let mut edges = BTreeSet::new();
        for (edge, guards) in &guard_edges {
            b.charge(guards.len() + 1, "completion split histogram")?;
            if guards.iter().any(|i| reached[*i]) {
                edges.insert(*edge);
            }
        }
        let score = edges.len();
        if score > 0 && best.as_ref().is_none_or(|(_, old)| score > *old) {
            best = Some((group, score));
        }
    }
    Ok(best)
}

fn specialize(e: &Engine, pins: &BTreeMap<GroundAtom, bool>, b: &mut Budget<'_>) -> Result<Engine> {
    b.check("completion branch preparation")?;
    let mut out = e.clone();
    // No branch can install a proof into another branch's pruning cache. Branch
    // rewrites would also need branch-tagged diagnostics, deferred from this stage.
    out.pruning = None;
    out.branches = None;
    let fold = |c: &Cone, b: &mut Budget<'_>| -> Result<Arc<Cone>> {
        let mut c = c.clone();
        for (a, v) in pins {
            c.fixed[e.program.atom_index[a]] = Some(*v);
        }
        c.fixed = encoding::fitting(&c, b)?;
        Ok(Arc::new(c))
    };
    out.cone = fold(&e.cone, b)?;
    out.world = fold(&e.world, b)?;
    out.classification = e
        .classification
        .as_ref()
        .map(|(c, m, h)| -> Result<_> { Ok((fold(c, b)?, m.clone(), *h)) })
        .transpose()?;
    Ok(out)
}

struct Unit {
    pins: BTreeMap<GroundAtom, bool>,
    depth: usize,
    work: usize,
    config: QueryLimits,
    worlds: usize,
}
fn divided(q: &QueryLimits, n: usize) -> QueryLimits {
    QueryLimits {
        max_solves: q.max_solves / n,
        max_solver_polls: q.max_solver_polls / n,
        max_conflicts: q.max_conflicts / n as u64,
        max_propagations: q.max_propagations / n as u64,
    }
}

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
    let phase = match (classification, existence) {
        (true, true) => "completion classification existence",
        (true, false) => "completion classification ambiguity",
        (false, true) => "completion processing existence",
        (false, false) => "completion processing ambiguity",
    };
    let limits = e.shared_limits(shares);
    let deadline = Instant::now() + limits.timeout;
    let mut queue = std::collections::VecDeque::from([Unit {
        pins: BTreeMap::new(),
        depth: 0,
        work: limits.max_work,
        config: e.config.clone(),
        worlds: options.max_worlds,
    }]);
    let mut report = BranchReport::default();
    let mut unknown = None;
    let mut answer = None;
    while let Some(unit) = queue.pop_front() {
        e.limits.cancellation.check()?;
        let started = Instant::now();
        let mut record = BranchRecord {
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
            children: 0,
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
        local_limits.timeout =
            deadline.saturating_duration_since(Instant::now()) / (queue.len() + 1) as u32;
        local_limits.max_work = unit.work;
        let mut budget = Budget::new(&local_limits);
        let mut config = unit.config.clone();
        let result: Result<Option<Engine>> = (|| {
            let mut branch = specialize(e, &unit.pins, &mut budget)?;
            branch.limits = local_limits.clone();
            branch.config = config.clone();
            let capacity = options
                .split_branches
                .saturating_sub(report.leaves + queue.len());
            if unit.depth < options.split_depth && capacity > 0 {
                if let Some((group, score)) = choose(
                    &branch,
                    classification,
                    existence,
                    capacity,
                    &mut config,
                    &mut budget,
                )? {
                    let choices: Vec<_> = group
                        .iter()
                        .copied()
                        .filter(|i| branch.cone.fixed[*i].is_none())
                        .collect();
                    let n = choices.len();
                    if n > 0 {
                        record.state = "split";
                        record.split = Some(e.cone.atoms[group[0]].clone());
                        record.children = n;
                        record.guarded_edges = score;
                        report.splits += 1;
                        for chosen in choices {
                            let mut pins = unit.pins.clone();
                            for i in &group {
                                pins.insert(e.cone.atoms[*i].clone(), *i == chosen);
                            }
                            queue.push_back(Unit {
                                pins,
                                depth: unit.depth + 1,
                                work: unit.work.saturating_sub(budget.used()) / n,
                                config: divided(&config, n),
                                worlds: unit.worlds / n,
                            });
                        }
                        return Ok(None);
                    }
                }
            }
            Ok(Some(if unit.pins.is_empty() {
                e.clone()
            } else {
                branch
            }))
        })();
        record.work = budget.used();
        let result = match result {
            Ok(None) => {
                forward(e, &sink, unit.depth);
                record.elapsed = started.elapsed();
                report.record(e, record);
                continue;
            }
            Ok(Some(mut branch)) => {
                report.leaves += 1;
                branch.limits = local_limits.clone();
                branch.limits.timeout = budget.remaining_time();
                branch.limits.max_work = unit.work.saturating_sub(budget.used());
                branch.config = config;
                let mut opts = options.clone();
                opts.split_depth = 0;
                opts.max_worlds = unit.worlds;
                record.state = "searching";
                let _progress = e.limits.progress.scope(
                    phase,
                    Some(crate::CheckingTarget::CompletionBranch(record.clone())),
                    true,
                );
                let value = leaf(&branch, &opts);
                for search in sink.snapshot().searches {
                    if search.phase == phase {
                        record.work = record.work.saturating_add(search.work.unwrap_or(0));
                    }
                }
                value
            }
            Err(error) => {
                report.leaves += 1;
                Ok(Search::Inconclusive(inconclusive(error)?))
            }
        }?;
        forward(e, &sink, unit.depth);
        record.elapsed = started.elapsed();
        match result {
            Search::Exists(value) => {
                record.state = "counterexample";
                answer = Some(Search::Exists(value));
            }
            Search::None => record.state = "proved",
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
