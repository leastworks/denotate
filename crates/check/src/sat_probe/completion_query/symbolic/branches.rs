//! Invocation-local input partitions. Units share only immutable preparation;
//! their equations, solver, work allowance and results belong to that branch.
use super::*;
mod fitting;
mod groups;
use groups::{Choice, Group};

#[derive(Debug, Clone)]
pub struct SplitAlternative {
    pub split: GroundAtom,
    pub assumption: Option<denotate_ir::AssumptionId>,
    pub children: usize,
    pub guarded_edges: usize,
    pub has_rest: bool,
}
#[derive(Debug, Clone)]
pub struct BranchRecord {
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

/// Rank the same structural guard/input dependency shape as the odd-component
/// histogram. Scores are candidates; Fitting in each child determines actual cuts.
fn choose(
    e: &Engine,
    state: &fitting::Bundle,
    classification: bool,
    existence: bool,
    capacity: usize,
    remaining: &mut QueryLimits,
    b: &mut Budget<'_>,
) -> Result<Option<(Choice, Option<Choice>)>> {
    let groups = groups::groups(e, state, b)?;
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
    let witnesses = witness_edges(c, &graph, b)?;
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
            if witnesses
                .get(&graph.component[*i])
                .is_some_and(|es| !es.contains(&(r.head, *i, !*p)))
            {
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
    // Rank separately for each targeted component. A group's other values stay
    // symbolic in one rest child; there is no assumed equivalence between them.
    let mut influence = BTreeMap::<usize, BTreeMap<usize, BTreeSet<(usize, usize, bool)>>>::new();
    let mut providers = vec![Vec::new(); c.fixed.len()];
    for r in &c.rules {
        if c.fixed[r.head].is_none()
            && !r
                .body
                .iter()
                .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
        {
            providers[r.head].extend(r.body.iter().map(|(i, _)| *i));
        }
    }
    let mut cached = BTreeMap::<usize, BTreeSet<usize>>::new();
    for (edge, guards) in &guard_edges {
        for guard in guards {
            if !cached.contains_key(guard) {
                let mut pending = vec![*guard];
                let mut seen = BTreeSet::new();
                let mut inputs = BTreeSet::new();
                while let Some(i) = pending.pop() {
                    b.tick("completion split histogram")?;
                    if !seen.insert(i) || c.fixed[i].is_some() {
                        continue;
                    }
                    if c.input[i] {
                        inputs.insert(i);
                    } else {
                        b.charge(providers[i].len(), "completion split histogram")?;
                        pending.extend(providers[i].iter().copied());
                    }
                }
                cached.insert(*guard, inputs);
            }
            for i in &cached[guard] {
                b.tick("completion split histogram")?;
                influence
                    .entry(graph.component[edge.0])
                    .or_default()
                    .entry(*i)
                    .or_default()
                    .insert(*edge);
            }
        }
    }
    let mut all = BTreeMap::<usize, BTreeSet<(usize, usize, bool)>>::new();
    for inputs in influence.values() {
        for (i, edges) in inputs {
            b.charge(edges.len() + 1, "completion split ranking")?;
            all.entry(*i).or_default().extend(edges.iter().copied());
        }
    }
    let mut best: Option<Choice> = None;
    let mut runner_up: Option<Choice> = None;
    let mut seen = BTreeSet::new();
    for inputs in influence.values() {
        for group in &groups {
            b.charge(group.atoms.len() + 1, "completion split ranking")?;
            if group.atoms.iter().any(|i| c.fixed[*i] == Some(true)) {
                continue;
            }
            let available: Vec<_> = group
                .atoms
                .iter()
                .copied()
                .filter(|i| c.fixed[*i].is_none())
                .collect();
            let selected: Vec<_> = available
                .iter()
                .copied()
                .filter(|i| inputs.contains_key(i))
                .collect();
            if selected.is_empty() {
                continue;
            }
            let rest = !group.exact || selected.len() != available.len();
            let n = selected.len() + usize::from(rest);
            if n < 2 || n > capacity {
                continue;
            }
            if !seen.insert((group.atoms.as_slice(), selected.clone(), rest)) {
                continue;
            }
            // A candidate can cut witness edges in several components. Count
            // their union, not only the component that suggested its values.
            b.charge(
                selected.iter().map(|i| all[i].len()).sum(),
                "completion split ranking",
            )?;
            let score = selected
                .iter()
                .flat_map(|i| all[i].iter())
                .collect::<BTreeSet<_>>()
                .len();
            let choice = Choice {
                group: group.clone(),
                selected,
                rest,
                score,
                binary: false,
            };
            if best.as_ref().is_none_or(|old| choice.rank(old).is_gt()) {
                runner_up = best.replace(choice);
            } else if runner_up
                .as_ref()
                .is_none_or(|old| choice.rank(old).is_gt())
            {
                runner_up = Some(choice);
            }
        }
    }
    // Without a certified useful partition, true/false on one input is always
    // exhaustive. In particular repeated elements never imply sibling exclusion.
    if best.is_none() && capacity >= 2 {
        if let Some((i, edges)) = all
            .into_iter()
            .max_by(|(i, a), (j, b)| a.len().cmp(&b.len()).then_with(|| j.cmp(i)))
        {
            best = Some(Choice {
                group: Group {
                    atoms: vec![i],
                    exact: false,
                    assumption: None,
                    mapping: vec![],
                },
                selected: vec![i],
                rest: true,
                score: edges.len(),
                binary: true,
            });
        }
    }
    Ok(best.map(|choice| (choice, runner_up)))
}

// Use the existing parity-doubled witness search on compact per-component arrays.
fn witness_edges(
    c: &Cone,
    g: &consistency::Core,
    b: &mut Budget<'_>,
) -> Result<BTreeMap<usize, BTreeSet<(usize, usize, bool)>>> {
    let mut seeds = BTreeMap::new();
    for seed in &g.conflicts {
        seeds.entry(g.component[seed.0]).or_insert(*seed);
    }
    let mut edges = BTreeMap::<usize, Vec<(usize, usize, bool)>>::new();
    for r in &c.rules {
        b.charge(r.body.len() + 1, "completion split witnesses")?;
        let id = g.component[r.head];
        if !seeds.contains_key(&id)
            || c.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        for (i, p) in &r.body {
            if !c.input[*i] && c.fixed[*i].is_none() && g.component[*i] == id {
                edges.entry(id).or_default().push((r.head, *i, !*p));
            }
        }
    }
    let mut out = BTreeMap::new();
    for (id, es) in edges {
        let atoms: Vec<_> = es
            .iter()
            .flat_map(|(a, b, _)| [*a, *b])
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let index: BTreeMap<_, _> = atoms.iter().enumerate().map(|(i, a)| (*a, i)).collect();
        let mut adj = vec![vec![]; atoms.len()];
        for (a, d, p) in es {
            adj[index[&a]].push((index[&a], index[&d], p));
        }
        for es in &mut adj {
            es.sort_unstable();
            es.dedup();
        }
        let (a, d, p) = seeds[&id];
        if let Some(mut cycle) = odd::shortest_return((index[&a], index[&d], p), &adj, b)? {
            odd::simplify_walk(&mut cycle, b)?;
            out.insert(
                id,
                cycle
                    .into_iter()
                    .map(|(a, d, p)| (atoms[a], atoms[d], p))
                    .collect(),
            );
        }
    }
    Ok(out)
}

struct Unit {
    id: usize,
    parent_id: Option<usize>,
    parent: Option<Arc<fitting::Bundle>>,
    delta: Vec<(usize, bool)>,
    rest: bool,
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

/// Try the original whole question before dividing it into partitions. Reserve
/// half of each logical allowance; retries never reset the original allowance.
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
    let limits = e.shared_limits(shares);
    if let Err(error) = Budget::new(&limits).check("completion unsplit attempt") {
        return Ok(Search::Inconclusive(inconclusive(error)?));
    }
    let started = Instant::now();
    let end = started + limits.timeout;
    let end = limits.run_deadline.map_or(end, |d| d.min(end));
    let mut first = e.clone();
    first.limits = limits.clone();
    first.limits.timeout /= 2;
    first.limits.run_deadline = Some(end.min(started + first.limits.timeout));
    first.limits.max_work /= 2;
    first.config = divided(&e.config, 2);
    let sink = crate::CompletionSizes::default();
    first.limits.completion_sizes = Some(sink.clone());
    let mut opts = options.clone();
    opts.split_depth = 0;
    opts.max_worlds /= 2;
    let phase = question_phase(classification, existence);
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
        children: 0,
        split_kind: "none",
        assumption: None,
        values: vec![],
        omitted_values: 0,
        mapping: vec![],
        omitted_mapping: 0,
        has_rest: false,
        rest: false,
        preparation_work: 0,
        search_work: work,
        guarded_edges: 0,
        work,
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
    if !matches!(result, Search::Inconclusive(_)) {
        return Ok(result);
    }
    let mut rest = e.clone();
    rest.limits = limits;
    rest.limits.timeout = end.saturating_duration_since(Instant::now());
    rest.limits.run_deadline = Some(end);
    rest.limits.max_work -= first.limits.max_work;
    rest.config = QueryLimits {
        max_solves: e.config.max_solves - first.config.max_solves,
        max_solver_polls: e.config.max_solver_polls - first.config.max_solver_polls,
        max_conflicts: e.config.max_conflicts - first.config.max_conflicts,
        max_propagations: e.config.max_propagations - first.config.max_propagations,
    };
    opts = options.clone();
    opts.max_worlds -= options.max_worlds / 2;
    partition(&rest, classification, existence, &opts, 1, leaf)
}
fn question_phase(classification: bool, existence: bool) -> &'static str {
    match (classification, existence) {
        (true, true) => "completion classification existence",
        (true, false) => "completion classification ambiguity",
        (false, true) => "completion processing existence",
        (false, false) => "completion processing ambiguity",
    }
}

pub(in crate::sat_probe::completion_query) fn partition<T>(
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
    let phase = question_phase(classification, existence);
    let limits = e.shared_limits(shares);
    let local_deadline = Instant::now() + limits.timeout;
    let deadline = limits
        .run_deadline
        .map_or(local_deadline, |d| d.min(local_deadline));
    let mut queue = std::collections::VecDeque::from([Unit {
        id: 1,
        parent_id: None,
        parent: None,
        delta: vec![],
        rest: false,
        pins: BTreeMap::new(),
        depth: 0,
        work: limits.max_work,
        config: e.config.clone(),
        worlds: options.max_worlds,
    }]);
    let mut report = BranchReport::default();
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
        local_limits.timeout =
            deadline.saturating_duration_since(Instant::now()) / (queue.len() + 1) as u32;
        local_limits.max_work = unit.work;
        local_limits.run_deadline = Some(
            local_limits
                .run_deadline
                .map_or(deadline, |d| d.min(deadline)),
        );
        let mut budget = Budget::new(&local_limits);
        let mut config = unit.config.clone();
        let result: Result<Option<Engine>> = (|| {
            let state = Arc::new(match &unit.parent {
                Some(parent) => parent.child(&unit.delta, &mut budget)?,
                None => fitting::Bundle::new(e, &mut budget)?,
            });
            let mut branch = state.engine(e, &mut budget)?;
            branch.limits = local_limits.clone();
            branch.config = config.clone();
            let capacity = options
                .split_branches
                .saturating_sub(report.leaves + queue.len());
            if unit.depth < options.split_depth && capacity > 0 {
                if let Some((choice, runner_up)) = choose(
                    &branch,
                    &state,
                    classification,
                    existence,
                    capacity,
                    &mut config,
                    &mut budget,
                )? {
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
                        record.split_kind = if choice.binary {
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
                        for (delta, rest) in children {
                            let mut pins = unit.pins.clone();
                            for (i, v) in &delta {
                                pins.insert(e.cone.atoms[*i].clone(), *v);
                            }
                            let id = next_id;
                            next_id += 1;
                            queue.push_back(Unit {
                                id,
                                parent_id: Some(unit.id),
                                parent: Some(state.clone()),
                                delta,
                                rest,
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
        record.preparation_work = budget.used();
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
        }?;
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
