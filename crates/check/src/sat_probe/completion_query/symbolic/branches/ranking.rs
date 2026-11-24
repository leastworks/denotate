use super::*;
/// Rank the same structural guard/input dependency shape as the odd-component
/// histogram. Scores are candidates; Fitting in each child determines actual cuts.
pub(super) fn choose(
    e: &Engine,
    state: &fitting::Bundle,
    classification: bool,
    existence: bool,
    capacity: usize,
    remaining: &mut QueryLimits,
    telemetry: &mut Vec<SplitCandidate>,
    omitted: &mut usize,
    b: &mut Budget<'_>,
) -> Result<Option<(Choice, Option<Choice>)>> {
    choose_in(
        e,
        state,
        classification,
        existence,
        capacity,
        None,
        remaining,
        telemetry,
        omitted,
        b,
    )
}
/// A child explores only the surviving parts of the parent components it cut.
/// Other components remain in the residual question, never silently proved.
pub(super) fn choose_in(
    e: &Engine,
    bundle: &fitting::Bundle,
    classification: bool,
    existence: bool,
    capacity: usize,
    allowed: Option<&[Arc<BTreeSet<usize>>]>,
    remaining: &mut QueryLimits,
    telemetry: &mut Vec<SplitCandidate>,
    omitted: &mut usize,
    b: &mut Budget<'_>,
) -> Result<Option<(Choice, Option<Choice>)>> {
    let groups = groups::groups(e, bundle, b)?;
    // H-first coverage and processing rank their stronger inherited view.
    // No-H fallbacks still use the separate W view in the leaf query.
    let (state, context) = bundle.ranking(classification, e.classification.is_some());
    let materialized = state.cone(b)?;
    let c = &*materialized;
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
            if !heads.iter().any(|i| relevant[*i])
                || allowed
                    .is_some_and(|sets| !heads.iter().any(|i| sets.iter().any(|s| s.contains(i))))
            {
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
    if let Some(sets) = allowed {
        let mut surviving = BTreeSet::new();
        for set in sets {
            b.charge(set.len(), "completion split surviving targets")?;
            surviving.extend(
                set.iter()
                    .filter(|i| graph.cyclic[**i])
                    .map(|i| graph.component[*i]),
            );
        }
        candidates.retain(|id| surviving.contains(id));
    }
    if candidates.is_empty() {
        return Ok(None);
    }
    b.charge(graph.component.len(), "completion split target members")?;
    let mut members = BTreeMap::<usize, BTreeSet<usize>>::new();
    for (i, id) in graph.component.iter().enumerate() {
        if graph.cyclic[i] && candidates.contains(id) {
            members.entry(*id).or_default().insert(i);
        }
    }
    let members: BTreeMap<_, _> = members
        .into_iter()
        .map(|(id, set)| (id, Arc::new(set)))
        .collect();
    let witnesses = witness_edges(c, &graph, &candidates, b)?;
    let mut guard_edges = Vec::new();
    // A cyclic producer can become redundant because an ALTERNATIVE producer
    // covers it. Its guard need not occur on the witness edge itself.
    let witness_heads: BTreeSet<_> = witnesses
        .values()
        .flat_map(|es| es.iter().map(|e| e.0))
        .take(32)
        .collect();
    let mut alternative_guards = BTreeMap::<usize, BTreeSet<usize>>::new();
    if bundle.trials.is_some() {
        let mut counts = BTreeMap::<usize, usize>::new();
        for r in &c.rules {
            b.tick("completion split alternative guards")?;
            if !witness_heads.contains(&r.head) {
                continue;
            }
            let count = counts.entry(r.head).or_default();
            if *count >= 32 {
                continue;
            }
            *count += 1;
            b.charge(r.body.len(), "completion split alternative guards")?;
            if r.body
                .iter()
                .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
            {
                continue;
            }
            let guards = alternative_guards.entry(r.head).or_default();
            for (i, _) in &r.body {
                if guards.len() == 32 {
                    break;
                }
                if c.fixed[*i].is_none() {
                    guards.insert(*i);
                }
            }
        }
    }
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
            let mut guards = r
                .body
                .iter()
                .filter_map(|(g, q)| ((*g, *q) != (*i, *p) && c.fixed[*g].is_none()).then_some(*g))
                .collect::<Vec<_>>();
            if let Some(alt) = alternative_guards.get(&r.head) {
                guards.extend(alt.iter().copied());
            }
            guards.sort_unstable();
            guards.dedup();
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
                    } else if !graph.cyclic[i] {
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
    let mut choices = Vec::new();
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
                formula: None,
                child_targets: vec![],
                child_states: vec![],
            };
            choices.push(choice);
            choices.sort_by(|a, b| b.rank(a));
            if choices.len() > 64 {
                choices.pop();
                *omitted += 1;
            }
        }
    }
    // Without a certified useful partition, true/false on one input is always
    // exhaustive. In particular repeated elements never imply sibling exclusion.
    if choices.is_empty() && capacity >= 2 {
        let mut inputs: Vec<_> = all.iter().collect();
        inputs.sort_by(|(i, a), (j, b)| b.len().cmp(&a.len()).then_with(|| i.cmp(j)));
        *omitted += inputs.len().saturating_sub(64);
        for (i, edges) in inputs.into_iter().take(64) {
            choices.push(Choice {
                group: Group {
                    atoms: vec![*i],
                    exact: false,
                    assumption: None,
                    mapping: vec![],
                },
                selected: vec![*i],
                rest: true,
                score: edges.len(),
                binary: true,
                formula: None,
                child_targets: vec![],
                child_states: vec![],
            });
        }
    }
    if capacity >= 2 {
        let formula_h = e.classification.is_some() && !(classification && existence);
        let (formula_state, formula_context) = bundle.ranking(classification, formula_h);
        let formula_cone = formula_state.cone(b)?;
        let mut producers = vec![vec![]; formula_cone.fixed.len()];
        for (j, r) in formula_cone.rules.iter().enumerate() {
            b.charge(r.body.len() + 1, "completion formula candidates")?;
            if formula_cone.fixed[r.head].is_none()
                && !r
                    .body
                    .iter()
                    .any(|(i, p)| formula_cone.fixed[*i].is_some_and(|v| v != *p))
            {
                producers[r.head].push(j);
            }
        }
        let mut derived = BTreeMap::<usize, BTreeSet<(usize, usize, bool)>>::new();
        for (edge, guards) in &guard_edges {
            for g in guards {
                if !c.input[*g] && c.fixed[*g].is_none() {
                    derived.entry(*g).or_default().insert(*edge);
                }
            }
        }
        let mut derived: Vec<_> = derived.into_iter().collect();
        derived.sort_by(|(i, a), (j, b)| b.len().cmp(&a.len()).then_with(|| i.cmp(j)));
        *omitted += derived.len().saturating_sub(64);
        let formula_scope = Arc::new(bundle.scope(classification));
        for (atom, edges) in derived.into_iter().take(64) {
            let context = if formula_context == "W+H" {
                PruningContext::Hypothesis
            } else {
                PruningContext::World
            };
            if let Some(formula) = branch_formula::SettledAtom::build(
                &formula_cone,
                &producers,
                atom,
                formula_scope.clone(),
                context,
                b,
            )? {
                choices.push(Choice {
                    group: Group {
                        atoms: vec![atom],
                        exact: false,
                        assumption: None,
                        mapping: vec![],
                    },
                    selected: vec![atom],
                    rest: true,
                    score: edges.len(),
                    binary: false,
                    formula: Some(formula),
                    child_targets: vec![],
                    child_states: vec![],
                });
            }
        }
    }
    let result = verify(
        e,
        bundle,
        classification,
        &witnesses,
        &members,
        choices,
        context,
        remaining,
        telemetry,
        omitted,
        b,
    )?;
    // Include certified groups that did not reach the shortlist, so absence of
    // a trial is distinguishable from an ineligible mapping or a report cap.
    for group in &groups {
        if telemetry
            .iter()
            .any(|r| group.atoms.iter().any(|i| e.cone.atoms[*i] == r.split))
        {
            continue;
        }
        if group.atoms.iter().any(|i| c.fixed[*i] == Some(true)) {
            continue;
        }
        let Some(i) = group.atoms.iter().find(|i| c.fixed[**i].is_none()) else {
            continue;
        };
        if telemetry.len() == 64 {
            *omitted += 1;
            continue;
        }
        let influenced = group.atoms.iter().any(|i| all.contains_key(i));
        telemetry.push(SplitCandidate {
            split: e.cone.atoms[*i].clone(),
            assumption: group.assumption,
            context,
            state: if influenced {
                "outside-partition-cap"
            } else {
                "no-acyclic-guard"
            },
            children: 0,
            guarded_edges: 0,
            checked_children: 0,
            disabled_edges: 0,
            minimum_disabled: 0,
            cycles_cut_every_child: 0,
            selected: false,
            cutoff: None,
            pruning_attempts: 0,
            pruning_proved: 0,
            derived_guards: vec![],
            child_trials: vec![],
            formula: false,
            omitted_derived_guards: 0,
            derived_guards_complete: false,
        });
    }
    Ok(result)
}

// Use the existing parity-doubled witness search on compact per-component arrays.
fn witness_edges(
    c: &Cone,
    g: &consistency::Core,
    candidates: &BTreeSet<usize>,
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
        if !candidates.contains(&id)
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
        let cycle = if let Some((a, d, p)) = seeds.get(&id) {
            odd::shortest_return((index[a], index[d], *p), &adj, b)?
        } else {
            directed_cycle(&adj, b)?
        };
        if let Some(mut cycle) = cycle {
            if seeds.contains_key(&id) {
                odd::simplify_walk(&mut cycle, b)?;
            }
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

// Non-unique even/positive components also need a concrete witness cycle.
fn directed_cycle(
    adj: &[Vec<(usize, usize, bool)>],
    b: &mut Budget<'_>,
) -> Result<Option<Vec<(usize, usize, bool)>>> {
    let Some(edge) = adj.iter().flatten().next().copied() else {
        return Ok(None);
    };
    let (head, start, _) = edge;
    let mut queue = std::collections::VecDeque::from([start]);
    let mut seen = vec![false; adj.len()];
    let mut prev = vec![None; adj.len()];
    seen[start] = true;
    while let Some(i) = queue.pop_front() {
        b.tick("completion split witnesses")?;
        if i == head {
            let mut out = vec![edge];
            let mut at = head;
            while at != start {
                let e: (usize, usize, bool) = prev[at].unwrap();
                out.push(e);
                at = e.0;
            }
            return Ok(Some(out));
        }
        for e in &adj[i] {
            b.tick("completion split witnesses")?;
            if !seen[e.1] {
                seen[e.1] = true;
                prev[e.1] = Some(*e);
                queue.push_back(e.1);
            }
        }
    }
    Ok(None)
}

fn verify(
    e: &Engine,
    bundle: &fitting::Bundle,
    classification: bool,
    witnesses: &BTreeMap<usize, BTreeSet<(usize, usize, bool)>>,
    members: &BTreeMap<usize, Arc<BTreeSet<usize>>>,
    mut choices: Vec<Choice>,
    context: &'static str,
    remaining: &mut QueryLimits,
    telemetry: &mut Vec<SplitCandidate>,
    omitted: &mut usize,
    b: &mut Budget<'_>,
) -> Result<Option<(Choice, Option<Choice>)>> {
    choices.sort_by(|a, b| b.rank(a)); // stable ties retain semantic input order
    // Inventory includes candidates not shortlisted; omission is explicit.
    *omitted += choices.len().saturating_sub(64);
    for c in choices.iter().take(64) {
        telemetry.push(SplitCandidate {
            split: e.cone.atoms[c.selected[0]].clone(),
            assumption: c.group.assumption,
            context: c.formula.as_ref().map_or(context, |f| {
                if f.context == PruningContext::Hypothesis {
                    "W+H"
                } else {
                    "W"
                }
            }),
            state: "not-shortlisted",
            children: c.child_count(),
            guarded_edges: c.score,
            checked_children: 0,
            disabled_edges: 0,
            minimum_disabled: 0,
            cycles_cut_every_child: 0,
            selected: false,
            cutoff: None,
            pruning_attempts: 0,
            pruning_proved: 0,
            derived_guards: vec![],
            child_trials: vec![],
            formula: c.formula.is_some(),
            omitted_derived_guards: 0,
            derived_guards_complete: false,
        });
    }
    // Diversify by certified group before trying different subsets of one group.
    let mut selected = Vec::new();
    let mut groups = BTreeSet::new();
    for (i, c) in choices.iter().take(64).enumerate() {
        if groups.insert(c.group.atoms.clone()) {
            selected.push(i);
        }
        if selected.len() == 8 {
            break;
        }
    }
    for i in 0..choices.len().min(64) {
        if selected.len() == 8 {
            break;
        }
        if !selected.contains(&i) {
            selected.push(i);
        }
    }
    let mut limits = e.limits.clone();
    limits.max_work = b.remaining() / 4;
    limits.timeout = b.remaining_time() / 4;
    if let Some(pool) = &bundle.trials {
        pool.lock().unwrap().fund_ranking(
            if classification {
                "classification"
            } else {
                "processing"
            },
            limits.timeout,
        );
    }
    let mut trial = Budget::new(&limits);
    let mut completed = Vec::new();
    let heads: BTreeSet<_> = witnesses
        .values()
        .flat_map(|es| es.iter().map(|e| e.0))
        .take(32)
        .collect();
    for i in selected {
        let row = &mut telemetry[i];
        row.state = "trial";
        let mut common: BTreeSet<_> = witnesses.keys().copied().collect();
        let result: Result<()> = (|| {
            for (child_index, (pins, rest)) in choices[i].children().into_iter().enumerate() {
                row.child_trials.push(SplitChild {
                    child: child_index,
                    context,
                    rest,
                    pruning_attempts: 0,
                    pruning_proved: 0,
                    removed_producers: 0,
                    removed_producer_examples: vec![],
                    omitted_producer_examples: 0,
                    removed_literals: 0,
                    pruned_heads: vec![],
                    omitted_pruned_heads: 0,
                    target_atoms: members.values().map(|s| s.len()).sum(),
                    settled_target_atoms: 0,
                    disabled_edges: 0,
                    complete: false,
                    cutoff: None,
                    omitted_derived_guards: 0,
                    derived_guards_complete: false,
                });
                let mut child_bundle =
                    bundle.child_with_formula(&pins, choices[i].formula.as_ref(), &mut trial)?;
                let (attempts, proved, cutoff) =
                    child_bundle.prune(e, classification, &heads, remaining, &mut trial)?;
                row.pruning_attempts += attempts;
                row.pruning_proved += proved;
                row.cutoff = row.cutoff.or(cutoff);
                let detail = row.child_trials.last_mut().unwrap();
                detail.pruning_attempts = attempts;
                detail.pruning_proved = proved;
                detail.cutoff = cutoff;
                detail.removed_producers = child_bundle.proofs.iter().map(|p| p.removed).sum();
                detail.removed_literals =
                    child_bundle.proofs.iter().map(|p| p.removed_literals).sum();
                let heads: BTreeSet<_> = child_bundle
                    .proofs
                    .iter()
                    .flat_map(|p| p.records.iter().map(|r| r.head.clone()))
                    .collect();
                detail.omitted_pruned_heads = heads.len().saturating_sub(8);
                detail.pruned_heads = heads.into_iter().take(8).collect();
                for record in child_bundle
                    .proofs
                    .iter()
                    .flat_map(|p| &p.records)
                    .filter(|r| r.removed > 0)
                {
                    for id in &record.rules {
                        if detail.removed_producer_examples.len() == 8 {
                            break;
                        }
                        let rule = e
                            .program
                            .rule(*id)
                            .ok_or(CheckError::Internal("missing trial source rule"))?;
                        trial.charge(
                            rule.body.len().min(16) + 1,
                            "completion split trial evidence",
                        )?;
                        detail.removed_producer_examples.push(PrunedProducer {
                            context: if record.context == PruningContext::World {
                                "W"
                            } else {
                                "W+H"
                            },
                            head: rule.head.atom.clone(),
                            original_body: rule
                                .body
                                .iter()
                                .take(16)
                                .map(|l| {
                                    (l.term.atom.clone(), l.polarity == crate::Polarity::Positive)
                                })
                                .collect(),
                            omitted_body_literals: rule.body.len().saturating_sub(16),
                        });
                    }
                }
                detail.omitted_producer_examples = detail
                    .removed_producers
                    .saturating_sub(detail.removed_producer_examples.len());
                let (child, child_context) =
                    child_bundle.ranking(classification, e.classification.is_some());
                row.child_trials.last_mut().unwrap().context = child_context;
                let mut cuts = BTreeSet::new();
                let mut disabled = 0;
                for (id, edges) in witnesses {
                    for &(a, d, p) in edges {
                        if !child.edge_live(a, d, p, &mut trial)? {
                            disabled += 1;
                            cuts.insert(*id);
                        }
                    }
                }
                let detail = row.child_trials.last_mut().unwrap();
                for members in members.values() {
                    trial.charge(members.len(), "completion split target settlement")?;
                    detail.settled_target_atoms += members
                        .iter()
                        .filter(|i| child.value(**i).is_some())
                        .count();
                }
                detail.disabled_edges = disabled;
                detail.complete = true;
                choices[i].child_states.push(Arc::new(child_bundle));
                choices[i]
                    .child_targets
                    .push(cuts.iter().map(|id| members[id].clone()).collect());
                common.retain(|id| cuts.contains(id));
                row.minimum_disabled = if row.checked_children == 0 {
                    disabled
                } else {
                    row.minimum_disabled.min(disabled)
                };
                row.checked_children += 1;
                row.disabled_edges += disabled;
            }
            row.cycles_cut_every_child = common.len();
            row.state = "verified";
            Ok(())
        })();
        match result {
            Ok(()) if row.disabled_edges > 0 => completed.push(i),
            Ok(()) => (),
            Err(error) => {
                e.limits.cancellation.check()?;
                row.state = "incomplete";
                row.cutoff = Some(inconclusive(error)?);
                if let Some(detail) = row.child_trials.last_mut() {
                    detail.cutoff = row.cutoff;
                }
                break;
            }
        }
        completed.sort_by(|a, b| compare_trials(*a, *b, telemetry, &choices));
        for old in completed.iter().skip(2) {
            choices[*old].child_states.clear();
        }
        if !completed.contains(&i) {
            choices[i].child_states.clear();
        }
    }
    b.charge(trial.used(), "completion split trials")?;
    completed.sort_by(|a, b| compare_trials(*a, *b, telemetry, &choices));
    if let Some(i) = completed.first().copied() {
        let mut limits = e.limits.clone();
        limits.timeout = (b.remaining_time() / 16).min(Duration::from_millis(50));
        limits.max_work = b.remaining() / 16;
        let started = Instant::now();
        let mut used = 0usize;
        let mut room = 32usize;
        let n = choices[i].child_states.len();
        telemetry[i].derived_guards_complete = true;
        for (child, bundle) in choices[i].child_states.iter().enumerate() {
            // Fair shares, with unused capacity/time/work passed to later children.
            let remaining = n - child;
            let share = room.div_ceil(remaining);
            let mut child_limits = limits.clone();
            child_limits.timeout =
                limits.timeout.saturating_sub(started.elapsed()) / remaining as u32;
            child_limits.max_work = limits.max_work.saturating_sub(used) / remaining;
            let mut diagnostic = Budget::new(&child_limits);
            let (state, _) = bundle.ranking(classification, e.classification.is_some());
            let before = telemetry[i].derived_guards.len();
            let omitted_before = telemetry[i].omitted_derived_guards;
            let result = derived_guards(
                state,
                witnesses,
                child,
                share,
                &mut telemetry[i],
                &mut diagnostic,
            );
            used += diagnostic.used();
            room -= telemetry[i].derived_guards.len() - before;
            let omissions = telemetry[i].omitted_derived_guards - omitted_before;
            let detail = &mut telemetry[i].child_trials[child];
            detail.omitted_derived_guards = omissions;
            detail.derived_guards_complete = result.is_ok();
            if let Err(error) = result {
                e.limits.cancellation.check()?;
                inconclusive(error)?;
                telemetry[i].derived_guards_complete = false;
            }
        }
        if let Err(error) = b.charge(used, "completion branch guard telemetry") {
            e.limits.cancellation.check()?;
            inconclusive(error)?;
            telemetry[i].derived_guards_complete = false;
        }
    }
    Ok(completed.first().map(|i| {
        telemetry[*i].selected = true;
        (
            choices[*i].clone(),
            completed.get(1).map(|j| choices[*j].clone()),
        )
    }))
}

// Bounded post-trial inventory. Sampling never changes candidate eligibility.
pub(super) fn derived_guards(
    state: &fitting::State,
    witnesses: &BTreeMap<usize, BTreeSet<(usize, usize, bool)>>,
    child: usize,
    room: usize,
    row: &mut SplitCandidate,
    b: &mut Budget<'_>,
) -> Result<()> {
    let cone = state.cone(b)?;
    let graph = consistency::analyse(&cone, None, b)?;
    let mut providers = vec![vec![]; cone.fixed.len()];
    for r in &cone.rules {
        b.charge(r.body.len() + 1, "completion branch guard telemetry")?;
        if cone.fixed[r.head].is_none()
            && !r
                .body
                .iter()
                .any(|(i, p)| cone.fixed[*i].is_some_and(|v| v != *p))
        {
            providers[r.head].extend(r.body.iter().map(|(i, _)| *i));
        }
    }
    let mut guards = BTreeSet::new();
    for edges in witnesses.values() {
        for &(a, d, p) in edges {
            if !state.edge_live(a, d, p, b)? {
                continue;
            }
            guards.extend(
                providers[a]
                    .iter()
                    .filter(|i| **i != d && !cone.input[**i] && cone.fixed[**i].is_none())
                    .copied(),
            );
        }
    }
    row.omitted_derived_guards += guards.len();
    for atom in guards.into_iter().take(room) {
        let mut pending = vec![atom];
        let mut seen = BTreeSet::new();
        let mut acyclic = true;
        while let Some(i) = pending.pop() {
            b.tick("completion branch guard telemetry")?;
            if !seen.insert(i) || cone.fixed[i].is_some() || cone.input[i] {
                continue;
            }
            if graph.cyclic[i] {
                acyclic = false;
                break;
            }
            pending.extend(providers[i].iter().copied());
        }
        row.omitted_derived_guards -= 1;
        row.derived_guards.push(DerivedGuard {
            atom: cone.atoms[atom].clone(),
            child,
            acyclic_upstream: acyclic,
        });
    }
    Ok(())
}

fn compare_trials(
    a: usize,
    b: usize,
    telemetry: &[SplitCandidate],
    choices: &[Choice],
) -> std::cmp::Ordering {
    let x = &telemetry[a];
    let y = &telemetry[b];
    y.cycles_cut_every_child
        .cmp(&x.cycles_cut_every_child)
        .then_with(|| {
            ((y.disabled_edges as u128) * (x.children - 1) as u128)
                .cmp(&((x.disabled_edges as u128) * (y.children - 1) as u128))
        })
        .then_with(|| y.minimum_disabled.cmp(&x.minimum_disabled))
        .then_with(|| choices[b].rank(&choices[a]))
}
