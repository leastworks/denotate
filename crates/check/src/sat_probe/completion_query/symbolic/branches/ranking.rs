use super::*;
use std::collections::VecDeque;
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
/// Unchanged sides of the selected target go to residual checking. Unrelated
/// components remain eligible; a parent cut is not a whitelist for this path.
pub(super) fn choose_in(
    e: &Engine,
    bundle: &fitting::Bundle,
    classification: bool,
    existence: bool,
    capacity: usize,
    deferred: Option<&[Arc<BTreeSet<usize>>]>,
    remaining: &mut QueryLimits,
    telemetry: &mut Vec<SplitCandidate>,
    omitted: &mut usize,
    b: &mut Budget<'_>,
) -> Result<Option<(Choice, Option<Choice>)>> {
    choose_noting(
        e,
        bundle,
        classification,
        existence,
        capacity,
        deferred,
        remaining,
        telemetry,
        omitted,
        &mut None,
        b,
    )
}

fn gap(
    reason: &'static str,
    targets: usize,
    witnesses: &BTreeMap<usize, BTreeSet<(usize, usize, bool)>>,
    c: &Cone,
    counts: (usize, usize, usize),
) -> RankingGap {
    let atoms: BTreeSet<_> = witnesses
        .values()
        .next()
        .into_iter()
        .flatten()
        .flat_map(|(a, d, _)| [*a, *d])
        .collect();
    RankingGap {
        reason,
        targets,
        witness: atoms.iter().take(16).map(|i| c.atoms[*i].clone()).collect(),
        omitted_witness: atoms.len().saturating_sub(16),
        guarded_edges: counts.0,
        inputs: counts.1,
        formulas: counts.2,
    }
}

/// `choose_in`, also reporting why no partition was found.
#[allow(clippy::too_many_arguments)]
pub(super) fn choose_noting(
    e: &Engine,
    bundle: &fitting::Bundle,
    classification: bool,
    existence: bool,
    capacity: usize,
    deferred: Option<&[Arc<BTreeSet<usize>>]>,
    remaining: &mut QueryLimits,
    telemetry: &mut Vec<SplitCandidate>,
    omitted: &mut usize,
    noted: &mut Option<RankingGap>,
    b: &mut Budget<'_>,
) -> Result<Option<(Choice, Option<Choice>)>> {
    let groups = groups::groups(e, bundle, b)?;
    // H-first coverage and processing rank their stronger inherited view.
    // No-H fallbacks still use the separate W view in the leaf query.
    let (state, context) = bundle.ranking(classification, e.classification.is_some());
    let materialized = state.analysis_cone(b)?;
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
        let discovered: Result<()> = (|| {
            for (id, heads) in sets {
                if !heads.iter().any(|i| relevant[*i])
                    || deferred.is_some_and(|sets| {
                        heads.iter().any(|i| sets.iter().any(|s| s.contains(i)))
                    })
                {
                    continue;
                }
                let local = existence::component(c, &producers, &heads, run.budget)?;
                let (unique, _, _, _) = run.local_unique(&local, |_, _| {});
                if !unique? {
                    candidates.insert(id);
                }
            }
            Ok(())
        })();
        let used = run.usage();
        remaining.max_solves = remaining.max_solves.saturating_sub(used.max_solves);
        remaining.max_solver_polls = remaining
            .max_solver_polls
            .saturating_sub(used.max_solver_polls);
        remaining.max_conflicts = remaining.max_conflicts.saturating_sub(used.max_conflicts);
        remaining.max_propagations = remaining
            .max_propagations
            .saturating_sub(used.max_propagations);
        discovered?;
    }
    if let Some(sets) = deferred {
        let mut surviving = BTreeSet::new();
        for set in sets {
            b.charge(set.len(), "completion split surviving targets")?;
            surviving.extend(
                set.iter()
                    .filter(|i| graph.cyclic[**i])
                    .map(|i| graph.component[*i]),
            );
        }
        candidates.retain(|id| !surviving.contains(id));
    }
    if candidates.is_empty() {
        *noted = Some(gap("no-target", 0, &BTreeMap::new(), c, (0, 0, 0)));
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
        *noted = Some(gap(
            "no-guarded-witness-edge",
            candidates.len(),
            &witnesses,
            c,
            (0, 0, 0),
        ));
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
    // Candidates dropped only because the partition exceeds the leaf capacity.
    let mut bounded = capacity < 2;
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
                bounded |= n > capacity;
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
        let formula_cone = formula_state.analysis_cone(b)?;
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
    let mut involvement = BTreeMap::<usize, BTreeSet<usize>>::new();
    for (atom, edges) in &all {
        involvement
            .entry(*atom)
            .or_default()
            .extend(edges.iter().map(|e| graph.component[e.0]));
    }
    for (edge, guards) in &guard_edges {
        for guard in guards {
            involvement
                .entry(*guard)
                .or_default()
                .insert(graph.component[edge.0]);
        }
    }
    let formulas = choices.iter().filter(|c| c.formula.is_some()).count();
    let counts = (guard_edges.len(), all.len(), formulas);
    let empty = choices.is_empty();
    let result = verify(
        e,
        bundle,
        classification,
        &witnesses,
        &members,
        &involvement,
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
    if result.is_none() {
        let reason = if !empty {
            "no-verified-cut"
        } else if bounded {
            "partition-bounds"
        } else {
            "no-input-or-formula"
        };
        *noted = Some(gap(reason, candidates.len(), &witnesses, c, counts));
    }
    Ok(result)
}

// Use the existing parity-doubled witness search on compact per-component arrays.
pub(super) fn witness_edges(
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
    involvement: &BTreeMap<usize, BTreeSet<usize>>,
    mut choices: Vec<Choice>,
    context: &'static str,
    remaining: &mut QueryLimits,
    telemetry: &mut Vec<SplitCandidate>,
    omitted: &mut usize,
    b: &mut Budget<'_>,
) -> Result<Option<(Choice, Option<Choice>)>> {
    let cycles = |c: &Choice| {
        c.selected
            .iter()
            .flat_map(|a| involvement.get(a).into_iter().flatten().copied())
            .collect::<BTreeSet<_>>()
            .len()
    };
    choices.sort_by(|a, b| cycles(b).cmp(&cycles(a)).then_with(|| b.rank(a)));
    // Neither raw edge scores nor inventory truncation may starve a kind.
    let mut inputs = VecDeque::new();
    let mut formulas = VecDeque::new();
    for c in choices {
        if c.formula.is_some() {
            formulas.push_back(c);
        } else {
            inputs.push_back(c);
        }
    }
    let mut choices = Vec::new();
    while !inputs.is_empty() || !formulas.is_empty() {
        if let Some(c) = inputs.pop_front() {
            choices.push(c);
        }
        if let Some(c) = formulas.pop_front() {
            choices.push(c);
        }
    }
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
    // Four slots per kind when both are available. Within each kind, distinct
    // groups precede alternative subsets; duplicate subsets cannot steal the
    // other kind's reserved turns. Empty-kind slots pass to the remaining kind.
    let mut orders = [VecDeque::new(), VecDeque::new()];
    for (kind, order) in orders.iter_mut().enumerate() {
        let mut groups = BTreeSet::new();
        let mut repeated = Vec::new();
        for (i, c) in choices.iter().take(64).enumerate() {
            if usize::from(c.formula.is_some()) != kind {
                continue;
            }
            if groups.insert(c.group.atoms.clone()) {
                order.push_back(i);
            } else {
                repeated.push(i);
            }
        }
        order.extend(repeated);
    }
    let mut selected = Vec::new();
    while selected.len() < 8 && orders.iter().any(|o| !o.is_empty()) {
        for order in &mut orders {
            if selected.len() == 8 {
                break;
            }
            if let Some(i) = order.pop_front() {
                selected.push(i);
            }
        }
    }
    // Reserve fair inventory slots for both kinds, then spend them on the
    // candidates involved in the most witness cycles. Stable ties retain the
    // interleaving above, rather than letting source order choose a kind.
    let cycles = |i: usize| {
        choices[i]
            .selected
            .iter()
            .flat_map(|a| involvement.get(a).into_iter().flatten().copied())
            .collect::<BTreeSet<_>>()
            .len()
    };
    let mut limits = e.limits.clone();
    limits.max_work = b.remaining() / e.limits.completion_share(4);
    limits.timeout = b.remaining_time() / e.limits.completion_share(4) as u32;
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
    if (if e.limits.completion_exploration {
        selected.len()
    } else {
        funded_trials(selected.len(), limits.timeout)
    }) == 0
    {
        return Ok(None);
    }
    let mut trials = Budget::new(&limits);
    let setup = bundle.trial_base(classification, e.classification.is_some(), &mut trials);
    b.charge(trials.used(), "completion trial parent setup")?;
    let bundle = match setup {
        Ok(bundle) => bundle,
        Err(error) => {
            e.limits.cancellation.check()?;
            inconclusive(error)?;
            return Ok(None);
        }
    };
    let mut completed = Vec::new();
    let heads: BTreeSet<_> = witnesses
        .values()
        .flat_map(|es| es.iter().map(|e| e.0))
        .take(32)
        .collect();
    // A floor limits the number of attempts; it never increases the allowance.
    // Unused shares pass forward. Do not launch another near-zero-time setup.
    let count = if e.limits.completion_exploration {
        selected.len()
    } else {
        funded_trials(selected.len(), trials.remaining_time())
    };
    selected.truncate(count);
    selected.sort_by_key(|i| std::cmp::Reverse(cycles(*i)));
    if e.limits.completion_exploration {
        for i in &selected {
            telemetry[*i].state = "not-started";
        }
    }
    for (position, i) in selected.into_iter().enumerate() {
        let mut candidate_limits = limits.clone();
        candidate_limits.max_work =
            trials.remaining() / e.limits.completion_share(count - position);
        candidate_limits.timeout =
            trials.remaining_time() / e.limits.completion_share(count - position) as u32;
        candidate_limits.run_deadline = Some(Instant::now() + candidate_limits.timeout);
        if let Some(end) = limits.run_deadline {
            candidate_limits.run_deadline = Some(candidate_limits.run_deadline.unwrap().min(end));
        }
        if !e.limits.completion_exploration && candidate_limits.timeout < MIN_TRIAL {
            break;
        }
        let trial_started = Instant::now();
        e.exploration("completion split trial", "started", 0, Duration::ZERO);
        let mut trial = Budget::new(&candidate_limits);
        let row = &mut telemetry[i];
        row.state = "trial";
        let _trial_scope = e.limits.completion_exploration.then(|| {
            e.limits.progress.scope(
                "completion split trial candidate",
                Some(crate::CheckingTarget::CompletionBranch(BranchRecord {
                    id: i,
                    phase: "completion split trial candidate",
                    state: "started",
                    split: Some(row.split.clone()),
                    candidates: vec![row.clone()],
                    split_kind: if row.formula { "formula" } else { "input" },
                    ..Default::default()
                })),
                true,
            )
        });
        let mut common: BTreeSet<_> = witnesses.keys().copied().collect();
        let result: Result<()> = (|| {
            for (child_index, (pins, rest)) in choices[i].children().into_iter().enumerate() {
                row.child_trials.push(SplitChild {
                    forcing: vec![],
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
                    cycles_cut: 0,
                    complete: false,
                    cutoff: None,
                    omitted_derived_guards: 0,
                    derived_guards_complete: false,
                });
                let mut child_bundle =
                    bundle.child_with_formula(&pins, choices[i].formula.as_ref(), &mut trial)?;
                let (attempts, proved, cutoff) =
                    child_bundle.prune(e, classification, &heads, remaining, &mut trial)?;
                child_bundle.settle(e, classification, true, remaining, &mut trial)?;
                row.child_trials.last_mut().unwrap().forcing = child_bundle.forcing.clone();
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
                // The parent already owns a reduced incidence index. Forks
                // propagate only changed literals; do not fold/reindex the
                // whole cone again merely to count witness cuts.
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
                detail.cycles_cut = cuts.len();
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
        e.exploration(
            "completion split trial",
            if result.is_ok() {
                "completed"
            } else {
                "cut-off"
            },
            trial.used(),
            trial_started.elapsed(),
        );
        b.charge(trial.used(), "completion split trials")?;
        let ledger_cutoff = trials
            .charge(trial.used(), "completion split candidate trials")
            .err();
        match result {
            Ok(()) if row.child_trials.iter().any(|c| c.cycles_cut > 0) => completed.push(i),
            Ok(()) => (),
            Err(error) => {
                e.limits.cancellation.check()?;
                row.state = "incomplete";
                row.cutoff = Some(inconclusive(error)?);
                if let Some(detail) = row.child_trials.last_mut() {
                    detail.cutoff = row.cutoff;
                }
                // Verified children remain evidence even if a later child
                // exhausts. Missing children are reconstructed and checked.
                if row
                    .child_trials
                    .iter()
                    .any(|c| c.complete && c.cycles_cut > 0)
                {
                    completed.push(i);
                }
            }
        }
        completed.sort_by(|a, b| compare_trials(*a, *b, telemetry, &choices));
        for old in completed.iter().skip(2) {
            choices[*old].child_states.clear();
        }
        if !completed.contains(&i) {
            choices[i].child_states.clear();
        }
        if let Some(error) = ledger_cutoff {
            inconclusive(error)?;
            break;
        }
    }
    completed.sort_by(|a, b| compare_trials(*a, *b, telemetry, &choices));
    if let Some(i) = completed.first().copied() {
        let mut limits = e.limits.clone();
        limits.timeout =
            e.limits
                .completion_slice(b.remaining_time(), 16, Duration::from_millis(50));
        limits.max_work = b.remaining() / e.limits.completion_share(16);
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
            child_limits.timeout = limits.timeout.saturating_sub(started.elapsed())
                / e.limits.completion_share(remaining) as u32;
            child_limits.max_work =
                limits.max_work.saturating_sub(used) / e.limits.completion_share(remaining);
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
    let cone = state.analysis_cone(b)?;
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

const MIN_TRIAL: Duration = Duration::from_millis(500);
fn funded_trials(candidates: usize, remaining: Duration) -> usize {
    candidates.min((remaining.as_nanos() / MIN_TRIAL.as_nanos()) as usize)
}

fn compare_trials(
    a: usize,
    b: usize,
    telemetry: &[SplitCandidate],
    choices: &[Choice],
) -> std::cmp::Ordering {
    let x = &telemetry[a];
    let y = &telemetry[b];
    let cuts =
        |r: &SplitCandidate| r.child_trials.iter().map(|c| c.cycles_cut).sum::<usize>() as u128;
    let forced = |r: &SplitCandidate| {
        r.child_trials
            .iter()
            .flat_map(|c| &c.forcing)
            .map(|r| r.forced_witnesses)
            .sum::<usize>() as u128
    };
    let forcing = x
        .child_trials
        .iter()
        .chain(&y.child_trials)
        .any(|c| !c.forcing.is_empty());
    (if forcing {
        (forced(y) * (x.children - 1) as u128).cmp(&(forced(x) * (y.children - 1) as u128))
    } else {
        std::cmp::Ordering::Equal
    })
    .then_with(|| (cuts(y) * (x.children - 1) as u128).cmp(&(cuts(x) * (y.children - 1) as u128)))
    .then_with(|| y.cycles_cut_every_child.cmp(&x.cycles_cut_every_child))
    .then_with(|| {
        ((y.disabled_edges as u128) * (x.children - 1) as u128)
            .cmp(&((x.disabled_edges as u128) * (y.children - 1) as u128))
    })
    .then_with(|| y.minimum_disabled.cmp(&x.minimum_disabled))
    .then_with(|| choices[b].rank(&choices[a]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_probe::completion_query::tests::{prepare, verification};
    use crate::test_support::rewrites::{rel, rule};

    #[test]
    fn partial_cut_beats_weaker_finished_trial_and_unchecked_child_is_residual() {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        for name in ["p", "q"] {
            let p = rel(&mut c, name, false);
            rule(&mut c, p, &[(i, false), (p, true)]);
        }
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &Default::default());
        let mut b = Budget::new(&e.limits);
        let root = fitting::Bundle::new(&e, &mut b).unwrap();
        let mut rows = vec![];
        let (choice, _) = choose(
            &e,
            &root,
            false,
            true,
            8,
            &mut e.config.clone(),
            &mut rows,
            &mut 0,
            &mut b,
        )
        .unwrap()
        .unwrap();
        let mut partial = rows.iter().find(|r| r.selected).unwrap().clone();
        let mut finished = partial.clone();
        // Retain only the verified cutting side: no timings or solver choices.
        partial.child_trials.retain(|c| c.cycles_cut > 0);
        partial.checked_children = 1;
        partial.state = "incomplete";
        partial.cycles_cut_every_child = 0;
        for child in &mut finished.child_trials {
            child.cycles_cut = usize::from(child.cycles_cut > 0);
        }
        assert!(
            compare_trials(
                0,
                1,
                &[partial, finished],
                &[choice.clone(), choice.clone()]
            )
            .is_lt()
        );
        let mut interrupted = choice;
        interrupted.child_targets = vec![interrupted.child_targets.into_iter().flatten().collect()];
        interrupted.child_states.truncate(1);
        assert!(!interrupted.residual_only(1).is_empty());
    }

    #[test]
    fn insufficient_trial_time_starts_no_setup_and_unused_time_can_fund_another() {
        assert_eq!(funded_trials(8, Duration::ZERO), 0);
        assert_eq!(funded_trials(8, MIN_TRIAL / 2), 0);
        assert!(funded_trials(8, MIN_TRIAL * 2) > funded_trials(8, MIN_TRIAL));
    }

    #[test]
    fn trial_children_share_reduced_parent_index_and_keep_sibling_values_separate() {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let p = rel(&mut c, "p", false);
        rule(&mut c, p, &[(i, false), (p, true)]);
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &Default::default());
        let mut b = Budget::new(&e.limits);
        let root = fitting::Bundle::new(&e, &mut b)
            .unwrap()
            .trial_base(false, false, &mut b)
            .unwrap();
        let i = e.cone.atoms.iter().position(|a| a.relation == i).unwrap();
        let yes = root.child(&[(i, true)], &mut b).unwrap();
        let no = root.child(&[(i, false)], &mut b).unwrap();
        let parent = root.ranking(false, false).0;
        let yes = yes.ranking(false, false).0;
        let no = no.ranking(false, false).0;
        assert!(Arc::ptr_eq(&parent.index_for_test(), &yes.index_for_test()));
        assert!(Arc::ptr_eq(&parent.index_for_test(), &no.index_for_test()));
        assert_eq!(parent.value(i), None);
        assert_eq!(yes.value(i), Some(true));
        assert_eq!(no.value(i), Some(false));
    }
}
