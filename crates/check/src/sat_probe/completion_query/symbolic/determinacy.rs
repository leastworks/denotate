//! Uniqueness is a two-model property, never a consequence of totality/parity.
//! Share certified functions of shared providers. Local SAT uses free shared
//! boundary values; restricted global searches still replay full interpretations.
use super::*;

struct Candidate {
    heads: Vec<usize>,
    detail: crate::CompletionComponentStats,
}
struct Decomposition {
    shared: Vec<bool>,
    readers: Vec<Vec<usize>>,
    candidates: Vec<Candidate>,
}

fn record(s: &mut Solver<'_, '_, '_>, detail: crate::CompletionComponentStats) {
    s.stats.current_component = Some(detail.clone());
    if s.stats.component_details.len() < 64 {
        s.stats.component_details.push(detail);
    } else {
        s.stats.omitted_components += 1;
    }
    s.metrics();
}

fn decompose(
    cone: &Cone,
    members: Option<&BTreeSet<GroundAtom>>,
    s: &mut Solver<'_, '_, '_>,
) -> Result<Decomposition> {
    let mut folded = cone.clone();
    folded.fixed = encoding::fitting(cone, s.run.budget)?;
    let graph = consistency::analyse(&folded, None, s.run.budget)?;
    let n = cone.fixed.len();
    let mut groups = vec![Vec::new(); graph.component.iter().max().map_or(0, |i| i + 1)];
    let mut producers = vec![Vec::new(); n];
    let mut providers = vec![Vec::new(); n];
    let mut readers = vec![Vec::new(); n];
    for i in 0..n {
        groups[graph.component[i]].push(i);
    }
    for (j, r) in folded.rules.iter().enumerate() {
        s.run
            .budget
            .charge(r.body.len() + 1, "completion determinacy graph")?;
        if folded.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| folded.fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        producers[r.head].push(j);
        for (i, _) in &r.body {
            if folded.fixed[*i].is_none() {
                providers[r.head].push(*i);
                readers[*i].push(r.head);
            }
        }
    }
    let mut relevant = vec![false; n];
    let mut pending: Vec<_> = cone
        .atoms
        .iter()
        .enumerate()
        .filter_map(|(i, a)| {
            (s.run.engine.decision(a) && members.is_none_or(|m| m.contains(a)) && !cone.input[i])
                .then_some(i)
        })
        .collect();
    while let Some(i) = pending.pop() {
        if relevant[i] {
            continue;
        }
        relevant[i] = true;
        s.run
            .budget
            .charge(providers[i].len() + 1, "completion determinacy graph")?;
        pending.extend(providers[i].iter().copied());
    }
    let cyclic = |g: &[usize]| g.len() > 1 || g.first().is_some_and(|i| providers[*i].contains(i));
    s.stats.components = groups
        .iter()
        .filter(|g| cyclic(g) && g.iter().any(|i| relevant[*i]))
        .count();
    s.metrics();
    let mut shared: Vec<_> = (0..n)
        .map(|i| folded.input[i] || folded.fixed[i].is_some())
        .collect();
    let mut candidates = Vec::new();
    let mut number = 0;
    // Kosaraju numbers consumers before providers; visit in reverse order.
    for heads in groups.into_iter().rev() {
        if heads.iter().all(|i| shared[*i]) {
            continue;
        }
        let boundary_shared = heads.iter().all(|h| {
            providers[*h]
                .iter()
                .all(|i| graph.component[*i] == graph.component[*h] || shared[*i])
        });
        if !cyclic(&heads) {
            for i in heads {
                shared[i] = boundary_shared;
            }
            continue;
        }
        if !heads.iter().any(|i| relevant[*i]) {
            continue;
        }
        let set = heads.iter().copied().collect();
        let local = existence::component(&folded, &producers, &set, s.run.budget)?;
        let relations: BTreeSet<_> = heads
            .iter()
            .filter_map(|i| cone.atoms.get(*i))
            .map(|a| a.relation)
            .collect();
        let mut detail = crate::CompletionComponentStats {
            index: number,
            atoms: heads.len(),
            rules: local.rules.len(),
            boundary: local.input.iter().filter(|v| **v).count(),
            duplicated_atoms: heads.len(),
            relation_count: relations.len(),
            relations: relations.into_iter().take(32).collect(),
            query: "local-uniqueness",
            state: "searching",
            ..Default::default()
        };
        number += 1;
        s.stats.current_component = Some(detail.clone());
        s.metrics();
        let start = Instant::now();
        let progress = s.run.engine.limits.progress.clone();
        let mut stats = s.stats.clone();
        let (answer, variables, clauses, validation_work) =
            s.run.local_unique(&local, |variables, clauses| {
                if let Some(d) = &mut stats.current_component {
                    d.state = "solving";
                    d.variables = variables;
                    d.clauses = clauses;
                    d.elapsed = start.elapsed();
                }
                progress.completion_existence(&stats);
            });
        s.stats.validation_work += validation_work;
        detail.elapsed = start.elapsed();
        detail.variables = variables;
        detail.clauses = clauses;
        detail.state = match &answer {
            Ok(true) => "unique",
            Ok(false) => "fallback",
            Err(_) => "incomplete",
        };
        record(s, detail.clone());
        if answer? {
            s.stats.unique_components += 1;
            if boundary_shared {
                for i in heads {
                    shared[i] = true;
                }
            }
        } else {
            s.stats.fallback_components += 1;
            candidates.push(Candidate { heads, detail });
        }
    }
    s.stats.shared_atoms = shared.iter().take(cone.atoms.len()).filter(|v| **v).count();
    s.metrics();
    Ok(Decomposition {
        shared,
        readers,
        candidates,
    })
}

/// Acyclic readers of a differing component need a second evaluation. Sharing
/// an unrelated unresolved component restricts pairs, so UNSAT there is not a
/// uniqueness proof: retain a joint fallback for coupled components.
pub(super) fn search(
    engine: &Engine,
    cone: &Cone,
    members: Option<&BTreeSet<GroundAtom>>,
    scope: ModelScope,
    classification: bool,
    unique: bool,
    options: &CheckOptions,
    s: &mut Solver<'_, '_, '_>,
) -> Result<Option<Pair>> {
    let plan = decompose(cone, members, s)?;
    if cone.atoms.iter().enumerate().all(|(i, a)| {
        cone.input[i]
            || !engine.decision(a)
            || members.is_some_and(|m| !m.contains(a))
            || plan.shared[i]
    }) {
        return Ok(None);
    }
    let a = s.encode(cone, true)?;
    let selector = s.gate()?;
    let mut examined = 0;
    for candidate in &plan.candidates {
        let mut changed = vec![false; cone.fixed.len()];
        let mut pending = candidate.heads.clone();
        while let Some(i) = pending.pop() {
            if changed[i] || plan.shared[i] {
                continue;
            }
            changed[i] = true;
            s.run
                .budget
                .charge(plan.readers[i].len() + 1, "completion determinacy readers")?;
            pending.extend(plan.readers[i].iter().copied());
        }
        let complete_pair = plan.candidates.len() == 1
            && plan
                .shared
                .iter()
                .zip(&changed)
                .all(|(known, changed)| *known || *changed);
        let shared: Vec<_> = changed.iter().map(|v| !*v).collect();
        let mut detail = candidate.detail.clone();
        detail.query = "reachable-decisions";
        detail.state = "searching";
        detail.elapsed = Default::default();
        detail.variables = 0;
        detail.clauses = 0;
        detail.duplicated_atoms = changed.iter().filter(|v| **v).count();
        s.stats.current_component = Some(detail.clone());
        s.metrics();
        let start = Instant::now();
        let result = (|| {
            let b = s.encode_shared(cone, true, &a, &shared)?;
            let diff = s.component_difference(cone, &a, &b, members, &candidate.heads)?;
            let active = [a.gate, b.gate, diff, selector];
            query(
                engine,
                cone,
                scope,
                classification,
                unique,
                options,
                s,
                &a,
                &b,
                &active,
                selector,
                &mut examined,
            )
        })();
        detail.elapsed = start.elapsed();
        detail.variables = s.run.cnf.solver.num_vars() as usize;
        detail.clauses = s.run.cnf.clauses;
        detail.state = match &result {
            Ok(Some(_)) => "ambiguous",
            Ok(None) if complete_pair => "unique",
            Ok(None) => "fallback",
            Err(_) => "incomplete",
        };
        record(s, detail);
        if let Some(pair) = result? {
            return Ok(Some(pair));
        }
        // If this is the only possible first differing SCC and its cone contains
        // every unshared atom, this restricted pair was already the full pair.
        if complete_pair {
            return Ok(None);
        }
    }
    // Independent loops may need to change together to satisfy downstream
    // equations or H. Only this unrestricted residual pair can close that gap.
    let mut detail = crate::CompletionComponentStats {
        query: "coupled-decisions",
        state: "searching",
        duplicated_atoms: plan.shared.iter().filter(|v| !**v).count(),
        ..Default::default()
    };
    s.stats.current_component = Some(detail.clone());
    s.metrics();
    let start = Instant::now();
    let result = (|| {
        let b = s.encode_shared(cone, true, &a, &plan.shared)?;
        let diff = s.difference(cone, &a, &b, members)?;
        query(
            engine,
            cone,
            scope,
            classification,
            unique,
            options,
            s,
            &a,
            &b,
            &[a.gate, b.gate, diff, selector],
            selector,
            &mut examined,
        )
    })();
    detail.elapsed = start.elapsed();
    detail.variables = s.run.cnf.solver.num_vars() as usize;
    detail.clauses = s.run.cnf.clauses;
    detail.state = match &result {
        Ok(Some(_)) => "ambiguous",
        Ok(None) => "unique",
        Err(_) => "incomplete",
    };
    record(s, detail);
    result
}

fn query(
    engine: &Engine,
    cone: &Cone,
    scope: ModelScope,
    classification: bool,
    unique: bool,
    options: &CheckOptions,
    s: &mut Solver<'_, '_, '_>,
    a: &Encoded,
    b: &Encoded,
    active: &[Lit],
    selector: Lit,
    examined: &mut usize,
) -> Result<Option<Pair>> {
    if let Some(d) = &mut s.stats.current_component {
        d.state = "solving";
        d.variables = s.run.cnf.solver.num_vars() as usize;
        d.clauses = s.run.cnf.clauses;
    }
    s.metrics();
    loop {
        if !s.solve(active, &[])? {
            return Ok(None);
        }
        s.run
            .budget
            .room(*examined, options.max_worlds, "completion pair", "worlds")?;
        *examined += 1;
        s.stats.rounds += 1;
        s.metrics();
        let world = s.world()?;
        if !classification && !unique && engine.classification.is_some() {
            if let Some(cube) = s.eligible(&world, unique)? {
                s.exclude(selector, &cube)?;
                continue;
            }
            let pins = s.pins(&world)?;
            if !s.solve(active, &pins)? {
                return Err(CheckError::Internal("eligible completion pair disappeared"));
            }
        }
        let first = engine.model(s.values(cone, a)?, scope);
        let second = engine.model(s.values(cone, b)?, scope);
        return Ok(Some(Pair { first, second }));
    }
}
