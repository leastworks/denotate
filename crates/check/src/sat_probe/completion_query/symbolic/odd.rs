//! Bounded diagnostics only. Walks use current scoped edges with preserved source
//! rules; guard-input reachability uses original instances and is structural.
use super::*;
use std::collections::{HashMap, VecDeque};
const PHASE: &str = "completion odd explanation";
type Edge = (usize, usize, bool);

pub(super) fn explain(
    engine: &Engine,
    c: &Cone,
    core: Option<&consistency::Core>,
    b: &mut Budget<'_>,
) -> Option<Arc<crate::CompletionOddExplanation>> {
    if core.is_some_and(|c| c.odd_components == 0)
        || (!engine.limits.progress.enabled() && engine.limits.completion_sizes.is_none())
    {
        return None;
    }
    let mut limits = engine.limits.clone();
    limits.max_work = limits.max_work.min(1_000_000);
    limits.timeout = limits.timeout.min(Duration::from_millis(100));
    limits.completion_sizes = None;
    // This advisory work has its own work/time allowance. The enclosing run's
    // global deadline and cancellation still apply.
    let mut out = crate::CompletionOddExplanation::default();
    let result = b.excluding_time(|| {
        let mut budget = Budget::new(&limits);
        let analysed;
        let core = match core {
            Some(c) => c,
            None => {
                analysed = consistency::analyse(c, None, &mut budget)?;
                &analysed
            }
        };
        build(engine, c, core, &mut out, &mut budget)
    });
    if let Err(e) = result {
        out.incomplete = Some(e.to_string());
    }
    out.omitted_negative_relations = cap(&mut out.negative_relations);
    out.omitted_input_groups = cap(&mut out.input_groups);
    Some(Arc::new(out))
}

struct Original<'a> {
    e: &'a Engine,
    components: BTreeSet<usize>,
    heads: HashMap<usize, Vec<usize>>,
}
impl<'a> Original<'a> {
    fn rules(&mut self, head: usize, b: &mut Budget<'_>) -> Result<&[usize]> {
        let comp = self.e.program.atom_components[head].index;
        if self.components.insert(comp) {
            for i in &self.e.program.component_rules[comp] {
                b.tick(PHASE)?;
                self.heads
                    .entry(self.e.cone.rules[*i].head)
                    .or_default()
                    .push(*i);
            }
        }
        Ok(self.heads.get(&head).map(Vec::as_slice).unwrap_or(&[]))
    }
    fn inputs(&mut self, root: &GroundAtom, b: &mut Budget<'_>) -> Result<BTreeSet<usize>> {
        let mut pending = vec![self.e.program.atom_index[root]];
        let mut seen = BTreeSet::new();
        let mut inputs = BTreeSet::new();
        while let Some(i) = pending.pop() {
            b.tick(PHASE)?;
            if !seen.insert(i) {
                continue;
            }
            if i >= self.e.cone.atoms.len() {
                continue;
            }
            if self.e.cone.input[i] {
                inputs.insert(i);
                continue;
            }
            for r in self.rules(i, b)?.to_vec() {
                b.charge(self.e.cone.rules[r].body.len(), PHASE)?;
                pending.extend(self.e.cone.rules[r].body.iter().map(|(i, _)| *i));
            }
        }
        Ok(inputs)
    }
}

fn build(
    e: &Engine,
    c: &Cone,
    core: &consistency::Core,
    out: &mut crate::CompletionOddExplanation,
    b: &mut Budget<'_>,
) -> Result<()> {
    out.odd_components = core.odd_components;
    b.charge(c.fixed.len() + c.rules.len(), PHASE)?;
    let mut edges = vec![Vec::<Edge>::new(); c.fixed.len()];
    let mut producers: BTreeMap<Edge, Vec<usize>> = BTreeMap::new();
    for (ri, r) in c.rules.iter().enumerate() {
        b.charge(r.body.len() + 1, PHASE)?;
        if c.input[r.head]
            || c.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        for (i, p) in &r.body {
            if c.input[*i] || c.fixed[*i].is_some() {
                continue;
            }
            let edge = (r.head, *i, !*p);
            producers.entry(edge).or_default().push(ri);
        }
    }
    for edge in producers.keys() {
        edges[edge.0].push(*edge);
    }
    let mut original = Original {
        e,
        components: BTreeSet::new(),
        heads: HashMap::new(),
    };
    let mut unique = BTreeSet::new();
    // At most three conflicting-edge seeds per odd SCC, and three retained
    // distinct cycles per explained component. Count is always a lower bound.
    let mut by_component: BTreeMap<usize, Vec<Edge>> = BTreeMap::new();
    for seed in &core.conflicts {
        by_component
            .entry(core.component[seed.0])
            .or_default()
            .push(*seed);
    }
    let seeds: Vec<_> = (0..3)
        .flat_map(|i| by_component.values().filter_map(move |v| v.get(i).copied()))
        .collect();
    let mut witnessed = BTreeSet::new();
    for seed in &seeds {
        if out.found == 3 {
            break;
        }
        if let Some(mut cycle) = shortest_return(*seed, &edges, b)? {
            simplify_walk(&mut cycle, b)?;
            let pivot = (0..cycle.len()).min_by_key(|i| cycle[*i]).unwrap();
            cycle.rotate_left(pivot);
            if !unique.insert(cycle.clone()) {
                continue;
            }
            out.found += 1;
            witnessed.insert(core.component[cycle[0].0]);
            out.witnessed_components = witnessed.len();
            if cycle.len() > 128 {
                out.omitted_cycles += 1;
                continue;
            }
            let mut shown = Vec::new();
            for edge in cycle {
                let rs = &producers[&edge];
                let mut sources = Vec::new();
                for ri in rs.iter().take(8) {
                    let r = &c.rules[*ri];
                    b.charge(r.body.len() + 1, PHASE)?;
                    let guards: Vec<_> = r
                        .body
                        .iter()
                        .filter(|(i, p)| c.fixed[*i].is_none() && !(*i == edge.1 && !*p == edge.2))
                        .collect();
                    sources.push(crate::CompletionOddProducer {
                        source: r.source,
                        guards: guards
                            .iter()
                            .take(16)
                            .map(|(i, p)| (c.atoms[*i].clone(), !*p))
                            .collect(),
                        omitted_guards: guards.len().saturating_sub(16),
                    });
                }
                shown.push(crate::CompletionOddEdge {
                    from: c.atoms[edge.0].clone(),
                    to: c.atoms[edge.1].clone(),
                    negative: edge.2,
                    producer_count: rs.len(),
                    producers: sources,
                });
            }
            out.cycles.push(shown);
        }
    }
    // Relation counts count negative rule-instance occurrences (parallel
    // producers count separately). Group counts count each graph edge once.
    for (edge, rs) in &producers {
        if !edge.2 {
            continue;
        }
        b.tick(PHASE)?;
        *out.negative_relations
            .entry((c.atoms[edge.0].relation, c.atoms[edge.1].relation))
            .or_default() += rs.len();
    }
    let mut group_index: BTreeMap<usize, Vec<crate::CompletionGuardGroup>> = BTreeMap::new();
    for a in e.assumptions.iter() {
        for (values, atoms) in &a.groups {
            for i in atoms {
                b.tick(PHASE)?;
                if e.cone.input[*i] {
                    group_index
                        .entry(*i)
                        .or_default()
                        .push(crate::CompletionGuardGroup {
                            relation: e.cone.atoms[*i].relation,
                            values: values.clone(),
                            assumption: Some(a.id),
                            declared: false,
                        });
                }
            }
        }
    }
    for g in &e.program.universe_groups {
        for a in &g.atoms {
            b.tick(PHASE)?;
            let values = e.program.input_cardinalities[&g.relation]
                .group_by
                .iter()
                .map(|i| a.arguments[*i])
                .collect();
            group_index
                .entry(e.program.atom_index[a])
                .or_default()
                .push(crate::CompletionGuardGroup {
                    relation: g.relation,
                    values,
                    assumption: None,
                    declared: true,
                });
        }
    }
    let mut reached: HashMap<GroundAtom, BTreeSet<usize>> = HashMap::new();
    for (edge, rs) in &producers {
        if !edge.2 {
            continue;
        }
        let mut groups = BTreeSet::new();
        for ri in rs {
            for (i, p) in &c.rules[*ri].body {
                b.tick(PHASE)?;
                if c.fixed[*i].is_some() || (*i == edge.1 && !*p == edge.2) {
                    continue;
                }
                let a = &c.atoms[*i];
                if !reached.contains_key(a) {
                    reached.insert(a.clone(), original.inputs(a, b)?);
                }
                for input in &reached[a] {
                    b.tick(PHASE)?;
                    if let Some(gs) = group_index.get(input) {
                        groups.extend(gs.iter().cloned());
                    } else {
                        let a = &e.cone.atoms[*input];
                        groups.insert(crate::CompletionGuardGroup {
                            relation: a.relation,
                            values: a.arguments.clone(),
                            assumption: None,
                            declared: false,
                        });
                    }
                }
            }
        }
        for g in groups {
            *out.input_groups.entry(g).or_default() += 1;
        }
    }
    out.histograms_complete = true;
    Ok(())
}

pub(super) fn shortest_return(
    seed: Edge,
    edges: &[Vec<Edge>],
    b: &mut Budget<'_>,
) -> Result<Option<Vec<Edge>>> {
    let (from, to, negative) = seed;
    // Take the conflicting edge, then find a directed return with opposite parity.
    let start = to * 2 + usize::from(negative);
    let target = from * 2 + 1;
    b.charge(edges.len() * 2, PHASE)?;
    let mut previous = vec![None; edges.len() * 2];
    let mut seen = vec![false; edges.len() * 2];
    let mut q = VecDeque::from([start]);
    seen[start] = true;
    while let Some(state) = q.pop_front() {
        b.tick(PHASE)?;
        if state == target {
            let mut path = Vec::new();
            let mut at = target;
            while at != start {
                let (p, edge) = previous[at].unwrap();
                path.push(edge);
                at = p;
            }
            path.reverse();
            let mut cycle = vec![seed];
            cycle.extend(path);
            return Ok(Some(cycle));
        }
        for edge in &edges[state / 2] {
            b.tick(PHASE)?;
            let next = edge.1 * 2 + ((state % 2) ^ usize::from(edge.2));
            if !seen[next] {
                seen[next] = true;
                previous[next] = Some((state, *edge));
                q.push_back(next);
            }
        }
    }
    Ok(None)
}
pub(super) fn simplify_walk(cycle: &mut Vec<Edge>, b: &mut Budget<'_>) -> Result<()> {
    loop {
        b.charge(cycle.len(), PHASE)?;
        let mut seen = BTreeMap::new();
        let mut repeated = None;
        for (i, e) in cycle.iter().enumerate() {
            if let Some(start) = seen.insert(e.0, i) {
                repeated = Some((start, i));
                break;
            }
        }
        let Some((start, end)) = repeated else {
            return Ok(());
        };
        if cycle[start..end].iter().filter(|e| e.2).count() % 2 == 1 {
            *cycle = cycle[start..end].to_vec();
        } else {
            cycle.drain(start..end);
        }
    }
}

fn cap<K: Ord + Clone>(map: &mut BTreeMap<K, usize>) -> usize {
    let omitted = map.len().saturating_sub(32);
    if omitted > 0 {
        let mut ranked: Vec<_> = map.iter().map(|(k, v)| (k.clone(), *v)).collect();
        ranked.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        *map = ranked.into_iter().take(32).collect();
    }
    omitted
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_probe::completion_query::tests::{prepare, verification};
    use crate::test_support::rewrites::{rel, rule};

    fn valid(cycle: &[Edge], edges: &[Vec<Edge>]) {
        assert!(!cycle.is_empty());
        assert_eq!(cycle.iter().filter(|e| e.2).count() % 2, 1);
        let mut vertices = BTreeSet::new();
        for (i, e) in cycle.iter().enumerate() {
            assert!(edges[e.0].contains(e));
            assert_eq!(e.1, cycle[(i + 1) % cycle.len()].0);
            assert!(vertices.insert(e.0), "simple cycle");
        }
    }
    #[test]
    fn parity_bfs_finds_odd_cycle_beside_even_cycle() {
        let edges = vec![
            vec![(0, 1, true), (0, 2, false)],
            vec![(1, 0, true)],
            vec![(2, 0, true)],
        ];
        let limits = Limits::default();
        // The selected conflict edge can belong to an even simple cycle.
        // Its shortest odd closed walk still contains an actual odd subcycle.
        let mut b = Budget::new(&limits);
        let mut c = shortest_return((0, 1, true), &edges, &mut b)
            .unwrap()
            .unwrap();
        simplify_walk(&mut c, &mut b).unwrap();
        valid(&c, &edges);
        assert_eq!(c.len(), 2);
        assert!(c.iter().any(|e| e.0 == 2));
    }
    #[test]
    fn exhaustive_signed_graphs_return_real_odd_cycles_only() {
        let mut corpus = denotate_ir::Corpus::new();
        let atoms: Vec<_> = (0..3)
            .map(|i| GroundAtom::new(rel(&mut corpus, &format!("a{i}"), false), []))
            .collect();
        let limits = Limits::default();
        // All 729 signed directed graphs without self edges on three vertices.
        for shape in 0..729 {
            let mut code = shape;
            let mut edges = vec![Vec::new(); 3];
            let mut rules = Vec::new();
            for i in 0..3 {
                for j in 0..3 {
                    if i != j {
                        let sign = code % 3;
                        code /= 3;
                        if sign > 0 {
                            edges[i].push((i, j, sign == 2));
                            rules.push(crate::sat_probe::Rule {
                                source: None,
                                head: i,
                                body: vec![(j, sign == 1)],
                            });
                        }
                    }
                }
            }
            let c = Cone {
                atoms: atoms.clone().into(),
                rules: rules.into(),
                fixed: vec![None; 3],
                input: vec![false; 3].into(),
                target: vec![true; 3].into(),
                duplicated: vec![false; 3].into(),
                groups: vec![].into(),
                source_rules: 0,
            };
            let mut b = Budget::new(&limits);
            let core = consistency::analyse(&c, None, &mut b).unwrap();
            // Independent enumeration of simple cycles.
            let expected = (0..3).any(|i| {
                edges[i].iter().any(|a| {
                    edges[a.1].iter().any(|d| {
                        (d.1 == i && a.2 != d.2)
                            || edges[d.1]
                                .iter()
                                .any(|f| d.1 != i && f.1 == i && (a.2 ^ d.2 ^ f.2))
                    })
                })
            });
            assert_eq!(core.odd_components > 0, expected, "shape {shape}");
            for seed in core.conflicts {
                let mut cycle = shortest_return(seed, &edges, &mut b)
                    .unwrap()
                    .expect("odd SCC has an odd return walk");
                simplify_walk(&mut cycle, &mut b).unwrap();
                valid(&cycle, &edges);
            }
        }
    }
    #[test]
    fn parallel_producers_keep_exact_sources_and_own_guard_inputs() {
        let mut c = denotate_ir::Corpus::new();
        let p = rel(&mut c, "p", false);
        let x = rel(&mut c, "x", true);
        let y = rel(&mut c, "y", true);
        rule(&mut c, p, &[(p, true), (x, false)]);
        rule(&mut c, p, &[(p, true), (y, false)]);
        // The test helper's true flag means a negated literal.
        let sources: BTreeSet<_> = c.rules().map(|r| r.id).collect();
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &crate::Domains::new());
        let mut b = Budget::new(&e.limits);
        let core = consistency::analyse(&e.cone, None, &mut b).unwrap();
        let mut out = crate::CompletionOddExplanation::default();
        build(&e, &e.cone, &core, &mut out, &mut b).unwrap();
        assert_eq!(out.found, 1);
        let edge = &out.cycles[0][0];
        assert!(edge.negative);
        assert_eq!(edge.producer_count, 2);
        assert_eq!(
            edge.producers
                .iter()
                .filter_map(|p| p.source)
                .collect::<BTreeSet<_>>(),
            sources
        );
        assert!(
            edge.producers
                .iter()
                .all(|p| p.guards.len() == 1 && !p.guards[0].1)
        );
        assert_eq!(out.input_groups.len(), 2);
        assert_eq!(out.negative_relations[&(p, p)], 2);
    }
    #[test]
    fn explanation_cutoff_is_advisory_and_does_not_charge_query() {
        let mut c = denotate_ir::Corpus::new();
        let p = rel(&mut c, "p", false);
        rule(&mut c, p, &[(p, true)]);
        let v = verification(&mut c, None, &[]);
        let mut e = prepare(&c, v, &crate::Domains::new());
        let limits = e.limits.clone();
        let mut b = Budget::new(&limits);
        let core = consistency::analyse(&e.cone, None, &mut b).unwrap();
        assert!(explain(&e, &e.cone, Some(&core), &mut b).is_none());
        e.limits.completion_sizes = Some(crate::CompletionSizes::default());
        e.limits.max_work = 0;
        let before = b.used();
        let out = explain(&e, &e.cone, Some(&core), &mut b).unwrap();
        assert!(out.incomplete.is_some());
        assert_eq!(before, b.used());
        assert!(!out.histograms_complete);
    }
    #[test]
    fn long_cycles_are_omitted_whole_and_producers_and_guards_are_bounded() {
        let mut c = denotate_ir::Corpus::new();
        let ps: Vec<_> = (0..129)
            .map(|i| rel(&mut c, &format!("p{i}"), false))
            .collect();
        for i in 0..ps.len() {
            rule(&mut c, ps[i], &[(ps[(i + 1) % ps.len()], i == 0)]);
        }
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &crate::Domains::new());
        let mut b = Budget::new(&e.limits);
        let core = consistency::analyse(&e.cone, None, &mut b).unwrap();
        let mut out = crate::CompletionOddExplanation::default();
        build(&e, &e.cone, &core, &mut out, &mut b).unwrap();
        assert_eq!(out.found, 1);
        assert_eq!(out.omitted_cycles, 1);
        assert!(out.cycles.is_empty());
        let mut c = denotate_ir::Corpus::new();
        let p = rel(&mut c, "p", false);
        let inputs: Vec<_> = (0..20)
            .map(|i| rel(&mut c, &format!("i{i}"), true))
            .collect();
        let body: Vec<_> = std::iter::once((p, true))
            .chain(inputs.iter().map(|i| (*i, false)))
            .collect();
        for _ in 0..10 {
            rule(&mut c, p, &body);
        }
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &crate::Domains::new());
        let mut b = Budget::new(&e.limits);
        let core = consistency::analyse(&e.cone, None, &mut b).unwrap();
        let mut out = crate::CompletionOddExplanation::default();
        build(&e, &e.cone, &core, &mut out, &mut b).unwrap();
        let edge = &out.cycles[0][0];
        assert_eq!(edge.producer_count, 10);
        assert_eq!(edge.producers.len(), 8);
        assert!(
            edge.producers
                .iter()
                .all(|p| p.guards.len() == 16 && p.omitted_guards == 4)
        );
    }
    #[test]
    fn caps_distinct_cycles_and_histogram_rows_with_explicit_omissions() {
        let mut c = denotate_ir::Corpus::new();
        for i in 0..40 {
            let p = rel(&mut c, &format!("p{i}"), false);
            let input = rel(&mut c, &format!("i{i}"), true);
            rule(&mut c, p, &[(p, true), (input, false)]);
        }
        let v = verification(&mut c, None, &[]);
        let mut e = prepare(&c, v, &crate::Domains::new());
        e.limits.completion_sizes = Some(crate::CompletionSizes::default());
        let mut b = Budget::new(&e.limits);
        let core = consistency::analyse(&e.cone, None, &mut b).unwrap();
        let out = explain(&e, &e.cone, Some(&core), &mut b).unwrap();
        assert_eq!(out.found, 3);
        assert_eq!(out.odd_components, 40);
        assert_eq!(out.witnessed_components, 3);
        assert!(out.histograms_complete);
        assert_eq!(out.negative_relations.len(), 32);
        assert_eq!(out.input_groups.len(), 32);
        assert_eq!(out.omitted_negative_relations, 8);
        assert_eq!(out.omitted_input_groups, 8);
    }
}
