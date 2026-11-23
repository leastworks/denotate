//! Structural target discovery for optional completion pruning. Never a scope
//! boundary. Local non-uniqueness is checked independently with a free boundary.
use super::super::pruning::{PruningComponent, PruningContext, PruningReport};
use super::*;

pub(in crate::sat_probe::completion_query) struct Targets {
    pub heads: Vec<usize>,
    pub rules: BTreeMap<usize, Vec<usize>>,
    pub components: BTreeMap<usize, usize>,
}
pub(in crate::sat_probe::completion_query) fn discover(
    engine: &Engine,
    cone: &Cone,
    fixed: &[Option<bool>],
    scope: &'static str,
    context: PruningContext,
    report: &mut PruningReport,
    b: &mut Budget<'_>,
) -> Result<Targets> {
    let mut folded = cone.clone();
    folded.fixed = fixed.to_vec();
    let core = consistency::analyse(&folded, None, b)?;
    let mut groups = BTreeMap::<usize, BTreeSet<usize>>::new();
    let mut producers = vec![Vec::new(); fixed.len()];
    let mut edges = vec![Vec::new(); fixed.len()];
    for (ri, r) in cone.rules.iter().enumerate() {
        b.charge(r.body.len() + 1, "completion pruning targets")?;
        if cone.input[r.head]
            || fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        producers[r.head].push(ri);
        for (i, p) in &r.body {
            if !cone.input[*i]
                && fixed[*i].is_none()
                && core.component[*i] == core.component[r.head]
            {
                groups
                    .entry(core.component[r.head])
                    .or_default()
                    .extend([*i, r.head]);
                edges[r.head].push((r.head, *i, !*p));
            }
        }
    }
    for es in &mut edges {
        es.sort_unstable();
        es.dedup();
    }
    let odd_ids: BTreeSet<_> = core
        .conflicts
        .iter()
        .map(|(i, _, _)| core.component[*i])
        .collect();
    let mut selected = Targets {
        heads: vec![],
        rules: BTreeMap::new(),
        components: BTreeMap::new(),
    };
    let mut scores = BTreeMap::new();
    let mut groups: Vec<_> = groups.into_iter().collect();
    groups.sort_by_key(|(id, _)| (!odd_ids.contains(id), *id));
    for (id, heads) in groups {
        let start = Instant::now();
        let row = report.components.len();
        report.components.push(PruningComponent {
            scope,
            context,
            representative: cone.atoms[*heads.first().unwrap()].clone(),
            atoms: heads.len(),
            rules: heads.iter().map(|h| producers[*h].len()).sum(),
            kind: "analysing",
            discovery_complete: false,
            candidate_heads: 0,
            candidate_examples: vec![],
            candidate_producers: 0,
            considered: 0,
            proved: 0,
            removed: 0,
            last_head: None,
            cutoff: None,
            elapsed: Duration::ZERO,
        });
        let processing: Result<()> = (|| {
            let qualifies = if odd_ids.contains(&id) {
                report.components[row].kind = "odd";
                true
            } else {
                let local = existence::component(&folded, &producers, &heads, b)?;
                let mut run = queries::Run::local(engine, b)?;
                run.label("completion pruning local uniqueness");
                let (unique, _, _, _) = run.local_unique(&local, |_, _| {});
                let unique = unique?;
                report.components[row].kind = if unique { "unique" } else { "non-unique" };
                !unique
            };
            if !qualifies {
                report.components[row].discovery_complete = true;
                return Ok(());
            }
            // Same parity-doubled BFS and simple-cycle reduction as 024.30, used
            // independently of whether diagnostic collection is enabled.
            let mut witness = BTreeSet::new();
            for seed in core
                .conflicts
                .iter()
                .filter(|(i, _, _)| core.component[*i] == id)
                .take(3)
            {
                if let Some(mut cycle) = odd::shortest_return(*seed, &edges, b)? {
                    odd::simplify_walk(&mut cycle, b)?;
                    witness.extend(cycle);
                }
            }
            // Negative-edge relation histogram prioritizes guards on the reported
            // cycles. It is structural guidance, never proof of dispensability.
            let mut negative = BTreeMap::new();
            for h in &heads {
                for ri in &producers[*h] {
                    b.charge(cone.rules[*ri].body.len() + 1, "completion pruning rank")?;
                    for (i, p) in &cone.rules[*ri].body {
                        if !*p && heads.contains(i) && fixed[*i].is_none() {
                            *negative
                                .entry((cone.atoms[*h].relation, cone.atoms[*i].relation))
                                .or_insert(0usize) += 1;
                        }
                    }
                }
            }
            for head in &heads {
                b.charge(
                    producers[*head].len() + edges[*head].len() + 1,
                    "completion pruning rank",
                )?;
                let rs: Vec<_> = producers[*head]
                    .iter()
                    .copied()
                    .filter(|ri| {
                        cone.rules[*ri]
                            .body
                            .iter()
                            .any(|(i, _)| heads.contains(i) && fixed[*i].is_none())
                    })
                    .collect();
                if rs.is_empty() {
                    continue;
                }
                let mut ranked = rs;
                ranked.sort_by_key(|ri| {
                    let hits = cone.rules[*ri]
                        .body
                        .iter()
                        .filter(|(i, p)| witness.contains(&(*head, *i, !*p)))
                        .count();
                    (std::cmp::Reverse(hits), *ri)
                });
                let hits = edges[*head].iter().filter(|e| witness.contains(e)).count();
                let weight: usize = edges[*head]
                    .iter()
                    .filter(|e| e.2)
                    .map(|e| negative[&(cone.atoms[e.0].relation, cone.atoms[e.1].relation)])
                    .sum();
                scores.insert(
                    *head,
                    (
                        producers[*head].len() < 2,
                        std::cmp::Reverse(hits),
                        std::cmp::Reverse(weight),
                        *head,
                    ),
                );
                report.components[row].candidate_heads += 1;
                report.components[row].candidate_producers += ranked.len();
                selected.rules.insert(*head, ranked);
                selected.components.insert(*head, row);
                selected.heads.push(*head);
            }
            report.components[row].discovery_complete = true;
            Ok(())
        })();
        report.components[row].elapsed += start.elapsed();
        if let Err(e) = processing {
            engine.limits.cancellation.check()?;
            let cause = inconclusive(e)?;
            if report.components[row].kind == "analysing" {
                report.components[row].kind = "incomplete";
            }
            report.components[row].cutoff = Some(cause);
            if report.incomplete.len() < 64 {
                report.incomplete.push(cause);
            }
            break;
        }
    }
    selected.heads.sort_by_key(|h| scores[h]);
    for h in &selected.heads {
        let row = &mut report.components[selected.components[h]];
        if row.candidate_examples.len() < 16 {
            row.candidate_examples.push(cone.atoms[*h].clone());
        }
    }
    Ok(selected)
}
