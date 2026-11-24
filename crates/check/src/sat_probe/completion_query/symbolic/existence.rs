//! Component totality is sufficient, never necessary. A failed local boundary
//! assignment may be unreachable: only the subsequent upstream-cone search may
//! report no meaning. Positive SCCs always extend their providers by a fixpoint.
use super::*;

/// Analysis components belong to the current solver view, never the frozen
/// preparation graph. Semantic classification/property membership stays frozen.
fn components(c: &Cone, b: &mut Budget<'_>) -> Result<(Vec<Vec<usize>>, Vec<BTreeSet<usize>>)> {
    let graph = consistency::analyse(c, None, b)?;
    let mut producers = vec![vec![]; c.fixed.len()];
    for (ri, r) in c.rules.iter().enumerate() {
        b.charge(r.body.len() + 1, "completion component index")?;
        if c.input[r.head]
            || c.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        producers[r.head].push(ri);
    }
    let mut groups = BTreeMap::<usize, BTreeSet<usize>>::new();
    for (i, id) in graph.component.iter().enumerate() {
        b.tick("completion component index")?;
        if graph.cyclic[i] {
            groups.entry(*id).or_default().insert(i);
        }
    }
    Ok((producers, groups.into_values().collect()))
}

pub(super) fn residual(
    engine: &Engine,
    cone: &Cone,
    view: &'static str,
    classification: bool,
    s: &mut Solver<'_, '_, '_>,
    options: &CheckOptions,
) -> Result<Option<Cone>> {
    let (producers, mut components) = components(cone, s.run.budget)?;
    let mut pending = Vec::new();
    if !classification {
        if let Some((_, members, _)) = &engine.classification {
            components.retain(|heads| !heads.iter().all(|i| members.contains(&cone.atoms[*i])));
        }
    }
    s.stats.components = components.len();
    s.metrics();
    for heads in components {
        let local = component(cone, &producers, &heads, s.run.budget)?;
        let mut detail = crate::CompletionComponentStats {
            scope: if classification {
                "classification"
            } else if engine.hypothesis.is_some() {
                "processing"
            } else {
                "whole-program"
            },
            context: if !classification && engine.hypothesis.is_some() {
                "W + H"
            } else {
                "W"
            },
            view,
            index: s.stats.total_components + s.stats.fallback_components,
            atoms: heads.len(),
            rules: local.rules.len(),
            boundary: local.input.iter().filter(|v| **v).count(),
            relations: local
                .atoms
                .iter()
                .enumerate()
                .filter(|(i, _)| !local.input[*i])
                .map(|(_, a)| a.relation)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .take(32)
                .collect(),
            relation_count: local
                .atoms
                .iter()
                .enumerate()
                .filter(|(i, _)| !local.input[*i])
                .map(|(_, a)| a.relation)
                .collect::<BTreeSet<_>>()
                .len(),
            state: "analysing",
            ..Default::default()
        };
        s.stats.current_component = Some(detail.clone());
        s.metrics();
        let core = consistency::analyse(&local, None, s.run.budget)?;
        detail.odd_components = core.odd_components;
        detail.odd_atoms = core.odd_atoms;
        detail.odd_explanation = odd::explain(engine, &local, Some(&core), s.run.budget);
        detail.state = "searching";
        s.stats.current_component = Some(detail.clone());
        s.metrics();
        let result = if core.odd_components == 0 {
            Ok(true)
        } else {
            // Compact the odd-cycle cores and their providers; discard total
            // downstream equations before model enumeration and cube building.
            let mut local_producers = vec![Vec::new(); local.fixed.len()];
            for (i, r) in local.rules.iter().enumerate() {
                local_producers[r.head].push(i);
            }
            let needed = core
                .needed
                .iter()
                .enumerate()
                .filter_map(|(i, v)| (*v).then_some(i))
                .collect();
            let reduced = component(&local, &local_producers, &needed, s.run.budget)?;
            total(&reduced, s, options)
        };
        detail.state = match &result {
            Ok(true) => "total",
            Ok(false) => "requires-upstream-search",
            Err(_) => "incomplete",
        };
        s.stats.current_component = Some(detail.clone());
        if s.stats.component_details.len() < 64 {
            s.stats.component_details.push(detail);
        } else {
            s.stats.omitted_components += 1;
        }
        s.metrics();
        if result? {
            s.stats.total_components += 1;
        } else {
            s.stats.fallback_components += 1;
            pending.extend(core.needed.iter().enumerate().filter_map(|(i, needed)| {
                needed.then(|| engine.program.atom_index[&local.atoms[i]])
            }));
        }
        s.metrics();
    }
    if pending.is_empty() {
        return Ok(None);
    }
    // All discarded SCCs are total for *every* provider assignment. Retaining
    // the failing SCCs and every upstream dependency therefore preserves
    // existence in both directions. H's cone stays intact for processing.
    if !classification {
        if let Some((_, members, _)) = &engine.classification {
            pending.extend(
                members
                    .iter()
                    .filter_map(|a| engine.program.atom_index.get(a).copied()),
            );
        }
    }
    let mut needed = vec![false; cone.fixed.len()];
    while let Some(i) = pending.pop() {
        s.run.budget.tick("completion existence cone")?;
        if needed[i] {
            continue;
        }
        needed[i] = true;
        for r in &producers[i] {
            s.run
                .budget
                .charge(cone.rules[*r].body.len(), "completion existence cone")?;
            pending.extend(cone.rules[*r].body.iter().map(|(a, _)| *a));
        }
    }
    // Global indices are kept for W/H; irrelevant equations become false. Local
    // totality validation above uses genuinely compact arrays.
    let mut result = cone.clone();
    result.rules.retain(|r| needed[r.head]);
    Ok(Some(result))
}

pub(super) fn component(
    c: &Cone,
    producers: &[Vec<usize>],
    heads: &BTreeSet<usize>,
    b: &mut Budget<'_>,
) -> Result<Cone> {
    let rules: Vec<_> = heads
        .iter()
        .flat_map(|h| producers[*h].iter().copied())
        .collect();
    let mut members = heads.clone();
    for r in &rules {
        b.charge(c.rules[*r].body.len() + 1, "completion component cone")?;
        members.extend(c.rules[*r].body.iter().map(|(i, _)| *i));
    }
    let index: BTreeMap<_, _> = members.iter().enumerate().map(|(j, i)| (*i, j)).collect();
    Ok(Cone {
        atoms: members
            .iter()
            .filter_map(|i| c.atoms.get(*i).cloned())
            .collect(),
        rules: rules
            .iter()
            .map(|r| crate::sat_probe::Rule {
                ground: None,
                source: c.rules[*r].source,
                head: index[&c.rules[*r].head],
                body: c.rules[*r]
                    .body
                    .iter()
                    .map(|(i, p)| (index[i], *p))
                    .collect(),
            })
            .collect(),
        fixed: members.iter().map(|i| c.fixed[*i]).collect(),
        input: members
            .iter()
            .map(|i| !heads.contains(i) || c.input[*i])
            .collect(),
        target: vec![true; members.len()].into(),
        duplicated: vec![false; members.len()].into(),
        groups: vec![].into(),
        source_rules: rules.len(),
    })
}

fn total(c: &Cone, s: &mut Solver<'_, '_, '_>, options: &CheckOptions) -> Result<bool> {
    if consistency::analyse(c, None, s.run.budget)?.odd_components == 0 {
        return Ok(true);
    }
    let gate = s.gate()?;
    s.run.cnf.gate = Some(gate);
    // Boundary atoms are independent variables, even when they name derived
    // providers. No W, H or other component equation constrains those variables.
    let encoding = encoding::encode_named(
        c,
        &mut s.run.cnf,
        s.run.truth,
        None,
        s.run.budget,
        "component-totality",
    )?;
    s.run.cnf.gate = None;
    let target = Encoded { gate, encoding };
    let selector = s.gate()?;
    loop {
        if !s.solve(&[selector], &[])? {
            return Ok(true);
        }
        s.run.budget.room(
            s.stats.rounds,
            options.max_worlds,
            "completion component existence",
            "worlds",
        )?;
        s.stats.rounds += 1;
        s.metrics();
        let pins: Vec<_> = c
            .input
            .iter()
            .enumerate()
            .filter(|(_, v)| **v)
            .map(|(i, _)| {
                let l = target.encoding.vars[i];
                if s.run.cnf.solver.value_lit(l) == lbool::TRUE {
                    l
                } else {
                    !l
                }
            })
            .collect();
        if !s.solve(&[target.gate], &pins)? {
            return Ok(false);
        }
        let values = s.values(c, &target)?;
        let mut cube = cover(c, &values, None, s.run.budget)?;
        if !cube.is_empty() {
            let specialized = consistency::analyse(c, Some(&values), s.run.budget)?;
            let mut structural = false;
            if specialized.odd_components == 0 {
                let guards = consistency::guard_cube(c, &values, &specialized, s.run.budget)?;
                if guards.len() < cube.len() {
                    cube = guards;
                    structural = true;
                }
            }
            // Equation lifting fixes derived values. Structural cubes allow
            // models to vary, so cannot go through that lifting query.
            if !structural {
                lift(c, &values, &target, &mut cube, s)?;
            }
        }
        s.cube_metrics(&cube);
        s.run.cnf.gate = Some(selector);
        let clause = cube
            .iter()
            .map(|(i, v)| {
                if *v {
                    !target.encoding.vars[*i]
                } else {
                    target.encoding.vars[*i]
                }
            })
            .collect();
        s.run.cnf.clause(clause, s.run.budget)?;
        s.run.cnf.gate = None;
    }
}

/// Existential models can be generalized without fixing every input used by the
/// first producer. Hold derived values fixed and ask whether *any original
/// equation* can be violated after dropping a pin. UNSAT alone permits removal.
/// The deterministic 64-attempt cap bounds optional block lifting; retaining a pin is
/// always sound. Required search/solver allowances still charge every operation.
pub(super) fn lift(
    c: &Cone,
    values: &[bool],
    target: &Encoded,
    cube: &mut Cube,
    s: &mut Solver<'_, '_, '_>,
) -> Result<()> {
    if cube.is_empty() {
        return Ok(());
    }
    let gate = s.gate()?;
    s.run.cnf.gate = Some(gate);
    let mut bodies = vec![Vec::new(); c.fixed.len()];
    for r in &c.rules {
        s.run
            .budget
            .charge(r.body.len() + 1, "completion cube lifting")?;
        if c.input[r.head] || c.fixed[r.head].is_some() {
            continue;
        }
        if r.body
            .iter()
            .any(|(i, p)| (!c.input[*i] || c.fixed[*i].is_some()) && values[*i] != *p)
        {
            continue;
        }
        let lits: Vec<_> = r
            .body
            .iter()
            .filter(|(i, _)| c.input[*i] && c.fixed[*i].is_none())
            .map(|(i, p)| {
                if *p {
                    target.encoding.vars[*i]
                } else {
                    !target.encoding.vars[*i]
                }
            })
            .collect();
        let body = if lits.is_empty() {
            s.run.truth
        } else {
            s.run.cnf.and(&lits, s.run.budget)?
        };
        bodies[r.head].push(body);
    }
    let mut bad = Vec::new();
    for (i, bodies) in bodies.iter().enumerate() {
        if c.input[i] || c.fixed[i].is_some() {
            continue;
        }
        let produced = if bodies.is_empty() {
            !s.run.truth
        } else {
            s.run.cnf.or(bodies, s.run.budget)?
        };
        bad.push(if values[i] { !produced } else { produced });
    }
    s.run.cnf.clause(bad, s.run.budget)?;
    s.run.cnf.gate = None;
    // Try large deletions first. The same 64 SAT-attempt allowance can
    // eliminate thousands of irrelevant pins instead of only the first 64.
    let keys: Vec<_> = cube.keys().copied().collect();
    let mut pending = vec![(0, keys.len())];
    let mut attempts = 0;
    while let Some((start, end)) = pending.pop() {
        if attempts == 64 {
            break;
        }
        let low = keys[start];
        let high = keys[end - 1];
        if cube.range(low..=high).next().is_none() {
            continue;
        }
        let pins: Vec<_> = cube
            .iter()
            .filter(|(i, _)| **i < low || **i > high)
            .map(|(i, v)| {
                if *v {
                    target.encoding.vars[*i]
                } else {
                    !target.encoding.vars[*i]
                }
            })
            .collect();
        attempts += 1;
        s.stats.lifting_attempts += 1;
        if !s.solve(&[gate], &pins)? {
            let before = cube.len();
            cube.retain(|i, _| *i < low || *i > high);
            s.stats.lifted_pins += before - cube.len();
        } else if end - start > 1 {
            let middle = start + (end - start) / 2;
            pending.push((middle, end));
            pending.push((start, middle));
        }
        s.metrics();
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_probe::completion_query::tests::{prepare, verification};
    use crate::test_support::rewrites::{rel, rule};
    #[test]
    fn totality_with_lifting_matches_exhaustive_boundary_assignments() {
        for left in 0..8 {
            for right in 0..8 {
                let mut c = denotate_ir::Corpus::new();
                let i = rel(&mut c, "i", true);
                let j = rel(&mut c, "j", true);
                let p = rel(&mut c, "p", false);
                let q = rel(&mut c, "q", false);
                let atoms = [i, j, p, q];
                rule(&mut c, p, &[(atoms[left / 2], left % 2 != 0)]);
                rule(&mut c, q, &[(atoms[right / 2], right % 2 != 0)]);
                rule(&mut c, p, &[(i, false), (j, true)]);
                let v = verification(&mut c, None, &[]);
                let e = prepare(&c, v, &crate::Domains::new());
                let cone = &e.cone;
                let mut b = Budget::new(&e.limits);
                let mut s = Solver::new(&e, &mut b).unwrap();
                let result = total(cone, &mut s, &CheckOptions::default()).unwrap();
                let n = cone.fixed.len();
                let inputs: Vec<_> = cone
                    .input
                    .iter()
                    .enumerate()
                    .filter_map(|(i, v)| (*v && cone.fixed[i].is_none()).then_some(i))
                    .collect();
                let expected = (0..1usize << inputs.len()).all(|world| {
                    (0..1usize << n).any(|bits| {
                        let values: Vec<_> = (0..n).map(|i| bits & (1 << i) != 0).collect();
                        inputs
                            .iter()
                            .enumerate()
                            .all(|(j, i)| values[*i] == (world & (1 << j) != 0))
                            && (0..n).all(|i| {
                                if let Some(f) = cone.fixed[i] {
                                    values[i] == f
                                } else {
                                    cone.input[i]
                                        || values[i]
                                            == cone.rules.iter().any(|r| {
                                                r.head == i
                                                    && r.body
                                                        .iter()
                                                        .all(|(j, pos)| values[*j] == *pos)
                                            })
                                }
                            })
                    })
                });
                assert_eq!(result, expected, "{left}, {right}");
            }
        }
    }
}

#[cfg(test)]
mod parity_oracle {
    use super::*;
    use crate::sat_probe::completion_query::tests::{prepare, verification};
    use crate::test_support::rewrites::{rel, rule};
    #[test]
    fn signed_three_atom_equations_match_exhaustive_totality_and_guard_cubes() {
        let mut corpus = denotate_ir::Corpus::new();
        let input = rel(&mut corpus, "input", true);
        let ids: Vec<_> = ["a", "b", "c"]
            .iter()
            .map(|n| rel(&mut corpus, n, false))
            .collect();
        for id in &ids {
            rule(&mut corpus, *id, &[(*id, false)]);
        }
        let v = verification(&mut corpus, None, &[]);
        let e = prepare(&corpus, v, &crate::Domains::new());
        let index = |r| e.cone.atoms.iter().position(|a| a.relation == r).unwrap();
        let input = index(input);
        let heads: Vec<_> = ids.into_iter().map(index).collect();
        let all: Vec<_> = std::iter::once(input)
            .chain(heads.iter().copied())
            .collect();
        for shape in 0..512usize {
            let mut c = e.cone.as_ref().clone();
            c.rules.clear();
            for (k, head) in heads.iter().enumerate() {
                let literal = (shape >> (3 * k)) & 7;
                c.rules.push(crate::sat_probe::Rule {
                    ground: None,
                    source: None,
                    head: *head,
                    body: vec![(all[literal / 2], literal % 2 == 0)],
                });
            }
            // Multiple producers and a guarded odd cycle, not only unary rings.
            c.rules.push(crate::sat_probe::Rule {
                ground: None,
                source: None,
                head: heads[0],
                body: vec![(input, true), (heads[2], false)],
            });
            let mut b = Budget::new(&e.limits);
            let proof = consistency::analyse(&c, None, &mut b).unwrap();
            let mut every = true;
            for input_value in [false, true] {
                let mut values = vec![false; c.fixed.len()];
                values[input] = input_value;
                let exists = (0..8).any(|bits| {
                    for (k, h) in heads.iter().enumerate() {
                        values[*h] = bits & (1 << k) != 0;
                    }
                    heads.iter().all(|h| {
                        values[*h]
                            == c.rules.iter().any(|r| {
                                r.head == *h && r.body.iter().all(|(i, p)| values[*i] == *p)
                            })
                    })
                });
                every &= exists;
                let specialized = consistency::analyse(&c, Some(&values), &mut b).unwrap();
                if specialized.odd_components == 0 {
                    assert!(exists, "shape {shape}, input {input_value}");
                    let cube = consistency::guard_cube(&c, &values, &specialized, &mut b).unwrap();
                    for other in [false, true] {
                        if cube.get(&input).is_some_and(|v| *v != other) {
                            continue;
                        }
                        values[input] = other;
                        assert_eq!(
                            consistency::analyse(&c, Some(&values), &mut b)
                                .unwrap()
                                .odd_components,
                            0
                        );
                    }
                }
            }
            if proof.odd_components == 0 {
                assert!(every, "shape {shape}");
            }
            let mut s = Solver::new(&e, &mut b).unwrap();
            assert_eq!(
                total(&c, &mut s, &CheckOptions::default()).unwrap(),
                every,
                "shape {shape}"
            );
        }
    }
}

/// Shape-only records for the H-first classification search. These are not
/// local totality certificates: the subsequent query uses the full C(H).
pub(super) fn classification_shape(
    engine: &Engine,
    cone: &Cone,
    view: &'static str,
    s: &mut Solver<'_, '_, '_>,
) -> Result<()> {
    let (producers, groups) = components(cone, s.run.budget)?;
    for heads in groups {
        let local = component(cone, &producers, &heads, s.run.budget)?;
        let core = consistency::analyse(&local, None, s.run.budget)?;
        let relations: BTreeSet<_> = local
            .atoms
            .iter()
            .enumerate()
            .filter(|(i, _)| !local.input[*i])
            .map(|(_, a)| a.relation)
            .collect();
        let detail = crate::CompletionComponentStats {
            scope: "classification",
            context: "W",
            view,
            index: s.stats.components,
            atoms: heads.len(),
            rules: local.rules.len(),
            boundary: local.input.iter().filter(|b| **b).count(),
            relations: relations.iter().copied().take(32).collect(),
            relation_count: relations.len(),
            odd_components: core.odd_components,
            odd_atoms: core.odd_atoms,
            odd_explanation: odd::explain(engine, &local, Some(&core), s.run.budget),
            query: "hypothesis-model-coverage",
            state: "pending",
            ..Default::default()
        };
        s.stats.components += 1;
        s.stats.current_component = Some(detail.clone());
        if s.stats.component_details.len() < 64 {
            s.stats.component_details.push(detail);
        } else {
            s.stats.omitted_components += 1;
        }
        s.metrics();
    }
    Ok(())
}
