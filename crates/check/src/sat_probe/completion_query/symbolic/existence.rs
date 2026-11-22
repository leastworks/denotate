//! Component totality is sufficient, never necessary. A failed local boundary
//! assignment may be unreachable: only the subsequent upstream-cone search may
//! report no meaning. Positive SCCs always extend their providers by a fixpoint.
use super::*;

pub(super) fn residual(
    engine: &Engine,
    cone: &Cone,
    classification: bool,
    s: &mut Solver<'_, '_, '_>,
    options: &CheckOptions,
) -> Result<Option<Cone>> {
    let b = &mut *s.run.budget;
    b.charge(
        cone.fixed.len() + cone.rules.len(),
        "completion component index",
    )?;
    let mut producers = vec![Vec::new(); cone.fixed.len()];
    for (i, r) in cone.rules.iter().enumerate() {
        producers[r.head].push(i);
    }
    let mut pending = Vec::new();
    let mut components = Vec::new();
    for c in engine.program.components() {
        b.tick("completion component index")?;
        if c.cycle.is_none() {
            continue;
        }
        let heads: BTreeSet<_> = c
            .atoms
            .iter()
            .map(|a| engine.program.atom_index[a])
            .filter(|i| !producers[*i].is_empty())
            .collect();
        // An upstream-closed query either contains the entire SCC or none of it.
        if heads.is_empty() {
            continue;
        }
        if !classification
            && engine
                .classification
                .as_ref()
                .is_some_and(|(_, m, _)| c.atoms.iter().all(|a| m.contains(a)))
        {
            continue;
        }
        components.push(heads);
    }
    s.stats.components = components.len();
    s.metrics();
    for heads in components {
        let local = component(cone, &producers, &heads, s.run.budget)?;
        if total(&local, s, options)? {
            s.stats.total_components += 1;
        } else {
            s.stats.fallback_components += 1;
            pending.extend(heads);
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

fn component(
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
        target: vec![true; members.len()],
        duplicated: vec![false; members.len()],
        groups: vec![],
        source_rules: rules.len(),
    })
}

fn total(c: &Cone, s: &mut Solver<'_, '_, '_>, options: &CheckOptions) -> Result<bool> {
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
        lift(c, &values, &target, &mut cube, s)?;
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
/// The deterministic 64-attempt cap bounds optional lifting; retaining a pin is
/// always sound. Required search/solver allowances still charge every operation.
fn lift(
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
    for i in cube.keys().copied().take(64).collect::<Vec<_>>() {
        let pins: Vec<_> = cube
            .iter()
            .filter(|(j, _)| **j != i)
            .map(|(j, v)| {
                if *v {
                    target.encoding.vars[*j]
                } else {
                    !target.encoding.vars[*j]
                }
            })
            .collect();
        s.stats.lifting_attempts += 1;
        if !s.solve(&[gate], &pins)? {
            cube.remove(&i);
            s.stats.lifted_pins += 1;
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
