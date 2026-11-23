//! Completion-preserving substitutions, local to an already-frozen query scope.
//! No W, H, cardinality or downstream equation participates in the Fitting fold.
use super::*;
use std::collections::VecDeque;

pub(super) struct Encoding {
    pub vars: Vec<Lit>,
    pub validation: Option<Validation>,
}

/// Precomputed scope of independent model validation. Omitted slots have the
/// literal false and no producer/constant to check; materialize them as false.
/// Every original rule (including folded rules) is still replayed below.
pub(super) struct Validation {
    pub read: Vec<usize>,
    pub heads: Vec<usize>,
}

pub(super) fn fitting(c: &Cone, b: &mut Budget<'_>) -> Result<Vec<Option<bool>>> {
    b.charge(c.fixed.len() + c.rules.len(), "completion folding")?;
    let mut values = c.fixed.clone();
    let mut readers = vec![Vec::new(); values.len()];
    let mut alive = vec![0usize; values.len()];
    let mut missing = vec![0usize; c.rules.len()];
    let mut dead = vec![false; c.rules.len()];
    let mut queue = VecDeque::new();
    for (j, r) in c.rules.iter().enumerate() {
        b.charge(r.body.len() + 1, "completion folding index")?;
        if r.body
            .iter()
            .any(|(a, positive)| values[*a].is_some_and(|v| v != *positive))
        {
            dead[j] = true;
            continue;
        }
        alive[r.head] += 1;
        for (a, positive) in &r.body {
            if values[*a].is_none() {
                missing[j] += 1;
                readers[*a].push((j, *positive));
            }
        }
        if missing[j] == 0 {
            queue.push_back((r.head, true));
        }
    }
    for (i, count) in alive.iter().enumerate() {
        b.tick("completion folding seeds")?;
        if *count == 0 && !c.input[i] {
            queue.push_back((i, false));
        }
    }
    while let Some((a, value)) = queue.pop_front() {
        b.tick("completion folding propagation")?;
        if c.input[a] || values[a].is_some() {
            continue;
        }
        values[a] = Some(value);
        for (j, positive) in &readers[a] {
            b.tick("completion folding propagation")?;
            if dead[*j] {
                continue;
            }
            let head = c.rules[*j].head;
            if value != *positive {
                dead[*j] = true;
                alive[head] -= 1;
                if alive[head] == 0 {
                    queue.push_back((head, false));
                }
            } else {
                missing[*j] -= 1;
                if missing[*j] == 0 {
                    queue.push_back((head, true));
                }
            }
        }
    }
    Ok(values)
}

/// Hash-consing is scoped to one clause gate. Sharing a gated definition with
/// an independent copy would be unsound when the defining gate is disabled.
pub(super) struct Booleans {
    truth: Lit,
    conjunctions: BTreeMap<Vec<Lit>, Lit>,
}
impl Booleans {
    pub fn new(truth: Lit) -> Self {
        Self {
            truth,
            conjunctions: BTreeMap::new(),
        }
    }
    fn normalized(&self, lits: &[Lit], b: &mut Budget<'_>) -> Result<Option<Vec<Lit>>> {
        b.charge(lits.len() + 1, "completion Boolean normalization")?;
        if lits.contains(&!self.truth) {
            return Ok(None);
        }
        Ok(crate::cnf_measurement::normalize_literals(
            lits.iter().copied().filter(|l| *l != self.truth).collect(),
            |l: Lit| !l,
        ))
    }
    pub fn and(&mut self, lits: &[Lit], cnf: &mut Cnf, b: &mut Budget<'_>) -> Result<Lit> {
        let Some(lits) = self.normalized(lits, b)? else {
            return Ok(!self.truth);
        };
        match lits.as_slice() {
            [] => return Ok(self.truth),
            [l] => return Ok(*l),
            _ => (),
        }
        if let Some(l) = self.conjunctions.get(&lits) {
            return Ok(*l);
        }
        let value = cnf.and(&lits, b)?;
        self.conjunctions.insert(lits, value);
        Ok(value)
    }
    pub fn or(&mut self, lits: &[Lit], cnf: &mut Cnf, b: &mut Budget<'_>) -> Result<Lit> {
        Ok(!self.and(&lits.iter().map(|l| !*l).collect::<Vec<_>>(), cnf, b)?)
    }
    fn clause(&self, lits: Vec<Lit>, cnf: &mut Cnf, b: &mut Budget<'_>) -> Result<()> {
        b.charge(lits.len() + 1, "completion clause normalization")?;
        if lits.contains(&self.truth) {
            return Ok(());
        }
        if let Some(lits) = crate::cnf_measurement::normalize_literals(
            lits.into_iter().filter(|l| *l != !self.truth).collect(),
            |l: Lit| !l,
        ) {
            cnf.clause(lits, b)?;
        }
        Ok(())
    }
}

pub(super) fn encode(
    c: &Cone,
    cnf: &mut Cnf,
    truth: Lit,
    inputs: Option<&[Lit]>,
    b: &mut Budget<'_>,
) -> Result<Encoding> {
    encode_named(c, cnf, truth, inputs, b, "model")
}

pub(super) fn encode_named(
    c: &Cone,
    cnf: &mut Cnf,
    truth: Lit,
    inputs: Option<&[Lit]>,
    b: &mut Budget<'_>,
    purpose: &'static str,
) -> Result<Encoding> {
    encode_shared(c, cnf, truth, inputs, b, purpose, None)
}

/// Shared heads keep the first copy's literal AND its defining gate. The caller
/// must activate that gate whenever this encoding is active. Only share heads
/// whose boundary is shared, or use the result as a restricted witness search.
pub(super) fn encode_shared(
    c: &Cone,
    cnf: &mut Cnf,
    truth: Lit,
    inputs: Option<&[Lit]>,
    b: &mut Budget<'_>,
    purpose: &'static str,
    shared: Option<(&[Lit], &[bool])>,
) -> Result<Encoding> {
    let aliases = |i: usize| shared.is_some_and(|(_, mask)| mask[i]);
    if let Some((_, stats)) = &mut cnf.measurement {
        stats.encodings += 1;
    }
    let before_variables = cnf.solver.num_vars() as usize;
    let before_clauses = cnf.clauses;
    let mut detail = crate::CompletionEncodingSize {
        purpose,
        atoms: c.atoms.len(),
        ..Default::default()
    };
    let result = (|| {
        let fixed = fitting(c, b)?;
        for (i, value) in fixed.iter().take(c.atoms.len()).enumerate() {
            if c.input[i] {
                detail.input_atoms += 1;
            } else {
                match value {
                    Some(true) => detail.folded_true += 1,
                    Some(false) => detail.folded_false += 1,
                    None => (),
                }
            }
        }
        let mut vars = Vec::with_capacity(fixed.len());
        for (i, value) in fixed.iter().enumerate() {
            b.tick("completion encoding")?;
            vars.push(match value {
                Some(true) => truth,
                Some(false) => !truth,
                None if aliases(i) => shared.unwrap().0[i],
                None if c.input[i] && inputs.is_some() => inputs.unwrap()[i],
                None => cnf.var(b)?,
            });
        }
        let mut logic = Booleans::new(truth);
        let mut producers = vec![BTreeSet::new(); vars.len()];
        for r in &c.rules {
            b.charge(r.body.len() + 1, "completion encoding")?;
            if fixed[r.head].is_some() || aliases(r.head) {
                continue;
            }
            let lits = r
                .body
                .iter()
                .map(|(a, pos)| if *pos { vars[*a] } else { !vars[*a] })
                .collect::<Vec<_>>();
            if let Some(body) = logic.normalized(&lits, b)? {
                producers[r.head].insert(body);
            }
        }
        for (i, bodies) in producers.into_iter().enumerate() {
            b.tick("completion encoding equations")?;
            if c.input[i] || fixed[i].is_some() || aliases(i) {
                continue;
            }
            if bodies.len() == 1 {
                // The measure_cnf single-definition reduction: resolve away the
                // private body register directly. All named query targets survive.
                let body = bodies.into_iter().next().unwrap();
                for l in &body {
                    logic.clause(vec![!vars[i], *l], cnf, b)?;
                }
                logic.clause(
                    std::iter::once(vars[i])
                        .chain(body.into_iter().map(|l| !l))
                        .collect(),
                    cnf,
                    b,
                )?;
            } else {
                let mut terms = Vec::new();
                for body in bodies {
                    let term = logic.and(&body, cnf, b)?;
                    logic.clause(vec![!term, vars[i]], cnf, b)?;
                    terms.push(term);
                }
                logic.clause(std::iter::once(!vars[i]).chain(terms).collect(), cnf, b)?;
            }
        }
        for (kind, group) in &c.groups {
            b.charge(group.len() + 1, "completion encoding groups")?;
            let lits = group.iter().map(|i| vars[*i]).collect::<Vec<_>>();
            if kind.has_coverage() {
                logic.clause(lits.clone(), cnf, b)?;
            }
            if kind.has_uniqueness() {
                cnf.at_most_one(&lits, b)?;
            }
            if *kind == Cardinality::Empty {
                for l in lits {
                    logic.clause(vec![!l], cnf, b)?;
                }
            }
        }
        let mut heads: BTreeSet<_> = c.rules.iter().map(|r| r.head).collect();
        heads.extend(
            c.fixed
                .iter()
                .enumerate()
                .filter_map(|(i, v)| v.is_some().then_some(i)),
        );
        let read = vars
            .iter()
            .enumerate()
            .filter_map(|(i, l)| (*l != !truth).then_some(i))
            .collect();
        b.charge(vars.len() + c.rules.len(), "completion validation index")?;
        Ok(Encoding {
            vars,
            validation: Some(Validation {
                read,
                heads: heads.into_iter().collect(),
            }),
        })
    })();
    if let Some((_, stats)) = &mut cnf.measurement {
        detail.complete = result.is_ok();
        detail.variables = (cnf.solver.num_vars() as usize).saturating_sub(before_variables);
        detail.clauses = cnf.clauses.saturating_sub(before_clauses);
        if stats.encoding_details.len() < 64 {
            stats.encoding_details.push(detail);
        } else {
            stats.omitted_encodings += 1;
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::super::tests::{prepare, verification};
    use super::*;
    use crate::test_support::rewrites::{rel, rule};

    fn assignments(engine: &Engine, folded: bool) -> BTreeSet<Vec<bool>> {
        let mut budget = Budget::new(&engine.limits);
        let mut run = queries::Run::universe(engine, &mut budget).unwrap();
        let c = &engine.cone;
        let vars = if folded {
            encode(
                c,
                &mut run.cnf,
                run.truth,
                Some(&run.world.vars),
                run.budget,
            )
            .unwrap()
            .vars
        } else {
            existence::encode(
                c,
                &mut run.cnf,
                run.truth,
                Some(&run.world.vars),
                run.budget,
            )
            .unwrap()
            .vars
        };
        let mut found = BTreeSet::new();
        for bits in 0..(1usize << c.atoms.len()) {
            let pins: Vec<_> = vars
                .iter()
                .take(c.atoms.len())
                .enumerate()
                .map(|(i, l)| if bits & (1 << i) != 0 { *l } else { !*l })
                .collect();
            if run.solve(&pins).unwrap() {
                let values = queries::checked_assignment(
                    c,
                    &Encoding {
                        vars: vars.clone(),
                        validation: None,
                    },
                    &run.cnf,
                    run.budget,
                )
                .unwrap();
                found.insert(values[..c.atoms.len()].to_vec());
            }
        }
        found
    }

    #[test]
    fn folded_and_unfolded_equations_have_identical_models() {
        // Empty definitions, facts, both polarities, self-support, contradictions,
        // duplicate premises and multiple producers; all inputs stay free.
        for left in 0..10 {
            for right in 0..10 {
                let mut c = Corpus::new();
                let input = rel(&mut c, "input", true);
                let p = rel(&mut c, "p", false);
                let q = rel(&mut c, "q", false);
                for (head, other, kind) in [(p, q, left), (q, p, right)] {
                    match kind {
                        0 => (),
                        1 => {
                            rule(&mut c, head, &[]);
                        }
                        2 => {
                            rule(&mut c, head, &[(input, false)]);
                        }
                        3 => {
                            rule(&mut c, head, &[(input, true)]);
                        }
                        4 => {
                            rule(&mut c, head, &[(other, false)]);
                        }
                        5 => {
                            rule(&mut c, head, &[(other, true)]);
                        }
                        6 => {
                            rule(&mut c, head, &[(head, false)]);
                        }
                        7 => {
                            rule(&mut c, head, &[(head, true)]);
                        }
                        8 => {
                            rule(
                                &mut c,
                                head,
                                &[(input, false), (input, false), (other, true)],
                            );
                        }
                        _ => {
                            rule(&mut c, head, &[(input, false)]);
                            rule(&mut c, head, &[(other, true)]);
                        }
                    }
                }
                let v = verification(&mut c, None, &[]);
                let engine = prepare(&c, v, &Domains::new());
                assert_eq!(
                    assignments(&engine, true),
                    assignments(&engine, false),
                    "{left}, {right}"
                );
            }
        }
    }

    #[test]
    fn fitting_preserves_unknown_inputs_and_unseeded_positive_recursion() {
        let mut c = Corpus::new();
        let input = rel(&mut c, "input", true);
        let p = rel(&mut c, "p", false);
        let fact = rel(&mut c, "fact", false);
        let no = rel(&mut c, "no", false);
        let yes = rel(&mut c, "yes", false);
        rule(&mut c, p, &[(p, false)]);
        rule(&mut c, fact, &[]);
        rule(&mut c, no, &[(fact, true)]);
        rule(&mut c, yes, &[(no, true)]);
        let v = verification(&mut c, Some(p), &[]);
        let e = prepare(&c, v, &Domains::new());
        let values = fitting(&e.cone, &mut Budget::new(&e.limits)).unwrap();
        for (r, expected) in [
            (input, None),
            (p, None),
            (fact, Some(true)),
            (no, Some(false)),
            (yes, Some(true)),
        ] {
            let i = e.cone.atoms.iter().position(|a| a.relation == r).unwrap();
            assert_eq!(values[i], expected);
        }
    }

    #[test]
    fn gated_copies_do_not_share_conditional_definitions() {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let p = rel(&mut c, "p", false);
        rule(&mut c, p, &[(i, false)]);
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &Domains::new());
        let mut budget = Budget::new(&e.limits);
        let mut run = queries::Run::universe(&e, &mut budget).unwrap();
        let ga = run.cnf.var(run.budget).unwrap();
        run.cnf.gate = Some(ga);
        let a = encode(
            &e.cone,
            &mut run.cnf,
            run.truth,
            Some(&run.world.vars),
            run.budget,
        )
        .unwrap();
        let gb = run.cnf.var(run.budget).unwrap();
        run.cnf.gate = Some(gb);
        let b = encode(
            &e.cone,
            &mut run.cnf,
            run.truth,
            Some(&run.world.vars),
            run.budget,
        )
        .unwrap();
        run.cnf.gate = None;
        let pi = e.cone.atoms.iter().position(|a| a.relation == p).unwrap();
        let ii = e.cone.atoms.iter().position(|a| a.relation == i).unwrap();
        assert!(
            run.solve(&[!ga, gb, !a.vars[ii], a.vars[pi], !b.vars[pi]])
                .unwrap()
        );
        assert!(!run.solve(&[ga, gb, !a.vars[ii], a.vars[pi]]).unwrap());
    }
    #[test]
    fn fact_heavy_encoding_reports_sizes_against_unfolded_and_stable_cnf() {
        let mut c = Corpus::new();
        let inputs: Vec<_> = (0..16)
            .map(|i| rel(&mut c, &format!("i{i}"), true))
            .collect();
        let facts: Vec<_> = (0..512)
            .map(|i| {
                let f = rel(&mut c, &format!("f{i}"), false);
                rule(&mut c, f, &[]);
                f
            })
            .collect();
        for i in 0..128 {
            let head = rel(&mut c, &format!("p{i}"), false);
            rule(
                &mut c,
                head,
                &[
                    (inputs[i % 16], false),
                    (inputs[(i + 1) % 16], true),
                    (facts[i], false),
                ],
            );
            rule(
                &mut c,
                head,
                &[(inputs[(i + 1) % 16], false), (facts[i], false)],
            );
        }
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &Domains::new());
        let measure = |folded| {
            let mut budget = Budget::new(&e.limits);
            let mut run = queries::Run::universe(&e, &mut budget).unwrap();
            let before = (run.cnf.solver.num_vars(), run.cnf.clauses);
            if folded {
                encode(
                    &e.cone,
                    &mut run.cnf,
                    run.truth,
                    Some(&run.world.vars),
                    run.budget,
                )
                .unwrap();
            } else {
                existence::encode(
                    &e.cone,
                    &mut run.cnf,
                    run.truth,
                    Some(&run.world.vars),
                    run.budget,
                )
                .unwrap();
            }
            (
                run.cnf.solver.num_vars() - before.0,
                run.cnf.clauses - before.1,
            )
        };
        let raw = measure(false);
        let folded = measure(true);
        let stable = crate::cnf_measurement::Measurement::prepare(&c, &Domains::new(), &e.limits)
            .unwrap()
            .measure(false, &e.limits)
            .unwrap();
        eprintln!(
            "fact-heavy: completion copy raw={raw:?}, optimized={folded:?}; stable CNF={} vars/{} clauses (includes inputs)",
            stable.before.variables, stable.before.clauses
        );
        assert!(folded.0 < raw.0 && folded.1 < raw.1);
    }
}
