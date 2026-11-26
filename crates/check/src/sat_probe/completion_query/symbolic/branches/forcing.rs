//! Context-local SAT constants. Replaced definitions remain side constraints:
//! an entailed constant is not a proof that the equations have a model.
use super::*;

#[derive(Clone, Debug, Default)]
pub struct ForcingRecord {
    pub context: &'static str,
    pub candidates: usize,
    pub attempted: usize,
    pub forced: usize,
    pub forced_witnesses: usize,
    pub examples: Vec<(GroundAtom, bool)>,
    pub omitted: usize,
    pub no_model: bool,
    pub cutoff: Option<Inconclusive>,
    pub cache: shadow_cache::Stats,
}

impl ForcingRecord {
    pub(super) fn not_installed(&mut self, error: CheckError) -> Result<()> {
        self.cutoff = Some(inconclusive(error)?);
        self.forced = 0;
        self.forced_witnesses = 0;
        self.examples.clear();
        self.omitted = 0;
        Ok(())
    }
}

pub(super) fn force(
    e: &Engine,
    c: Arc<Cone>,
    context: PruningContext,
    pins: &[(usize, bool)],
    b: &mut Budget<'_>,
    remaining: &mut QueryLimits,
) -> Result<(Arc<Cone>, ForcingRecord)> {
    let mut report = ForcingRecord {
        context: if context == PruningContext::World {
            "W"
        } else {
            "W+H"
        },
        ..Default::default()
    };
    let graph = consistency::analyse(&c, None, b)?;
    let mut candidates: Vec<_> = graph
        .cyclic
        .iter()
        .enumerate()
        .filter_map(|(i, cyclic)| {
            (*cyclic && i < c.atoms.len() && !c.input[i] && c.fixed[i].is_none()).then_some(i)
        })
        .collect();
    let components = candidates.iter().map(|i| graph.component[*i]).collect();
    let witness: BTreeSet<_> = ranking::witness_edges(&c, &graph, &components, b)?
        .values()
        .flat_map(|edges| edges.iter().flat_map(|(a, d, _)| [*a, *d]))
        .collect();
    candidates.sort_by_key(|i| (!witness.contains(i), *i));
    report.candidates = candidates.len();
    if candidates.is_empty() {
        return Ok((c, report));
    }
    let mut local = e.clone();
    local.config = remaining.clone();
    let mut run = queries::Run::new(&local, b)?;
    run.label("completion branch forcing");
    let mut constants = vec![];
    let result: Result<()> = (|| {
        let encoded = encoding::encode_named(
            &c,
            &mut run.cnf,
            run.truth,
            Some(&run.world.vars),
            run.budget,
            "branch-forcing",
        )?;
        let mut assumptions: Vec<_> = pins
            .iter()
            .filter(|(i, _)| c.input[*i])
            .map(|(i, v)| {
                if *v {
                    encoded.vars[*i]
                } else {
                    !encoded.vars[*i]
                }
            })
            .collect();
        if context == PruningContext::Hypothesis {
            let h = e
                .classification
                .as_ref()
                .ok_or(CheckError::Internal("forcing H without classification"))?
                .2;
            assumptions.push(encoded.vars[h]);
        }
        let mut queries = if e.limits.completion_cache_enforce {
            shadow_cache::FixedQueries::enforcing(&mut run)?
        } else {
            shadow_cache::FixedQueries::new(&mut run)?
        };
        let outcome: Result<()> = (|| {
            if !queries.solve(&assumptions)? {
                report.no_model = true;
                return Ok(());
            }
            for i in candidates {
                report.attempted += 1;
                assumptions.push(encoded.vars[i]);
                let yes = queries.solve(&assumptions)?;
                assumptions.pop();
                let value = if !yes {
                    Some(false)
                } else {
                    assumptions.push(!encoded.vars[i]);
                    let no = queries.solve(&assumptions)?;
                    assumptions.pop();
                    (!no).then_some(true)
                };
                if let Some(value) = value {
                    constants.push((i, value));
                }
            }
            Ok(())
        })();
        report.cache = queries.stats().clone();
        outcome
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
    drop(run);
    if let Err(error) = result {
        e.limits.cancellation.check()?;
        report.cutoff = Some(inconclusive(error)?);
    }
    report.forced = constants.len();
    report.forced_witnesses = constants
        .iter()
        .filter(|(i, _)| witness.contains(i))
        .count();
    report.examples = constants
        .iter()
        .take(32)
        .map(|(i, v)| (c.atoms[*i].clone(), *v))
        .collect();
    report.omitted = constants.len().saturating_sub(report.examples.len());
    if constants.is_empty() {
        return Ok((c, report));
    }
    // Installation has its own charged scan. If it cannot finish, the caller
    // keeps the old view; no partially built equation system is ever installed.
    let installed: Result<Arc<Cone>> = (|| {
        let mut out = (*c).clone();
        let heads: BTreeSet<_> = constants.iter().map(|(i, _)| *i).collect();
        let mut definitions: BTreeMap<_, Vec<_>> = heads.iter().map(|i| (*i, vec![])).collect();
        for rule in &c.rules {
            b.charge(rule.body.len() + 1, "completion forcing definitions")?;
            if let Some(bodies) = definitions.get_mut(&rule.head) {
                bodies.push(rule.body.clone());
            }
        }
        let mut retained: Vec<_> = c.retained.iter().cloned().collect();
        for (head, bodies) in definitions {
            retained.push(RetainedEquation { head, bodies });
        }
        out.retained = retained.into();
        for (i, v) in constants {
            out.fixed[i] = Some(v);
        }
        Ok(Arc::new(out))
    })();
    match installed {
        Ok(out) => Ok((out, report)),
        Err(error) => {
            e.limits.cancellation.check()?;
            report.not_installed(error)?;
            Ok((c, report))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_probe::completion_query::tests::{prepare, verification};
    use crate::test_support::rewrites::{atom, rel, rule};

    fn models(e: &Engine, c: &Cone, h: bool) -> BTreeSet<Vec<bool>> {
        let mut b = Budget::new(&e.limits);
        let mut run = queries::Run::new(e, &mut b).unwrap();
        let enc = encode(
            c,
            &mut run.cnf,
            run.truth,
            Some(&run.world.vars),
            run.budget,
        )
        .unwrap();
        let mut out = BTreeSet::new();
        for bits in 0..1usize << c.fixed.len() {
            let values: Vec<_> = (0..c.fixed.len()).map(|i| bits & (1 << i) != 0).collect();
            if h && !values[e.classification.as_ref().unwrap().2] {
                continue;
            }
            let pins: Vec<_> = values
                .iter()
                .zip(&enc.vars)
                .map(|(v, l)| if *v { *l } else { !*l })
                .collect();
            if run.raw_solve(&pins).unwrap() {
                queries::validate_assignment(c, &values, None, run.budget).unwrap();
                out.insert(values);
            }
        }
        out
    }
    #[test]
    fn forced_false_retains_no_model_inputs_and_self_support_is_not_forced() {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let x = rel(&mut c, "x", false);
        rule(&mut c, x, &[(i, false), (x, true)]);
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &Default::default());
        let mut b = Budget::new(&e.limits);
        let (forced, report) = force(
            &e,
            e.cone.clone(),
            PruningContext::World,
            &[],
            &mut b,
            &mut e.config.clone(),
        )
        .unwrap();
        assert_eq!(report.examples, [(atom(x), false)]);
        assert!(!forced.retained.is_empty());
        assert_eq!(models(&e, &e.cone, false), models(&e, &forced, false));
        assert_eq!(models(&e, &forced, false).len(), 1);
        // The existential slice may not discard the retained defining equation.
        let slice = existence_slice::Slice::new(&forced, None, &mut b).unwrap();
        assert_eq!(models(&e, &forced, false), models(&e, &slice.core, false));

        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let x = rel(&mut c, "x", false);
        rule(&mut c, x, &[(x, false)]);
        rule(&mut c, x, &[(i, false)]);
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &Default::default());
        let (_, report) = force(
            &e,
            e.cone.clone(),
            PruningContext::World,
            &[],
            &mut Budget::new(&e.limits),
            &mut e.config.clone(),
        )
        .unwrap();
        assert_eq!(report.forced, 0);
    }
    #[test]
    fn every_tiny_signed_equation_model_is_preserved_including_vacuous_contexts() {
        for left in 0..8 {
            for right in 0..8 {
                let mut c = Corpus::new();
                let i = rel(&mut c, "i", true);
                let x = rel(&mut c, "x", false);
                let y = rel(&mut c, "y", false);
                for (head, choice) in [(x, left), (y, right)] {
                    match choice {
                        0 => (),
                        1 => {
                            rule(&mut c, head, &[]);
                        }
                        2 => {
                            rule(&mut c, head, &[(i, false)]);
                        }
                        3 => {
                            rule(&mut c, head, &[(x, false)]);
                        }
                        4 => {
                            rule(&mut c, head, &[(x, true)]);
                        }
                        5 => {
                            rule(&mut c, head, &[(y, false)]);
                        }
                        6 => {
                            rule(&mut c, head, &[(y, true)]);
                        }
                        _ => {
                            rule(&mut c, head, &[(i, false), (head, true)]);
                        }
                    }
                }
                let v = verification(&mut c, Some(x), &[]);
                let e = prepare(&c, v, &Default::default());
                for context in [PruningContext::World, PruningContext::Hypothesis] {
                    let (forced, report) = force(
                        &e,
                        e.cone.clone(),
                        context,
                        &[],
                        &mut Budget::new(&e.limits),
                        &mut e.config.clone(),
                    )
                    .unwrap();
                    let h = context == PruningContext::Hypothesis;
                    // Independent truth-table oracle: evaluate the original
                    // equations directly, without the encoder or its folding.
                    let expected: BTreeSet<Vec<bool>> =
                        (0..1usize << e.cone.fixed.len())
                            .map(|bits| {
                                (0..e.cone.fixed.len())
                                    .map(|i| bits & (1 << i) != 0)
                                    .collect::<Vec<_>>()
                            })
                            .filter(|values| !h || values[e.classification.as_ref().unwrap().2])
                            .filter(|values| {
                                (0..values.len()).all(|i| {
                                    if let Some(v) = e.cone.fixed[i] {
                                        values[i] == v
                                    } else if e.cone.input[i] {
                                        true
                                    } else {
                                        values[i]
                                            == e.cone.rules.iter().filter(|r| r.head == i).any(
                                                |r| r.body.iter().all(|(j, p)| values[*j] == *p),
                                            )
                                    }
                                })
                            })
                            .collect();
                    assert_eq!(
                        models(&e, &e.cone, h),
                        expected,
                        "original {left}/{right}/{context:?}"
                    );
                    assert_eq!(
                        models(&e, &forced, h),
                        expected,
                        "forced {left}/{right}/{context:?}"
                    );
                    assert_eq!(report.cache.mismatches, 0);
                    if report.no_model {
                        assert_eq!(report.forced, 0);
                    }
                }
            }
        }
    }
    #[test]
    fn forced_views_preserve_whole_verification_results_and_context_isolation() {
        use crate::sat_probe::completion_query::tests::{keys, scale::same_report};
        for shape in 0..5 {
            let mut c = Corpus::new();
            let i = rel(&mut c, "i", true);
            let x = rel(&mut c, "x", false);
            let y = rel(&mut c, "y", false);
            match shape {
                0 => {
                    rule(&mut c, x, &[(i, false), (x, true)]);
                }
                1 => {
                    rule(&mut c, x, &[(x, true)]);
                }
                2 => {
                    rule(&mut c, x, &[(x, false)]);
                    rule(&mut c, x, &[(i, false)]);
                }
                3 => {
                    rule(&mut c, x, &[(y, false)]);
                    rule(&mut c, x, &[(y, true)]);
                    rule(&mut c, y, &[(x, false), (i, false)]);
                }
                _ => {
                    rule(&mut c, x, &[(x, false)]);
                }
            }
            for h in [None, Some(x)] {
                let v = verification(&mut c, h, &[]);
                let e = prepare(&c, v, &Default::default());
                let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
                for prune in [false, true] {
                    let options = CheckOptions {
                        force: true,
                        prune,
                        split_depth: 2,
                        ..Default::default()
                    };
                    let actual = e.check(&keys(&c), &options).unwrap();
                    same_report(&actual, &expected);
                    // Cache on/off agreement: shadow mode solves every query.
                    let mut shadow = e.clone();
                    shadow.limits.completion_cache_enforce = false;
                    same_report(&actual, &shadow.check(&keys(&c), &options).unwrap());

                    same_report(&actual, &e.check(&keys(&c), &options).unwrap());
                    same_report(
                        &actual,
                        &prepare(&c, v, &Default::default())
                            .check(&keys(&c), &options)
                            .unwrap(),
                    );
                    assert!(
                        actual
                            .branches
                            .records
                            .iter()
                            .flat_map(|b| &b.forcing)
                            .all(|r| r.cache.mismatches == 0)
                    );
                }
                // Invocation-local forced views may never leak into the next off run.
                same_report(&e.check(&keys(&c), &Default::default()).unwrap(), &expected);
            }
        }
    }

    #[test]
    fn forcing_breaks_a_loop_and_makes_its_dependent_an_available_formula() {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let x = rel(&mut c, "x", false);
        let y = rel(&mut c, "y", false);
        rule(&mut c, x, &[(y, false)]);
        rule(&mut c, x, &[(y, true)]);
        rule(&mut c, y, &[(x, false), (i, false)]);
        let v = verification(&mut c, None, &[]);
        let mut e = prepare(&c, v, &Default::default());
        e.forcing = true;
        let mut b = Budget::new(&e.limits);
        let mut bundle = fitting::Bundle::new(&e, &mut b).unwrap();
        let y = e.program.atom_index[&atom(y)];
        assert!(consistency::analyse(&e.cone, None, &mut b).unwrap().cyclic[y]);
        bundle
            .settle(&e, false, false, &mut e.config.clone(), &mut b)
            .unwrap();
        let (state, _) = bundle.ranking(false, false);
        let view = state.cone(&mut b).unwrap();
        assert!(!consistency::analyse(&view, None, &mut b).unwrap().cyclic[y]);
        let mut producers = vec![vec![]; view.fixed.len()];
        for (n, r) in view.rules.iter().enumerate() {
            producers[r.head].push(n);
        }
        assert!(
            branch_formula::SettledAtom::build(
                &view,
                &producers,
                y,
                Arc::new(bundle.scope(false)),
                PruningContext::World,
                &mut b
            )
            .unwrap()
            .is_some()
        );
        assert!(
            bundle
                .forcing
                .iter()
                .any(|r| r.examples.contains(&(atom(x), true)))
        );
    }
    #[test]
    fn ordinary_processing_first_attempt_precedes_installing_any_forced_view() {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let x = rel(&mut c, "x", false);
        rule(&mut c, x, &[(i, false), (x, true)]);
        let v = verification(&mut c, None, &[]);
        let mut e = prepare(&c, v, &Default::default());
        e.forcing = true;
        for existence in [false, true] {
            let calls = std::cell::Cell::new(0);
            let options = CheckOptions {
                force: true,
                split_depth: 2,
                ..Default::default()
            };
            let answer = super::super::run(&e, false, existence, &options, 1, |first, _| {
                calls.set(calls.get() + 1);
                assert!(
                    first.pruning.is_none(),
                    "root forcing must not install a preflight view"
                );
                assert_eq!(first.cone.fixed, e.cone.fixed);
                Ok(Search::Exists(()))
            })
            .unwrap();
            assert!(answer.exists());
            assert_eq!(calls.get(), 1);
        }
    }
}
