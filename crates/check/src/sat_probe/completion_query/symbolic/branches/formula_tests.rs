use super::*;
use crate::sat_probe::completion_query::tests::{keys, prepare, verification};
use crate::test_support::rewrites::{atom, rel, rule};

fn formula(
    c: &Cone,
    i: usize,
    scope: Vec<usize>,
    context: PruningContext,
    b: &mut Budget<'_>,
) -> Option<Arc<branch_formula::SettledAtom>> {
    let mut producers = vec![vec![]; c.fixed.len()];
    for (j, r) in c.rules.iter().enumerate() {
        if !r
            .body
            .iter()
            .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
        {
            producers[r.head].push(j);
        }
    }
    branch_formula::SettledAtom::build(c, &producers, i, Arc::new(scope), context, b).unwrap()
}
fn fixture(no_model: bool, hypothesis: bool) -> (Corpus, Engine, usize, [usize; 2]) {
    let mut c = Corpus::new();
    let a = rel(&mut c, "left", true);
    let b = rel(&mut c, "right", true);
    let g = rel(&mut c, "term", false);
    rule(&mut c, g, &[(a, false), (b, true)]);
    rule(&mut c, g, &[(a, true), (b, false)]);
    let p = rel(&mut c, "selected", false);
    let q = rel(&mut c, "profile", false);
    if no_model {
        rule(&mut c, p, &[(g, false), (p, true)]);
    } else {
        rule(&mut c, p, &[(g, false), (q, false)]);
        rule(&mut c, q, &[(g, true), (p, true)]);
    }
    let h = rel(&mut c, "accepted", false);
    rule(&mut c, h, &[(p, true)]);
    let v = verification(&mut c, hypothesis.then_some(h), &[]);
    let e = prepare(&c, v, &Default::default());
    let gi = e.program.atom_index[&atom(g)];
    let inputs = [a, b].map(|r| e.program.atom_index[&atom(r)]);
    (c, e, gi, inputs)
}
#[test]
fn formula_children_partition_inputs_including_no_model_worlds() {
    for h in [false, true] {
        for no_model in [false, true] {
            let (c, e, g, inputs) = fixture(no_model, h);
            let mut b = Budget::new(&e.limits);
            let root = fitting::Bundle::new(&e, &mut b).unwrap();
            let cone = root.cone.cone(&mut b).unwrap();
            let f = formula(&cone, g, root.scope(false), PruningContext::World, &mut b).unwrap();
            for value in [false, true] {
                let child = root
                    .child_with_formula(&[(g, value)], Some(&f), &mut b)
                    .unwrap();
                let branch = child.engine(&e, &mut b).unwrap();
                // A pin must constrain the inputs, not invent a value for g.
                for bits in 0..4 {
                    let pins = inputs
                        .iter()
                        .enumerate()
                        .map(|(j, i)| (e.cone.atoms[*i].clone(), bits & (1 << j) != 0))
                        .collect();
                    let answer = branch
                        .worlds(&WorldQuery {
                            pins,
                            ..Default::default()
                        })
                        .unwrap();
                    assert_eq!(
                        matches!(answer, WorldAnswer::World(_)),
                        (bits == 1 || bits == 2) == value
                    );
                }
            }
            let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
            let options = CheckOptions {
                split_depth: 2,
                ..Default::default()
            };
            let actual = e.check(&keys(&c), &options).unwrap();
            crate::sat_probe::completion_query::tests::scale::same_report(&actual, &expected);
            for class in [false, true] {
                if class && !h {
                    continue;
                }
                for existence in [false, true] {
                    let answer = test_partition(&e, class, existence, &options).unwrap();
                    let expected = if class {
                        let r = actual.classification.as_ref().unwrap();
                        if existence {
                            r.no_meaning.exists()
                        } else {
                            r.ambiguous.exists()
                        }
                    } else {
                        let r = &actual.meaning;
                        if existence {
                            r.no_meaning.exists()
                        } else {
                            r.ambiguous.exists()
                        }
                    };
                    assert_eq!(answer.exists(), expected);
                    assert!(matches!(answer, Search::None | Search::Exists(())));
                }
            }
        }
    }
}
#[test]
fn composite_term_cuts_where_neither_input_does_and_children_inherit() {
    let (_, e, g, inputs) = fixture(false, false);
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    for i in inputs {
        for value in [false, true] {
            let child = root.child(&[(i, value)], &mut b).unwrap();
            let graph =
                consistency::analyse(&child.cone.cone(&mut b).unwrap(), None, &mut b).unwrap();
            assert!(!graph.conflicts.is_empty());
        }
    }
    let mut rows = vec![];
    let mut omitted = 0;
    let mut config = e.config.clone();
    let (choice, _) = choose(
        &e,
        &root,
        false,
        true,
        8,
        &mut config,
        &mut rows,
        &mut omitted,
        &mut b,
    )
    .unwrap()
    .unwrap();
    assert_eq!(choice.selected, vec![g]);
    assert!(choice.formula.is_some());
    let row = rows.iter().find(|r| r.selected).unwrap();
    assert!(row.formula);
    assert_eq!(row.child_trials.len(), 2);
    for child in &choice.child_states {
        let descendant = child.child(&[], &mut b).unwrap();
        let (s, _) = descendant.ranking(false, false);
        assert!(
            consistency::analyse(&s.cone(&mut b).unwrap(), None, &mut b)
                .unwrap()
                .conflicts
                .is_empty()
        );
        assert_eq!(descendant.formulas.len(), 1);
    }
}
#[test]
fn cyclic_upstream_is_ineligible_but_a_pinned_dead_producer_can_remove_it() {
    let mut c = Corpus::new();
    let gate = rel(&mut c, "gate", true);
    let cycle = rel(&mut c, "cycle", false);
    let g = rel(&mut c, "guard", false);
    rule(&mut c, cycle, &[(cycle, false)]);
    rule(&mut c, g, &[(cycle, false), (gate, false)]);
    rule(&mut c, g, &[(gate, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let gi = e.program.atom_index[&atom(g)];
    let input = e.program.atom_index[&atom(gate)];
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    assert!(
        formula(
            &root.cone.cone(&mut b).unwrap(),
            gi,
            root.scope(false),
            PruningContext::World,
            &mut b
        )
        .is_none()
    );
    let child = root.child(&[(input, false)], &mut b).unwrap();
    assert_eq!(child.cone.value(gi), Some(true));
}
#[test]
fn h_only_formula_views_never_fix_w_or_assumptions() {
    let (_, e, g, _) = fixture(false, true);
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let cone = root.classification.as_ref().unwrap().cone(&mut b).unwrap();
    let f = formula(
        &cone,
        g,
        root.scope(true),
        PruningContext::Hypothesis,
        &mut b,
    )
    .unwrap();
    let child = root
        .child_with_formula(&[(g, true)], Some(&f), &mut b)
        .unwrap();
    assert_eq!(child.ranking(true, false).0.value(g), None);
    assert_eq!(child.ranking(true, true).0.value(g), Some(true));
    assert_eq!(child.world.value(g), root.world.value(g));
    let descendant = child.child(&[], &mut b).unwrap();
    assert_eq!(descendant.ranking(true, false).0.value(g), None);
    assert_eq!(descendant.ranking(true, true).0.value(g), Some(true));
}

#[test]
fn splice_trial_reports_pruned_self_admission_and_false_child_settlement() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "left", true);
    let b = rel(&mut c, "right", true);
    let value = rel(&mut c, "payload", true);
    let g = rel(&mut c, "splice", false);
    rule(&mut c, g, &[(a, false), (b, true)]);
    rule(&mut c, g, &[(a, true), (b, false)]);
    let p = rel(&mut c, "admitted", false);
    let q = rel(&mut c, "profile", false);
    rule(&mut c, p, &[(g, false), (value, false)]);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(g, false), (value, false), (p, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    let gi = e.program.atom_index[&atom(g)];
    let mut cache = pruning::Cache::for_engine(&e);
    cache.enable_trials(&e);
    e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut rows = vec![];
    let mut omitted = 0;
    let mut config = e.config.clone();
    choose(
        &e,
        &root,
        false,
        true,
        8,
        &mut config,
        &mut rows,
        &mut omitted,
        &mut b,
    )
    .unwrap()
    .unwrap();
    let row = rows
        .iter()
        .find(|r| r.formula && r.split == e.cone.atoms[gi])
        .unwrap();
    assert_eq!(row.child_trials.len(), 2);
    let yes = &row.child_trials[0];
    let no = &row.child_trials[1];
    assert!(!yes.rest && no.rest);
    assert!(yes.pruning_proved > 0 && yes.removed_producers > 0);
    assert!(yes.pruned_heads.contains(&atom(p)) || yes.pruned_heads.contains(&atom(q)));
    assert!(yes.removed_producer_examples.iter().any(|r| {
        r.original_body
            .iter()
            .any(|(a, _)| *a == atom(p) || *a == atom(q))
    }));
    assert_eq!(no.settled_target_atoms, no.target_atoms);
    assert!(yes.disabled_edges > 0 && no.disabled_edges > 0);
    let options = CheckOptions {
        prune: true,
        split_depth: 2,
        ..Default::default()
    };
    crate::sat_probe::completion_query::tests::scale::same_report(
        &e.check(&keys(&c), &options).unwrap(),
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
}

#[test]
fn selected_split_guard_cap_is_shared_with_per_child_omissions() {
    // A selected term cuts one loop. Many other surviving loops have derived
    // guards, including guards present in only one child. Both children get room.
    for sparse_first in [false, true] {
        let (mut c, _, _, _) = fixture(false, false);
        let t = c.relations().find(|r| r.name == "term").unwrap().id;
        for n in 0..40 {
            let x = rel(&mut c, &format!("raw_{n}"), true);
            let g = rel(&mut c, &format!("guard_{n}"), false);
            let p = rel(&mut c, &format!("loop_{n}"), false);
            let body = if sparse_first {
                vec![(x, false), (t, true)]
            } else {
                vec![(x, false)]
            };
            rule(&mut c, g, &body);
            rule(&mut c, p, &[(g, false), (p, true)]);
            // Tautologically reading t puts its partition in the candidate inventory,
            // but the edge survives in either child (one parallel producer remains).
            rule(&mut c, p, &[(g, false), (p, true), (t, false)]);
            rule(&mut c, p, &[(g, false), (p, true), (t, true)]);
        }
        let v = c.verifications().next().unwrap().id;
        let e = prepare(&c, v, &Default::default());
        let mut b = Budget::new(&e.limits);
        let root = fitting::Bundle::new(&e, &mut b).unwrap();
        let mut rows = vec![];
        let mut config = e.config.clone();
        choose(
            &e,
            &root,
            false,
            true,
            8,
            &mut config,
            &mut rows,
            &mut 0,
            &mut b,
        )
        .unwrap()
        .unwrap();
        let row = rows.iter().find(|r| r.selected).unwrap();
        assert_eq!(row.child_trials.len(), 2);
        assert_eq!(row.derived_guards.len(), 32);
        for child in &row.child_trials {
            let retained = row
                .derived_guards
                .iter()
                .filter(|g| g.child == child.child)
                .count();
            if sparse_first && child.child == 0 {
                assert_eq!(retained, 0);
                assert_eq!(child.omitted_derived_guards, 0);
            } else {
                assert!(retained > 0);
                assert!(child.omitted_derived_guards > 0);
                if sparse_first {
                    assert_eq!(retained, 32, "unused first-child share passes forward");
                }
            }
            assert!(child.derived_guards_complete);
        }
        assert_eq!(
            row.omitted_derived_guards,
            row.child_trials
                .iter()
                .map(|c| c.omitted_derived_guards)
                .sum()
        );
    }
}

#[test]
fn formula_views_preserve_every_tiny_model_under_each_partition() {
    fn models(
        c: &Cone,
        f: &branch_formula::SettledAtom,
        value: bool,
        h: Option<usize>,
        b: &mut Budget<'_>,
    ) -> BTreeSet<usize> {
        (0..1usize << c.atoms.len())
            .filter(|bits| {
                let v = |i: usize| bits & (1 << i) != 0;
                f.evaluate(v, b).unwrap() == value
                    && h.is_none_or(v)
                    && (0..c.atoms.len()).all(|i| {
                        if let Some(fixed) = c.fixed[i] {
                            v(i) == fixed
                        } else if c.input[i] {
                            true
                        } else {
                            v(i) == c
                                .rules
                                .iter()
                                .filter(|r| r.head == i)
                                .any(|r| r.body.iter().all(|(j, p)| v(*j) == *p))
                        }
                    })
            })
            .collect()
    }
    // Both polarities, even/odd/self loops, alternative producers and equations
    // with zero models. No SAT witness or chosen partition is a golden.
    for code in 0..216 {
        let mut c = Corpus::new();
        let a = rel(&mut c, "a", true);
        let b = rel(&mut c, "b", true);
        let g = rel(&mut c, "g", false);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        rule(&mut c, g, &[(a, false), (b, true)]);
        rule(&mut c, g, &[(a, true), (b, false)]);
        let atoms = [g, p, q];
        let mut n = code;
        for head in [p, p, q] {
            let lit = n % 6;
            n /= 6;
            rule(&mut c, head, &[(atoms[lit / 2], lit % 2 != 0)]);
        }
        let v = verification(&mut c, Some(q), &[]);
        let mut e = prepare(&c, v, &Default::default());
        let mut cache = pruning::Cache::for_engine(&e);
        cache.enable_trials(&e);
        e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
        let gi = e.program.atom_index[&atom(g)];
        let mut budget = Budget::new(&e.limits);
        let root = fitting::Bundle::new(&e, &mut budget).unwrap();
        let f = formula(
            &root.cone.cone(&mut budget).unwrap(),
            gi,
            root.scope(false),
            PruningContext::World,
            &mut budget,
        )
        .unwrap();
        for value in [false, true] {
            let mut child = root
                .child_with_formula(&[(gi, value)], Some(&f), &mut budget)
                .unwrap();
            let mut config = e.config.clone();
            let heads = [p, q].map(|r| e.program.atom_index[&atom(r)]).into();
            child
                .prune(&e, false, &heads, &mut config, &mut budget)
                .unwrap();
            let branch = child.engine(&e, &mut budget).unwrap();
            for hypothesis in [false, true] {
                let view =
                    pruning::view(&branch, &branch.cone, hypothesis, Duration::ZERO).unwrap();
                let h = hypothesis.then(|| e.classification.as_ref().unwrap().2);
                assert_eq!(
                    models(&e.cone, &f, value, h, &mut budget),
                    models(&view, &f, value, h, &mut budget),
                    "code {code} value {value} H {hypothesis}"
                );
            }
        }
    }
}

#[test]
fn formula_eligible_only_under_h_is_not_offered_to_mixed_existence() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let g = rel(&mut c, "g", false);
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, g, &[(b, false)]);
    rule(&mut c, g, &[(p, false), (a, true)]);
    rule(&mut c, p, &[(g, false), (p, true)]);
    rule(&mut c, h, &[(a, false), (p, true)]);
    let v = verification(&mut c, Some(h), &[]);
    let mut e = prepare(&c, v, &Default::default());
    let ai = e.program.atom_index[&atom(a)];
    let gi = e.program.atom_index[&atom(g)];
    // H entails a. Model a valid inherited H-only view, leaving W intact.
    let mut views = BTreeMap::new();
    for cone in [&e.cone, &e.classification.as_ref().unwrap().0] {
        let key = pruning::view_key(cone, PruningContext::Hypothesis);
        let mut specialized = (**cone).clone();
        specialized.fixed[ai] = Some(true);
        views.insert(key, Arc::new(specialized));
    }
    e.pruning = Some(Arc::new(std::sync::Mutex::new(pruning::Cache::inherited(
        views,
        vec![],
    ))));
    let mut budget = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut budget).unwrap();
    for classification in [false, true] {
        let mut rows = vec![];
        choose(
            &e,
            &root,
            classification,
            true,
            8,
            &mut e.config.clone(),
            &mut rows,
            &mut 0,
            &mut budget,
        )
        .unwrap();
        let offered = rows
            .iter()
            .find(|r| r.formula && r.split == e.cone.atoms[gi]);
        if classification {
            assert!(offered.is_none());
        } else {
            assert_eq!(offered.unwrap().context, "W+H");
        }
    }
}

#[test]
fn formula_branch_keeps_free_boundary_local_uniqueness_independent() {
    let (mut c, _, _, _) = fixture(false, false);
    let other = rel(&mut c, "unrelated", false);
    rule(&mut c, other, &[(other, false)]);
    let v = c.verifications().next().unwrap().id;
    let e = prepare(&c, v, &Default::default());
    let term = c.relations().find(|r| r.name == "term").unwrap().id;
    let gi = e.program.atom_index[&atom(term)];
    let oi = e.program.atom_index[&atom(other)];
    let mut budget = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut budget).unwrap();
    let f = formula(
        &root.cone.cone(&mut budget).unwrap(),
        gi,
        root.scope(false),
        PruningContext::World,
        &mut budget,
    )
    .unwrap();
    let child = root
        .child_with_formula(&[(gi, true)], Some(&f), &mut budget)
        .unwrap();
    let branch = child.engine(&e, &mut budget).unwrap();
    let mut producers = vec![vec![]; e.cone.fixed.len()];
    for (i, r) in e.cone.rules.iter().enumerate() {
        producers[r.head].push(i);
    }
    let local =
        existence::component(&e.cone, &producers, &BTreeSet::from([oi]), &mut budget).unwrap();
    let mut run = queries::Run::new(&branch, &mut budget).unwrap();
    assert!(!run.local_unique(&local, |_, _| {}).0.unwrap());
    // After restoring the original solver, the branch formula still holds.
    assert!(run.solve(&[]).unwrap());
    assert!(
        f.evaluate(
            |i| run.cnf.solver.value_lit(run.world.vars[i]) == lbool::TRUE,
            run.budget
        )
        .unwrap()
    );
    drop(run);
    assert!(
        branch
            .symbolic_pair_in(&BTreeMap::new(), false, false, &Default::default(), 1)
            .unwrap()
            .exists()
    );
}

#[test]
fn formula_pin_removes_contradicted_producers_without_coverage_proofs() {
    // Neither source producer is redundant at the root. Each is impossible in
    // one child solely because of the formula pin, before any SAT pruning.
    let (c, e, g, _) = fixture(false, false);
    let p = c
        .relations()
        .find(|r| r.name.as_str() == "selected")
        .unwrap()
        .id;
    let q = c
        .relations()
        .find(|r| r.name.as_str() == "profile")
        .unwrap()
        .id;
    let p = e.program.atom_index[&atom(p)];
    let q = e.program.atom_index[&atom(q)];
    let mut budget = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut budget).unwrap();
    let source = root.cone.cone(&mut budget).unwrap();
    let f = formula(
        &source,
        g,
        root.scope(false),
        PruningContext::World,
        &mut budget,
    )
    .unwrap();
    for value in [false, true] {
        let child = root
            .child_with_formula(&[(g, value)], Some(&f), &mut budget)
            .unwrap();
        let contradicted = if value { q } else { p };
        let branch = child.engine(&e, &mut budget).unwrap();
        for hypothesis in [false, true] {
            let view = pruning::view_using(
                &branch,
                &branch.cone,
                hypothesis,
                e.limits.timeout,
                &mut budget,
            )
            .unwrap();
            assert_eq!(view.fixed[contradicted], Some(false));
            // Source slots are retained for replay, but no producer is active.
            assert!(
                view.rules
                    .iter()
                    .filter(|r| r.head == contradicted)
                    .all(|r| r
                        .body
                        .iter()
                        .any(|(i, p)| view.fixed[*i].is_some_and(|v| v != *p)))
            );
            assert!(
                !consistency::analyse(&view, None, &mut budget)
                    .unwrap()
                    .cyclic[contradicted]
            );
            assert_eq!(
                encoding::fitting(&view, &mut budget).unwrap()[contradicted],
                Some(false)
            );
        }
        // Rules in the source and its sibling were never mutated.
        assert!(source.rules.iter().any(|r| r.head == contradicted));
        assert!(child.proofs.is_empty(), "no coverage proof was needed");
    }
}
