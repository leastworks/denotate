use super::*;
use crate::sat_probe::completion_query::tests::{keys, prepare, verification};
use crate::test_support::rewrites::{atom, rel, rule};
use denotate_ir::Namespace;

fn fixture(h: bool) -> (Corpus, Engine, usize, usize) {
    let mut c = Corpus::new();
    let gate = rel(&mut c, "guard", true);
    let raw = rel(&mut c, "payload", true);
    let value = rel(&mut c, "known_payload", false);
    rule(&mut c, value, &[(raw, false)]);
    let p = rel(&mut c, "selected", false);
    let q = rel(&mut c, "profile", false);
    rule(&mut c, p, &[(value, false), (gate, false)]);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(value, false), (p, true)]);
    // A unary at-most-one is harmless, but supplies a named input partition.
    let a = c
        .assume_in(
            Namespace::default(),
            "functional",
            Cardinality::AtMostOne,
            gate,
            [],
        )
        .unwrap();
    let v = verification(&mut c, h.then_some(p), &[a]);
    let mut e = prepare(&c, v, &Default::default());
    let mut cache = pruning::Cache::for_engine(&e);
    cache.enable_trials(&e);
    for scope in ["classification", "processing"] {
        cache
            .trials
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .fund_ranking(scope, e.limits.timeout / 4);
    }
    e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
    pruning::prepare(&e, false).unwrap();
    let g = e.program.atom_index[&atom(gate)];
    let p = e.program.atom_index[&atom(p)];
    (c, e, g, p)
}
#[test]
fn alternative_guard_discovers_a_partition_with_a_pruning_only_cut() {
    let (_, e, g, p) = fixture(false);
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let before = root.child(&[(g, true)], &mut b).unwrap();
    let (s, _) = before.ranking(false, false);
    let graph = consistency::analyse(&s.cone(&mut b).unwrap(), None, &mut b).unwrap();
    assert!(
        !graph.conflicts.is_empty(),
        "Fitting alone leaves the odd cycle"
    );
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
    .expect("pin-relative proof makes a partition useful");
    // Formula candidates may now win. The original input guard must still
    // reach a pruning trial and cut an edge; pin it directly to inspect its view.
    assert!(
        rows.iter()
            .any(|r| r.split == e.cone.atoms[g] && r.pruning_proved > 0 && r.disabled_edges > 0)
    );
    assert!(!choice.child_states.is_empty());
    let mut true_child = root.child(&[(g, true)], &mut b).unwrap();
    true_child
        .prune(&e, false, &BTreeSet::from([p]), &mut config, &mut b)
        .unwrap();
    let (s, _) = true_child.ranking(false, false);
    let graph = consistency::analyse(&s.cone(&mut b).unwrap(), None, &mut b).unwrap();
    assert!(!graph.cyclic[p]);
    assert!(!true_child.proofs.is_empty());
    // A ranking trial is not yet a source finding.
    assert!(
        e.pruning
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .report
            .records
            .iter()
            .all(|r| r.pins.is_empty())
    );
}
#[test]
fn branch_views_are_isolated_and_extend_only_to_descendants() {
    let (_, e, g, p) = fixture(false);
    let mut b = Budget::new(&e.limits);
    let mut q = e.config.clone();
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut yes = root.child(&[(g, true)], &mut b).unwrap();
    yes.prune(&e, false, &BTreeSet::from([p]), &mut q, &mut b)
        .unwrap();
    let no = root.child(&[(g, false)], &mut b).unwrap();
    let descendant = yes.child(&[], &mut b).unwrap();
    for (state, cyclic) in [
        (&root, true),
        (&yes, false),
        (&no, true),
        (&descendant, false),
    ] {
        let engine = state.engine(&e, &mut b).unwrap();
        let view = pruning::view(&engine, &engine.cone, false, Duration::ZERO).unwrap();
        let graph = consistency::analyse(&view, None, &mut b).unwrap();
        assert_eq!(graph.cyclic[p], cyclic);
    }
    assert!(yes.child(&[(g, false)], &mut b).is_err());
}
#[test]
fn conditional_pruning_agrees_with_exhaustive_equations_and_h_contexts() {
    for h in [false, true] {
        let (c, e, _, _) = fixture(h);
        let options = CheckOptions {
            prune: true,
            split_depth: 2,
            ..Default::default()
        };
        let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
        let actual = e.check(&keys(&c), &options).unwrap();
        crate::sat_probe::completion_query::tests::scale::same_report(&actual, &expected);
        crate::sat_probe::completion_query::tests::scale::same_report(
            &actual,
            &e.check(&keys(&c), &options).unwrap(),
        );
        let fresh = prepare(&c, e.verification, &Default::default())
            .check(&keys(&c), &options)
            .unwrap();
        crate::sat_probe::completion_query::tests::scale::same_report(&actual, &fresh);
        for classification in [false, true] {
            if classification && !h {
                continue;
            }
            for existence in [false, true] {
                let answer = test_partition(&e, classification, existence, &options).unwrap();
                let expected = if classification {
                    let r = actual.classification.as_ref().unwrap();
                    if existence {
                        r.no_meaning.exists()
                    } else {
                        r.ambiguous.exists()
                    }
                } else if existence {
                    actual.meaning.no_meaning.exists()
                } else {
                    actual.meaning.ambiguous.exists()
                };
                assert_eq!(answer.exists(), expected);
                assert!(matches!(answer, Search::None | Search::Exists(_)));
            }
        }
    }
}

#[test]
fn h_only_branch_proofs_never_enter_no_h_queries() {
    let (_, mut e, g, p) = fixture(true);
    let mut cache = pruning::Cache::for_engine(&e);
    cache.enable_trials(&e);
    for scope in ["classification", "processing"] {
        cache
            .trials
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .fund_ranking(scope, e.limits.timeout / 4);
    }
    e.pruning = Some(Arc::new(std::sync::Mutex::new(cache))); // branch proofs, no global H pruning
    let mut b = Budget::new(&e.limits);
    let mut q = e.config.clone();
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut child = root.child(&[(g, false)], &mut b).unwrap();
    child
        .prune(&e, true, &BTreeSet::from([p]), &mut q, &mut b)
        .unwrap();
    let engine = child.engine(&e, &mut b).unwrap();
    let cone = &engine.classification.as_ref().unwrap().0;
    let w = pruning::view(&engine, cone, false, Duration::ZERO).unwrap();
    let h = pruning::view(&engine, cone, true, Duration::ZERO).unwrap();
    assert!(consistency::analyse(&w, None, &mut b).unwrap().cyclic[p]);
    assert!(!consistency::analyse(&h, None, &mut b).unwrap().cyclic[p]);
    assert!(
        child
            .proofs
            .iter()
            .flat_map(|p| &p.records)
            .all(|p| p.context == PruningContext::Hypothesis)
    );
    assert!(
        e.pruning
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .report
            .branch_records
            .is_empty()
    );
}
#[test]
fn successful_prefix_survives_a_later_query_cutoff_and_is_conditional() {
    // Search a small range for an interrupted successful prefix. The exact
    // candidate/solver-call order is not a contract.
    for solves in 1..=16 {
        let (_, e, g, p) = fixture(false);
        let mut b = Budget::new(&e.limits);
        let mut config = e.config.clone();
        config.max_solves = solves;
        let root = fitting::Bundle::new(&e, &mut b).unwrap();
        let mut child = root.child(&[(g, true)], &mut b).unwrap();
        let heads = e.cone.rules.iter().map(|r| r.head).collect();
        let (_, proved, cutoff) = child.prune(&e, false, &heads, &mut config, &mut b).unwrap();
        if proved == 0 || cutoff.is_none() {
            continue;
        }
        let (state, _) = child.ranking(false, false);
        assert!(
            !consistency::analyse(&state.cone(&mut b).unwrap(), None, &mut b)
                .unwrap()
                .cyclic[p]
        );
        child.publish(&e);
        let cache = e.pruning.as_ref().unwrap().lock().unwrap();
        assert!(
            cache
                .report
                .branch_records
                .iter()
                .all(|r| r.pins == vec![(e.cone.atoms[g].clone(), true)])
        );
        assert!(!cache.report.branch_records.is_empty());
        return;
    }
    panic!("no successful prefix followed by cutoff");
}
#[test]
fn impossible_branch_pruning_does_not_filter_the_parent_worlds() {
    let mut c = Corpus::new();
    let gate = rel(&mut c, "gate", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(p, true)]);
    let assumption = c
        .assume_empty_in(Namespace::default(), "absent_gate", gate)
        .unwrap();
    let v = verification(&mut c, None, &[assumption]);
    let mut e = prepare(&c, v, &Default::default());
    let mut cache = pruning::Cache::for_engine(&e);
    cache.enable_trials(&e);
    for scope in ["classification", "processing"] {
        cache
            .trials
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .fund_ranking(scope, e.limits.timeout / 4);
    }
    e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
    let mut b = Budget::new(&e.limits);
    let mut config = e.config.clone();
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let gi = e.program.atom_index[&atom(gate)];
    let pi = e.program.atom_index[&atom(p)];
    let mut child = root.child(&[(gi, true)], &mut b).unwrap();
    child
        .prune(&e, false, &BTreeSet::from([pi]), &mut config, &mut b)
        .unwrap();
    let engine = child.engine(&e, &mut b).unwrap();
    assert!(matches!(
        engine.worlds(&Default::default()).unwrap(),
        WorldAnswer::NoWorld
    ));
    assert!(
        e.symbolic_no_meaning_in(&BTreeMap::new(), false, false, &Default::default(), 1)
            .unwrap()
            .exists()
    );
}

#[test]
fn conditional_prefixes_preserve_every_tiny_completion_model() {
    fn models(c: &Cone, h: Option<usize>) -> BTreeSet<usize> {
        (0..1usize << c.atoms.len())
            .filter(|bits| {
                let value = |i: usize| bits & (1 << i) != 0;
                h.is_none_or(value)
                    && (0..c.atoms.len()).all(|i| {
                        if let Some(v) = c.fixed[i] {
                            value(i) == v
                        } else if c.input[i] {
                            true
                        } else {
                            value(i)
                                == c.rules
                                    .iter()
                                    .filter(|r| r.head == i)
                                    .any(|r| r.body.iter().all(|(j, p)| value(*j) == *p))
                        }
                    })
            })
            .collect()
    }
    let mut saw_proof = false;
    for code in 0..216 {
        let mut c = Corpus::new();
        let input = rel(&mut c, "input", true);
        let guard = rel(&mut c, "guard", true);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        let atoms = [input, p, q];
        let mut n = code;
        for (index, head) in [p, p, q].into_iter().enumerate() {
            let lit = n % 6;
            n /= 6;
            let mut body = vec![(atoms[lit / 2], lit % 2 != 0)];
            if index == 1 {
                body.push((guard, false));
            }
            rule(&mut c, head, &body);
        }
        for hypothesis in [None, Some(p)] {
            let v = verification(&mut c, hypothesis, &[]);
            let mut e = prepare(&c, v, &Default::default());
            let mut cache = pruning::Cache::for_engine(&e);
            cache.enable_trials(&e);
            for scope in ["classification", "processing"] {
                cache
                    .trials
                    .as_ref()
                    .unwrap()
                    .lock()
                    .unwrap()
                    .fund_ranking(scope, e.limits.timeout / 4);
            }
            e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
            let gi = e.program.atom_index[&atom(guard)];
            let heads = [p, q].map(|r| e.program.atom_index[&atom(r)]).into();
            let mut b = Budget::new(&e.limits);
            let root = fitting::Bundle::new(&e, &mut b).unwrap();
            for pin in [false, true] {
                let mut child = root.child(&[(gi, pin)], &mut b).unwrap();
                let original = child.engine(&e, &mut b).unwrap();
                let mut config = e.config.clone();
                let (_, proved, _) = child.prune(&e, false, &heads, &mut config, &mut b).unwrap();
                saw_proof |= proved > 0;
                let branch = child.engine(&e, &mut b).unwrap();
                for h in [false, true] {
                    if h && hypothesis.is_none() {
                        continue;
                    }
                    let view = pruning::view(&branch, &branch.cone, h, Duration::ZERO).unwrap();
                    let h = h.then(|| e.classification.as_ref().unwrap().2);
                    assert_eq!(
                        models(&original.cone, h),
                        models(&view, h),
                        "code {code}, pin {pin}, H {h:?}"
                    );
                }
            }
        }
    }
    assert!(saw_proof);
}

#[test]
fn closed_target_still_checks_an_unrelated_odd_component() {
    let (mut c, _, _, _) = fixture(false);
    let bad = rel(&mut c, "independent", false);
    rule(&mut c, bad, &[(bad, true)]);
    let v = c.verifications().next().unwrap().id;
    let mut e = prepare(&c, v, &Default::default());
    let mut cache = pruning::Cache::for_engine(&e);
    cache.enable_trials(&e);
    for scope in ["classification", "processing"] {
        cache
            .trials
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .fund_ranking(scope, e.limits.timeout / 4);
    }
    e.pruning = Some(Arc::new(std::sync::Mutex::new(cache)));
    let options = CheckOptions {
        prune: true,
        split_depth: 2,
        ..Default::default()
    };
    assert!(matches!(
        test_partition(&e, false, true, &options).unwrap(),
        Search::Exists(())
    ));
}

#[test]
fn derived_guard_eligibility_checks_the_whole_upstream_not_just_its_own_scc() {
    let (_, e, _, _) = fixture(false);
    let mut b = Budget::new(&e.limits);
    let bundle = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut rows = vec![];
    let mut omitted = 0;
    let mut query = e.config.clone();
    choose(
        &e,
        &bundle,
        false,
        true,
        8,
        &mut query,
        &mut rows,
        &mut omitted,
        &mut b,
    )
    .unwrap()
    .unwrap();
    let mut row = rows.into_iter().find(|r| r.selected).unwrap();
    row.derived_guards.clear();
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let guard = rel(&mut c, "guard", false);
    let cyclic = rel(&mut c, "cyclic", false);
    rule(&mut c, cyclic, &[(cyclic, false)]);
    rule(&mut c, guard, &[(cyclic, false)]);
    rule(&mut c, p, &[(guard, false), (p, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let pi = e.program.atom_index[&atom(p)];
    let gi = e.program.atom_index[&atom(guard)];
    let mut b = Budget::new(&e.limits);
    let bundle = fitting::Bundle::new(&e, &mut b).unwrap();
    let (state, _) = bundle.ranking(false, false);
    assert!(
        !consistency::analyse(&state.cone(&mut b).unwrap(), None, &mut b)
            .unwrap()
            .cyclic[gi]
    );
    ranking::derived_guards(
        state,
        &BTreeMap::from([(0, BTreeSet::from([(pi, pi, true)]))]),
        0,
        32,
        &mut row,
        &mut b,
    )
    .unwrap();
    assert!(
        row.derived_guards
            .iter()
            .any(|g| g.atom == atom(guard) && !g.acyclic_upstream)
    );
}

#[test]
fn unchanged_saturated_views_are_not_pruned_again() {
    // With the guard false the odd loop survives pruning: the first settle does
    // real work and proves nothing; repeating it on the unchanged view would
    // repeat the same attempts (three times per trial child on the corpus).
    let (_, mut e, g, _) = fixture(false);
    e.limits.completion_exploration = true;
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut child = root.child(&[(g, false)], &mut b).unwrap();
    let mut config = e.config.clone();
    let start = b.used();
    child.settle(&e, false, true, &mut config, &mut b).unwrap();
    assert!(b.used() > start, "the first pass prunes");
    let start = b.used();
    child.settle(&e, false, true, &mut config, &mut b).unwrap();
    assert_eq!(
        b.used(),
        start,
        "an unchanged saturated view was pruned again"
    );
    // A new bundle (as for a child unit or a new pin set) prunes again.
    let mut fresh = child.child(&[(g, false)], &mut b).unwrap();
    let start = b.used();
    fresh.settle(&e, false, true, &mut config, &mut b).unwrap();
    assert!(b.used() > start);
}

/// Counts `completion unit pruning` starts; a saturated scope returns before that
/// event, so the count shows whether pruning actually ran again.
fn count_pruning_starts(e: &mut Engine) -> Arc<std::sync::atomic::AtomicUsize> {
    let starts = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let seen = starts.clone();
    e.limits.progress = crate::CheckingProgress::new(move |event| {
        if event.stage == "completion unit pruning" && event.state == "started" {
            seen.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    });
    starts
}

#[test]
fn exploration_trials_leave_forcing_to_selected_children() {
    // As in production: the completed trial state becomes the selected child's
    // prepared state, then its unit settles it with forcing. Here forcing W
    // installs constants once and then finds nothing more.
    let (_, mut e, g, _) = fixture(false);
    e.limits.completion_exploration = true;
    e.forcing = true;
    let starts = count_pruning_starts(&mut e);
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut config = e.config.clone();
    let mut trial = root.child(&[(g, false)], &mut b).unwrap();
    trial.settle(&e, false, true, &mut config, &mut b).unwrap();
    assert!(trial.forcing.is_empty(), "a trial child forced");
    assert_eq!(starts.load(std::sync::atomic::Ordering::Relaxed), 1);
    let mut unit = trial.clone();
    unit.settle(&e, false, false, &mut config, &mut b).unwrap();
    assert!(
        unit.forcing.iter().any(|r| r.forced > 0),
        "the selected child's unit forces"
    );
    // Records name the forced witness atoms, not only their count.
    for r in &unit.forcing {
        assert_eq!(r.witnesses.len(), r.forced_witnesses.min(32));
    }
    assert!(unit.forcing.iter().any(|r| !r.witnesses.is_empty()));
    // The unit skips re-pruning the trial's saturated view; the installed
    // constants invalidate it, so pruning runs exactly once more; the second
    // forcing round changes nothing, so no third pass. Without the memo this
    // is 4, without invalidation 1.
    assert_eq!(starts.load(std::sync::atomic::Ordering::Relaxed), 2);
}
