use super::*;
use crate::test_support::rewrites::{atom, rel, rule, summaries};
use denotate_ir::*;

fn cones(
    c: &Corpus,
    reading: RuleId,
    root: RelationId,
    test: impl FnOnce(&BorrowedCone<'_>, &BorrowedCone<'_>, &ConditionContext),
) {
    let l = Limits::default();
    let p = GroundProgram::prepare(c, &Domains::new(), &l).unwrap();
    let model = p.symbolic(&l).unwrap();
    let summaries = summaries(&p, &model, &l);
    let candidate = summaries
        .values()
        .find(|p| p.rule.source == reading)
        .unwrap();
    let mut index = BTreeMap::<_, Vec<_>>::new();
    for s in summaries.values() {
        index.entry(&s.rule.head.atom).or_default().push(s.rule.id);
    }
    let root = atom(root);
    let mut budget = Budget::new(&l);
    let mut retained = 0;
    let mut stats = Preparation::default();
    let old = super::super::prepare_inner(
        &p,
        p.component_for(&root).unwrap(),
        candidate,
        &root,
        &summaries,
        &index,
        model.context(),
        &mut retained,
        &mut budget,
        &mut stats,
        true,
        &mut PruningCache::default(),
    )
    .unwrap();
    let new = prepare(
        Arc::clone(&old),
        &root,
        model.context(),
        &mut retained,
        &mut budget,
        &mut stats,
    )
    .unwrap();
    assert_eq!(stats.pruning, Some("complete"));
    assert_eq!(retained, new.temporary_nodes());
    test(&old, &new, model.context());

    // Across candidates/preparations only the independent Boolean tests may be
    // shared. The complete cone and every reason/source must still agree.
    let mut shared = PruningCache::default();
    let mut held = 0;
    shared.reserve(&mut held, &mut budget).unwrap();
    for _ in 0..2 {
        let cached = super::super::prepare_cached(
            &p,
            p.component_for(&root).unwrap(),
            candidate,
            &root,
            &summaries,
            &index,
            model.context(),
            &mut held,
            &mut budget,
            &mut stats,
            &mut shared,
        )
        .unwrap();
        assert!(new.same_computation(&cached, &mut budget).unwrap());
        assert_eq!(
            new.pruning
                .sources
                .iter()
                .map(|s| s.rule.id)
                .collect::<Vec<_>>(),
            cached
                .pruning
                .sources
                .iter()
                .map(|s| s.rule.id)
                .collect::<Vec<_>>()
        );
        held -= cached.temporary_nodes();
        assert_eq!(held, shared.reserved());
    }
    held -= shared.release();
    assert_eq!(held, 0);

    // Optional storage failure retains the SAME old cone, with no error and no
    // partial marks or retained storage. Normal bounds still compute afterwards.
    let limits = Limits {
        max_condition_nodes: old.temporary_nodes(),
        progress: CheckingProgress::new(|event| {
            assert!(
                event.failure.is_none(),
                "optional fallback must not emit a stopped phase"
            )
        }),
        ..l.clone()
    };
    let mut held = old.temporary_nodes();
    let mut optional_budget = Budget::tracked(&limits);
    let fallback_cone = prepare(
        Arc::clone(&old),
        &root,
        model.context(),
        &mut held,
        &mut optional_budget,
        &mut stats,
    )
    .unwrap();
    assert_eq!(stats.pruning, Some("condition nodes"));
    assert!(optional_budget.snapshot().exhausted.is_empty());
    assert!(Arc::ptr_eq(&old, &fallback_cone));
    assert_eq!(held, old.temporary_nodes());
    let size_error = run(
        &old,
        &root,
        model.context(),
        &mut held,
        &mut Budget::new(&l),
        0,
    )
    .unwrap_err();
    assert!(Arc::ptr_eq(
        &old,
        &fallback(size_error, Arc::clone(&old), &mut stats).unwrap()
    ));
    assert_eq!(stats.pruning, Some("pruning items"));
    super::super::compute(
        &fallback_cone,
        model.context(),
        &mut held,
        &mut Budget::new(&l),
        None,
    )
    .unwrap();
    for limits in [
        Limits {
            max_work: 0,
            ..l.clone()
        },
        Limits {
            timeout: std::time::Duration::ZERO,
            ..l.clone()
        },
    ] {
        assert!(
            prepare(
                Arc::clone(&old),
                &root,
                model.context(),
                &mut held,
                &mut Budget::new(&limits),
                &mut stats
            )
            .is_err()
        );
    }
    let limits = Limits::default();
    limits.cancellation.cancel();
    assert!(matches!(
        prepare(
            Arc::clone(&old),
            &root,
            model.context(),
            &mut held,
            &mut Budget::new(&limits),
            &mut stats
        ),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn positive_chain_prunes_and_owns_transitive_sources_outside_the_new_cone() {
    let mut c = Corpus::new();
    let kind = rel(&mut c, "kind", true);
    let root = rel(&mut c, "root", false);
    let middle = rel(&mut c, "middle", false);
    let seed = rel(&mut c, "seed", false);
    let reader = rel(&mut c, "reader", false);
    rule(&mut c, root, &[(middle, false)]);
    let transitive = rule(&mut c, middle, &[(seed, false)]);
    let seed_rule = rule(&mut c, seed, &[(kind, false), (reader, false)]);
    let reading = rule(&mut c, reader, &[(kind, true), (root, true)]);
    cones(&c, reading, root, |old, new, ctx| {
        assert!(new.atoms.len() < old.atoms.len());
        assert_eq!(new.atoms, [atom(root)]);
        assert!(new.producers.iter().all(|p| !p.live));
        for source in [transitive, seed_rule] {
            assert!(new.pruning.sources.iter().any(|p| p.rule.source == source));
        }
        assert!(
            new.pruning
                .reasons
                .values()
                .any(|r| matches!(r, DeadReason::Positive(_)))
        );
        let mut held = new.temporary_nodes();
        let b = super::super::compute(
            &Arc::new(new.clone()),
            ctx,
            &mut held,
            &mut Budget::new(&Limits::default()),
            None,
        )
        .unwrap();
        let owned = b.owned(&mut Budget::new(&Limits::default())).unwrap();
        assert!(owned.conditions[&atom(root)].is_false());
        assert!(
            owned
                .cone
                .pruning
                .sources
                .iter()
                .any(|p| p.rule.source == transitive)
        );
    });
}

#[test]
fn negative_requires_an_exact_guarantee_and_keeps_its_sources() {
    for guaranteed in [true, false] {
        let mut c = Corpus::new();
        let kind = rel(&mut c, "kind", true);
        let root = rel(&mut c, "root", false);
        let q = rel(&mut c, "q", false);
        let reader = rel(&mut c, "reader", false);
        let negative = rule(&mut c, root, &[(q, true)]);
        rule(&mut c, root, &[(reader, false)]);
        rule(&mut c, q, &[(root, false)]);
        let exact = guaranteed.then(|| rule(&mut c, q, &[(kind, false)]));
        let reading = rule(&mut c, reader, &[(kind, false), (root, false)]);
        cones(&c, reading, root, |old, new, ctx| {
            let producer = new
                .producers
                .iter()
                .find(|p| p.rule.source == negative)
                .unwrap();
            assert_eq!(producer.live, !guaranteed);
            if let Some(exact) = exact {
                assert!(matches!(
                    new.pruning.reasons[&producer.rule.id],
                    DeadReason::Negative { .. }
                ));
                assert!(!new.atoms.contains(&atom(q)));
                assert!(new.pruning.sources.iter().any(|p| p.rule.source == exact));
                for limits in [
                    Limits {
                        max_bdd_nodes: 1,
                        ..Limits::default()
                    },
                    Limits {
                        max_bdd_tasks: 0,
                        ..Limits::default()
                    },
                ] {
                    let old = Arc::new(old.clone());
                    let mut held = old.temporary_nodes();
                    let mut stats = Preparation::default();
                    let fallback = prepare(
                        Arc::clone(&old),
                        &atom(root),
                        ctx,
                        &mut held,
                        &mut Budget::new(&limits),
                        &mut stats,
                    )
                    .unwrap();
                    assert!(Arc::ptr_eq(&old, &fallback));
                    assert!(matches!(stats.pruning, Some("BDD nodes" | "BDD tasks")));
                    assert_eq!(held, old.temporary_nodes());
                }
            } else {
                assert!(new.atoms.contains(&atom(q)));
            }
        });
    }
}

#[test]
fn negative_guarantee_can_require_the_union_of_exact_producers() {
    let mut c = Corpus::new();
    let kind = rel(&mut c, "kind", true);
    let bit = rel(&mut c, "bit", true);
    let root = rel(&mut c, "root", false);
    let q = rel(&mut c, "q", false);
    let reader = rel(&mut c, "reader", false);
    let negative = rule(&mut c, root, &[(q, true)]);
    rule(&mut c, root, &[(reader, false)]);
    rule(&mut c, q, &[(root, false)]);
    rule(&mut c, q, &[(kind, false), (bit, false)]);
    rule(&mut c, q, &[(kind, false), (bit, true)]);
    let reading = rule(&mut c, reader, &[(kind, false), (root, false)]);
    cones(&c, reading, root, |_, new, _| {
        let p = new
            .producers
            .iter()
            .find(|p| p.rule.source == negative)
            .unwrap();
        assert!(!p.live);
        let DeadReason::Negative {
            exact_producers, ..
        } = &new.pruning.reasons[&p.rule.id]
        else {
            panic!()
        };
        assert_eq!(
            exact_producers.len(),
            2,
            "neither producer alone implies the guarantee"
        );
    });
}

#[test]
fn unseeded_positive_recursion_stays_possible() {
    let mut c = Corpus::new();
    let kind = rel(&mut c, "kind", true);
    let root = rel(&mut c, "root", false);
    let q = rel(&mut c, "q", false);
    let reader = rel(&mut c, "reader", false);
    rule(&mut c, root, &[(q, false)]);
    rule(&mut c, q, &[(root, false)]);
    rule(&mut c, root, &[(reader, true)]);
    let reading = rule(&mut c, reader, &[(kind, false), (root, false)]);
    cones(&c, reading, root, |old, new, _| {
        assert_eq!(old.atoms, new.atoms);
        assert!(new.producers.iter().all(|p| p.live));
        assert!(new.pruning.reasons.is_empty());
    });
}

#[test]
fn reading_rule_survives_its_dead_loop_premise() {
    let mut c = Corpus::new();
    let kind = rel(&mut c, "kind", true);
    let root = rel(&mut c, "root", false);
    let dead = rel(&mut c, "dead", false);
    let reader = rel(&mut c, "reader", false);
    rule(&mut c, root, &[(reader, true)]);
    rule(&mut c, root, &[(dead, false)]);
    rule(&mut c, dead, &[(kind, false), (root, false)]);
    let reading = rule(&mut c, reader, &[(kind, true), (dead, false)]);
    cones(&c, reading, root, |_, new, _| {
        assert!(
            new.producers
                .iter()
                .find(|p| p.rule.source == reading)
                .unwrap()
                .live
        );
        assert!(
            new.pruning
                .reasons
                .values()
                .any(|r| matches!(r,DeadReason::Positive(a) if *a == atom(dead)))
        );
        assert!(!new.atoms.contains(&atom(dead)));
    });
}
