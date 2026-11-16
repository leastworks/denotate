use super::*;
use crate::test_support::rewrites::{
    atom, compare, rel, rule, subsets, summaries, supported_models,
};
use denotate_ir::{Corpus, RelationId, RuleId};
use std::cell::RefCell;

fn four(implied: bool) -> (Corpus, RuleId, [RelationId; 4]) {
    four_fixed(implied, false)
}
fn four_fixed(implied: bool, fixed: bool) -> (Corpus, RuleId, [RelationId; 4]) {
    let mut c = Corpus::new();
    let fixed = fixed.then(|| rel(&mut c, "fixed", true));
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let guards = std::array::from_fn(|i| rel(&mut c, &format!("g{i}"), false));
    for (i, g) in guards.iter().enumerate() {
        rule(&mut c, *g, &[(x, i & 1 != 0)]);
        rule(&mut c, *g, &[(y, i & 2 != 0)]);
    }
    let cycle: [RelationId; 4] = std::array::from_fn(|i| rel(&mut c, &format!("a{i}"), false));
    let reader = if implied {
        let fails = rel(&mut c, "fails", false);
        rule(&mut c, fails, &[(guards[0], true)]);
        rule(&mut c, fails, &[(cycle[1], false)]);
        rule(&mut c, cycle[0], &[(fails, true)])
    } else {
        rule(&mut c, cycle[0], &[(guards[0], false), (cycle[1], true)])
    };
    for i in 1..4 {
        let mut body = vec![(guards[i], false), (cycle[(i + 1) % 4], true)];
        body.extend(fixed.map(|r| (r, true)));
        rule(&mut c, cycle[i], &body);
    }
    (c, reader, guards)
}
fn oracle(c: &Corpus, p: &GroundProgram) {
    compare(c, &Domains::new(), p);
    let before = p.original_rules().cloned().collect::<Vec<_>>();
    let after = p.rules().cloned().collect::<Vec<_>>();
    for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
        assert_eq!(
            supported_models(p, &before, &world),
            supported_models(p, &after, &world)
        );
    }
}

#[test]
fn four_guard_cycle_uses_two_levels_and_preserves_models_and_implied_guard() {
    for implied in [false, true] {
        let (c, _, _) = four(implied);
        let l = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        assert!(!raw.is_admitted());
        let events = RefCell::new(Vec::new());
        let p = raw
            .clone()
            .admit_fallback_for_test(
                &mut Budget::new(&l),
                Some(&|e| events.borrow_mut().push(e.clone())),
            )
            .unwrap();
        assert!(p.is_admitted(), "{implied}: {:?}", p.admission_limit());
        let proofs = p
            .rewrite_proofs()
            .filter_map(|p| p.guarded_settlement())
            .collect::<Vec<_>>();
        assert!(
            proofs
                .iter()
                .any(|p| matches!(p.certificate, GuardedCertificate::Split { .. }))
        );
        for p in &proofs {
            for case in p.certificate.walk() {
                if let GuardedCertificate::Split { atom, .. } = case {
                    assert!(raw.component_for(atom).unwrap().blocked_by.is_empty());
                    assert_eq!(
                        c.relation(atom.relation).unwrap().role,
                        denotate_ir::RelationRole::Derived
                    );
                }
            }
        }
        let events = events.borrow();
        let splits = events
            .iter()
            .filter_map(|e| e.guarded.as_ref()?.splits.as_ref())
            .collect::<Vec<_>>();
        assert!(splits.iter().any(|s| {
            s.state == "split"
                && s.branch_cyclic_atoms
                    .is_some_and(|[a, b]| a.max(b) == s.cyclic_atoms.unwrap())
        }));
        assert!(splits.iter().any(|s| s.max_depth >= 2));
        assert!(splits.iter().any(|s| s.fixed_candidates > 0));
        oracle(&c, &p);
        if implied {
            assert!(proofs.iter().any(|p| p.implied_guard.is_some()));
        }
    }
}

#[test]
fn executable_scores_differ_from_relaxed_proofs_and_constant_leaves_combine() {
    let (c, reader, guards) = four(false);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let m = p.symbolic(&l).unwrap();
    let all = summaries(&p, &m, &l);
    let candidate = all.values().find(|s| s.rule.source == reader).unwrap();
    let literal = candidate.rule.body.last().unwrap();
    let component = p.component_for(&literal.term.atom).unwrap();
    let mut producers = BTreeMap::<_, Vec<_>>::new();
    for s in all.values() {
        producers
            .entry(&s.rule.head.atom)
            .or_default()
            .push(s.rule.id);
    }
    let mut retained = 0;
    let mut budget = Budget::new(&l);
    let relaxed = crate::guarded_bounds::prepare(
        &p,
        component,
        candidate,
        &literal.term.atom,
        &all,
        &producers,
        m.context(),
        &mut retained,
        &mut budget,
        &mut Preparation::default(),
    )
    .unwrap();
    // Score excludes the relaxed edge explicitly, as the proof traversal does.
    let mut proof_graph = (*relaxed).clone();
    proof_graph
        .producers
        .retain(|p| Some(p.rule.id) != proof_graph.relaxed_rule);
    assert_eq!(
        cyclic_size(&proof_graph, &mut retained, &mut budget).unwrap(),
        0
    );
    let executable = crate::guarded_bounds::executable(
        &p,
        component,
        candidate,
        &literal.term.atom,
        &all,
        &producers,
        m.context(),
        &mut retained,
        &mut budget,
        &mut Preparation::default(),
    )
    .unwrap();
    assert_eq!(
        cyclic_size(&executable, &mut retained, &mut budget).unwrap(),
        4
    );
    // Under g0 and g1, one useful split suffices and its leaves are constants.
    let SymbolicFact::Settled(g1) = m.fact(&atom(guards[1])).unwrap() else {
        panic!()
    };
    let domain = m.context().and(&candidate.condition, &g1, &l).unwrap();
    let mut search = Search {
        program: &p,
        component,
        candidate,
        literal,
        meaning: &m,
        summaries: &all,
        producers: &producers,
        limits: CaseLimits::default(),
        stats: GuardedSplitProgress {
            leaves: 1,
            ..Default::default()
        },
    };
    let progress = crate::admission_progress::AdmissionReporter::new(None);
    let result = search
        .node(&domain, 0, false, &mut retained, &mut budget, &progress)
        .unwrap()
        .unwrap();
    assert!(matches!(
        result.expression.as_ref(),
        SettledExpression::Atom(_) | SettledExpression::Not(_)
    ));
    assert!(matches!(
        result.certificate,
        GuardedCertificate::Split { .. }
    ));
    let empty = search
        .node(
            &m.context().false_condition(),
            0,
            true,
            &mut retained,
            &mut budget,
            &progress,
        )
        .unwrap()
        .unwrap();
    assert!(matches!(
        empty.certificate,
        GuardedCertificate::Empty { .. }
    ));
}

fn with_search<T>(
    p: &GroundProgram,
    reader: RuleId,
    l: &Limits,
    run: impl FnOnce(&mut Search<'_, '_>) -> T,
) -> T {
    let m = p.symbolic(l).unwrap();
    let all = summaries(p, &m, l);
    let candidate = all.values().find(|s| s.rule.source == reader).unwrap();
    let literal = candidate.rule.body.last().unwrap();
    let component = p.component_for(&literal.term.atom).unwrap();
    let mut producers = BTreeMap::<_, Vec<_>>::new();
    for s in all.values() {
        producers
            .entry(&s.rule.head.atom)
            .or_default()
            .push(s.rule.id);
    }
    run(&mut Search {
        program: p,
        component,
        candidate,
        literal,
        meaning: &m,
        summaries: &all,
        producers: &producers,
        limits: CaseLimits::default(),
        stats: GuardedSplitProgress {
            leaves: 1,
            ..Default::default()
        },
    })
}

#[test]
fn split_cutoffs_leave_every_rule_intact_and_work_exhaustion_propagates() {
    let (c, reader, _) = four(false);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    with_search(&p, reader, &l, |s| {
        for limit in [
            CaseLimits {
                depth: 0,
                ..Default::default()
            },
            CaseLimits {
                leaves: 1,
                ..Default::default()
            },
            CaseLimits {
                candidates: 0,
                ..Default::default()
            },
        ] {
            s.limits = limit;
            s.stats = GuardedSplitProgress {
                leaves: 1,
                ..Default::default()
            };
            let mut retained = 0;
            let events = RefCell::new(Vec::new());
            let observer = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
            let progress = crate::admission_progress::AdmissionReporter::new(Some(&observer));
            progress.guarded_start(
                &p,
                1,
                &s.candidate.rule,
                &s.literal.term.atom,
                false,
                (0, 0),
            );
            let result = s
                .node(
                    &s.candidate.condition,
                    0,
                    false,
                    &mut retained,
                    &mut Budget::new(&l),
                    &progress,
                )
                .unwrap();
            assert!(result.is_none());
            assert_eq!(retained, 0);
            assert!(s.stats.cutoffs > 0);
            assert!(
                events
                    .borrow()
                    .iter()
                    .all(|e| e.failure.is_none() && e.skipped.is_none())
            );
        }
        s.limits = CaseLimits::default();
        let tight = Limits {
            max_work: 0,
            ..l.clone()
        };
        let progress = crate::admission_progress::AdmissionReporter::new(None);
        assert!(matches!(
            s.node(
                &s.candidate.condition,
                0,
                false,
                &mut 0,
                &mut Budget::new(&tight),
                &progress
            ),
            Err(CheckError::LimitExceeded {
                resource: "work",
                ..
            })
        ));
        let cancelled = Limits::default();
        cancelled.cancellation.cancel();
        assert!(matches!(
            s.node(
                &s.candidate.condition,
                0,
                false,
                &mut 0,
                &mut Budget::new(&cancelled),
                &progress
            ),
            Err(CheckError::Cancelled)
        ));
    });
    assert_eq!(
        p.rules().cloned().collect::<Vec<_>>(),
        p.original_rules().cloned().collect::<Vec<_>>()
    );
}

#[test]
fn assumption_fixed_and_guard_fixed_candidates_use_no_depth_or_leaves() {
    let (c, reader, _) = four_fixed(false, true);
    let l = Limits::default();
    let fixed = c.relations().find(|r| r.name == "fixed").unwrap().id;
    let mut p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    p.install_assumptions(
        &[denotate_ir::Restriction::Empty { relation: fixed }],
        None,
        &mut Budget::new(&l),
    )
    .unwrap();
    with_search(&p, reader, &l, |s| {
        s.limits.depth = 2;
        s.limits.leaves = 3;
        let d = s
            .meaning
            .context()
            .restrict(&s.candidate.condition, &mut Budget::new(&l))
            .unwrap();
        let result = s
            .node(
                &d,
                0,
                false,
                &mut 0,
                &mut Budget::new(&l),
                &crate::admission_progress::AdmissionReporter::new(None),
            )
            .unwrap()
            .unwrap();
        assert!(s.stats.fixed_candidates >= 2);
        assert_eq!(s.stats.cutoffs, 0);
        assert!(
            !result
                .certificate
                .walk()
                .any(|n| matches!(n,GuardedCertificate::Split{atom:a,..} if a.relation==fixed))
        );
    });
}

#[test]
fn same_cone_in_different_domains_never_reuses_a_branch_result() {
    let (mut c, reader, _) = four(false);
    let extra = rel(&mut c, "independent", true);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    with_search(&p, reader, &l, |s| {
        let ctx = s.meaning.context();
        let extra = ctx.input(&atom(extra), &l).unwrap();
        let domains = [
            ctx.and(&s.candidate.condition, &extra, &l).unwrap(),
            ctx.and(&s.candidate.condition, &ctx.not(&extra, &l).unwrap(), &l)
                .unwrap(),
        ];
        let mut outcomes = Vec::new();
        for domain in domains {
            s.stats = GuardedSplitProgress {
                leaves: 1,
                ..Default::default()
            };
            let result = s
                .node(
                    &domain,
                    0,
                    false,
                    &mut 0,
                    &mut Budget::new(&l),
                    &crate::admission_progress::AdmissionReporter::new(None),
                )
                .unwrap()
                .unwrap();
            outcomes.push(result);
        }
        let a = outcomes[0].certificate.bounds().next().unwrap();
        let b = outcomes[1].certificate.bounds().next().unwrap();
        assert_eq!(a.cone.atoms, b.cone.atoms);
        assert_eq!(
            a.cone
                .producers
                .iter()
                .map(|p| (p.rule.id, p.live))
                .collect::<Vec<_>>(),
            b.cone
                .producers
                .iter()
                .map(|p| (p.rule.id, p.live))
                .collect::<Vec<_>>()
        );
        assert!(
            !ctx.equivalent(&outcomes[0].truth, &outcomes[1].truth, &l)
                .unwrap()
        );
        assert!(!a.cone.domain.same_representation(&b.cone.domain));
    });
}

#[test]
fn a_dependency_used_by_only_one_branch_still_prevents_batching() {
    let (c, reader, _) = four(false);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    with_search(&p, reader, &l, |s| {
        let result = s
            .node(
                &s.candidate.condition,
                0,
                false,
                &mut 0,
                &mut Budget::new(&l),
                &crate::admission_progress::AdmissionReporter::new(None),
            )
            .unwrap()
            .unwrap();
        let GuardedCertificate::Split {
            when_true,
            when_false,
            ..
        } = &result.certificate
        else {
            panic!()
        };
        let left: BTreeSet<_> = when_true.summaries().map(|s| s.rule.id).collect();
        let right: BTreeSet<_> = when_false.summaries().map(|s| s.rule.id).collect();
        let changed = *left
            .symmetric_difference(&right)
            .find(|id| **id != s.candidate.rule.id)
            .expect("branch-specific producer");
        let mut batch = IndependentBatch::default();
        batch.insert(changed, BTreeSet::new());
        let complete = left.union(&right).copied().collect();
        assert!(!batch.accepts(s.candidate.rule.id, &complete));
        let missed = if left.contains(&changed) { right } else { left };
        assert!(batch.accepts(s.candidate.rule.id, &missed));
    });
}

#[test]
fn ambiguous_or_nonexistent_live_branch_is_not_a_certificate() {
    for self_loop in [false, true] {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        rule(
            &mut c,
            a,
            &[(x, false), (if self_loop { a } else { b }, true)],
        );
        if !self_loop {
            rule(&mut c, b, &[(x, false), (a, true)]);
        }
        let l = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &l)
            .unwrap()
            .admit(&l)
            .unwrap();
        assert!(!p.is_admitted());
        assert!(p.rewrite_proofs().all(|p| p.guarded_settlement().is_none()));
        oracle(&c, &p);
    }
}

#[test]
fn random_two_and_three_input_variants_preserve_stable_and_supported_models() {
    let mut seed = 93891u64;
    let mut random = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    let mut splits = 0;
    for i in 0..64 {
        let (mut c, _, _) = four(i % 2 == 0);
        if i % 2 == 0 {
            rel(&mut c, "z", true);
        }
        if i % 4 != 0 {
            let all = c.relations().map(|r| r.id).collect::<Vec<_>>();
            let derived = c
                .relations()
                .filter(|r| r.role == denotate_ir::RelationRole::Derived)
                .map(|r| r.id)
                .collect::<Vec<_>>();
            rule(
                &mut c,
                derived[random() % derived.len()],
                &[
                    (all[random() % all.len()], random() % 2 == 0),
                    (all[random() % all.len()], random() % 2 == 0),
                ],
            );
        }
        let l = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &l)
            .unwrap()
            .admit(&l)
            .unwrap();
        splits += p
            .rewrite_proofs()
            .filter_map(|p| p.guarded_settlement())
            .filter(|p| matches!(p.certificate, GuardedCertificate::Split { .. }))
            .count();
        oracle(&c, &p);
    }
    assert!(splits > 0);
}

#[test]
fn full_domain_storage_failure_does_not_suppress_narrower_branch_certificates() {
    let mut c = Corpus::new();
    // Wide settled guards make full-domain bound maps costly; branches prune
    // positive chains before constructing their much smaller maps.
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", true);
    for n in 0..32 {
        let input = rel(&mut c, &format!("input{n}"), true);
        rule(&mut c, x, &[(input, false)]);
    }
    let guards: [RelationId; 4] = std::array::from_fn(|i| rel(&mut c, &format!("g{i}"), false));
    for (i, guard) in guards.iter().enumerate() {
        rule(&mut c, *guard, &[(x, i & 1 != 0)]);
        rule(&mut c, *guard, &[(y, i & 2 != 0)]);
    }
    let cycle: [RelationId; 4] = std::array::from_fn(|i| rel(&mut c, &format!("a{i}"), false));
    let mut reader = None;
    for i in 0..4 {
        let mut next = cycle[(i + 1) % 4];
        for j in 0..16 {
            let link = rel(&mut c, &format!("link{i}_{j}"), false);
            rule(&mut c, link, &[(next, false)]);
            next = link;
        }
        let id = rule(&mut c, cycle[i], &[(guards[i], false), (next, true)]);
        if i == 0 {
            reader = Some(id);
        }
    }
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    with_search(&p, reader.unwrap(), &l, |s| {
        let limits = Limits {
            max_condition_nodes: 4096,
            ..l.clone()
        };
        let mut budget = Budget::new(&limits);
        let mut retained = 0;
        let cone = crate::guarded_bounds::prepare(
            &p,
            s.component,
            s.candidate,
            &s.literal.term.atom,
            s.summaries,
            s.producers,
            s.meaning.context(),
            &mut retained,
            &mut budget,
            &mut Preparation::default(),
        )
        .unwrap();
        assert!(matches!(
            crate::guarded_bounds::compute(
                &cone,
                s.meaning.context(),
                &mut retained,
                &mut budget,
                None
            ),
            Err(CheckError::LimitExceeded {
                resource: "condition nodes",
                ..
            })
        ));
        // Release failed broad-domain values, keeping the same work budget.
        drop(cone);
        retained = 0;
        let proof = p
            .case_settlement(
                s.candidate,
                s.literal,
                s.component,
                s.meaning,
                s.summaries,
                s.producers,
                None,
                &mut BTreeSet::new(),
                CaseLimits::default(),
                &mut retained,
                &mut budget,
                &crate::admission_progress::AdmissionReporter::new(None),
            )
            .unwrap()
            .unwrap();
        assert!(matches!(
            proof.certificate,
            GuardedCertificate::Split { .. }
        ));
        assert_eq!(retained, proof.nodes());
        assert!(
            proof
                .certificate
                .bounds()
                .all(|b| b.cone.atoms.len() < s.component.atoms.len())
        );
    });
}
