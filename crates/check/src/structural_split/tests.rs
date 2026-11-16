use super::*;
use crate::test_support::rewrites::{atom, compare, rel, rule, subsets, supported_models};

#[test]
fn four_guard_component_has_one_joint_certificate_and_no_bounds() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let guards: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("g{i}"), false));
    for (i, g) in guards.iter().enumerate() {
        rule(&mut c, *g, &[(x, i & 1 != 0)]);
        rule(&mut c, *g, &[(y, i & 2 != 0)]);
    }
    let cycle: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("a{i}"), false));
    for i in 0..4 {
        rule(
            &mut c,
            cycle[i],
            &[(guards[i], false), (cycle[(i + 1) % 4], true)],
        );
    }
    let l = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let events = std::cell::RefCell::new(Vec::new());
    let p = raw
        .clone()
        .admit_observed(
            &mut Budget::new(&l),
            Some(&|e| events.borrow_mut().push(e.clone())),
        )
        .unwrap();
    assert!(p.is_admitted(), "{:?}", p.admission_limit());
    let proofs: Vec<_> = p
        .rewrite_proofs()
        .filter_map(|p| p.guarded_settlement())
        .collect();
    assert_eq!(proofs.len(), 4);
    let GuardedCertificate::Joint(first) = &proofs[0].certificate else {
        panic!()
    };
    for proof in &proofs {
        let GuardedCertificate::Joint(j) = &proof.certificate else {
            panic!()
        };
        assert!(Arc::ptr_eq(first, j));
        assert!(proof.certificate.bounds().next().is_none());
    }
    assert!(
        events
            .borrow()
            .iter()
            .all(|e| e.attempts.keys().all(|k| !matches!(
                k,
                AdmissionAttemptKind::UpperBounds
                    | AdmissionAttemptKind::GuaranteedBounds
                    | AdmissionAttemptKind::GuardedBounds
            )))
    );
    compare(&c, &Domains::new(), &p);
    for world in subsets(&[atom(x), atom(y)]) {
        assert_eq!(
            supported_models(&p, &p.original_rules().cloned().collect::<Vec<_>>(), &world),
            supported_models(&p, &p.rules().cloned().collect::<Vec<_>>(), &world)
        );
    }
}

fn oracle(c: &denotate_ir::Corpus, p: &GroundProgram) {
    compare(c, &Domains::new(), p);
    // The offered source action removes just the proved negative occurrences,
    // not all the other replacements in the joint batch. Check it independently.
    let mut deletions = p.original_rules().cloned().collect::<Vec<_>>();
    for proof in p.rewrite_proofs().filter(|p| p.is_redundant_negation()) {
        let occurrence = match proof.kind {
            RewriteKind::Discharge { literal_occurrence }
            | RewriteKind::GuardedSettlement { literal_occurrence } => literal_occurrence,
            _ => unreachable!(),
        };
        deletions
            .iter_mut()
            .find(|r| r.id == proof.candidate().id)
            .unwrap()
            .body
            .retain(|l| l.term.occurrence != occurrence);
    }
    for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
        assert_eq!(
            supported_models(p, &p.original_rules().cloned().collect::<Vec<_>>(), &world),
            supported_models(p, &p.rules().cloned().collect::<Vec<_>>(), &world)
        );
        assert_eq!(
            supported_models(p, &p.original_rules().cloned().collect::<Vec<_>>(), &world),
            supported_models(p, &deletions, &world),
            "removal action"
        );
        let atoms = p.atoms().cloned().collect::<Vec<_>>();
        let inputs = p.input_atoms().cloned().collect::<BTreeSet<_>>();
        assert_eq!(
            crate::test_support::rewrites::stable_models(
                &atoms,
                &inputs,
                &p.original_rules().cloned().collect::<Vec<_>>(),
                &world
            ),
            crate::test_support::rewrites::stable_models(&atoms, &inputs, &deletions, &world),
            "removal action stable models"
        );
    }
}
fn proofs(p: &GroundProgram, head: &GroundAtom, l: &Limits) -> Vec<GuardedSettlementProof> {
    let m = p.symbolic(&Limits::default()).unwrap();
    let summaries = crate::test_support::rewrites::summaries(p, &m, &Limits::default());
    p.structural_splits(
        p.component_for(head).unwrap(),
        &summaries,
        &m,
        &mut 0,
        &mut Budget::new(l),
        &AdmissionReporter::new(None),
        &mut false,
    )
    .unwrap()
}

#[test]
fn constant_values_and_multiple_occurrences_commit_together() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let d = rel(&mut c, "d", false);
    rule(&mut c, a, &[(x, false)]);
    rule(&mut c, a, &[(x, true)]);
    let two = rule(&mut c, a, &[(b, true), (d, true)]);
    rule(&mut c, b, &[(a, true)]);
    rule(&mut c, d, &[(a, true)]);
    // A dead positive occurrence must be replaced too, with false.
    rule(&mut c, d, &[(b, false)]);
    let l = Limits::default();
    let mut p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let batch = proofs(&p, &atom(a), &l);
    assert!(
        batch
            .iter()
            .any(|p| matches!(*p.replacement, SettledExpression::Constant(true)))
    );
    assert!(
        batch
            .iter()
            .any(|p| matches!(*p.replacement, SettledExpression::Constant(false)))
    );
    assert_eq!(
        batch
            .iter()
            .filter(|p| p.proof.candidate.rule.source == two)
            .count(),
        2
    );
    p.commit_joint_for_test(batch, &mut Budget::new(&l))
        .unwrap();
    assert!(p.is_admitted());
    oracle(&c, &p);
}

#[test]
fn unresolved_external_premise_is_not_absence() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let u = rel(&mut c, "u", false);
    let v = rel(&mut c, "v", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, u, &[(v, true)]);
    rule(&mut c, v, &[(u, true)]);
    rule(&mut c, a, &[(x, false), (b, true)]);
    rule(&mut c, b, &[(x, true), (a, true)]);
    rule(&mut c, a, &[(u, false)]);
    let l = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    assert!(proofs(&raw, &atom(a), &l).is_empty());
    assert_eq!(raw.rewrite_proofs().count(), 0);
    let p = raw.admit(&l).unwrap();
    assert!(!p.is_admitted());
    oracle(&c, &p);
}

#[test]
fn ambiguous_and_no_meaning_islands_are_not_hidden_by_a_split() {
    for odd in [false, true] {
        let mut c = denotate_ir::Corpus::new();
        let x = rel(&mut c, "x", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        let u = rel(&mut c, "u", false);
        let v = rel(&mut c, "v", false);
        rule(&mut c, a, &[(x, false), (b, true)]);
        rule(&mut c, b, &[(x, true), (a, true)]);
        rule(&mut c, u, &[(if odd { u } else { v }, true)]);
        rule(&mut c, v, &[(u, true)]);
        // One original SCC; splitting x disconnects the still-cyclic island.
        rule(&mut c, a, &[(x, false), (u, false)]);
        rule(&mut c, u, &[(x, true), (a, false)]);
        let l = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        assert_eq!(
            raw.component_for(&atom(a)).unwrap().id,
            raw.component_for(&atom(u)).unwrap().id
        );
        assert!(proofs(&raw, &atom(a), &l).is_empty());
        let p = raw.admit(&l).unwrap();
        assert!(!p.is_admitted());
        oracle(&c, &p);
    }
}

#[test]
fn random_two_and_three_input_components_preserve_both_model_oracles() {
    let mut seed = 0x12235_u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut joint = 0;
    for n in 0..128 {
        let mut c = denotate_ir::Corpus::new();
        let inputs: Vec<_> = (0..2 + n % 2)
            .map(|i| rel(&mut c, &format!("x{i}"), true))
            .collect();
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        let d = rel(&mut c, "d", false);
        rule(&mut c, a, &[(inputs[0], false), (b, true)]);
        rule(&mut c, b, &[(inputs[0], true), (a, true)]);
        rule(&mut c, d, &[(a, false), (b, true)]);
        let derived = [a, b, d];
        let all: Vec<_> = inputs.iter().chain(&derived).copied().collect();
        for _ in 0..next() % 5 {
            let head = derived[next() as usize % 3];
            let body: Vec<_> = (0..1 + next() % 3)
                .map(|_| (all[next() as usize % all.len()], next() % 2 == 0))
                .collect();
            rule(&mut c, head, &body);
        }
        let l = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &l)
            .unwrap()
            .admit(&l)
            .unwrap();
        joint += p
            .rewrite_proofs()
            .filter_map(|p| p.guarded_settlement())
            .filter(|p| matches!(p.certificate, GuardedCertificate::Joint(_)))
            .count();
        oracle(&c, &p);
    }
    assert!(joint > 0);
}

#[test]
fn staging_exhaustion_and_interrupted_commit_install_nothing() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    // Many retained authored occurrences make staging larger than the search.
    for _ in 0..12 {
        rule(&mut c, a, &[(x, false), (b, true)]);
        rule(&mut c, b, &[(x, true), (a, true)]);
    }
    let l = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let m = raw.symbolic(&l).unwrap();
    let summaries = crate::test_support::rewrites::summaries(&raw, &m, &l);
    let component = raw.component_for(&atom(a)).unwrap();
    let mut staging_failed = false;
    for cap in (100..20_000).step_by(25) {
        let limited = Limits {
            max_condition_nodes: cap,
            ..l.clone()
        };
        let events = std::cell::RefCell::new(Vec::new());
        let observe = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
        let report = AdmissionReporter::new(Some(&observe));
        let p = raw
            .structural_splits(
                component,
                &summaries,
                &m,
                &mut 0,
                &mut Budget::new(&limited),
                &report,
                &mut false,
            )
            .unwrap();
        let events = events.borrow();
        if events.iter().any(|e| {
            e.structural_split
                .as_ref()
                .is_some_and(|s| s.state == "staging")
        }) && events.iter().any(|e| e.split_fallback.is_some())
        {
            assert!(p.is_empty());
            assert_eq!(raw.rewrite_proofs().count(), 0);
            let fallback = raw.clone().admit(&l).unwrap();
            assert!(fallback.is_admitted());
            oracle(&c, &fallback);
            staging_failed = true;
            break;
        }
    }
    assert!(staging_failed);
    let batch = proofs(&raw, &atom(a), &l);
    assert!(!batch.is_empty());
    let mut interrupted = false;
    let mut committed = false;
    for cap in (0..5000).step_by(20) {
        let limited = Limits {
            max_work: cap,
            ..l.clone()
        };
        let mut p = raw.clone();
        match p.commit_joint_for_test(batch.clone(), &mut Budget::new(&limited)) {
            Ok(()) => {
                assert!(p.is_admitted());
                oracle(&c, &p);
                committed = true;
                break;
            }
            Err(_) => {
                interrupted = true;
                assert_eq!(
                    p.rules().collect::<Vec<_>>(),
                    raw.rules().collect::<Vec<_>>()
                );
                assert_eq!(p.rewrite_proofs().count(), 0);
            }
        }
    }
    assert!(interrupted && committed);
}

#[test]
fn optional_caps_fall_back_and_global_work_failure_propagates() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(x, false), (b, true)]);
    rule(&mut c, b, &[(x, true), (a, true)]);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let m = p.symbolic(&l).unwrap();
    let summaries = crate::test_support::rewrites::summaries(&p, &m, &l);
    let component = p.component_for(&atom(a)).unwrap();
    let progress = AdmissionReporter::new(None);
    for limits in [
        SplitLimits {
            scoring_work: 0,
            ..SplitLimits::default()
        },
        SplitLimits {
            depth: 0,
            ..SplitLimits::default()
        },
        SplitLimits {
            leaves: 1,
            ..SplitLimits::default()
        },
    ] {
        let mut search = Search {
            expressions: Expressions::default(),
            program: &p,
            component,
            summaries: &summaries,
            meaning: &m,
            limits,
            work_start: 0,
            stats: GuardedSplitProgress {
                leaves: 1,
                ..Default::default()
            },
        };
        let mut retained = 0;
        assert!(
            search
                .node(
                    &m.context().permitted_worlds(),
                    0,
                    &mut retained,
                    &mut Budget::new(&l),
                    &progress
                )
                .unwrap()
                .is_none()
        );
        assert_eq!(retained, 0);
        assert_eq!(p.rewrite_proofs().count(), 0);
    }
    let exhausted = Limits {
        max_work: 0,
        ..l.clone()
    };
    let result = p.structural_splits(
        component,
        &summaries,
        &m,
        &mut 0,
        &mut Budget::new(&exhausted),
        &progress,
        &mut false,
    );
    assert!(matches!(
        result,
        Err(CheckError::LimitExceeded {
            resource: "work",
            ..
        })
    ));
}

#[test]
fn sparse_false_atoms_do_not_become_positive_replacement_dependencies() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let never = rel(&mut c, "never", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(x, false), (b, true), (never, true)]);
    rule(&mut c, b, &[(x, true), (a, true)]);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l)
        .unwrap()
        .admit(&l)
        .unwrap();
    assert!(p.is_admitted());
    assert!(
        p.rules()
            .flat_map(|r| &r.replacements)
            .all(|r| r.expression.atoms().all(|a| a.relation != never))
    );
    oracle(&c, &p);
}

#[test]
fn recoverable_staging_failure_continues_the_same_admission_pipeline() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let gs: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("g{i}"), false));
    let rs: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("r{i}"), false));
    for i in 0..4 {
        rule(&mut c, gs[i], &[(x, i & 1 != 0)]);
        rule(&mut c, gs[i], &[(y, i & 2 != 0)]);
        rule(&mut c, rs[i], &[(gs[i], false), (rs[(i + 1) % 4], true)]);
    }
    let l = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let mut exercised = false;
    for cap in (100..5000).step_by(20) {
        let events = std::cell::RefCell::new(Vec::new());
        let limited = Limits {
            max_condition_nodes: cap,
            ..l.clone()
        };
        let p = raw
            .clone()
            .admit_observed(
                &mut Budget::new(&limited),
                Some(&|e| events.borrow_mut().push(e.clone())),
            )
            .unwrap();
        let events = events.borrow();
        if let Some(failure) = events.iter().position(|e| e.split_fallback.is_some()) {
            if events[..failure].iter().any(|e| {
                e.structural_split
                    .as_ref()
                    .is_some_and(|s| s.state == "staging")
            }) {
                assert!(
                    events[failure + 1..]
                        .iter()
                        .any(|e| e.stage == "bound-removals")
                );
                assert!(
                    p.rewrite_proofs()
                        .filter_map(|p| p.guarded_settlement())
                        .all(|p| !matches!(p.certificate, GuardedCertificate::Joint(_)))
                );
                oracle(&c, &p);
                exercised = true;
                break;
            }
        }
    }
    assert!(exercised);
}

#[test]
fn findings_keep_authored_forwarding_sources_in_scoped_replay() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    // Declare the forwarding consumer first: execution order after replacement
    // need not be the authored evidence order.
    let forwarded = rel(&mut c, "forwarded", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let u = rel(&mut c, "unrelated", false);
    rule(&mut c, a, &[(x, false), (b, true)]);
    rule(&mut c, b, &[(x, true), (forwarded, true)]);
    rule(&mut c, forwarded, &[(a, false)]);
    rule(&mut c, u, &[(u, true)]);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l)
        .unwrap()
        .admit(&l)
        .unwrap();
    assert!(!p.is_admitted());
    let roots = BTreeSet::from([atom(forwarded)]);
    let cone = p.dependency_cone(roots.clone(), &l).unwrap();
    assert!(cone.blocked_by.is_empty());
    assert!(cone.facts.contains(&atom(a)));
    let replay = p
        .evaluate_selected([atom(x)], Some(&cone.components), &mut Budget::new(&l))
        .unwrap();
    let evidence =
        crate::findings::collect_evidence(&replay, &roots, &mut Budget::new(&l)).unwrap();
    assert!(evidence[&atom(a)].order < evidence[&atom(forwarded)].order);
    let GroundEvidence::Derived { premises, .. } = &evidence[&atom(forwarded)].evidence else {
        panic!()
    };
    assert!(
        premises
            .iter()
            .any(|p| matches!(p, PremiseEvidence::Positive {fact,..} if fact == &atom(a)))
    );
    assert!(
        premises
            .iter()
            .any(|p| matches!(p, PremiseEvidence::Replaced { .. }))
    );
}

#[test]
fn scoring_cutoff_keeps_a_useful_partial_split() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let guards: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("g{i}"), false));
    let cycle: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("a{i}"), false));
    for i in 0..4 {
        rule(&mut c, guards[i], &[(x, i & 1 != 0)]);
        rule(&mut c, guards[i], &[(y, i & 2 != 0)]);
        rule(
            &mut c,
            cycle[i],
            &[(guards[i], false), (cycle[(i + 1) % 4], true)],
        );
    }
    let l = Limits::default();
    let mut p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let batch = {
        let m = p.symbolic(&l).unwrap();
        let summaries = crate::test_support::rewrites::summaries(&p, &m, &l);
        let mut search = Search {
            expressions: Expressions::default(),
            program: &p,
            component: p.component_for(&atom(cycle[0])).unwrap(),
            summaries: &summaries,
            meaning: &m,
            limits: SplitLimits {
                scoring_work: 1,
                ..Default::default()
            },
            work_start: 0,
            stats: GuardedSplitProgress {
                leaves: 1,
                ..Default::default()
            },
        };
        let mut retained = 0;
        let mut budget = Budget::new(&l);
        let progress = AdmissionReporter::new(None);
        let tree = search
            .node(
                &m.context().permitted_worlds(),
                0,
                &mut retained,
                &mut budget,
                &progress,
            )
            .unwrap()
            .expect("the best partial split must survive the scoring cutoff");
        assert!(search.stats.cutoffs > 0);
        search
            .stage(tree, &mut retained, &mut budget, &progress)
            .unwrap()
    };
    p.commit_joint_for_test(batch, &mut Budget::new(&l))
        .unwrap();
    assert!(p.is_admitted());
    oracle(&c, &p);
}

#[test]
fn cheap_scoring_can_reach_a_useful_candidate_after_sixteen_decoys() {
    let mut c = denotate_ir::Corpus::new();
    let decoys: Vec<_> = (0..20)
        .map(|i| rel(&mut c, &format!("decoy{i}"), true))
        .collect();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    for (head, other, negative) in [(a, b, false), (b, a, true)] {
        let mut body: Vec<_> = decoys.iter().map(|r| (*r, false)).collect();
        body.extend([(x, negative), (other, true)]);
        rule(&mut c, head, &body);
    }
    let l = Limits::default();
    let mut p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    // Every candidate has the same frequency. Each early split leaves the cycle
    // in its true branch; only x makes both leaves acyclic. Stopping at 16 used
    // to abandon this component even though each score is very cheap.
    let batch = proofs(&p, &atom(a), &l);
    assert!(!batch.is_empty());
    p.commit_joint_for_test(batch, &mut Budget::new(&l))
        .unwrap();
    assert!(p.is_admitted());
    for enabled in [false, true] {
        let mut world: Vec<_> = decoys.iter().map(|r| atom(*r)).collect();
        if enabled {
            world.push(atom(x));
        }
        let replay = p.evaluate(world, &l).unwrap();
        assert_eq!(replay.fact(&atom(a)).unwrap(), FactState::Settled(enabled));
        assert_eq!(replay.fact(&atom(b)).unwrap(), FactState::Settled(!enabled));
    }
}

#[test]
fn configurable_depth_leaves_and_total_work_leave_fallback_usable() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let guards: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("g{i}"), false));
    let cycle: [_; 4] = std::array::from_fn(|i| rel(&mut c, &format!("r{i}"), false));
    for i in 0..4 {
        rule(&mut c, guards[i], &[(x, i & 1 != 0)]);
        rule(&mut c, guards[i], &[(y, i & 2 != 0)]);
        rule(
            &mut c,
            cycle[i],
            &[(guards[i], false), (cycle[(i + 1) % 4], true)],
        );
    }
    let defaults = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &defaults).unwrap();
    let enough = Limits {
        max_structural_split_depth: 8,
        max_structural_split_leaves: 64,
        ..defaults.clone()
    };
    assert!(!proofs(&p, &atom(cycle[0]), &enough).is_empty());
    for limited in [
        Limits {
            max_structural_split_depth: 1,
            ..enough.clone()
        },
        Limits {
            max_structural_split_leaves: 1,
            ..enough.clone()
        },
        Limits {
            max_structural_split_work: 1,
            ..enough.clone()
        },
        Limits {
            max_structural_split_work: 0,
            ..enough.clone()
        },
    ] {
        assert!(proofs(&p, &atom(cycle[0]), &limited).is_empty());
        assert_eq!(p.rewrite_proofs().count(), 0);
        let events = std::cell::RefCell::new(Vec::new());
        let admitted = p
            .clone()
            .admit_observed(
                &mut Budget::new(&limited),
                Some(&|e| events.borrow_mut().push(e.clone())),
            )
            .unwrap();
        assert!(
            admitted.admission_limit().is_none(),
            "{:?}",
            admitted.admission_limit()
        );
        assert!(events.borrow().iter().any(|e| e.stage == "bound-removals"));
        oracle(&c, &admitted);
    }
}
