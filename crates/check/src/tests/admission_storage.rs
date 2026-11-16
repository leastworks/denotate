use crate::{
    admission_scope::AdmissionScope,
    admission_skips::Attempts,
    admission_storage::SummaryPlan,
    contracts::ConeIndex,
    limits::Budget,
    test_support::rewrites::{atom, rel, rule, subsets},
    *,
};
use denotate_ir::*;
use std::{cell::RefCell, collections::BTreeSet, sync::Arc};

#[test]
fn released_shared_providers_and_replacement_leaves_remain_live_until_their_last_reader() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", true);
    let q = rel(&mut c, "q", true);
    let common = rel(&mut c, "common", false);
    let first = rel(&mut c, "first", false);
    let last = rel(&mut c, "last", false);
    rule(&mut c, common, &[(p, false), (q, false)]);
    rule(&mut c, first, &[(common, false)]);
    let changed = rule(&mut c, last, &[(common, true)]);
    let limits = Limits::default();
    let mut raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let r = raw.rules.iter_mut().find(|r| r.source == changed).unwrap();
    let old = r.body.remove(0);
    r.replacements.push(SettledReplacement {
        occurrence: old.term.occurrence,
        expression: Arc::new(SettledExpression::Not(Arc::new(SettledExpression::Atom(
            atom(common),
        )))),
    });
    crate::graph::analyze(&mut raw, &mut Budget::new(&limits)).unwrap();
    let mut budget = Budget::new(&limits);
    let cone = ConeIndex::new(&raw, &mut budget)
        .unwrap()
        .build(raw.atoms().cloned(), &mut budget)
        .unwrap();
    let retained = raw
        .symbolic_for_admission(
            &mut budget,
            None,
            &cone,
            &BTreeSet::from([atom(first), atom(last)]),
            0,
        )
        .unwrap();
    assert!(matches!(
        retained.fact(&atom(common)),
        Err(CheckError::Internal("read of released symbolic condition"))
    ));
    let full = raw.symbolic(&limits).unwrap();
    for world in subsets(&[atom(p), atom(q)]) {
        for output in [first, last] {
            let SymbolicFact::Settled(a) = retained.fact(&atom(output)).unwrap() else {
                panic!()
            };
            let SymbolicFact::Settled(b) = full.fact(&atom(output)).unwrap() else {
                panic!()
            };
            assert_eq!(
                retained
                    .context()
                    .evaluate(&a, world.iter().cloned(), &limits)
                    .unwrap(),
                full.context()
                    .evaluate(&b, world.iter().cloned(), &limits)
                    .unwrap()
            );
        }
    }
}

#[test]
fn recursive_restart_keeps_its_external_readers_and_never_exposes_partial_conditions() {
    let mut c = Corpus::new();
    let wide = rel(&mut c, "wide", false);
    for i in 0..8 {
        let input = rel(&mut c, &format!("input{i}"), true);
        rule(&mut c, wide, &[(input, false)]);
    }
    let copy = rel(&mut c, "copy", false);
    let reader = rel(&mut c, "reader", false);
    rule(&mut c, copy, &[(wide, false)]);
    rule(&mut c, wide, &[(copy, false)]);
    rule(&mut c, reader, &[(copy, true)]);
    let limits = Limits {
        max_bdd_nodes: 5,
        ..Limits::default()
    };
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut budget = Budget::new(&limits);
    let cone = ConeIndex::new(&raw, &mut budget)
        .unwrap()
        .build([atom(reader)], &mut budget)
        .unwrap();
    let kept = raw
        .symbolic_for_admission(&mut budget, None, &cone, &BTreeSet::from([atom(reader)]), 0)
        .unwrap();
    let full = raw.symbolic(&limits).unwrap();
    assert_eq!(kept.unknown, full.unknown);
    for r in [wide, copy, reader] {
        assert!(matches!(
            kept.fact(&atom(r)).unwrap(),
            SymbolicFact::Inconclusive(_)
        ));
        assert!(!kept.conditions.contains_key(&atom(r)));
    }
}

#[test]
fn summary_frontier_keeps_complete_one_hop_support_without_the_whole_upstream_chain() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let early = rel(&mut c, "early", false);
    let middle = rel(&mut c, "middle", false);
    let guard = rel(&mut c, "guard", false);
    rule(&mut c, early, &[(i, false)]);
    rule(&mut c, middle, &[(early, false)]);
    rule(&mut c, guard, &[(middle, false)]);
    rule(&mut c, guard, &[(i, false)]);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(guard, false), (b, true)]);
    rule(&mut c, b, &[(guard, true), (a, true)]);
    let l = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let mut budget = Budget::new(&l);
    let scope = AdmissionScope::build(&raw, AdmissionPhase::Relevant, &mut budget).unwrap();
    let mut attempts = Attempts::default();
    let plan = SummaryPlan::build(&raw, &scope, &attempts, &mut budget).unwrap();
    let m = raw
        .symbolic_for_admission(&mut budget, None, &scope.cone, &plan.keep, plan.nodes)
        .unwrap();
    assert!(matches!(m.fact(&atom(early)), Err(CheckError::Internal(_))));
    let mut held = m.metrics().retained_condition_nodes + plan.nodes;
    let s = plan
        .build_summaries(
            &raw,
            &m,
            &mut held,
            &mut attempts,
            &mut budget,
            &crate::admission_progress::AdmissionReporter::new(None),
        )
        .unwrap();
    assert_eq!(
        s.values()
            .filter(|s| s.rule.head.atom == atom(guard))
            .count(),
        2
    );
    assert!(
        s.values()
            .all(|s| ![atom(early), atom(middle)].contains(&s.rule.head.atom))
    );
    let full = raw.symbolic(&l).unwrap();
    let all = crate::test_support::rewrites::summaries(&raw, &full, &l);
    for (id, summary) in &s {
        assert_eq!(summary.exact, all[id].exact);
        assert!(
            m.context()
                .equivalent(&summary.condition, &all[id].condition, &l)
                .unwrap()
        );
    }
    let admitted = raw.admit(&l).unwrap();
    assert!(admitted.is_admitted());
    crate::test_support::rewrites::compare(&c, &Domains::new(), &admitted);
    let expanded = crate::boolean::condition_storage(
        admitted
            .rewrite_proofs()
            .flat_map(RewriteProof::profile_conditions),
    );
    let compact = crate::boolean::condition_storage(crate::rewrite::profile_proof_conditions(
        admitted.rewrite_proofs(),
    ));
    assert_eq!(compact.nodes, expanded.nodes);
    assert_eq!(compact.distinct_arrays, expanded.distinct_arrays);
    assert!(
        compact.references < expanded.references,
        "shared joint evidence is traversed only once in pool reporting"
    );
}

#[test]
fn summary_overflow_skips_dependent_components_and_preserves_an_independent_certificate() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", true);
    let q = rel(&mut c, "q", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let mut wide = vec![(p, false), (q, false)].repeat(150);
    wide.push((b, true));
    rule(&mut c, a, &wide);
    rule(&mut c, b, &[(a, true)]);
    let dependent = rel(&mut c, "dependent", false);
    let dependent_back = rel(&mut c, "dependent_back", false);
    rule(&mut c, dependent, &[(a, false), (dependent_back, true)]);
    rule(&mut c, dependent_back, &[(dependent, true)]);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    rule(&mut c, x, &[(p, false), (y, true)]);
    rule(&mut c, y, &[(p, true), (x, true)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut found = false;
    for cap in (200..2400).step_by(50) {
        let l = Limits {
            max_condition_nodes: cap,
            ..Limits::default()
        };
        let events = RefCell::new(Vec::new());
        let admitted = raw
            .clone()
            .admit_observed(
                &mut Budget::new(&l),
                Some(&|e| events.borrow_mut().push(e.clone())),
            )
            .unwrap();
        if admitted.admission_limit().is_none()
            && admitted
                .admission_skips()
                .any(|s| s.kind == AdmissionAttemptKind::SummaryStorage)
            && admitted
                .component_for(&atom(x))
                .unwrap()
                .blocked_by
                .is_empty()
        {
            assert!(
                !admitted
                    .component_for(&atom(a))
                    .unwrap()
                    .blocked_by
                    .is_empty()
            );
            for head in [a, dependent] {
                let component = admitted.component_for(&atom(head)).unwrap();
                assert!(
                    admitted
                        .admission_skips_for(component)
                        .any(|s| s.kind == AdmissionAttemptKind::SummaryStorage)
                );
            }
            assert!(events.borrow().iter().any(|e| {
                e.stage == "summaries"
                    && e.skipped
                        .as_ref()
                        .is_some_and(|s| s.kind == AdmissionAttemptKind::SummaryStorage)
            }));
            found = true;
            break;
        }
    }
    assert!(
        found,
        "exercise summary-local storage exhaustion with independent progress"
    );
}

#[test]
fn split_unblocks_a_layered_cone_that_fits_only_with_last_reader_release() {
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    let a = rel(&mut c, "upstream_a", false);
    let b = rel(&mut c, "upstream_b", false);
    rule(&mut c, a, &[(flag, false), (b, true)]);
    rule(&mut c, b, &[(flag, true), (a, true)]);
    let inputs: Vec<_> = (0..16)
        .map(|i| rel(&mut c, &format!("input{i}"), true))
        .collect();
    let mut previous = a;
    for i in 0..120 {
        let next = rel(&mut c, &format!("layer{i}"), false);
        rule(
            &mut c,
            next,
            &[(previous, false), (inputs[i % inputs.len()], false)],
        );
        previous = next;
    }
    let x = rel(&mut c, "downstream_x", false);
    let y = rel(&mut c, "downstream_y", false);
    rule(&mut c, x, &[(previous, false), (y, true)]);
    rule(&mut c, y, &[(previous, true), (x, true)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let unlimited = raw.clone().admit(&Limits::default()).unwrap();
    assert!(unlimited.is_admitted());
    let mut exercised = false;
    for cap in (600..6000).step_by(100) {
        let limits = Limits {
            max_condition_nodes: cap,
            ..Limits::default()
        };
        let events = RefCell::new(Vec::new());
        let admitted = raw
            .clone()
            .admit_observed(
                &mut Budget::new(&limits),
                Some(&|e| events.borrow_mut().push(e.clone())),
            )
            .unwrap();
        if !admitted.is_admitted() || admitted.admission_limit().is_some() {
            continue;
        }
        // The old retain-all evaluator cannot preserve the terminal guard at
        // this allowance, even on the fully admitted graph.
        let full = unlimited.symbolic(&limits).unwrap();
        if !matches!(
            full.fact(&atom(previous)).unwrap(),
            SymbolicFact::Inconclusive(_)
        ) {
            continue;
        }
        assert!(
            events
                .borrow()
                .iter()
                .filter(|e| e
                    .structural_split
                    .as_ref()
                    .is_some_and(|s| s.state == "certified"))
                .count()
                >= 2
        );
        assert!(admitted.admission_skips().next().is_none());
        exercised = true;
        break;
    }
    assert!(
        exercised,
        "a split followed by a wide provider cone must fit without retaining its intermediates"
    );
}

#[test]
fn layered_condition_sizes_and_restriction_to_w_preserve_permitted_meanings() {
    let mut c = Corpus::new();
    let sort = c.declare_sort("Choice").unwrap();
    let choices: Vec<_> = (0..8)
        .map(|i| c.declare_constant(format!("c{i}"), sort).unwrap())
        .collect();
    let selected = c
        .declare_relation(
            "selected",
            RelationRole::Input,
            [Parameter::new("choice", sort)],
        )
        .unwrap();
    let mut previous = None;
    let mut outputs = Vec::new();
    for i in 0..40 {
        let output = rel(&mut c, &format!("layer{i}"), false);
        let head = c.atom(output, []).unwrap();
        let input = c
            .atom(selected, [Term::Constant(choices[i % choices.len()])])
            .unwrap();
        c.add_rule(head, [Literal::Positive(input)]).unwrap();
        if let Some(previous) = previous {
            rule(&mut c, output, &[(previous, false)]);
        }
        previous = Some(output);
        outputs.push(atom(output));
    }
    let l = Limits::default();
    let p = GroundProgram::prepare_with_input_groups(
        &c,
        &Domains::from([(sort, choices.clone())]),
        &[InputAtMostOne {
            relation: selected,
            group_by: vec![],
        }],
        &l,
    )
    .unwrap();
    let m = p.symbolic(&l).unwrap();
    let mut sizes = Vec::new();
    for output in outputs {
        let SymbolicFact::Settled(raw) = m.fact(&output).unwrap() else {
            panic!()
        };
        let restricted = m.context().restrict(&raw, &mut Budget::new(&l)).unwrap();
        for choice in std::iter::once(None).chain(choices.iter().map(Some)) {
            let world = choice.map(|choice| GroundAtom::new(selected, [*choice]));
            assert_eq!(
                m.context().evaluate(&raw, world.clone(), &l).unwrap(),
                m.context().evaluate(&restricted, world, &l).unwrap()
            );
        }
        sizes.push((raw.node_count(), restricted.node_count()));
    }
    sizes.sort_by(|a, b| b.0.cmp(&a.0).then(b.1.cmp(&a.1)));
    // Manual measurement, deliberately no node-count golden.
    println!(
        "largest layered conditions (unrestricted, within W): {:?}",
        &sizes[..5]
    );
}
