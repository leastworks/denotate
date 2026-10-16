use super::rewrites::{atom, dsl_fixture, rel, rule, stable_models, subsets, supported_models};
use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;

// Independent Cartesian grounder + assignment enumeration. These fixtures have
// a single unresolved SCC with acyclic upstream rules, so completion solutions
// also uniquely fix the settled boundary. No checker BDD/admission is an oracle.
fn oracle(c: &Corpus, domains: &Domains, p: &GroundProgram) {
    let limits = Limits::default();
    let raw = GroundProgram::prepare_cartesian(c, domains, &limits).unwrap();
    let m = p.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    assert_eq!(report.unresolved.len(), 1);
    let outcome = &report.unresolved[0].completion;
    let atoms: Vec<_> = raw.atoms().cloned().collect();
    let inputs: BTreeSet<_> = raw.input_atoms().cloned().collect();
    let rules: Vec<_> = raw.rules().cloned().collect();
    for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        let solutions = supported_models(&raw, &rules, &world);
        let bad = match outcome {
            CompletionOutcome::NoMeaning(f) => m
                .context()
                .evaluate(&f.bad_input, world.iter().cloned(), &limits)
                .unwrap(),
            CompletionOutcome::NoContradiction => false,
            other => panic!("unexpected completion result: {other:?}"),
        };
        assert_eq!(bad, solutions.is_empty());
        if bad {
            assert!(stable_models(&atoms, &inputs, &rules, &world).is_empty());
        }
    }
    if let CompletionOutcome::NoMeaning(f) = outcome {
        assert!(stable_models(&atoms, &inputs, &rules, &f.observation.present).is_empty());
    }
}

#[test]
fn no_meaning_is_input_only_and_absent_input_does_not_become_admitted() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(t, false), (p, true)]);
    let limits = Limits::default();
    let g = GroundProgram::prepare(&c, &Domains::new(), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    oracle(&c, &Domains::new(), &g);
    let m = g.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    let CompletionOutcome::NoMeaning(f) = &report.unresolved[0].completion else {
        panic!()
    };
    assert_eq!(f.observation.present, BTreeSet::from([atom(t)]));
    assert!(
        m.context()
            .equivalent(
                &f.bad_input,
                &m.context().input(&atom(t), &limits).unwrap(),
                &limits
            )
            .unwrap()
    );
    assert_eq!(
        f.upstream[&atom(t)].provider,
        CompletedProvider::InputSnapshot
    );
    assert!(f.upstream[&atom(t)].value_in_witness);
    assert!(!report.whole_program_admitted());
    assert!(matches!(
        m.fact(&atom(p)).unwrap(),
        SymbolicFact::Blocked(_)
    ));
    assert!(matches!(
        g.evaluate([], &limits).unwrap().fact(&atom(p)).unwrap(),
        FactState::Blocked(_)
    ));
}

#[test]
fn completion_is_deliberately_incomplete_for_positive_self_support() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(p, true)]);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(p, false)]);
    let limits = Limits::default();
    let g = GroundProgram::prepare(&c, &Domains::new(), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    oracle(&c, &Domains::new(), &g);
    let report = g
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    assert_eq!(report.unresolved[0].outcome, RegionOutcome::Unsupported);
    assert!(matches!(
        report.unresolved[0].completion,
        CompletionOutcome::NoContradiction
    ));
    assert!(
        stable_models(
            &g.atoms().cloned().collect::<Vec<_>>(),
            &BTreeSet::new(),
            &g.original_rules().cloned().collect::<Vec<_>>(),
            &BTreeSet::new()
        )
        .is_empty()
    );
}

#[test]
fn correlated_settled_dependencies_are_substituted_not_fresh_choices() {
    let limits = Limits::default();
    for contradictory in [false, true] {
        let mut c = Corpus::new();
        let t = rel(&mut c, "t", true);
        let yes = rel(&mut c, "yes", false);
        let no = rel(&mut c, "no", false);
        let bad = rel(&mut c, "bad", false);
        rule(&mut c, yes, &[(t, false)]);
        rule(&mut c, no, &[(t, true)]);
        rule(
            &mut c,
            bad,
            &[(yes, false), (no, contradictory), (bad, true)],
        );
        // Do not discharge first: also test completion on unrevised equations.
        let g = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        oracle(&c, &Domains::new(), &g);
        let m = g.symbolic(&limits).unwrap();
        let report = m.verify_at_most_one(&limits).unwrap();
        if contradictory {
            let CompletionOutcome::NoMeaning(f) = &report.unresolved[0].completion else {
                panic!()
            };
            assert!(
                m.context()
                    .equivalent(
                        &f.bad_input,
                        &m.context().input(&atom(t), &limits).unwrap(),
                        &limits
                    )
                    .unwrap()
            );
            assert_eq!(f.rules.len(), 1);
            assert_eq!(f.upstream.len(), 2);
            assert!(
                f.upstream
                    .values()
                    .all(|v| matches!(v.provider, CompletedProvider::Component(_)))
            );
        } else {
            assert!(matches!(
                report.unresolved[0].completion,
                CompletionOutcome::NoContradiction
            ));
        }
    }
}

#[test]
fn downstream_broken_cycle_defers_to_its_unsettled_predecessor() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(a, true)]);
    rule(&mut c, b, &[(a, false), (b, true)]);
    let limits = Limits::default();
    let g = GroundProgram::prepare(&c, &Domains::new(), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let report = g
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    assert_eq!(report.unresolved.len(), 2);
    let upstream = g.component_for(&atom(a)).unwrap().id;
    let downstream = report
        .unresolved
        .iter()
        .find(|r| r.component == g.component_for(&atom(b)).unwrap().id)
        .unwrap();
    assert!(
        matches!(&downstream.completion,CompletionOutcome::Deferred { blocked_by } if blocked_by==&BTreeSet::from([upstream]))
    );
    assert_eq!(downstream.outcome, RegionOutcome::Unsupported);
    assert!(matches!(
        report
            .unresolved
            .iter()
            .find(|r| r.component == upstream)
            .unwrap()
            .completion,
        CompletionOutcome::NoMeaning(_)
    ));
}

#[test]
fn rewritten_equations_keep_all_producers_and_authored_proof_references() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(p, true)]);
    let rewritten = rule(&mut c, p, &[(t, false), (q, true)]);
    rule(&mut c, q, &[(t, true), (p, true)]);
    let limits = Limits::default();
    let g = GroundProgram::prepare(&c, &Domains::new(), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert_eq!(g.rewrite_proofs().count(), 1);
    oracle(&c, &Domains::new(), &g);
    let m = g.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    let CompletionOutcome::NoMeaning(f) = &report.unresolved[0].completion else {
        panic!()
    };
    assert_eq!(f.rules.len(), 2); // cycle path itself has just p :- !p
    assert_eq!(f.rewrites, vec![g.rewrite_proofs().next().unwrap().id]);
    assert_eq!(
        f.rules
            .iter()
            .find(|r| r.source == rewritten)
            .unwrap()
            .body
            .len(),
        1
    );
    assert!(
        m.context()
            .equivalent(
                &f.bad_input,
                &m.context()
                    .not(&m.context().input(&atom(t), &limits).unwrap(), &limits)
                    .unwrap(),
                &limits
            )
            .unwrap()
    );
}

#[test]
fn ambiguous_input_mapping_has_answers_but_no_admitted_meaning() {
    let f = dsl_fixture::Fixture::ambiguous();
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &dsl_fixture::domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    oracle(&p.corpus, &dsl_fixture::domains(&p), &g);
    let report = g
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    assert!(!report.whole_program_admitted());
    assert!(matches!(
        report.unresolved[0].completion,
        CompletionOutcome::NoContradiction
    ));
    let raw =
        GroundProgram::prepare_cartesian(&p.corpus, &dsl_fixture::domains(&p), &limits).unwrap();
    let inputs: BTreeSet<_> = raw.input_atoms().cloned().collect();
    assert_eq!(
        stable_models(
            &raw.atoms().cloned().collect::<Vec<_>>(),
            &inputs,
            &raw.rules().cloned().collect::<Vec<_>>(),
            &inputs
        )
        .len(),
        2
    );
}

#[test]
fn lowered_self_negative_mapping_matches_both_independent_oracles() {
    let text = "input input_a;\nslot a;\na <- input_a when not available(a);\n";
    let mut f = dsl_fixture::Fixture::new(text, &["input_a"], &["a"]);
    let span = f.span(text.lines().nth(2).unwrap());
    f.mapping(
        span,
        "a",
        "input_a",
        Some(f.not(f.atom(span, "available", "a"))),
    );
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &dsl_fixture::domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    oracle(&p.corpus, &dsl_fixture::domains(&p), &g);
    let m = g.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    let CompletionOutcome::NoMeaning(f) = &report.unresolved[0].completion else {
        panic!()
    };
    assert_eq!(f.rules.len(), 3);
    let input = dsl_fixture::atom(&p, "present", &["input_a"]);
    assert_eq!(f.observation.present, BTreeSet::from([input.clone()]));
    assert!(
        m.context()
            .equivalent(
                &f.bad_input,
                &m.context().input(&input, &limits).unwrap(),
                &limits
            )
            .unwrap()
    );
}

#[test]
fn completion_limits_preserve_overlaps_and_never_publish_partial_failure_claims() {
    let p = dsl_fixture::Fixture::mixed(false, false).lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &dsl_fixture::domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let m = g.symbolic(&limits).unwrap();
    let mut passed = false;
    for max_work in (0..10000).step_by(31) {
        let report = m
            .verify_with_completion_limits(
                &limits,
                &Limits {
                    max_work,
                    ..limits.clone()
                },
            )
            .unwrap();
        assert!(
            report
                .groups
                .iter()
                .any(|g| matches!(g.outcome, VerifiedOutcome::Counterexample(_)))
        );
        assert!(!report.all_obligations_proved());
        match &report.unresolved[0].completion {
            CompletionOutcome::Inconclusive(_) => {}
            CompletionOutcome::NoMeaning(_) => {
                passed = true;
                break;
            }
            other => panic!("{other:?}"),
        }
    }
    assert!(passed);
    for small in [
        Limits {
            max_bdd_variables: g.input_atoms().count(),
            ..limits.clone()
        },
        Limits {
            max_bdd_nodes: 2,
            ..limits.clone()
        },
        Limits {
            max_condition_nodes: 4,
            ..limits.clone()
        },
        Limits {
            max_bdd_tasks: 0,
            ..limits.clone()
        },
    ] {
        let report = m.verify_with_completion_limits(&limits, &small).unwrap();
        assert!(matches!(
            report.unresolved[0].completion,
            CompletionOutcome::Inconclusive(_)
        ));
    }
}

#[test]
fn unrelated_components_keep_separate_equations_and_completed_results_survive_limits() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let u = rel(&mut c, "u", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(t, false), (a, true)]);
    rule(&mut c, b, &[(u, false), (b, true)]);
    let limits = Limits::default();
    let g = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let m = g.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    for region in &report.unresolved {
        let CompletionOutcome::NoMeaning(f) = &region.completion else {
            panic!()
        };
        assert_eq!(f.rules.len(), 1);
        assert_eq!(f.upstream.len(), 1);
        let expected = if f.rules[0].head.atom == atom(a) {
            atom(t)
        } else {
            atom(u)
        };
        assert!(f.upstream.contains_key(&expected));
        assert!(
            m.context()
                .equivalent(
                    &f.bad_input,
                    &m.context().input(&expected, &limits).unwrap(),
                    &limits
                )
                .unwrap()
        );
    }
    let mut partial = false;
    for max_work in (0..5000).step_by(17) {
        let report = m
            .verify_with_completion_limits(
                &limits,
                &Limits {
                    max_work,
                    ..limits.clone()
                },
            )
            .unwrap();
        let completed = report
            .unresolved
            .iter()
            .filter(|r| matches!(r.completion, CompletionOutcome::NoMeaning(_)))
            .count();
        if completed == 1 {
            assert_eq!(
                report
                    .unresolved
                    .iter()
                    .filter(|r| matches!(r.completion, CompletionOutcome::Inconclusive(_)))
                    .count(),
                1
            );
            partial = true;
            break;
        }
    }
    assert!(partial);
}

#[test]
fn false_symbolic_boundary_is_rejected_by_concrete_witness_replay() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let gate = rel(&mut c, "gate", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, gate, &[(t, false)]);
    rule(&mut c, bad, &[(gate, false), (bad, true)]);
    let limits = Limits::default();
    let g = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let mut m = g.symbolic(&limits).unwrap();
    m.conditions
        .insert(atom(gate), m.context().true_condition());
    assert!(matches!(
        m.verify_at_most_one(&limits),
        Err(CheckError::Internal("completion boundary did not replay"))
    ));
}

#[test]
fn signed_cycle_matrix_matches_exhaustive_completion_and_stable_model_oracles() {
    let limits = Limits::default();
    for left in 0..5 {
        for right in 0..5 {
            for extra in 0..4 {
                let mut c = Corpus::new();
                let t = rel(&mut c, "t", true);
                let u = rel(&mut c, "u", true);
                let a = rel(&mut c, "a", false);
                let b = rel(&mut c, "b", false);
                let guards = [
                    vec![],
                    vec![(t, false)],
                    vec![(t, true)],
                    vec![(u, false)],
                    vec![(u, true)],
                ];
                let mut body = guards[left].clone();
                body.push((b, true));
                rule(&mut c, a, &body);
                let mut body = guards[right].clone();
                body.push((a, extra & 1 == 0));
                rule(&mut c, b, &body);
                if extra & 2 != 0 {
                    rule(&mut c, a, &[(a, true)]);
                }
                let g = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
                oracle(&c, &Domains::new(), &g);
            }
        }
    }
}
