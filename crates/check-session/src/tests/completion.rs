use super::rewrites::dsl_fixture;
use denotate_check::test_support::completion::*;
use denotate_check::test_support::rewrites::*;
use denotate_check::*;
use std::collections::BTreeSet;
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
