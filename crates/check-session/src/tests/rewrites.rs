use denotate_check::test_support::rewrites::*;
use denotate_check::*;
use std::collections::BTreeSet;
#[path = "../../../../test-dsl/tests/support/mod.rs"]
pub(super) mod dsl_fixture;
pub(super) use denotate_check::test_support::rewrites::subsets;
#[test]
fn lowered_test_dsl_forwarding_agrees_with_cartesian_stable_model_oracle() {
    let f = dsl_fixture::Fixture::exclusive();
    let lowered = f.lower();
    let domains = dsl_fixture::domains(&lowered);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&lowered.corpus, &domains, &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert!(p.is_admitted());
    assert_eq!(p.rewrite_proofs().count(), 2);
    assert_eq!(compare(&lowered.corpus, &domains, &p), 8);
    let proofs: Vec<_> = p.rewrite_proofs().collect();
    let certificate = proofs[0].upper_bounds.as_ref().unwrap();
    assert!(std::sync::Arc::ptr_eq(
        certificate,
        proofs[1].upper_bounds.as_ref().unwrap()
    ));
    assert_eq!(certificate.snapshot, proofs[0].snapshot);
    // The certificate includes the forwarding rules, not just mapped_to's
    // immediately visible guard or a single reported cycle path.
    assert_eq!(certificate.producers.len(), 6);
    let m = p.symbolic(&limits).unwrap();
    let ctx = m.context();
    let x = ctx
        .input(
            &dsl_fixture::atom(&lowered, "present", &["input_x"]),
            &limits,
        )
        .unwrap();
    for (slot, input, guard) in [
        ("a", "input_a", x.clone()),
        ("b", "input_b", ctx.not(&x, &limits).unwrap()),
    ] {
        let present = ctx
            .input(&dsl_fixture::atom(&lowered, "present", &[input]), &limits)
            .unwrap();
        let expected = ctx.and(&guard, &present, &limits).unwrap();
        let available = dsl_fixture::atom(&lowered, "available", &[slot]);
        assert!(
            ctx.equivalent(&certificate.conditions[&available], &expected, &limits)
                .unwrap()
        );
    }
}

#[test]
fn masking_self_contradiction_and_mutual_ambiguity_match_independent_stable_models() {
    use denotate_test_dsl::ast::Mask;
    for mutual in [false, true] {
        let text = if mutual {
            "input i, j;\nslot a, b;\na <- i;\nb <- j;\nmask a when available(b);\nmask b when available(a);"
        } else {
            "input i;\nslot a;\na <- i;\nmask a when available(a);"
        };
        let mut f = dsl_fixture::Fixture::new(
            text,
            if mutual { &["i", "j"] } else { &["i"] },
            if mutual { &["a", "b"] } else { &["a"] },
        );
        f.mapping(f.span("a <- i;"), "a", "i", None);
        if mutual {
            f.mapping(f.span("b <- j;"), "b", "j", None);
        }
        for (slot, guard) in if mutual {
            vec![("a", "b"), ("b", "a")]
        } else {
            vec![("a", "a")]
        } {
            let span = f.span(&format!("mask {slot} when available({guard});"));
            // The target starts after `mask ` (searching "a" would hit the keyword).
            let target_span = f
                .sources
                .span(
                    f.snapshot,
                    span.byte_range().start + 5..span.byte_range().start + 6,
                )
                .unwrap();
            f.ast.masks.push(Mask {
                target: denotate_test_dsl::ast::Name {
                    text: slot.into(),
                    span: target_span,
                },
                condition: Some(f.atom(span, "available", guard)),
                span,
            });
        }
        let p = f.lower();
        let domains = dsl_fixture::domains(&p);
        let limits = Limits::default();
        let oracle = GroundProgram::prepare_cartesian(&p.corpus, &domains, &limits).unwrap();
        let atoms: Vec<_> = oracle.atoms().cloned().collect();
        let inputs: BTreeSet<_> = oracle.input_atoms().cloned().collect();
        let rules: Vec<_> = oracle.rules().cloned().collect();
        let ground = GroundProgram::prepare(&p.corpus, &domains, &limits)
            .unwrap()
            .admit(&limits)
            .unwrap();
        assert!(!ground.is_admitted());
        let meaning = ground.symbolic(&limits).unwrap();
        let report = meaning.verify_at_most_one(&limits).unwrap();
        for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
            let models = stable_models(&atoms, &inputs, &rules, &world);
            assert_eq!(
                models.len(),
                if mutual {
                    if world.len() == 2 { 2 } else { 1 }
                } else {
                    if world.is_empty() { 1 } else { 0 }
                }
            );
            for region in &report.unresolved {
                match &region.completion {
                    CompletionOutcome::NoMeaning(finding) => assert_eq!(
                        meaning
                            .context()
                            .evaluate(&finding.bad_input, world.iter().cloned(), &limits)
                            .unwrap(),
                        models.is_empty()
                    ),
                    CompletionOutcome::NoContradiction => assert!(mutual),
                    other => panic!("unexpected completion {other:?}"),
                }
            }
        }
    }
}

// Completion/supported-model oracle, independent of BDDs and the rewrite
// implementation. Unlike stable models, these can contain positive self-support.
#[test]
fn upper_bound_iteration_budget_failure_never_commits_partial_discharge() {
    let lowered = dsl_fixture::Fixture::exclusive().lower();
    let limits = Limits::default();
    let raw =
        GroundProgram::prepare(&lowered.corpus, &dsl_fixture::domains(&lowered), &limits).unwrap();
    let mut interrupted_bound = false;
    let mut completed = false;
    for max_work in (0..5000).step_by(7) {
        let p = raw
            .clone()
            .admit(&Limits {
                max_work,
                ..limits.clone()
            })
            .unwrap();
        if let Some(cause) = p.admission_limit() {
            interrupted_bound |= cause.phase.starts_with("upper-bound");
            assert!(!p.is_admitted());
            assert_eq!(p.rewrite_proofs().count(), 0);
            assert_eq!(
                p.rules().collect::<Vec<_>>(),
                raw.rules().collect::<Vec<_>>()
            );
        } else {
            completed = true;
            assert!(p.is_admitted());
            assert_eq!(p.rewrite_proofs().count(), 2);
            break;
        }
    }
    assert!(interrupted_bound && completed);
}
