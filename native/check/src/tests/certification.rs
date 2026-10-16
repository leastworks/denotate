use super::rewrites::{atom, dsl_fixture, rel, rule, stable_models, subsets};
use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;

/// Cartesian grounding and plain-set reduct oracle over the original rules.
/// Neither certification nor production evaluation defines the expected models.
fn compare(c: &Corpus, domains: &Domains, admit: bool) -> usize {
    let limits = Limits::default();
    let oracle = GroundProgram::prepare_cartesian(c, domains, &limits).unwrap();
    let atoms: Vec<_> = oracle.atoms().cloned().collect();
    let inputs: BTreeSet<_> = oracle.input_atoms().cloned().collect();
    let rules: Vec<_> = oracle.rules().cloned().collect();
    let p = GroundProgram::prepare(c, domains, &limits).unwrap();
    let p = if admit { p.admit(&limits).unwrap() } else { p };
    let before = format!("{p:?}");
    let mut certified = 0;
    for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        let models = stable_models(&atoms, &inputs, &rules, &world);
        match p
            .certify_observation(world.iter().cloned(), &limits)
            .unwrap()
        {
            CertificationOutcome::Certified(replay) => {
                certified += 1;
                assert_eq!(models.len(), 1);
                assert_eq!(models.first(), Some(&replay.facts));
                assert_eq!(replay.observation.present, world);
                assert_eq!(
                    replay.evidence.keys().cloned().collect::<BTreeSet<_>>(),
                    replay.facts
                );
                for step in &replay.pruning {
                    assert_ne!(step.value, step.premise.polarity == Polarity::Positive);
                    assert!(p.rule(step.rule).unwrap().body.contains(&step.premise));
                    if let CompletedProvider::Component(id) = &step.provider {
                        assert!(replay.providers[id].contains(&step.premise.term.atom));
                    }
                }
                for (fact, step) in &replay.evidence {
                    match &step.evidence {
                        GroundEvidence::Input => assert!(world.contains(fact)),
                        GroundEvidence::Derived { rule, premises } => {
                            assert_eq!(p.original_rule(rule.id), Some(rule));
                            for premise in premises {
                                match premise {
                                    PremiseEvidence::Positive { fact, .. } => {
                                        assert!(replay.evidence[fact].order < step.order)
                                    }
                                    PremiseEvidence::Absent { fact, provider, .. } => {
                                        assert!(!replay.facts.contains(fact));
                                        if let CompletedProvider::Component(id) = provider {
                                            assert!(replay.providers[id].contains(fact));
                                        }
                                    }
                                    PremiseEvidence::Discharged { proof, .. } => {
                                        assert!(p.rewrite_proof(*proof).is_some());
                                    }
                                }
                            }
                        }
                    }
                }
            }
            CertificationOutcome::NotCertified => {}
            CertificationOutcome::Inconclusive(cause) => {
                panic!("tiny oracle fixture exhausted {cause:?}")
            }
        }
        assert_eq!(
            format!("{p:?}"),
            before,
            "specialization mutated the original"
        );
    }
    certified
}

#[test]
fn signed_guard_matrix_certificates_match_original_stable_models() {
    let mut certified = 0;
    for t_negative in [false, true] {
        for u_negative in [false, true] {
            for p_negative in [false, true] {
                for q_negative in [false, true] {
                    for extra in 0..3 {
                        let mut c = Corpus::new();
                        let t = rel(&mut c, "t", true);
                        let u = rel(&mut c, "u", true);
                        let p = rel(&mut c, "p", false);
                        let q = rel(&mut c, "q", false);
                        rule(&mut c, p, &[(t, t_negative), (q, q_negative)]);
                        rule(&mut c, q, &[(u, u_negative), (p, p_negative)]);
                        match extra {
                            1 => {
                                rule(&mut c, p, &[(p, false)]);
                            }
                            2 => {
                                rule(&mut c, p, &[(u, false)]);
                            }
                            _ => {}
                        }
                        for admit in [false, true] {
                            certified += compare(&c, &Domains::new(), admit);
                        }
                    }
                }
            }
        }
    }
    assert!(certified > 100);
}

#[test]
fn lowered_mapping_certificates_match_the_independent_oracle() {
    // Keep head counts within the oracle's deliberate exponential bound.
    for f in [
        dsl_fixture::Fixture::ambiguous(),
        dsl_fixture::Fixture::exclusive(),
    ] {
        let p = f.lower();
        for admit in [false, true] {
            assert!(compare(&p.corpus, &dsl_fixture::domains(&p), admit) > 0);
        }
    }
    let text = "input input_c;\nslot c;\nc <- input_c when not available(c);\n";
    let mut f = dsl_fixture::Fixture::new(text, &["input_c"], &["c"]);
    let span = f.span(text.lines().nth(2).unwrap());
    f.mapping(
        span,
        "c",
        "input_c",
        Some(f.not(f.atom(span, "available", "c"))),
    );
    let p = f.lower();
    assert_eq!(compare(&p.corpus, &dsl_fixture::domains(&p), true), 1);
}

#[test]
fn new_settled_derived_facts_enable_later_rounds_but_unknown_is_not_false() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, p, &[(t, false), (p, true)]);
    rule(&mut c, q, &[(p, false), (q, true)]);
    rule(&mut c, out, &[(q, true)]);
    let limits = Limits::default();
    let g = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let CertificationOutcome::Certified(replay) = g.certify_observation([], &limits).unwrap()
    else {
        panic!()
    };
    assert_eq!(replay.facts, BTreeSet::from([atom(out)]));
    assert_eq!(
        replay
            .pruning
            .iter()
            .map(|s| s.round)
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([0, 1])
    );
    assert!(matches!(
        g.certify_observation([atom(t)], &limits).unwrap(),
        CertificationOutcome::NotCertified
    ));
    assert_eq!(compare(&c, &Domains::new(), false), 1);
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, p, &[(q, true)]);
    rule(&mut c, q, &[(p, true)]);
    rule(&mut c, out, &[(q, true)]);
    assert_eq!(compare(&c, &Domains::new(), true), 0);
}

fn alternate_fixture() -> (Corpus, Domains, RelationId, GroundAtom) {
    let mut c = Corpus::new();
    let value = c.declare_sort("Value").unwrap();
    let a = c.declare_constant("a", value).unwrap();
    let b = c.declare_constant("b", value).unwrap();
    let z = rel(&mut c, "z", true);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, bad, &[(z, true), (bad, true)]);
    let r = c
        .declare_relation("r", RelationRole::Derived, [Parameter::new("value", value)])
        .unwrap();
    let head = c.atom(r, [a.into()]).unwrap();
    c.add_rule(head, []).unwrap();
    for negative in [false, true] {
        let head = c.atom(r, [b.into()]).unwrap();
        let premise = c.atom(z, []).unwrap();
        c.add_rule(
            head,
            [if negative {
                Literal::Negative(premise)
            } else {
                Literal::Positive(premise)
            }],
        )
        .unwrap();
    }
    c.at_most_one("unique", r, [], "test").unwrap();
    (
        c,
        Domains::from([(value, vec![a, b])]),
        z,
        GroundAtom::new(r, [b]),
    )
}

fn example<'a>(report: &'a Verification<'_>) -> &'a Counterexample {
    let VerifiedOutcome::Counterexample(example) = &report.groups[0].outcome else {
        panic!()
    };
    example
}

#[test]
fn unconditional_no_meaning_does_not_confine_an_unrelated_overlap() {
    let mut c = Corpus::new();
    let input = c.declare_sort("Input").unwrap();
    let slot = c.declare_sort("Slot").unwrap();
    let i1 = c.declare_constant("i1", input).unwrap();
    let i2 = c.declare_constant("i2", input).unwrap();
    let s1 = c.declare_constant("s1", slot).unwrap();
    let supplies = c
        .declare_relation(
            "supplies",
            RelationRole::Derived,
            [Parameter::new("input", input), Parameter::new("slot", slot)],
        )
        .unwrap();
    for value in [i1, i2] {
        let head = c.atom(supplies, [value.into(), s1.into()]).unwrap();
        c.add_rule(head, []).unwrap();
    }
    c.at_most_one("unique", supplies, [Column::Name("slot".into())], "test")
        .unwrap();
    // An independent contradiction, not a condition selecting this conflict.
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, bad, &[(bad, true)]);
    let limits = Limits::default();
    let domains = Domains::from([(input, vec![i1, i2]), (slot, vec![s1])]);
    let p = GroundProgram::prepare(&c, &domains, &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let report = p
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    let conflict = example(&report);
    assert_eq!(conflict.tuples.len(), 2);
    assert_eq!(conflict.replay_scope, ReplayScope::ConeOnly);
    assert!(conflict.confined_to_no_meaning.is_empty());
    assert_eq!(report.unresolved.len(), 1);
    let CompletionOutcome::NoMeaning(failure) = &report.unresolved[0].completion else {
        panic!()
    };
    assert!(
        failure.bad_input.is_true(),
        "keep the separate unconditional failure"
    );
    assert!(!report.whole_program_admitted());
}

#[test]
fn alternate_completion_replaces_witness_and_evidence_atomically() {
    let (c, domains, z, b) = alternate_fixture();
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &domains, &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let m = p.symbolic(&limits).unwrap();
    let disabled = Limits {
        max_work: 0,
        ..limits.clone()
    };
    let before = m
        .verify_with_phase_limits(&limits, &limits, &disabled)
        .unwrap();
    let old = example(&before);
    assert_eq!(old.replay_scope, ReplayScope::ConeOnly);
    assert!(old.observation.absent.contains(&atom(z)));
    let GroundEvidence::Derived { premises, .. } = &old.evidence[&b].evidence else {
        panic!()
    };
    assert!(matches!(&premises[0], PremiseEvidence::Absent { .. }));
    let after = m.verify_at_most_one(&limits).unwrap();
    let new = example(&after);
    assert!(!after.whole_program_admitted());
    assert_eq!(new.replay_scope, ReplayScope::WholeProgram);
    assert!(new.observation.present.contains(&atom(z)));
    let Some(CertificationOutcome::Certified(replay)) = &new.certification else {
        panic!()
    };
    assert_eq!(
        replay.pruning.len(),
        1,
        "only the blocked cycle needs pruning"
    );
    assert!(
        replay
            .pruning
            .iter()
            .all(|step| p.rule(step.rule).unwrap().head.atom.relation != b.relation),
        "the admitted r(b) :- !z producer must not enter the pruning log"
    );
    assert_eq!(replay.observation, new.observation);
    for (fact, step) in &new.evidence {
        assert_eq!(&replay.evidence[fact], step);
    }
    let GroundEvidence::Derived { premises, .. } = &new.evidence[&b].evidence else {
        panic!()
    };
    assert!(matches!(&premises[0], PremiseEvidence::Positive { fact, .. } if *fact == atom(z)));
    assert_eq!(compare(&c, &domains, true), 1);
}

#[test]
fn certification_limits_never_replace_any_part_of_the_original_cone_finding() {
    let (c, domains, z, invalid) = alternate_fixture();
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &domains, &limits).unwrap();
    let m = p.symbolic(&limits).unwrap();
    let baseline = m
        .verify_with_phase_limits(
            &limits,
            &limits,
            &Limits {
                max_work: 0,
                ..limits.clone()
            },
        )
        .unwrap();
    let original = example(&baseline);
    let mut exhausted = 0;
    let mut successes = 0;
    for work in (0..3000).step_by(23) {
        let report = m
            .verify_with_phase_limits(
                &limits,
                &limits,
                &Limits {
                    max_work: work,
                    ..limits.clone()
                },
            )
            .unwrap();
        let current = example(&report);
        match current.certification {
            Some(CertificationOutcome::Inconclusive(_)) => {
                exhausted += 1;
                assert_eq!(current.observation, original.observation);
                assert_eq!(current.evidence, original.evidence);
                assert_eq!(current.tuples, original.tuples);
                assert_eq!(current.replay_scope, ReplayScope::ConeOnly);
                assert!(matches!(
                    report.unresolved[0].completion,
                    CompletionOutcome::NoMeaning(_)
                ));
            }
            Some(CertificationOutcome::Certified(_)) => successes += 1,
            _ => panic!("fixture should certify when budget permits"),
        }
    }
    assert!(exhausted > 5 && successes > 5);
    assert!(matches!(
        p.certify_observation(
            [atom(z)], // Disables the cycle, requiring a bounded graph rebuild.
            &Limits {
                max_dependencies: 0,
                ..limits.clone()
            }
        )
        .unwrap(),
        CertificationOutcome::Inconclusive(_)
    ));
    assert!(matches!(
        p.certify_observation([invalid], &limits),
        Err(CheckError::InvalidObservation(_))
    ));
}

#[test]
fn alternate_keeps_full_boolean_support_not_just_the_witness_path() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let z = rel(&mut c, "z", true);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let ctx = p.condition_context(&limits).unwrap();
    let condition = ctx
        .or(
            &ctx.not(&ctx.input(&atom(x), &limits).unwrap(), &limits)
                .unwrap(),
            &ctx.input(&atom(y), &limits).unwrap(),
            &limits,
        )
        .unwrap();
    let original = ctx.witness(&condition, &limits).unwrap().unwrap();
    assert!(original.present.is_empty()); // !x already true; y skipped on path.
    let alternate = ctx
        .present_dont_cares(
            &condition,
            &original,
            &mut crate::limits::Budget::new(&limits),
        )
        .unwrap();
    assert_eq!(alternate.present, BTreeSet::from([atom(z)]));
    assert_eq!(alternate.absent, BTreeSet::from([atom(x), atom(y)]));
}

#[test]
fn not_certified_does_not_imply_no_unique_meaning() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(q, true)]);
    rule(&mut c, q, &[(p, true)]);
    rule(&mut c, q, &[(p, false)]);
    let limits = Limits::default();
    let oracle = GroundProgram::prepare_cartesian(&c, &Domains::new(), &limits).unwrap();
    let models = stable_models(
        &oracle.atoms().cloned().collect::<Vec<_>>(),
        &BTreeSet::new(),
        &oracle.rules().cloned().collect::<Vec<_>>(),
        &BTreeSet::new(),
    );
    assert_eq!(models, BTreeSet::from([BTreeSet::from([atom(q)])]));
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    assert!(matches!(
        p.certify_observation([], &limits).unwrap(),
        CertificationOutcome::NotCertified
    ));
}

#[test]
fn certification_replay_mismatch_is_an_error_not_a_limit_or_an_upgrade() {
    let (c, domains, _, b) = alternate_fixture();
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &domains, &limits).unwrap();
    let mut m = p.symbolic(&limits).unwrap();
    let mut report = m
        .verify_with_phase_limits(
            &limits,
            &limits,
            &Limits {
                max_work: 0,
                ..limits.clone()
            },
        )
        .unwrap();
    let group = report.groups.remove(0);
    let VerifiedOutcome::Counterexample(mut example) = group.outcome else {
        panic!()
    };
    let original = example.observation.clone();
    let violation = m.context().true_condition();
    m.conditions.insert(b, m.context().false_condition());
    assert_eq!(
        m.certify_counterexample(
            &mut example,
            &group.group,
            &violation,
            &mut crate::limits::Budget::new(&limits)
        ),
        Err(CheckError::Internal(
            "certified replay disagrees with symbolic fact"
        ))
    );
    assert_eq!(example.observation, original);
    assert_eq!(example.replay_scope, ReplayScope::ConeOnly);
}
