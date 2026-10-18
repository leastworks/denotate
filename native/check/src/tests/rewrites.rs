use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;

#[path = "../../../test-dsl/tests/support/mod.rs"]
pub(super) mod dsl_fixture;

pub(super) fn rel(c: &mut Corpus, name: &str, input: bool) -> RelationId {
    c.declare_relation(
        name,
        if input {
            RelationRole::Input
        } else {
            RelationRole::Derived
        },
        [],
    )
    .unwrap()
}
pub(super) fn atom(r: RelationId) -> GroundAtom {
    GroundAtom::new(r, [])
}
pub(super) fn rule(c: &mut Corpus, head: RelationId, body: &[(RelationId, bool)]) -> RuleId {
    let head = c.atom(head, []).unwrap();
    let body: Vec<_> = body
        .iter()
        .map(|(r, negative)| {
            let a = c.atom(*r, []).unwrap();
            if *negative {
                Literal::Negative(a)
            } else {
                Literal::Positive(a)
            }
        })
        .collect();
    c.add_rule(head, body).unwrap()
}

// Independent truth oracle: no BDD, SCC/admission result, sparse grounding or
// production evaluator. Exponential enumeration is deliberately capped.
pub(super) fn subsets(atoms: &[GroundAtom]) -> Vec<BTreeSet<GroundAtom>> {
    assert!(atoms.len() <= 12, "tiny stable-model oracle only");
    (0..1usize << atoms.len())
        .map(|bits| {
            atoms
                .iter()
                .enumerate()
                .filter(|(i, _)| bits & (1 << i) != 0)
                .map(|(_, a)| a.clone())
                .collect()
        })
        .collect()
}
// Enumerate guesses only for atoms not functionally fixed by the input world
// or unused positive output definitions. This eliminates added value-copy leaves
// without using SCCs, admission, BDDs or a production evaluator. Positive cycles
// remain guessed, preserving supported (not necessarily stable) models too.
fn candidates(
    derived: &[GroundAtom],
    inputs: &BTreeSet<GroundAtom>,
    rules: &[GroundRule],
    world: &BTreeSet<GroundAtom>,
) -> Vec<BTreeSet<GroundAtom>> {
    let fixed: BTreeSet<_> = derived
        .iter()
        .filter(|a| {
            let producers: Vec<_> = rules.iter().filter(|r| r.head.atom == **a).collect();
            !producers.is_empty()
                && producers
                    .iter()
                    .all(|r| r.body.iter().all(|l| l.polarity == Polarity::Positive))
                && (producers
                    .iter()
                    .all(|r| r.body.iter().all(|l| inputs.contains(&l.term.atom)))
                    || !rules
                        .iter()
                        .any(|r| r.body.iter().any(|l| l.term.atom == **a)))
        })
        .cloned()
        .collect();
    let guessed: Vec<_> = derived
        .iter()
        .filter(|a| !fixed.contains(*a))
        .cloned()
        .collect();
    subsets(&guessed)
        .into_iter()
        .map(|mut candidate| {
            candidate.extend(world.iter().cloned());
            loop {
                let before = candidate.len();
                for r in rules {
                    if fixed.contains(&r.head.atom)
                        && r.body.iter().all(|l| candidate.contains(&l.term.atom))
                    {
                        candidate.insert(r.head.atom.clone());
                    }
                }
                if before == candidate.len() {
                    break;
                }
            }
            candidate
        })
        .collect()
}

pub(super) fn stable_models(
    atoms: &[GroundAtom],
    inputs: &BTreeSet<GroundAtom>,
    rules: &[GroundRule],
    world: &BTreeSet<GroundAtom>,
) -> BTreeSet<BTreeSet<GroundAtom>> {
    let derived: Vec<_> = atoms
        .iter()
        // Headless atoms cannot belong to a stable model. This only shrinks
        // exhaustive assignment enumeration; no production pruning is reused.
        .filter(|a| !inputs.contains(*a) && rules.iter().any(|r| r.head.atom == **a))
        .cloned()
        .collect();
    candidates(&derived, inputs, rules, world)
        .into_iter()
        .filter_map(|candidate| {
            // Gelfond-Lifschitz reduct of the AUTHORED ground rules.
            let reduct: Vec<_> = rules
                .iter()
                .filter(|r| {
                    !r.body.iter().any(|l| {
                        l.polarity == Polarity::Negative && candidate.contains(&l.term.atom)
                    })
                })
                .collect();
            let mut least = world.clone();
            loop {
                let before = least.len();
                for r in &reduct {
                    if r.body
                        .iter()
                        .filter(|l| l.polarity == Polarity::Positive)
                        .all(|l| least.contains(&l.term.atom))
                    {
                        least.insert(r.head.atom.clone());
                    }
                }
                if before == least.len() {
                    break;
                }
            }
            (least == candidate).then_some(candidate)
        })
        .collect()
}

#[test]
fn lowered_input_mapping_forwarding_agrees_with_cartesian_stable_model_oracle() {
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
pub(super) fn supported_models(
    p: &GroundProgram,
    rules: &[GroundRule],
    world: &BTreeSet<GroundAtom>,
) -> BTreeSet<BTreeSet<GroundAtom>> {
    let derived: Vec<_> = p
        .atoms()
        .filter(|a| !p.inputs.contains(*a))
        .cloned()
        .collect();
    candidates(&derived, &p.inputs, rules, world)
        .into_iter()
        .filter_map(|candidate| {
            derived
                .iter()
                .all(|a| {
                    candidate.contains(a)
                        == rules.iter().any(|r| {
                            r.head.atom == *a
                                && r.body.iter().all(|l| {
                                    candidate.contains(&l.term.atom)
                                        == (l.polarity == Polarity::Positive)
                                })
                        })
                })
                .then_some(candidate)
        })
        .collect()
}

#[test]
fn descending_bounds_preserve_self_support_and_do_not_use_least_fixed_point() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let u = rel(&mut c, "u", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let ar = rule(&mut c, a, &[(t, false), (b, true)]);
    rule(&mut c, b, &[(b, false)]);
    // Keeps b structurally possible in sparse grounding and closes the SCC;
    // its settled guard is false, but b's self-support must remain possible.
    rule(&mut c, b, &[(u, false), (u, true), (a, true)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&Limits::default())
        .unwrap();
    assert!(p.is_admitted());
    assert_eq!(p.rewrite_proofs().count(), 1);
    assert_eq!(p.rules().find(|r| r.source == ar).unwrap().body.len(), 2);
    let proof = p.rewrite_proofs().next().unwrap();
    assert!(proof.upper_bounds.as_ref().unwrap().conditions[&atom(b)].is_true());
    for world in subsets(&[atom(t), atom(u)]) {
        let before = supported_models(&p, &p.original_rules().cloned().collect::<Vec<_>>(), &world);
        let after = supported_models(&p, &p.rules().cloned().collect::<Vec<_>>(), &world);
        assert_eq!(before, after);
        assert!(before.iter().any(|m| m.contains(&atom(b))));
    }
    assert_eq!(compare(&c, &Domains::new(), &p), 4);
}

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
fn compare(c: &Corpus, domains: &Domains, rewritten: &GroundProgram) -> usize {
    let oracle = GroundProgram::prepare_cartesian(c, domains, &Limits::default()).unwrap();
    let atoms: Vec<_> = oracle.atoms().cloned().collect();
    let inputs: BTreeSet<_> = oracle.input_atoms().cloned().collect();
    let originals: Vec<_> = oracle.rules().cloned().collect();
    let active: Vec<_> = rewritten.rules().cloned().collect();
    let mut nonempty = 0;
    let meaning = rewritten.symbolic(&Limits::default()).unwrap();
    for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        let before = stable_models(&atoms, &inputs, &originals, &world);
        assert_eq!(before, stable_models(&atoms, &inputs, &active, &world));
        nonempty += usize::from(!before.is_empty());
        let replay = rewritten
            .evaluate(world.iter().cloned(), &Limits::default())
            .unwrap();
        if rewritten.is_admitted() {
            assert_eq!(
                before.len(),
                1,
                "admission requires a unique original stable model"
            );
            assert_eq!(
                *before.first().unwrap(),
                replay.established_facts().cloned().collect()
            );
        }
        for a in &atoms {
            if let SymbolicFact::Settled(condition) = meaning.fact(a).unwrap() {
                let truth = meaning
                    .context()
                    .evaluate(&condition, world.iter().cloned(), &Limits::default())
                    .unwrap();
                assert_eq!(replay.fact(a).unwrap(), FactState::Settled(truth));
                for model in &before {
                    assert_eq!(model.contains(a), truth);
                }
            }
        }
    }
    nonempty
}

#[test]
fn oracle_controls_distinguish_ambiguity_contradiction_and_unseeded_recursion() {
    for (shape, expected) in [(0, 2), (1, 0), (2, 1)] {
        let mut c = Corpus::new();
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        match shape {
            0 => {
                rule(&mut c, a, &[(b, true)]);
                rule(&mut c, b, &[(a, true)]);
            }
            1 => {
                rule(&mut c, a, &[(a, true)]);
            }
            _ => {
                rule(&mut c, a, &[(a, false)]);
            }
        }
        let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &Limits::default()).unwrap();
        let models = stable_models(
            &p.atoms().cloned().collect::<Vec<_>>(),
            &BTreeSet::new(),
            &p.rules().cloned().collect::<Vec<_>>(),
            &BTreeSet::new(),
        );
        assert_eq!(models.len(), expected);
        if shape == 2 {
            assert!(models.first().unwrap().is_empty());
        }
    }
}

#[test]
fn mutual_negation_discharge_preserves_original_models_and_evidence() {
    for backup in [false, true] {
        let mut c = Corpus::new();
        let t = rel(&mut c, "t", true);
        let first = rel(&mut c, "first", false);
        let second = rel(&mut c, "second", false);
        // Put the removed literal first: evidence validation must not run until
        // the complete executable body succeeds in this observation.
        let ar = rule(&mut c, first, &[(second, true), (t, false)]);
        let pr = rule(&mut c, second, &[(t, true), (first, true)]);
        if backup {
            let b = rel(&mut c, "backup", true);
            rule(&mut c, second, &[(b, false)]);
        }
        let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        let old_component = raw.component_for(&atom(first)).unwrap().id;
        let p = raw.admit(&Limits::default()).unwrap();
        assert!(p.is_admitted());
        assert!(
            p.component(old_component).is_none(),
            "component handles must not alias after rebuild"
        );
        assert_eq!(p.rewrite_proofs().count(), if backup { 1 } else { 2 });
        assert_eq!(
            p.rules().find(|r| r.source == ar).unwrap().body.len(),
            if backup { 2 } else { 1 }
        );
        let second_rule = p.rules().find(|r| r.source == pr).unwrap();
        assert_eq!(second_rule.body[0].term.atom, atom(t));
        assert_eq!(
            second_rule.body[0].polarity,
            Polarity::Negative,
            "input negation is never discharged"
        );
        assert!(compare(&c, &Domains::new(), &p) > 0);
        if !backup {
            let replay = p.evaluate([atom(t)], &Limits::default()).unwrap();
            let Evidence::Derived { rule, premises } =
                &replay.derivation(&atom(first)).unwrap().evidence
            else {
                panic!()
            };
            assert!(matches!(
                premises.as_slice(),
                [
                    PremiseEvidence::Discharged { .. },
                    PremiseEvidence::Positive { .. }
                ]
            ));
            let PremiseEvidence::Discharged {
                literal_occurrence,
                proof,
            } = premises[0]
            else {
                panic!()
            };
            assert_eq!(literal_occurrence, c.rule(ar).unwrap().body[0].atom().id());
            assert_eq!(p.original_rule(*rule).unwrap().body.len(), 2);
            assert_eq!(p.rewrite_proof(proof).unwrap().candidate.rule.id, *rule);
        }
    }
}

#[test]
fn producer_removal_uses_exact_coverage_and_never_admits_bad() {
    for shape in 0..6 {
        let mut c = Corpus::new();
        let t = rel(&mut c, "t", true);
        let u = rel(&mut c, "u", true);
        let bad = rel(&mut c, "bad", false);
        let other = rel(&mut c, "other", false);
        let out = rel(&mut c, "out", false);
        match shape {
            1 => {
                rule(&mut c, bad, &[(u, false), (bad, true)]);
            }
            5 => {
                rule(&mut c, bad, &[(other, true)]);
                rule(&mut c, other, &[(bad, true)]);
            }
            _ => {
                rule(&mut c, bad, &[(bad, true)]);
            }
        }
        let (cover, candidate) = match shape {
            2 => (
                vec![(t, false), (bad, false)],
                vec![(t, false), (u, false), (bad, false)],
            ),
            3 => (vec![(t, false)], vec![(t, false), (u, false), (bad, false)]),
            4 => (vec![(u, false)], vec![(t, false), (bad, false)]),
            _ => (vec![], vec![(t, false), (bad, false)]),
        };
        let kept = rule(&mut c, out, &cover);
        let dropped = rule(&mut c, out, &candidate);
        let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
            .unwrap()
            .admit(&Limits::default())
            .unwrap();
        assert!(!p.is_admitted());
        assert!(p.rules().any(|r| r.source == kept));
        let should_drop = !matches!(shape, 2 | 4);
        assert_eq!(!p.rules().any(|r| r.source == dropped), should_drop);
        assert_eq!(p.rewrite_proofs().count(), usize::from(should_drop));
        let meaning = p.symbolic(&Limits::default()).unwrap();
        assert!(matches!(
            meaning.fact(&atom(bad)).unwrap(),
            SymbolicFact::Blocked(_)
        ));
        match meaning.fact(&atom(out)).unwrap() {
            SymbolicFact::Settled(condition) => {
                assert!(should_drop);
                if shape == 3 {
                    assert!(
                        meaning
                            .context()
                            .equivalent(
                                &condition,
                                &meaning
                                    .context()
                                    .input(&atom(t), &Limits::default())
                                    .unwrap(),
                                &Limits::default()
                            )
                            .unwrap()
                    );
                } else {
                    assert!(condition.is_true());
                }
            }
            _ => assert!(!should_drop),
        }
        let worlds = compare(&c, &Domains::new(), &p);
        if matches!(shape, 1 | 5) {
            assert!(worlds > 0, "nonvacuous preservation test");
        }
    }
}

#[test]
fn independent_input_guards_are_not_exclusive() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let u = rel(&mut c, "u", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(t, false), (b, true)]);
    rule(&mut c, b, &[(u, false), (a, true)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&Limits::default())
        .unwrap();
    assert!(!p.is_admitted());
    assert_eq!(p.rewrite_proofs().count(), 0);
    assert!(compare(&c, &Domains::new(), &p) > 0);
}

#[test]
fn counterexample_evidence_uses_authored_rules_without_reintroducing_removed_edges() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let values = [
        c.declare_constant("a", s).unwrap(),
        c.declare_constant("b", s).unwrap(),
    ];
    let out = c
        .declare_relation("out", RelationRole::Derived, [Parameter::new("value", s)])
        .unwrap();
    let t = rel(&mut c, "t", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let ar = rule(&mut c, a, &[(t, false), (b, true)]);
    rule(&mut c, b, &[(t, true), (a, true)]);
    let head = c.atom(out, [values[0].into()]).unwrap();
    c.add_rule(head, []).unwrap();
    let head = c.atom(out, [values[1].into()]).unwrap();
    let body = c.atom(a, []).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    c.at_most_one("unique", out, [], "test").unwrap();
    let domains = Domains::from([(s, values.to_vec())]);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &domains, &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert_eq!(compare(&c, &domains, &p), 2);
    let m = p.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    let g = &report.groups[0];
    assert!(!g.cone.facts.contains(&atom(b)));
    let VerifiedOutcome::Counterexample(example) = &g.outcome else {
        panic!()
    };
    let GroundEvidence::Derived { rule, premises } = &example.evidence[&atom(a)].evidence else {
        panic!()
    };
    assert_eq!(rule.source, ar);
    assert_eq!(rule.body.len(), 2);
    let PremiseEvidence::Discharged {
        literal_occurrence,
        proof,
    } = premises[1]
    else {
        panic!()
    };
    assert_eq!(literal_occurrence, c.rule(ar).unwrap().body[1].atom().id());
    let replay = p
        .evaluate(example.observation.present.iter().cloned(), &limits)
        .unwrap();
    let mut budget = crate::limits::Budget::new(&limits);
    replay
        .validate_discharge(rule.id, literal_occurrence, proof, &mut budget)
        .unwrap();
    let other = p.rewrite_proofs().find(|x| x.id != proof).unwrap();
    assert!(matches!(
        replay.validate_discharge(rule.id, literal_occurrence, other.id, &mut budget),
        Err(CheckError::Internal(_))
    ));
    let absent = p.evaluate([], &limits).unwrap();
    assert!(matches!(
        absent.validate_discharge(rule.id, literal_occurrence, proof, &mut budget),
        Err(CheckError::Internal(_))
    ));
    let foreign = GroundProgram::prepare(&c, &domains, &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert!(foreign.rewrite_proof(proof).is_none());
}

#[test]
fn newly_settled_components_feed_only_the_next_snapshot() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    rule(&mut c, a, &[(t, false), (b, true)]);
    rule(&mut c, b, &[(t, true), (a, true)]);
    rule(&mut c, x, &[(a, false), (y, true)]);
    rule(&mut c, y, &[(a, true), (x, true)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let p = raw.clone().admit(&Limits::default()).unwrap();
    assert!(p.is_admitted());
    let snapshots: BTreeSet<_> = p.rewrite_proofs().map(|p| p.snapshot).collect();
    assert_eq!(snapshots.len(), 2);
    assert_eq!(p.rewrite_proofs().count(), 4);
    compare(&c, &Domains::new(), &p);
    let mut partial = false;
    for max_work in (0..2000).step_by(10) {
        let p = raw
            .clone()
            .admit(&Limits {
                max_work,
                ..Limits::default()
            })
            .unwrap();
        if p.admission_limit().is_some() && p.rewrite_proofs().count() == 2 {
            partial = true;
            assert!(p.component_for(&atom(a)).unwrap().blocked_by.is_empty());
            assert!(!p.component_for(&atom(x)).unwrap().blocked_by.is_empty());
            compare(&c, &Domains::new(), &p);
        }
    }
    assert!(
        partial,
        "exercise retained, completed first batch after a later limit"
    );
}

#[test]
fn signed_guard_and_extra_producer_matrix_preserves_original_stable_models() {
    for forwarding in [false, true] {
        for left in 0..5 {
            for right in 0..5 {
                for extra in 0..4 {
                    let mut c = Corpus::new();
                    let t = rel(&mut c, "t", true);
                    let u = rel(&mut c, "u", true);
                    let a = rel(&mut c, "a", false);
                    let b = rel(&mut c, "b", false);
                    let (left_head, right_head) = if forwarding {
                        let a_guard = rel(&mut c, "a_guard", false);
                        let b_guard = rel(&mut c, "b_guard", false);
                        rule(&mut c, a, &[(a_guard, false)]);
                        rule(&mut c, b, &[(b_guard, false)]);
                        (a_guard, b_guard)
                    } else {
                        (a, b)
                    };
                    let guards = [
                        vec![],
                        vec![(t, false)],
                        vec![(t, true)],
                        vec![(u, false)],
                        vec![(u, true)],
                    ];
                    let mut body = guards[left].clone();
                    body.push((b, true));
                    rule(&mut c, left_head, &body);
                    let mut body = guards[right].clone();
                    body.push((a, true));
                    rule(&mut c, right_head, &body);
                    if extra & 1 != 0 {
                        rule(&mut c, a, &[(u, false)]);
                    }
                    if extra & 2 != 0 {
                        rule(&mut c, b, &[(t, false)]);
                    }
                    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
                        .unwrap()
                        .admit(&Limits::default())
                        .unwrap();
                    compare(&c, &Domains::new(), &p);
                    for world in subsets(&[atom(t), atom(u)]) {
                        assert_eq!(
                            supported_models(
                                &p,
                                &p.original_rules().cloned().collect::<Vec<_>>(),
                                &world
                            ),
                            supported_models(&p, &p.rules().cloned().collect::<Vec<_>>(), &world),
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn unresolved_positive_provider_outside_the_component_is_not_assumed_false() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let u = rel(&mut c, "u", false);
    let v = rel(&mut c, "v", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let bridge = rel(&mut c, "bridge", false);
    rule(&mut c, u, &[(v, true)]);
    rule(&mut c, v, &[(u, true)]);
    rule(&mut c, a, &[(t, false), (b, true)]);
    rule(&mut c, b, &[(u, false), (bridge, false)]);
    rule(&mut c, bridge, &[(t, false), (a, true)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&Limits::default())
        .unwrap();
    assert!(!p.is_admitted());
    assert!(p.admission_limit().is_none());
    assert_eq!(p.rewrite_proofs().count(), 0);
    assert_eq!(compare(&c, &Domains::new(), &p), 2);
}

#[test]
fn checked_boundaries_distinguish_limits_and_keep_completed_components() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let good = c
        .declare_relation("good", RelationRole::Derived, [Parameter::new("v", s)])
        .unwrap();
    let t = rel(&mut c, "t", true);
    let bad = rel(&mut c, "bad", false);
    for value in [a, b] {
        let head = c.atom(good, [value.into()]).unwrap();
        c.add_rule(head, []).unwrap();
    }
    rule(&mut c, bad, &[(t, false)]);
    c.at_most_one("unique", good, [], "test").unwrap();
    let domains = Domains::from([(s, vec![a, b])]);
    let limits = Limits::default();
    let low = Limits {
        max_work: 0,
        ..limits.clone()
    };
    assert!(matches!(
        GroundProgram::prepare_checked(&c, &domains, &low).unwrap(),
        AnalysisOutcome::Inconclusive(_)
    ));
    let p = GroundProgram::prepare(&c, &domains, &limits).unwrap();
    assert!(matches!(
        p.symbolic_checked(&low).unwrap(),
        AnalysisOutcome::Inconclusive(_)
    ));
    let m = p.symbolic(&limits).unwrap();
    assert!(matches!(
        m.verify_checked(&low).unwrap(),
        AnalysisOutcome::Inconclusive(_)
    ));
    let r = m
        .verify_at_most_one(&Limits {
            max_condition_nodes: 0,
            ..limits.clone()
        })
        .unwrap();
    assert!(matches!(
        r.groups[0].outcome,
        VerifiedOutcome::Inconclusive(_)
    ));
    assert!(!r.all_obligations_proved());
    let mut observed = false;
    let mut kept_conflict = false;
    for max_work in 0..300 {
        let AnalysisOutcome::Complete(m) = p
            .symbolic_checked(&Limits {
                max_work,
                ..limits.clone()
            })
            .unwrap()
        else {
            continue;
        };
        if !m.is_complete() && m.conditions.keys().any(|a| !p.inputs.contains(a)) {
            // Provider-first order need not be source order. Whatever completes
            // remains usable; every interrupted component is explicitly unknown.
            observed = true;
            for (id, cause) in &m.inconclusive {
                for a in &p.component(*id).unwrap().atoms {
                    assert!(
                        matches!(m.fact(a).unwrap(),SymbolicFact::Inconclusive(got) if got==*cause)
                    );
                    if !p.inputs.contains(a) {
                        assert!(!m.conditions.contains_key(a));
                    }
                }
            }
            let report = m.verify_at_most_one(&limits).unwrap();
            assert!(!report.all_obligations_proved());
            kept_conflict |= report
                .groups
                .iter()
                .any(|g| matches!(g.outcome, VerifiedOutcome::Counterexample(_)));
        }
    }
    assert!(observed);
    assert!(kept_conflict);
}

#[test]
fn every_small_budget_leaves_an_atomic_sound_rewrite_prefix() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(t, false), (b, true)]);
    rule(&mut c, b, &[(t, true), (a, true)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut successes = 0;
    for max_work in 0..650 {
        let result = p
            .clone()
            .admit(&Limits {
                max_work,
                ..Limits::default()
            })
            .unwrap();
        if result.admission_limit().is_some() {
            assert!(!result.is_admitted());
            assert_eq!(result.rewrite_proofs().count(), 0);
        } else {
            successes += 1;
            assert!(result.is_admitted());
        }
        compare(&c, &Domains::new(), &result);
    }
    assert!(successes > 0);
}
