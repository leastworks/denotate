use super::*;

fn declared(
    c: &mut Corpus,
    h: Option<RelationId>,
    decisions: Option<BTreeSet<RelationId>>,
    obligations: &[ObligationId],
) -> VerificationId {
    c.verification_with_options_in(
        Namespace::default(),
        format!("projection{}", c.verifications().count()),
        [],
        obligations.iter().copied(),
        [],
        VerificationOptions {
            semantics: Semantics::Completion,
            hypothesis: h,
            decisions,
        },
    )
    .unwrap()
}

#[test]
fn a_contradictory_classification_is_not_rejection_even_with_empty_decisions() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(h, true)]);
    let total = c
        .require_no_rejections_in(Namespace::default(), "total", h, "")
        .unwrap();
    for decisions in [None, Some(BTreeSet::new())] {
        let v = declared(&mut c, Some(h), decisions, &[total]);
        let e = prepare(&c, v, &Domains::new());
        assert!(matches!(
            e.observation([]).unwrap(),
            ObservationOutcome::ClassificationNoMeaning
        ));
        for _ in 0..2 {
            let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
            let class = r.classification.as_ref().unwrap();
            assert!(class.no_meaning.exists());
            assert!(matches!(class.rejected, Search::None));
            assert!(r.has_failures());
            assert!(!r.all_rejected());
            assert!(!r.is_incomplete());
            assert!(r.obligations[&total].complete());
            assert!(!r.obligations[&total].failed());
        }
    }
}

#[test]
fn second_query_cutoff_is_unknown_and_one_base_model_suffices_for_rejection() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    let p = rel(&mut c, "p", false);
    let absent = rel(&mut c, "absent", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false), (absent, false)]);
    let total = c
        .require_no_rejections_in(Namespace::default(), "total", h, "")
        .unwrap();
    let v = declared(&mut c, Some(h), None, &[total]);
    let mut e = prepare(&c, v, &Domains::new());
    e.config.max_solves = 1;
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.is_incomplete());
    assert!(!r.all_rejected());
    assert!(!r.has_failures());
    assert!(!r.obligations[&total].complete());
    let class = r.classification.unwrap();
    assert!(matches!(class.rejected, Search::Inconclusive(_)));
    assert!(matches!(class.no_meaning, Search::None));
    // The dead producer leaves only H in the classification cone. Existence
    // does not spend another solve distinguishing processing interpretations.
    e.config.max_solves = 3;
    let ObservationOutcome::Rejected { without_hypothesis } = e.observation([]).unwrap() else {
        panic!()
    };
    assert_eq!(
        without_hypothesis.scope(),
        ModelScope::ClassificationWithoutHypothesis
    );
    assert_eq!(without_hypothesis.value(&atom(h)), Some(false));
    assert_eq!(without_hypothesis.value(&atom(absent)), None);
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.all_rejected());
    assert!(r.obligations[&total].failed());
    assert!(!r.is_incomplete());
}

#[test]
fn no_meaning_and_rejection_coexist_without_an_all_rejected_label() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(i, false), (h, true)]);
    let total = c
        .require_no_rejections_in(Namespace::default(), "total", h, "")
        .unwrap();
    let v = declared(&mut c, Some(h), None, &[total]);
    let r = prepare(&c, v, &Domains::new())
        .check(&keys(&c), &CheckOptions::default())
        .unwrap();
    let class = r.classification.as_ref().unwrap();
    assert!(class.rejected.exists());
    assert!(class.no_meaning.exists());
    assert!(!class.accepted.exists());
    assert!(!r.all_rejected());
    assert!(r.has_failures());
    assert!(!r.is_incomplete());
}

#[test]
fn projected_helpers_remain_free_for_processing_and_each_property() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "helper", false);
    let h = rel(&mut c, "h", false);
    let not_p = rel(&mut c, "not_helper", false);
    let not_h = rel(&mut c, "not_h", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, h, &[(p, true)]);
    rule(&mut c, not_p, &[(p, true)]);
    rule(&mut c, not_h, &[(h, true)]);
    let yes = c.empty("no_yes", p, "").unwrap();
    let no = c.empty("no_no", not_p, "").unwrap();
    let accepted_only = c.empty("accepted_only", not_h, "").unwrap();
    for decisions in [Some([h].into()), Some(BTreeSet::new())] {
        let v = declared(&mut c, Some(h), decisions, &[yes, no, accepted_only]);
        let e = prepare(&c, v, &Domains::new());
        for _ in 0..2 {
            let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
            assert!(r.classification.as_ref().unwrap().accepted.exists());
            assert!(!r.meaning.ambiguous.exists());
            assert!(!r.meaning.no_meaning.exists());
            assert!(r.obligations[&yes].failed());
            assert!(r.obligations[&no].failed());
            assert!(!r.obligations[&accepted_only].failed());
            assert!(!r.is_incomplete());
        }
        // A downstream contradiction for helper=false may narrow the helper,
        // but must not reject the already established decision h=true.
        let name = format!("odd{}", c.relations().count());
        let odd = rel(&mut c, &name, false);
        rule(&mut c, odd, &[(odd, true), (p, true)]);
        let fresh = prepare(&c, v, &Domains::new());
        let ObservationOutcome::Accepted {
            processing: Interpretations::Unique(model),
            ..
        } = fresh.observation([]).unwrap()
        else {
            panic!()
        };
        assert_eq!(model.value(&atom(p)), Some(true));
    }
    let strict = declared(&mut c, Some(h), None, &[]);
    assert!(matches!(
        prepare(&c, strict, &Domains::new())
            .observation([])
            .unwrap(),
        ObservationOutcome::Ambiguous { .. }
    ));
}

#[test]
fn projected_verification_reports_match_exhaustive_authored_equations() {
    for left in 0..6 {
        for right in 0..6 {
            let mut c = Corpus::new();
            let input = rel(&mut c, "input", true);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            let atoms = [input, p, q];
            rule(&mut c, p, &[(atoms[left / 2], left % 2 != 0)]);
            rule(&mut c, q, &[(atoms[right / 2], right % 2 != 0)]);
            let o = c.empty("empty_q", q, "").unwrap();
            for h in [None, Some(p)] {
                for decisions in [
                    None,
                    Some(BTreeSet::new()),
                    Some([p].into()),
                    Some([q].into()),
                ] {
                    let count = |models: &[BTreeSet<RelationId>]| {
                        models
                            .iter()
                            .map(|m| {
                                m.iter()
                                    .copied()
                                    .filter(|r| decisions.as_ref().is_none_or(|ds| ds.contains(r)))
                                    .collect::<BTreeSet<_>>()
                            })
                            .collect::<BTreeSet<_>>()
                            .len()
                    };
                    let v = declared(&mut c, h, decisions.clone(), &[o]);
                    let e = prepare(&c, v, &Domains::new());
                    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
                    let (
                        mut accepted,
                        mut rejected,
                        mut class_many,
                        mut class_none,
                        mut processing_none,
                        mut processing_many,
                        mut failure,
                    ) = (false, false, false, false, false, false, false);
                    for value in [false, true] {
                        if let Some(h) = h {
                            let models = oracle(&c, &[h], input, value, Some(h));
                            match count(&models) {
                                0 => {
                                    if oracle(&c, &[h], input, value, None).is_empty() {
                                        class_none = true;
                                    } else {
                                        rejected = true;
                                    }
                                    continue;
                                }
                                1 => accepted = true,
                                _ => {
                                    class_many = true;
                                    continue;
                                }
                            }
                        }
                        let meanings = oracle(&c, &[p, q], input, value, h);
                        processing_none |= meanings.is_empty();
                        processing_many |= count(&meanings) > 1;
                        let mut roots = vec![q];
                        roots.extend(h);
                        failure |= oracle(&c, &roots, input, value, h)
                            .iter()
                            .any(|m| m.contains(&q));
                    }
                    assert!(!r.is_incomplete(), "{left}/{right}/{h:?}/{decisions:?}");
                    if let Some(class) = &r.classification {
                        assert_eq!(class.accepted.exists(), accepted);
                        assert_eq!(class.rejected.exists(), rejected);
                        assert_eq!(class.ambiguous.exists(), class_many);
                        assert_eq!(class.no_meaning.exists(), class_none);
                    }
                    assert_eq!(r.meaning.no_meaning.exists(), processing_none);
                    assert_eq!(r.meaning.ambiguous.exists(), processing_many);
                    assert_eq!(r.obligations[&o].failed(), failure);
                }
            }
        }
    }
}

#[test]
fn hypothesis_stays_required_when_it_is_not_a_selected_decision() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, bad, &[(p, true)]);
    let o = c.empty("clean", bad, "").unwrap();
    let v = declared(&mut c, Some(h), Some(BTreeSet::new()), &[o]);
    let e = prepare(&c, v, &Domains::new());
    let ObservationOutcome::Accepted {
        processing: Interpretations::Unique(model),
        ..
    } = e.observation([]).unwrap()
    else {
        panic!()
    };
    assert_eq!(model.value(&atom(h)), Some(true));
    assert_eq!(model.value(&atom(p)), Some(true));
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.obligations[&o].complete());
    assert!(!r.obligations[&o].failed());
}

// Compare whole-verification answers with the independent world/model enumerator.
// A repeated query and freshly prepared engine exercise the no-hidden-state contract.
fn component_oracle(c: &Corpus, v: VerificationId) -> super::super::Report {
    let e = prepare(c, v, &Domains::new());
    let options = CheckOptions::default();
    let expected = e.check_enumerated(&keys(c), &options).unwrap();
    let actual = e.check(&keys(c), &options).unwrap();
    super::scale::same_report(&actual, &expected);
    super::scale::same_report(&actual, &e.check(&keys(c), &options).unwrap());
    super::scale::same_report(
        &actual,
        &prepare(c, v, &Domains::new())
            .check(&keys(c), &options)
            .unwrap(),
    );
    actual
}

#[test]
fn component_pairs_preserve_coupled_loops_outside_the_selected_decisions() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, a, &[(a, false)]);
    rule(&mut c, b, &[(b, false)]);
    rule(&mut c, bad, &[(a, false), (b, true), (bad, true)]);
    rule(&mut c, bad, &[(a, true), (b, false), (bad, true)]);
    let v = declared(&mut c, None, Some(BTreeSet::from([a])), &[]);
    let r = component_oracle(&c, v);
    let Search::Exists(pair) = r.meaning.ambiguous else {
        panic!("coupled 00/11 must remain ambiguous")
    };
    assert_eq!(pair.first.value(&atom(a)), pair.first.value(&atom(b)));
    assert_eq!(pair.second.value(&atom(a)), pair.second.value(&atom(b)));
    assert_ne!(pair.first.value(&atom(a)), pair.second.value(&atom(a)));
}

#[test]
fn component_totality_is_not_uniqueness_for_even_or_positive_loops() {
    for even in [false, true] {
        let mut c = Corpus::new();
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        if even {
            rule(&mut c, a, &[(b, true)]);
            rule(&mut c, b, &[(a, true)]);
        } else {
            rule(&mut c, a, &[(a, false)]);
        }
        let v = declared(&mut c, None, Some(BTreeSet::from([a])), &[]);
        let r = component_oracle(&c, v);
        assert!(r.meaning.ambiguous.exists());
        assert!(matches!(r.meaning.no_meaning, Search::None));
    }
}

#[test]
fn local_ambiguity_at_unreachable_boundaries_and_free_helpers_are_not_findings() {
    for mode in 0..3 {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let guard = rel(&mut c, "guard", false);
        let p = rel(&mut c, "p", false);
        let out = rel(&mut c, "out", false);
        rule(&mut c, guard, &[(i, false), (i, true)]);
        rule(
            &mut c,
            p,
            &[(p, false), (if mode == 0 { guard } else { i }, false)],
        );
        rule(&mut c, out, &[(p, false)]);
        if mode == 1 {
            rule(&mut c, out, &[(p, true)]);
        }
        let h = (mode == 2).then(|| {
            let h = rel(&mut c, "h", false);
            rule(&mut c, h, &[(i, true)]);
            h
        });
        let v = declared(&mut c, h, Some(BTreeSet::from([out])), &[]);
        let r = component_oracle(&c, v);
        assert!(matches!(r.meaning.ambiguous, Search::None), "mode {mode}");
    }
}

#[test]
fn pair_search_requires_extension_through_unselected_contradiction() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, bad, &[(bad, true)]);
    let v = declared(&mut c, None, Some(BTreeSet::from([p])), &[]);
    let r = component_oracle(&c, v);
    assert!(r.meaning.no_meaning.exists());
    assert!(matches!(r.meaning.ambiguous, Search::None));
}

#[test]
fn local_function_proofs_share_cycles_and_their_acyclic_readers() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false)]);
    rule(&mut c, p, &[(p, false), (i, false)]);
    rule(&mut c, q, &[(p, true)]);
    let v = declared(&mut c, None, Some(BTreeSet::from([q])), &[]);
    let mut e = prepare(&c, v, &Domains::new());
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let r = e.check_unpruned(&keys(&c), &Default::default()).unwrap();
    super::scale::same_report(
        &r,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(matches!(r.meaning.ambiguous, Search::None));
    let snapshot = sizes.snapshot();
    let s = snapshot
        .searches
        .iter()
        .find(|s| s.phase == "completion processing ambiguity")
        .unwrap();
    assert!(s.existence.unique_components > 0);
    assert!(
        s.existence
            .component_details
            .iter()
            .all(|d| d.query == "local-uniqueness")
    );
    // An interrupted local proof must not become a uniqueness certificate.
    e.config.max_solves = 0;
    let r = e.check_unpruned(&keys(&c), &Default::default()).unwrap();
    assert!(!r.meaning.ambiguous.complete());
    assert!(r.is_incomplete());
}

#[test]
fn component_determinacy_matches_enumeration_across_signed_three_atom_graphs() {
    for edges in 0..216 {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        let d = rel(&mut c, "d", false);
        let atoms = [i, a, b];
        let mut code = edges;
        for head in [a, b, d] {
            let e = code % 6;
            code /= 6;
            rule(&mut c, head, &[(atoms[e / 2], e % 2 != 0)]);
        }
        // This extra producer includes a correlated positive guard, so local
        // boundary freedom differs from reachable inputs in some graph shapes.
        rule(&mut c, d, &[(a, false), (b, false)]);
        let v = declared(&mut c, None, Some(BTreeSet::from([d])), &[]);
        component_oracle(&c, v);
    }
}

#[test]
fn reachable_component_pairs_enforce_selected_assumptions() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(p, false), (i, false)]);
    let restriction = c.assume_empty_in(Namespace::default(), "no_i", i).unwrap();
    let v = verification(&mut c, None, &[restriction]);
    let r = component_oracle(&c, v);
    assert!(matches!(r.meaning.ambiguous, Search::None));
    let v = verification(&mut c, None, &[]);
    assert!(component_oracle(&c, v).meaning.ambiguous.exists());
}

#[test]
fn acyclic_decisions_need_no_second_model() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false)]);
    rule(&mut c, q, &[(p, true)]);
    let v = declared(&mut c, None, Some(BTreeSet::from([q])), &[]);
    let mut e = prepare(&c, v, &Domains::new());
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let actual = e.check(&keys(&c), &Default::default()).unwrap();
    super::scale::same_report(
        &actual,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    let snapshot = sizes.snapshot();
    let query = snapshot
        .searches
        .iter()
        .find(|s| s.phase == "completion processing ambiguity")
        .unwrap();
    assert!(
        query
            .encoding_details
            .iter()
            .all(|e| e.purpose != "shared-pair" && e.purpose != "model-under-hypothesis")
    );
    assert_eq!(query.existence.shared_atoms, e.cone.atoms.len());
}

#[test]
fn local_component_proofs_do_not_restart_the_query_solve_allowance() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    for (head, input) in [(p, i), (q, j)] {
        rule(&mut c, head, &[(input, false)]);
        rule(&mut c, head, &[(head, false), (input, false)]);
    }
    let v = declared(&mut c, None, Some(BTreeSet::from([p, q])), &[]);
    let mut e = prepare(&c, v, &Domains::new());
    e.config.max_solves = 1;
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let r = e.check(&keys(&c), &Default::default()).unwrap();
    assert!(matches!(r.meaning.ambiguous, Search::Inconclusive(_)));
    let snapshot = sizes.snapshot();
    let query = snapshot
        .searches
        .iter()
        .find(|s| s.phase == "completion processing ambiguity")
        .unwrap();
    assert!(
        query
            .existence
            .component_details
            .iter()
            .any(|c| c.state == "unique")
    );
    assert!(
        query
            .existence
            .component_details
            .iter()
            .any(|c| c.state == "incomplete")
    );
}
