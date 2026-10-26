use crate::Session;
use denotate_check::*;
use denotate_ir::*;
use std::collections::{BTreeMap, BTreeSet};

struct Fixture {
    corpus: Corpus,
    keys: SemanticKeys,
    domains: Domains,
    with_a: VerificationId,
    unrestricted: VerificationId,
    no_obligations: VerificationId,
}

fn qualified(name: &str) -> QualifiedKey {
    QualifiedKey::new("", name)
}

// None removes the unselected assumption; Some chooses its grouping columns.
fn fixture(b_grouping: Option<Vec<Column>>) -> Fixture {
    let mut c = Corpus::new();
    let key = c.declare_sort("Key").unwrap();
    let choice = c.declare_sort("Choice").unwrap();
    let k = c.declare_constant("k", key).unwrap();
    let c1 = c.declare_constant("c1", choice).unwrap();
    let c2 = c.declare_constant("c2", choice).unwrap();
    let value = c
        .declare_relation(
            "value",
            RelationRole::Input,
            [Parameter::new("key", key), Parameter::new("choice", choice)],
        )
        .unwrap();
    let other = c
        .declare_relation("other", RelationRole::Input, [Parameter::new("key", key)])
        .unwrap();
    let copy = c
        .declare_relation(
            "copy",
            RelationRole::Derived,
            [Parameter::new("key", key), Parameter::new("choice", choice)],
        )
        .unwrap();
    let first = c
        .declare_relation("first", RelationRole::Derived, [Parameter::new("key", key)])
        .unwrap();
    let second = c
        .declare_relation(
            "second",
            RelationRole::Derived,
            [Parameter::new("key", key)],
        )
        .unwrap();
    let kv = || Term::variable("K", key);
    let cv = || Term::variable("C", choice);
    let head = c.atom(copy, [kv(), cv()]).unwrap();
    let body = c.atom(value, [kv(), cv()]).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    for (head, other, constant) in [(first, second, c1), (second, first, c2)] {
        let head = c.atom(head, [kv()]).unwrap();
        let input = c.atom(value, [kv(), Term::Constant(constant)]).unwrap();
        let negated = c.atom(other, [kv()]).unwrap();
        c.add_rule(head, [Literal::Positive(input), Literal::Negative(negated)])
            .unwrap();
    }
    let a = c
        .assume_at_most_one_in(Namespace::default(), "A", value, ["key".into()])
        .unwrap();
    if let Some(grouping) = b_grouping {
        c.assume_at_most_one_in(Namespace::default(), "B", other, grouping)
            .unwrap();
    }
    let unique = c
        .at_most_one("unique_copy", copy, ["key".into()], "")
        .unwrap();
    // Trivial groups must not leak into results via the keyed group domains.
    c.at_most_one("unselected_copy", copy, ["key".into(), "choice".into()], "")
        .unwrap();
    let with_a = c
        .verification_in(Namespace::default(), "with_a", [a], [unique])
        .unwrap();
    let unrestricted = c
        .verification_in(Namespace::default(), "unrestricted", [], [unique])
        .unwrap();
    let no_obligations = c
        .verification_in(Namespace::default(), "no_obligations", [a], [])
        .unwrap();

    let mut keys = SemanticKeys::default();
    for s in c.sorts() {
        keys.bind_sort(&c, s.id, SortKey(qualified(&s.name)))
            .unwrap();
    }
    for constant in c.constants() {
        keys.bind_constant(
            &c,
            constant.id,
            ConstantKey {
                sort: keys.sort(constant.sort).unwrap().clone(),
                name: constant.name.as_str().into(),
            },
        )
        .unwrap();
    }
    for r in c.relations() {
        keys.bind_relation(&c, r.id, RelationKey::Named(qualified(&r.name)))
            .unwrap();
    }
    for (i, r) in c.rules().enumerate() {
        let rule = RuleKey::Library(qualified(&format!("rule_{i}")));
        keys.bind_rule(&c, r.id, rule.clone()).unwrap();
        for (atom, a) in std::iter::once(&r.head)
            .chain(r.body.iter().map(Literal::atom))
            .enumerate()
        {
            keys.bind_occurrence(
                &c,
                a.id(),
                OccurrenceKey::Library {
                    rule: rule.clone(),
                    atom,
                    argument: None,
                },
            )
            .unwrap();
            for (argument, term) in a.arguments().iter().enumerate() {
                keys.bind_occurrence(
                    &c,
                    term.id(),
                    OccurrenceKey::Library {
                        rule: rule.clone(),
                        atom,
                        argument: Some(argument),
                    },
                )
                .unwrap();
            }
        }
    }
    for a in c.assumptions() {
        keys.bind_assumption(&c, a.id, AssumptionKey(qualified(&a.name)))
            .unwrap();
    }
    for o in c.obligations() {
        keys.bind_obligation(&c, o.id, ObligationKey(qualified(&o.name)))
            .unwrap();
    }
    for v in c.verifications() {
        keys.bind_verification(&c, v.id, VerificationKey(qualified(&v.name)))
            .unwrap();
    }
    keys.validate(&c).unwrap();
    Fixture {
        corpus: c,
        keys,
        domains: BTreeMap::from([(key, vec![k]), (choice, vec![c1, c2])]),
        with_a,
        unrestricted,
        no_obligations,
    }
}

fn request(f: &Fixture, verification: VerificationId) -> CheckRequest {
    let request = CheckRequest::for_verification(
        &f.corpus,
        &f.keys,
        &f.domains,
        verification,
        &Limits::default(),
    )
    .unwrap();
    request
}

#[derive(Debug, PartialEq, Eq)]
struct Capture {
    results: ScopedResults,
    admitted: bool,
    rewrites: BTreeSet<RewriteEvidenceKey>,
}

fn check(f: &Fixture, request: &CheckRequest, mut session: Option<&mut Session>) -> Capture {
    let operations = OperationalLimits::from(&Limits::default());
    let preparation = if let Some(session) = session.as_deref_mut() {
        session.prepare(request, &f.corpus, &f.keys, &operations)
    } else {
        request.prepare(&f.corpus, &f.keys, &operations)
    }
    .unwrap();
    let RequestPreparation::Complete(prepared) = preparation else {
        panic!("preparation exhausted")
    };
    let prepared = prepared.admit(&operations).unwrap();
    let results = if let Some(session) = session {
        let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &operations).unwrap()
        else {
            panic!("local checking exhausted")
        };
        report.checked.results.value
    } else {
        let CheckOutcome::Complete(report) = prepared.verify(&operations).unwrap() else {
            panic!("checking exhausted")
        };
        report.results.value
    };
    assert_eq!(&results.context, request);
    assert_eq!(
        results
            .group_domains
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>(),
        request.obligations
    );
    assert!(results.unfinished.is_none() && results.incomplete.is_empty());
    Capture {
        results,
        admitted: prepared.program().is_admitted(),
        rewrites: prepared.keys().rewrites.values().cloned().collect(),
    }
}

fn assert_behavior(capture: &Capture, restricted: bool, obligations: bool) {
    assert_eq!(capture.admitted, restricted);
    if restricted {
        assert!(
            capture
                .rewrites
                .iter()
                .any(|r| matches!(r.kind, KeyedRewriteKind::Discharge(_)))
        );
        assert!(capture.results.regions.is_empty());
    } else {
        assert!(capture.rewrites.is_empty());
        assert!(!capture.results.regions.is_empty());
        for region in capture.results.regions.values() {
            assert!(
                matches!(region.outcome, ScopedResult::Unsupported(_)),
                "{region:?}"
            );
            assert_eq!(region.completion, RegionCompletion::NoContradiction);
        }
    }
    if obligations {
        assert_eq!(capture.results.groups.len(), 1);
        let (group, outcome) = capture.results.groups.first_key_value().unwrap();
        assert_eq!(group.obligation, ObligationKey(qualified("unique_copy")));
        if restricted {
            assert_eq!(*outcome, ScopedResult::Proved);
        } else {
            let ScopedResult::Counterexample(candidate, _) = outcome else {
                panic!("{outcome:?}")
            };
            assert!(candidate.tuples.len() >= 2);
        }
    } else {
        assert!(capture.results.groups.is_empty());
        assert!(capture.results.group_domains.is_empty());
    }
    assert!(
        capture
            .results
            .group(&GroupKey {
                obligation: ObligationKey(qualified("unselected_copy")),
                tuple: vec![
                    ConstantKey {
                        sort: SortKey(qualified("Key")),
                        name: "k".into()
                    },
                    ConstantKey {
                        sort: SortKey(qualified("Choice")),
                        name: "c1".into()
                    }
                ],
            })
            .is_none()
    );
}

#[test]
fn selected_context_controls_admission_and_obligations_across_sessions() {
    let f = fixture(Some(vec![]));
    {
        for mut session in [Session::default(), Session::with_grounding()] {
            for (verification, restricted, obligations) in [
                (f.with_a, true, true),
                (f.unrestricted, false, true),
                (f.with_a, true, true),
                (f.no_obligations, true, false),
                (f.unrestricted, false, true),
                (f.with_a, true, true),
            ] {
                let request = request(&f, verification);
                let fresh = check(&f, &request, None);
                assert_behavior(&fresh, restricted, obligations);
                let warm = check(&f, &request, Some(&mut session));
                assert_eq!(warm, fresh);
            }
        }
    }
}

#[test]
fn edits_to_unselected_assumptions_do_not_change_the_selected_context() {
    {
        for mut session in [Session::default(), Session::with_grounding()] {
            let baseline = fixture(Some(vec![]));
            let expected = check(
                &baseline,
                &request(&baseline, baseline.with_a),
                Some(&mut session),
            );
            for grouping in [Some(vec!["key".into()]), None, Some(vec![])] {
                let f = fixture(grouping);
                let request = request(&f, f.with_a);
                assert_eq!(check(&f, &request, None), expected);
                assert_eq!(check(&f, &request, Some(&mut session)), expected);
            }
        }
    }
}

#[test]
fn unnamed_subsets_keep_only_selected_trivial_group_domains_and_raw_preparation_keeps_all() {
    let f = fixture(None);
    let limits = Limits::default();
    let raw = GroundProgram::prepare(&f.corpus, &f.domains, &limits).unwrap();
    let raw_keys = GroundKeyIndex::build(&f.corpus, &f.keys, &raw).unwrap();
    let mut request =
        CheckRequest::all_obligations(&f.corpus, &f.keys, &f.domains, &[], &limits).unwrap();
    assert_eq!(
        raw_keys.groups.keys().cloned().collect::<BTreeSet<_>>(),
        request.obligations
    );
    assert_eq!(request.obligations.len(), 2);
    let selected = ObligationKey(qualified("unselected_copy"));
    request.obligations = BTreeSet::from([selected.clone()]);
    for mut session in [Session::default(), Session::with_grounding()] {
        let fresh = check(&f, &request, None);
        assert_eq!(check(&f, &request, Some(&mut session)), fresh);
        assert!(fresh.results.groups.is_empty());
        let domain = &fresh.results.group_domains[&selected];
        let tuple = domain
            .domains
            .iter()
            .map(|d| d.first().unwrap().clone())
            .collect();
        let group = domain.key(&selected, tuple).unwrap();
        assert_eq!(fresh.results.group(&group), Some(ScopedResult::Proved));
        let omitted = GroupKey {
            obligation: ObligationKey(qualified("unique_copy")),
            tuple: group.tuple[..1].to_vec(),
        };
        assert_eq!(fresh.results.group(&omitted), None);
        let mut empty = request.clone();
        empty.obligations.clear();
        let fresh = check(&f, &empty, None);
        assert_behavior(&fresh, false, false);
        assert_eq!(check(&f, &empty, Some(&mut session)), fresh);
    }
}

#[test]
fn verification_requests_reject_unknown_or_mismatched_selections() {
    let f = fixture(Some(vec![]));
    let operations = OperationalLimits::from(&Limits::default());
    for change in 0..6 {
        let mut request = request(&f, f.with_a);
        match change {
            0 => request.obligations.clear(),
            1 => request.constraints.clear(),
            2 => request.constraints.push(InputConstraint::AtMostOne {
                relation: RelationKey::Named(qualified("other")),
                group_by: vec![],
            }),
            3 => {
                request
                    .obligations
                    .insert(ObligationKey(qualified("missing")));
            }
            4 => request.verification = Some(VerificationKey(qualified("missing"))),
            _ => {
                request
                    .obligations
                    .insert(ObligationKey(qualified("unselected_copy")));
            }
        }
        assert!(
            matches!(
                request.prepare(&f.corpus, &f.keys, &operations),
                Err(CheckError::InvalidRequest(_))
            ),
            "change {change}"
        );
        assert!(
            matches!(
                Session::with_grounding().prepare(&request, &f.corpus, &f.keys, &operations),
                Err(CheckError::InvalidRequest(_))
            ),
            "change {change}"
        );
    }
    let foreign = fixture(None);
    assert!(matches!(
        CheckRequest::for_verification(
            &f.corpus,
            &f.keys,
            &f.domains,
            foreign.with_a,
            &Limits::default()
        ),
        Err(CheckError::InvalidRequest(_))
    ));
    let mut legacy =
        CheckRequest::all_obligations(&f.corpus, &f.keys, &f.domains, &[], &Limits::default())
            .unwrap();
    assert!(legacy.verification.is_none());
    legacy
        .obligations
        .insert(ObligationKey(qualified("missing")));
    assert!(matches!(
        legacy.prepare(&f.corpus, &f.keys, &operations),
        Err(CheckError::InvalidRequest(_))
    ));
}
