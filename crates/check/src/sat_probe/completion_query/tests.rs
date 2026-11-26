use super::*;
use crate::test_support::rewrites::{atom, rel, rule};
use denotate_ir::*;
mod branches;
mod contracts;
mod cover_lifting;
mod determinacy;
mod exploration;
mod implied_literals;
mod ledger;
mod pruning;
mod reports;
pub(super) mod scale;
mod search_free;

pub(super) fn keys(c: &Corpus) -> SemanticKeys {
    let mut k = SemanticKeys::default();
    let qualified = |name: &str| QualifiedKey::new("test", name.to_owned());
    for s in c.sorts() {
        k.bind_sort(c, s.id, SortKey(qualified(&s.name))).unwrap();
    }
    for a in c.constants() {
        k.bind_constant(
            c,
            a.id,
            ConstantKey {
                sort: k.sort(a.sort).unwrap().clone(),
                name: a.name.clone().into(),
            },
        )
        .unwrap();
    }
    for r in c.relations() {
        k.bind_relation(c, r.id, RelationKey::Named(qualified(&r.name)))
            .unwrap();
    }
    for (i, r) in c.rules().enumerate() {
        let key = RuleKey::Library(qualified(&format!("rule{i}")));
        k.bind_rule(c, r.id, key.clone()).unwrap();
        for (i, a) in std::iter::once(&r.head)
            .chain(r.body.iter().map(Literal::atom))
            .enumerate()
        {
            k.bind_occurrence(
                c,
                a.id(),
                OccurrenceKey::Library {
                    rule: key.clone(),
                    atom: i,
                    argument: None,
                },
            )
            .unwrap();
            for (j, t) in a.arguments().iter().enumerate() {
                k.bind_occurrence(
                    c,
                    t.id(),
                    OccurrenceKey::Library {
                        rule: key.clone(),
                        atom: i,
                        argument: Some(j),
                    },
                )
                .unwrap();
            }
        }
    }
    for a in c.assumptions() {
        k.bind_assumption(c, a.id, AssumptionKey(qualified(&a.name)))
            .unwrap();
    }
    for o in c.obligations() {
        k.bind_obligation(c, o.id, ObligationKey(qualified(&o.name)))
            .unwrap();
    }
    for n in c.notices() {
        k.bind_notice(c, n.id, NoticeKey(qualified(&n.name)))
            .unwrap();
    }
    for v in c.verifications() {
        k.bind_verification(c, v.id, VerificationKey(qualified(&v.name)))
            .unwrap();
    }
    k
}

pub(super) fn verification(
    c: &mut Corpus,
    h: Option<RelationId>,
    assumptions: &[AssumptionId],
) -> VerificationId {
    c.verification_with_options_in(
        Namespace::new(["test"]).unwrap(),
        format!("v{}", c.verifications().count()),
        assumptions.iter().copied(),
        [],
        [],
        VerificationOptions {
            semantics: Semantics::Completion,
            hypothesis: h,
            decisions: None,
        },
    )
    .unwrap()
}
pub(super) fn prepare(c: &Corpus, v: VerificationId, d: &Domains) -> Engine {
    match Engine::prepare(
        c,
        d,
        &keys(c),
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap()
    {
        Preparation::Ready(e) => e,
        Preparation::InputDomains(e) => panic!("domains: {e:?}"),
        Preparation::Inconclusive(e) => panic!("inconclusive: {e:?}"),
    }
}
fn size(a: &Interpretations) -> usize {
    match a {
        Interpretations::NoMeaning => 0,
        Interpretations::Unique(_) => 1,
        Interpretations::Multiple { .. } => 2,
        _ => panic!("{a:?}"),
    }
}

#[test]
fn self_support_is_a_completion_model_and_hypothesis_can_select_it() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "recognized", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    let plain = verification(&mut c, None, &[]);
    let selected = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, plain, &Domains::new());
    let ObservationOutcome::WholeProgram(Interpretations::Multiple { first, second }) =
        e.observation([]).unwrap()
    else {
        panic!()
    };
    assert_ne!(first.value(&atom(p)), second.value(&atom(p)));
    let e = prepare(&c, selected, &Domains::new());
    let ObservationOutcome::Accepted {
        classification,
        processing,
    } = e.observation([]).unwrap()
    else {
        panic!()
    };
    assert_eq!(classification.value(&atom(p)), Some(true));
    assert_eq!(classification.scope(), ModelScope::Classification);
    assert_eq!(size(&processing), 1);
}

#[test]
fn rejected_is_not_no_meaning_or_inconsistent_worlds() {
    let mut c = Corpus::new();
    let raw = rel(&mut c, "raw", true);
    let h = rel(&mut c, "recognized", false);
    let odd = rel(&mut c, "odd", false);
    rule(&mut c, h, &[(raw, false)]);
    rule(&mut c, odd, &[(odd, true)]);
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    assert!(matches!(
        e.observation([]).unwrap(),
        ObservationOutcome::Rejected { .. }
    ));
    assert!(matches!(
        e.observation([atom(raw)]).unwrap(),
        ObservationOutcome::Accepted {
            processing: Interpretations::NoMeaning,
            ..
        }
    ));
    assert!(matches!(
        e.worlds(&WorldQuery::default()).unwrap(),
        WorldAnswer::World(_)
    ));
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Domains::new());
    assert!(matches!(
        e.observation([]).unwrap(),
        ObservationOutcome::WholeProgram(Interpretations::NoMeaning)
    ));
    let missing = rel(&mut c, "missing", false);
    let a = c
        .assume_at_least_one_in(Namespace::new(["test"]).unwrap(), "impossible", missing, [])
        .unwrap();
    let v = verification(&mut c, Some(h), &[a]);
    let e = prepare(&c, v, &Domains::new());
    assert!(matches!(
        e.worlds(&WorldQuery::default()).unwrap(),
        WorldAnswer::NoWorld
    ));
    assert!(matches!(
        e.observation([atom(raw)]).unwrap(),
        ObservationOutcome::NotPermitted
    ));
}

#[test]
fn downstream_cannot_choose_classification_or_erase_its_ambiguity() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    let downstream = rel(&mut c, "downstream", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[]);
    // A possible producer remains in scope even when its input is false in
    // this particular observation: liveness is independent of the observation.
    let absent = rel(&mut c, "absent", true);
    rule(&mut c, h, &[(p, false), (absent, false)]);
    // Only the p=true classification has a whole-program extension.
    rule(&mut c, downstream, &[(p, true), (downstream, true)]);
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    let ObservationOutcome::Ambiguous { first, second } = e.observation([]).unwrap() else {
        panic!()
    };
    assert_ne!(first.value(&atom(p)), second.value(&atom(p)));
    assert_eq!(first.value(&atom(downstream)), None);
}

#[test]
fn classification_keeps_all_inputs_and_processing_pins_its_model() {
    let mut c = Corpus::new();
    let outside = rel(&mut c, "outside", true);
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, out, &[(p, true)]);
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    for present in [vec![], vec![atom(outside)], vec![]] {
        let fresh = prepare(&c, v, &Domains::new());
        for engine in [&e, &fresh] {
            let ObservationOutcome::Accepted {
                classification,
                processing: Interpretations::Unique(m),
            } = engine.observation(present.clone()).unwrap()
            else {
                panic!()
            };
            assert_eq!(
                classification.value(&atom(outside)),
                Some(!present.is_empty())
            );
            assert_eq!(classification.value(&atom(out)), None);
            assert_eq!(m.value(&atom(p)), Some(true));
            assert_eq!(m.value(&atom(out)), Some(false));
        }
    }
    let exclude_all = WorldQuery {
        exclude: vec![vec![]],
        ..Default::default()
    };
    assert!(matches!(
        e.worlds(&exclude_all).unwrap(),
        WorldAnswer::NoWorld
    ));
    assert!(matches!(
        e.worlds(&WorldQuery::default()).unwrap(),
        WorldAnswer::World(_)
    ));
}

#[test]
fn finite_unseeded_instances_and_domain_edits_survive_preparation() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let p = c
        .declare_relation("p", RelationRole::Derived, [Parameter::new("x", s)])
        .unwrap();
    let head = c.atom(p, [Term::variable("X", s)]).unwrap();
    let body = c.atom(p, [Term::variable("X", s)]).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    let v = verification(&mut c, None, &[]);
    for values in [vec![a, b], vec![], vec![b]] {
        let e = prepare(&c, v, &Domains::from([(s, values.clone())]));
        assert_eq!(e.original_program().rules().count(), values.len());
        let ObservationOutcome::WholeProgram(result) = e.observation([]).unwrap() else {
            panic!()
        };
        assert_eq!(size(&result), if values.is_empty() { 1 } else { 2 });
    }
}

#[test]
fn assumption_truth_is_selected_and_never_conditioned_on_h_or_other_assumptions() {
    for negative in [false, true] {
        let mut c = Corpus::new();
        let p = rel(&mut c, "p", false);
        let h = rel(&mut c, "h", false);
        let flag = rel(&mut c, "flag", true);
        rule(&mut c, p, &[(p, negative), (flag, false)]);
        let a = c
            .assume_empty_in(Namespace::new(["test"]).unwrap(), "cyclic", p)
            .unwrap();
        let no_flag = c
            .assume_empty_in(Namespace::new(["test"]).unwrap(), "no_flag", flag)
            .unwrap();
        let v = verification(&mut c, Some(h), &[a, no_flag]);
        let e = prepare(&c, v, &Domains::new());
        let report = e.check(&keys(&c), &CheckOptions::default()).unwrap();
        assert!(report.is_incomplete());
        assert!(report.assumptions.iter().any(|a| a.failed()));
        assert!(matches!(
            e.observation([atom(flag)]).unwrap(),
            ObservationOutcome::UndeterminedAssumptions(_)
        ));
        // Extra completion compatibility is not a global declaration check.
        let v = verification(&mut c, Some(h), &[no_flag]);
        let e = prepare(&c, v, &Domains::new());
        assert!(matches!(
            e.observation([]).unwrap(),
            ObservationOutcome::Rejected { .. }
        ));
    }
}

#[test]
fn acyclic_derived_assumptions_define_w_independently() {
    let mut c = Corpus::new();
    let raw = rel(&mut c, "raw", true);
    let permitted = rel(&mut c, "permitted", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, permitted, &[(raw, true)]);
    rule(&mut c, h, &[]);
    let a = c
        .assume_at_least_one_in(Namespace::new(["test"]).unwrap(), "a", permitted, [])
        .unwrap();
    let v = verification(&mut c, Some(h), &[a]);
    let e = prepare(&c, v, &Domains::new());
    assert!(matches!(
        e.observation([atom(raw)]).unwrap(),
        ObservationOutcome::NotPermitted
    ));
    assert!(matches!(
        e.observation([]).unwrap(),
        ObservationOutcome::Accepted { .. }
    ));
    let without = verification(&mut c, Some(h), &[]);
    assert!(matches!(
        prepare(&c, without, &Domains::new())
            .observation([atom(raw)])
            .unwrap(),
        ObservationOutcome::Accepted { .. }
    ));
    let limits = Limits {
        max_bdd_variables: 0,
        max_bdd_nodes: 0,
        max_bdd_tasks: 0,
        max_condition_nodes: 0,
        ..Default::default()
    };
    let Preparation::Ready(e) = Engine::prepare(
        &c,
        &Domains::new(),
        &keys(&c),
        v,
        &limits,
        QueryLimits::default(),
    )
    .unwrap() else {
        panic!()
    };
    assert!(matches!(
        e.observation([]).unwrap(),
        ObservationOutcome::Accepted { .. }
    ));
}

#[test]
fn within_is_checked_before_evaluation_and_eligibility_edits_rebuild() {
    let mut c = Corpus::new();
    let raw = rel(&mut c, "raw", true);
    let eligible = rel(&mut c, "eligible", false);
    let h = rel(&mut c, "h", false);
    c.restrict_input(raw, eligible).unwrap();
    rule(&mut c, h, &[(raw, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    assert!(e.observation([atom(raw)]).is_err());
    assert!(matches!(
        e.observation([]).unwrap(),
        ObservationOutcome::Rejected { .. }
    ));
    rule(&mut c, eligible, &[]);
    let e = prepare(&c, v, &Domains::new());
    assert!(matches!(
        e.observation([atom(raw)]).unwrap(),
        ObservationOutcome::Accepted { .. }
    ));
    rule(&mut c, eligible, &[(eligible, false)]);
    let e = prepare(&c, v, &Domains::new());
    assert!(matches!(
        e.observation([atom(raw)]).unwrap(),
        ObservationOutcome::Accepted { .. }
    ));
}

#[test]
fn finite_input_cardinality_and_derived_restrictions_share_the_same_universe() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let input = c
        .declare_relation("input", RelationRole::Input, [Parameter::new("x", s)])
        .unwrap();
    let derived = c
        .declare_relation("derived", RelationRole::Derived, [Parameter::new("x", s)])
        .unwrap();
    c.constrain_input(input, Cardinality::ExactlyOne, [])
        .unwrap();
    let head = c.atom(derived, [Term::variable("X", s)]).unwrap();
    let body = c.atom(input, [Term::variable("X", s)]).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    let h = rel(&mut c, "recognized", false);
    rule(&mut c, h, &[]);
    let a_input = GroundAtom::new(input, [a]);
    let b_input = GroundAtom::new(input, [b]);
    let domains = Domains::from([(s, vec![a, b])]);
    for kind in [
        Cardinality::Empty,
        Cardinality::AtMostOne,
        Cardinality::AtLeastOne,
        Cardinality::ExactlyOne,
    ] {
        let ns = Namespace::new(["test"]).unwrap();
        let name = format!("assumption{}", c.assumptions().count());
        let restriction = match kind {
            Cardinality::Empty => c.assume_empty_in(ns, name, derived),
            Cardinality::AtMostOne => c.assume_at_most_one_in(ns, name, derived, []),
            Cardinality::AtLeastOne => c.assume_at_least_one_in(ns, name, derived, []),
            Cardinality::ExactlyOne => c.assume_exactly_one_in(ns, name, derived, []),
        }
        .unwrap();
        let v = verification(&mut c, Some(h), &[restriction]);
        let e = prepare(&c, v, &domains);
        for world in [
            vec![],
            vec![a_input.clone()],
            vec![b_input.clone()],
            vec![a_input.clone(), b_input.clone()],
        ] {
            let allowed = world.len() == 1 && kind != Cardinality::Empty;
            assert_eq!(
                matches!(
                    e.observation(world).unwrap(),
                    ObservationOutcome::Accepted { .. }
                ),
                allowed
            );
        }
        let e = prepare(&c, v, &Domains::from([(s, vec![])]));
        assert_eq!(
            matches!(
                e.worlds(&WorldQuery::default()).unwrap(),
                WorldAnswer::NoWorld
            ),
            kind.has_coverage()
        );
    }
}

#[test]
fn mixed_semantics_keep_stable_behavior_and_completion_refusals() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(p, false)]);
    let v = verification(&mut c, None, &[]);
    let stable = c
        .verification_in(Namespace::new(["test"]).unwrap(), "stable", [], [])
        .unwrap();
    let mut stable_engine = stable_query::Engine::prepare(
        &c,
        &Domains::new(),
        &keys(&c),
        stable,
        &Limits::default(),
        stable_query::QueryLimits::default(),
    )
    .unwrap();
    let q = stable_query::Query {
        pins: vec![(atom(p), true)],
        ..Default::default()
    };
    assert!(matches!(
        stable_engine.models(&q).unwrap(),
        stable_query::Answer::NoModel
    ));
    assert!(matches!(
        prepare(&c, v, &Domains::new()).observation([]).unwrap(),
        ObservationOutcome::WholeProgram(Interpretations::Multiple { .. })
    ));
    assert!(matches!(
        Engine::prepare(
            &c,
            &Domains::new(),
            &keys(&c),
            stable,
            &Limits::default(),
            QueryLimits::default()
        ),
        Err(CheckError::InvalidRequest(_))
    ));
    assert!(matches!(
        stable_query::Engine::prepare(
            &c,
            &Domains::new(),
            &keys(&c),
            v,
            &Limits::default(),
            stable_query::QueryLimits::default()
        ),
        Err(CheckError::InvalidRequest(_))
    ));
}

#[test]
fn world_queries_accept_only_legal_input_pins_and_preserve_empty_definitions() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "input", true);
    let h = rel(&mut c, "missing_hypothesis", false);
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    for value in [false, true] {
        let q = WorldQuery {
            pins: vec![(atom(i), value)],
            ..Default::default()
        };
        let WorldAnswer::World(w) = e.worlds(&q).unwrap() else {
            panic!()
        };
        assert_eq!(w.present.contains(&atom(i)), value);
        assert!(matches!(
            e.observation(w.present).unwrap(),
            ObservationOutcome::Rejected { .. }
        ));
        let q = WorldQuery {
            pins: vec![(atom(h), value)],
            ..Default::default()
        };
        assert!(matches!(e.worlds(&q), Err(CheckError::InvalidRequest(_))));
    }
}

#[test]
fn cutoffs_never_become_rejection_or_erase_completed_classification() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[]);
    let v = verification(&mut c, Some(h), &[]);
    for cap in [0, 1, 2, 3, 4] {
        let mut e = prepare(&c, v, &Domains::new());
        e.config.max_solves = cap;
        let r = e.observation([]).unwrap();
        match cap {
            0 | 1 => assert!(matches!(
                r,
                ObservationOutcome::Inconclusive { example: None, .. }
            )),
            2 => assert!(matches!(
                r,
                ObservationOutcome::Inconclusive {
                    example: Some(_),
                    ..
                }
            )),
            3 => assert!(matches!(
                r,
                ObservationOutcome::Accepted {
                    processing: Interpretations::Inconclusive { example: None, .. },
                    ..
                }
            )),
            4 => assert!(matches!(
                r,
                ObservationOutcome::Accepted {
                    processing: Interpretations::Inconclusive {
                        example: Some(_),
                        ..
                    },
                    ..
                }
            )),
            _ => unreachable!(),
        }
        e.config = QueryLimits::default();
        assert!(matches!(
            e.observation([]).unwrap(),
            ObservationOutcome::Accepted { .. }
        ));
    }
    for limits in [
        Limits {
            max_rules: 0,
            ..Default::default()
        },
        Limits {
            max_work: 0,
            ..Default::default()
        },
        Limits {
            timeout: Duration::ZERO,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            Engine::prepare(
                &c,
                &Domains::new(),
                &keys(&c),
                v,
                &limits,
                QueryLimits::default()
            )
            .unwrap(),
            Preparation::Inconclusive(_)
        ));
    }
    let e = prepare(&c, v, &Domains::new());
    e.limits.cancellation.cancel();
    assert!(matches!(e.observation([]), Err(CheckError::Cancelled)));
}

// Independent oracle: evaluate equations directly from the authored zero-arity
// IR. It does not read the ground program, SAT clauses or their auxiliaries.
fn oracle(
    c: &Corpus,
    roots: &[RelationId],
    input: RelationId,
    value: bool,
    require: Option<RelationId>,
) -> Vec<BTreeSet<RelationId>> {
    // Independent positive-support gfp: negation does not prune scope edges.
    let mut possible: BTreeSet<_> = c.relations().map(|r| r.id).collect();
    loop {
        let next: BTreeSet<_> = c
            .relations()
            .filter(|r| {
                r.role == RelationRole::Input
                    || c.rules()
                        .filter(|rule| rule.head.relation() == r.id)
                        .any(|rule| {
                            rule.body.iter().all(|l| {
                                !matches!(l, Literal::Positive(_))
                                    || possible.contains(&l.atom().relation())
                            })
                        })
            })
            .map(|r| r.id)
            .collect();
        if next == possible {
            break;
        }
        possible = next;
    }
    let live = |r: &denotate_ir::Rule| {
        r.body
            .iter()
            .all(|l| !matches!(l, Literal::Positive(_)) || possible.contains(&l.atom().relation()))
    };
    let mut scope: BTreeSet<_> = roots.iter().copied().collect();
    loop {
        let n = scope.len();
        for r in c.rules().filter(|r| live(r)) {
            if scope.contains(&r.head.relation()) {
                scope.extend(r.body.iter().map(|l| l.atom().relation()));
            }
        }
        if scope.len() == n {
            break;
        }
    }
    let derived: Vec<_> = scope.iter().copied().filter(|r| *r != input).collect();
    (0..1usize << derived.len())
        .filter_map(|bits| {
            let mut m: BTreeSet<_> = derived
                .iter()
                .enumerate()
                .filter_map(|(i, r)| ((bits & (1 << i)) != 0).then_some(*r))
                .collect();
            if value {
                m.insert(input);
            }
            if require.is_some_and(|h| !m.contains(&h)) {
                return None;
            }
            let valid = derived.iter().all(|head| {
                m.contains(head)
                    == c.rules().filter(|r| r.head.relation() == *head).any(|r| {
                        r.body.iter().all(|l| {
                            m.contains(&l.atom().relation()) == matches!(l, Literal::Positive(_))
                        })
                    })
            });
            valid.then_some(m)
        })
        .collect()
}

#[test]
fn exhaustive_authored_equations_agree_in_both_modes() {
    // All pairs of two one-literal definitions over two derived atoms and one
    // input. Include positive recursion, negation cycles and input dependence.
    for left in 0..6 {
        for right in 0..6 {
            let mut c = Corpus::new();
            let input = rel(&mut c, "input", true);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            let atoms = [input, p, q];
            rule(&mut c, p, &[(atoms[left / 2], left % 2 != 0)]);
            rule(&mut c, q, &[(atoms[right / 2], right % 2 != 0)]);
            // Duplicate bodies exercise auxiliaries without creating meanings.
            rule(&mut c, q, &[(atoms[right / 2], right % 2 != 0)]);
            for h in [None, Some(p), Some(q), Some(input)] {
                let v = verification(&mut c, h, &[]);
                let e = prepare(&c, v, &Domains::new());
                for value in [false, true] {
                    let present = if value { vec![atom(input)] } else { vec![] };
                    let observed = e.observation(present).unwrap();
                    let roots = h.map_or(vec![p, q], |h| vec![h]);
                    let meanings = oracle(&c, &roots, input, value, h);
                    let expected = meanings.len().min(2);
                    match observed {
                        ObservationOutcome::WholeProgram(m) => assert_eq!(size(&m), expected),
                        ObservationOutcome::Rejected { without_hypothesis } => {
                            assert_eq!(expected, 0);
                            assert!(!oracle(&c, &roots, input, value, None).is_empty());
                            assert_eq!(without_hypothesis.value(&atom(h.unwrap())), Some(false));
                        }
                        ObservationOutcome::ClassificationNoMeaning => {
                            assert_eq!(expected, 0);
                            assert!(oracle(&c, &roots, input, value, None).is_empty());
                        }
                        ObservationOutcome::Ambiguous { .. } => assert_eq!(expected, 2),
                        ObservationOutcome::Accepted {
                            classification,
                            processing,
                        } => {
                            assert_eq!(expected, 1);
                            let all = oracle(&c, &[p, q], input, value, h);
                            let extensions = all
                                .iter()
                                .filter(|m| {
                                    [p, q].iter().all(|r| {
                                        classification
                                            .value(&atom(*r))
                                            .is_none_or(|v| v == m.contains(r))
                                    })
                                })
                                .count();
                            assert_eq!(size(&processing), extensions.min(2));
                        }
                        other => panic!("{left}/{right}/{h:?}/{value}: {other:?}"),
                    }
                }
            }
        }
    }
}

#[test]
fn common_preparation_is_charged_once_for_several_providers() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let z = c.declare_constant("z", s).unwrap();
    let facts = c
        .declare_relation("facts", RelationRole::Derived, [Parameter::new("x", s)])
        .unwrap();
    let head = c.atom(facts, [Term::Constant(a)]).unwrap();
    c.add_rule(head, []).unwrap();
    let mut inputs = Vec::new();
    for i in 0..4 {
        let provider = rel(&mut c, &format!("provider{i}"), false);
        rule(&mut c, provider, &[]);
        let input = rel(&mut c, &format!("input{i}"), true);
        c.restrict_input(input, provider).unwrap();
        let used = rel(&mut c, &format!("used{i}"), false);
        rule(&mut c, used, &[(input, false)]);
        inputs.push(input);
    }
    let v = verification(&mut c, None, &[]);
    // Unsorted caller domains remain valid; sharing must use the normalized set.
    let domains = Domains::from([(s, vec![z, a])]);
    let limits = Limits::default();
    let mut reference = Budget::new(&limits);
    let validated = crate::ground::CompletionDomains::new(&c, &domains, &mut reference).unwrap();
    let validation_work = reference.used();
    crate::ground::OriginalDependencies::from_validated(&c, &validated, &mut reference).unwrap();
    let original_work = reference.used() - validation_work;
    for _ in 0..2 {
        let sink = crate::CompletionSizes::default();
        let observed = Limits {
            completion_sizes: Some(sink.clone()),
            ..limits.clone()
        };
        let Preparation::Ready(e) =
            Engine::prepare(&c, &domains, &keys(&c), v, &observed, Default::default()).unwrap()
        else {
            panic!()
        };
        assert!(matches!(
            e.observation(inputs.iter().map(|i| atom(*i))).unwrap(),
            ObservationOutcome::WholeProgram(Interpretations::Unique(_))
        ));
        let stats = sink.snapshot();
        let work = stats.preparation_work.unwrap();
        // Compare to one independently built common value, never a numeric work golden.
        assert_eq!(work.by_stage["domains"], validation_work);
        assert_eq!(work.by_phase["domains"], validation_work);
        assert_eq!(work.by_stage["original-dependencies"], original_work);
        assert_eq!(
            stats
                .preparations
                .iter()
                .filter(|p| p.static_provider)
                .count(),
            inputs.len()
        );
        assert!(
            stats
                .preparations
                .iter()
                .all(|p| p.work_by_stage.get("domains").copied().unwrap_or(0) == 0)
        );
    }
    for invalid in [vec![a, a], vec![z]] {
        let result = Engine::prepare(
            &c,
            &Domains::from([(s, invalid)]),
            &keys(&c),
            v,
            &limits,
            Default::default(),
        );
        assert!(matches!(
            result,
            Err(CheckError::InvalidDomain { .. } | CheckError::ConstantOutsideDomain(_))
        ));
    }
}
