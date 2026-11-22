use super::*;
#[test]
fn restriction_truth_matches_exhaustive_completion_cones_for_all_cardinalities() {
    for left in 0..6 {
        for right in 0..6 {
            for kind in [
                Cardinality::Empty,
                Cardinality::AtMostOne,
                Cardinality::AtLeastOne,
                Cardinality::ExactlyOne,
            ] {
                let mut c = Corpus::new();
                let input = rel(&mut c, "i", true);
                let p = rel(&mut c, "p", false);
                let q = rel(&mut c, "q", false);
                let rs = [input, p, q];
                rule(&mut c, p, &[(rs[left / 2], left % 2 != 0)]);
                rule(&mut c, q, &[(rs[right / 2], right % 2 != 0)]);
                let s = c.declare_sort("S").unwrap();
                let a = c.declare_constant("a", s).unwrap();
                let z = c.declare_constant("b", s).unwrap();
                let r = c
                    .declare_relation("r", RelationRole::Derived, [Parameter::new("x", s)])
                    .unwrap();
                for (constant, source) in [(a, p), (z, q)] {
                    let head = c.atom(r, [Term::Constant(constant)]).unwrap();
                    let body = c.atom(source, []).unwrap();
                    c.add_rule(head, [Literal::Positive(body)]).unwrap();
                }
                let a = c.assume_in(Namespace::default(), "a", kind, r, []).unwrap();
                let v = verification(&mut c, None, &[a]);
                let e = prepare(&c, v, &Domains::from([(s, vec![a_constant(&c, "a"), z])]));
                let mut ambiguous = false;
                let mut missing = false;
                for value in [false, true] {
                    let models = oracle(&c, &[p, q], input, value, None);
                    let truths: BTreeSet<_> = models
                        .iter()
                        .map(|m| {
                            let count = usize::from(m.contains(&p)) + usize::from(m.contains(&q));
                            match kind {
                                Cardinality::Empty => count == 0,
                                Cardinality::AtMostOne => count <= 1,
                                Cardinality::AtLeastOne => count >= 1,
                                Cardinality::ExactlyOne => count == 1,
                            }
                        })
                        .collect();
                    ambiguous |= truths.len() > 1;
                    missing |= models.is_empty();
                    let observed = e
                        .observation(if value { vec![atom(input)] } else { vec![] })
                        .unwrap();
                    match truths.len() {
                        0 | 2 => assert!(
                            matches!(observed, ObservationOutcome::UndeterminedAssumptions(_)),
                            "{left} {right} {kind:?} {value}: {observed:?}"
                        ),
                        1 if truths.contains(&false) => {
                            assert!(matches!(observed, ObservationOutcome::NotPermitted))
                        }
                        1 => assert!(matches!(
                            observed,
                            ObservationOutcome::WholeProgram(
                                Interpretations::Unique(_) | Interpretations::Multiple { .. }
                            )
                        )),
                        _ => unreachable!(),
                    }
                }
                let analysis = e.assumption_analysis(&CheckOptions::default()).unwrap();
                assert_eq!(
                    analysis[0].ambiguous.exists(),
                    ambiguous,
                    "{left} {right} {kind:?}"
                );
                assert_eq!(
                    analysis[0].no_meaning.exists(),
                    missing,
                    "{left} {right} {kind:?}"
                );
            }
        }
    }
}
fn a_constant(c: &Corpus, name: &str) -> ConstantId {
    c.constants().find(|a| a.name == name).unwrap().id
}
#[test]
fn contract_limits_are_unknown_and_cancellation_still_stops() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(p, true)]);
    let a = c.assume_empty_in(Namespace::default(), "a", p).unwrap();
    let v = verification(&mut c, None, &[a]);
    let mut e = prepare(&c, v, &Domains::new());
    e.config.max_solves = 0;
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.is_incomplete());
    assert!(!r.assumptions[0].failed());
    assert!(matches!(
        r.assumptions[0].ambiguous,
        Search::Inconclusive(_)
    ));
    assert!(matches!(
        r.assumptions[0].no_meaning,
        Search::Inconclusive(_)
    ));
    e.limits.cancellation.cancel();
    assert!(matches!(
        e.check(&keys(&c), &CheckOptions::default()),
        Err(CheckError::Cancelled)
    ));
}
