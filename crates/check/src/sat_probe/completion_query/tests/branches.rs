use super::*;
fn domains(c: &Corpus) -> Domains {
    c.sorts()
        .map(|s| {
            (
                s.id,
                c.constants()
                    .filter(|a| a.sort == s.id)
                    .map(|a| a.id)
                    .collect(),
            )
        })
        .collect()
}

fn tags(c: &mut Corpus, selected: bool) -> (RelationId, Vec<ConstantId>, Vec<AssumptionId>) {
    let s = c.declare_sort("Tag").unwrap();
    let values = ["a", "b"]
        .map(|n| c.declare_constant(n, s).unwrap())
        .to_vec();
    let input = c
        .declare_relation("tag", RelationRole::Input, [Parameter::new("v", s)])
        .unwrap();
    let assumptions = if selected {
        vec![
            c.assume_in(
                Namespace::default(),
                "one",
                Cardinality::ExactlyOne,
                input,
                [],
            )
            .unwrap(),
        ]
    } else {
        c.constrain_input(input, Cardinality::ExactlyOne, [])
            .unwrap();
        vec![]
    };
    (input, values, assumptions)
}
fn guarded(
    c: &mut Corpus,
    h: RelationId,
    tag: RelationId,
    value: ConstantId,
    body: &[(RelationId, bool)],
) {
    let head = c.atom(h, []).unwrap();
    let mut literals = vec![Literal::Positive(
        c.atom(tag, [Term::Constant(value)]).unwrap(),
    )];
    for (r, negative) in body {
        let a = c.atom(*r, []).unwrap();
        literals.push(if *negative {
            Literal::Negative(a)
        } else {
            Literal::Positive(a)
        });
    }
    c.add_rule(head, literals).unwrap();
}
fn opts() -> CheckOptions {
    CheckOptions {
        split_depth: 3,
        split_branches: 16,
        ..Default::default()
    }
}

fn partition_report(c: &Corpus, e: &Engine, options: &CheckOptions) -> BranchReport {
    let expected = e.check_enumerated(&keys(c), &Default::default()).unwrap();
    let mut e = e.clone();
    e.branches = Some(Arc::new(std::sync::Mutex::new(BranchReport::default())));
    for classification in [false, true] {
        if classification && e.classification.is_none() {
            continue;
        }
        for existence in [false, true] {
            let got = super::super::symbolic::branches::test_partition(
                &e,
                classification,
                existence,
                options,
            )
            .unwrap();
            let expected_failure = match (classification, existence) {
                (true, true) => expected
                    .classification
                    .as_ref()
                    .unwrap()
                    .no_meaning
                    .exists(),
                (true, false) => expected.classification.as_ref().unwrap().ambiguous.exists(),
                (false, true) => expected.meaning.no_meaning.exists(),
                (false, false) => expected.meaning.ambiguous.exists(),
            };
            assert_eq!(got.exists(), expected_failure);
            assert!(!matches!(
                got,
                Search::Inconclusive(_) | Search::NotAnalysed
            ));
        }
    }
    let report = e.branches.as_ref().unwrap().lock().unwrap().clone();
    report
}

#[test]
fn fitting_input_branches_cut_an_odd_loop_for_declared_and_selected_groups() {
    for selected in [false, true] {
        for hypothesis in [false, true] {
            let mut c = Corpus::new();
            let (tag, v, a) = tags(&mut c, selected);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            guarded(&mut c, p, tag, v[0], &[]);
            guarded(&mut c, p, tag, v[1], &[(q, false)]);
            guarded(&mut c, q, tag, v[1], &[]);
            guarded(&mut c, q, tag, v[0], &[(p, true)]);
            let verification = verification(&mut c, hypothesis.then_some(p), &a);
            let e = prepare(&c, verification, &domains(&c));
            let reference = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
            for prune in [false, true] {
                let options = CheckOptions { prune, ..opts() };
                let got = e.check(&keys(&c), &options).unwrap();
                super::scale::same_report(&got, &reference);
                assert!(!got.is_incomplete());
                assert!(!got.has_failures());
                let partitions = partition_report(&c, &e, &options);
                assert!(partitions.splits > 0);
                assert!(
                    partitions
                        .records
                        .iter()
                        .any(|r| r.depth > 0 && r.state == "proved")
                );
                super::scale::same_report(&got, &e.check(&keys(&c), &options).unwrap());
                super::scale::same_report(
                    &got,
                    &prepare(&c, verification, &domains(&c))
                        .check(&keys(&c), &options)
                        .unwrap(),
                );
            }
        }
    }
}

#[test]
fn branch_queries_agree_with_exhaustive_signed_equations_including_real_failures() {
    for left in 0..4 {
        for right in 0..4 {
            for hypothesis in [false, true] {
                let mut c = Corpus::new();
                let (tag, v, a) = tags(&mut c, false);
                let p = rel(&mut c, "p", false);
                let q = rel(&mut c, "q", false);
                let rs = [p, q];
                guarded(&mut c, p, tag, v[0], &[]);
                guarded(&mut c, p, tag, v[1], &[(rs[left / 2], left % 2 != 0)]);
                guarded(&mut c, q, tag, v[1], &[]);
                guarded(&mut c, q, tag, v[0], &[(rs[right / 2], right % 2 != 0)]);
                let verification = verification(&mut c, hypothesis.then_some(q), &a);
                let e = prepare(&c, verification, &domains(&c));
                let reference = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
                for depth in [1, 3] {
                    let options = CheckOptions {
                        split_depth: depth,
                        ..opts()
                    };
                    super::scale::same_report(&e.check(&keys(&c), &options).unwrap(), &reference);
                    partition_report(&c, &e, &options);
                }
            }
        }
    }
}

#[test]
fn branch_limits_fall_back_without_claiming_totality_or_uniqueness() {
    let mut c = Corpus::new();
    let (tag, v, a) = tags(&mut c, false);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    guarded(&mut c, p, tag, v[0], &[(p, true)]);
    guarded(&mut c, q, tag, v[1], &[(q, false)]);
    let verification = verification(&mut c, None, &a);
    let e = prepare(&c, verification, &domains(&c));
    let reference = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
    assert!(reference.meaning.no_meaning.exists());
    assert!(reference.meaning.ambiguous.exists());
    for cap in [0, 1, 2] {
        let got = e
            .check(
                &keys(&c),
                &CheckOptions {
                    split_branches: cap,
                    ..opts()
                },
            )
            .unwrap();
        super::scale::same_report(&got, &reference);
        if cap < 2 {
            assert_eq!(got.branches.splits, 0);
        }
    }
    let mut limited = e.clone();
    limited.limits.max_work = 1;
    let got = limited.check(&keys(&c), &opts()).unwrap();
    assert!(got.is_incomplete());
}

#[test]
fn unselected_exactly_one_never_discards_absent_or_multi_value_worlds() {
    let mut c = Corpus::new();
    let (tag, v, _) = tags(&mut c, true);
    let p = rel(&mut c, "p", false);
    guarded(&mut c, p, tag, v[0], &[]);
    guarded(&mut c, p, tag, v[1], &[(p, true)]);
    let verification = verification(&mut c, None, &[]);
    let e = prepare(&c, verification, &domains(&c));
    let got = e.check(&keys(&c), &opts()).unwrap();
    super::scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(
        got.branches
            .records
            .iter()
            .filter(|r| r.state == "split")
            .all(|r| r.split_kind == "binary")
    );
    assert!(got.meaning.no_meaning.exists());
}

#[test]
fn nested_partitions_respect_depth_and_preserve_residual_search() {
    let mut c = Corpus::new();
    let (tag, v, a) = tags(&mut c, false);
    let s = c.declare_sort("Other").unwrap();
    let x = c.declare_constant("x", s).unwrap();
    let y = c.declare_constant("y", s).unwrap();
    let other = c
        .declare_relation("other", RelationRole::Input, [Parameter::new("v", s)])
        .unwrap();
    c.constrain_input(other, Cardinality::ExactlyOne, [])
        .unwrap();
    let mut heads = vec![];
    for (i, input, values) in [(0, tag, v.clone()), (1, other, vec![x, y])] {
        let p = rel(&mut c, &format!("p{i}"), false);
        let q = rel(&mut c, &format!("q{i}"), false);
        heads.push(p);
        guarded(&mut c, p, input, values[0], &[]);
        guarded(&mut c, p, input, values[1], &[(q, false)]);
        guarded(&mut c, q, input, values[1], &[]);
        guarded(&mut c, q, input, values[0], &[(p, true)]);
    }
    // One parent component, with a surviving subloop after a tag cut. Independent
    // loops now go directly to residual checking instead of deeper exploration.
    guarded(&mut c, heads[0], tag, v[0], &[(heads[1], false)]);
    guarded(&mut c, heads[1], tag, v[0], &[(heads[0], false)]);
    let verification = verification(&mut c, None, &a);
    let e = prepare(&c, verification, &domains(&c));
    let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
    for depth in [1, 2] {
        let got = e
            .check(
                &keys(&c),
                &CheckOptions {
                    split_depth: depth,
                    ..opts()
                },
            )
            .unwrap();
        super::scale::same_report(&got, &expected);
        let partitions = partition_report(
            &c,
            &e,
            &CheckOptions {
                split_depth: depth,
                ..opts()
            },
        );
        assert!(partitions.records.iter().all(|r| r.depth <= depth));
        assert!(
            partitions
                .records
                .iter()
                .any(|r| r.depth == depth && r.state == "proved")
        );
    }
}

#[test]
fn a_confirmed_branch_failure_survives_another_branch_cutoff() {
    let mut c = Corpus::new();
    let (tag, v, a) = tags(&mut c, false);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    guarded(&mut c, p, tag, v[0], &[]);
    guarded(&mut c, p, tag, v[1], &[(q, false)]);
    guarded(&mut c, q, tag, v[1], &[]);
    guarded(&mut c, q, tag, v[0], &[(p, true)]);
    let verification = verification(&mut c, None, &a);
    let e = prepare(&c, verification, &domains(&c));
    let input = GroundAtom::new(tag, [v[0]]);
    let index = e.program.atom_index[&input];
    let result =
        super::super::symbolic::branches::partition(&e, false, true, &opts(), 1, |branch, _| {
            assert!(Arc::ptr_eq(&e.program, &branch.program));
            assert!(branch.pruning.is_none());
            assert!(branch.config.max_solves <= e.config.max_solves);
            if branch.cone.fixed[index] == Some(true) {
                Ok(Search::Inconclusive(
                    inconclusive(CheckError::limit("test branch", "work", 1, Some(2))).unwrap(),
                ))
            } else {
                Ok(Search::Exists("confirmed"))
            }
        })
        .unwrap();
    assert!(matches!(result, Search::Exists("confirmed")));
}

#[test]
fn branches_keep_projected_helpers_free_and_respect_world_restrictions() {
    for restrict in [false, true] {
        let mut c = Corpus::new();
        let (tag, v, _) = tags(&mut c, false);
        let p = rel(&mut c, "helper", false);
        let q = rel(&mut c, "decision", false);
        let excluded = rel(&mut c, "excluded", false);
        guarded(&mut c, p, tag, v[0], &[(p, false)]);
        guarded(&mut c, q, tag, v[1], &[]);
        guarded(&mut c, q, tag, v[0], &[]);
        guarded(&mut c, q, tag, v[0], &[(p, false)]);
        guarded(&mut c, excluded, tag, v[1], &[]);
        let a = c
            .assume_empty_in(Namespace::default(), "only_a", excluded)
            .unwrap();
        let o = c.empty("no_helper", p, "").unwrap();
        let v = c
            .verification_with_options_in(
                Namespace::default(),
                "checks",
                if restrict { vec![a] } else { vec![] },
                [o],
                [],
                VerificationOptions {
                    semantics: Semantics::Completion,
                    hypothesis: None,
                    decisions: Some(BTreeSet::from([q])),
                },
            )
            .unwrap();
        let e = prepare(&c, v, &domains(&c));
        let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
        let got = e.check(&keys(&c), &opts()).unwrap();
        super::scale::same_report(&got, &expected);
        assert!(!got.meaning.ambiguous.exists());
        assert!(partition_report(&c, &e, &opts()).splits > 0);
        assert!(got.obligations[&o].failed());
    }
}
