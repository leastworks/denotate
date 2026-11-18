use crate::Session;
use denotate_check::*;
use denotate_ir_text::{ProgramMembership, SourceFile, load, presentation};

#[test]
fn input_orders_share_only_compatible_contexts_and_agree_fresh_cold_warm() {
    let ordinary = "input a(); input b(); relation bad(); bad():-a(),!b();
assumption valid:empty(bad); obligation no_bad:empty(bad);
verification checks{assumptions:[valid];obligations:[no_bad];}
verification again{assumptions:[valid];obligations:[no_bad];}
verification unrestricted{assumptions:[];obligations:[no_bad];}";
    let specialized = "sort S; const a,b,excluded:S;
relation candidates(s:S); candidates(a); candidates(b);
input present(s:S) within candidates;
relation guarded(s:S); guarded(a); relation gives(s:S); gives(b);
relation holds(s:S); relation supplied(s:S);
holds(X):-present(X); holds(X):-guarded(X),!supplied(X);
supplied(X):-gives(X),!holds(X);
relation bad(); bad():-!holds(a); bad():-present(a);
assumption valid:empty(bad); obligation no_bad:empty(bad);
verification checks{assumptions:[valid];obligations:[no_bad];}
verification again{assumptions:[valid];obligations:[no_bad];}
verification unrestricted{assumptions:[];obligations:[no_bad];}";
    let overlapping = "sort S; const a,b:S; input cell(row:S,col:S);
assumption rows:at_most_one(cell,group_by:(row));
assumption cols:at_most_one(cell,group_by:(col));
input enabled(); input blocked();
relation selected(row:S,col:S); selected(R,C):-cell(R,C),enabled(),!blocked();
obligation unique:at_most_one(selected,group_by:());
verification checks{assumptions:[rows,cols];obligations:[unique];}
verification again{assumptions:[rows,cols];obligations:[unique];}";
    let disjoint = overlapping.replace("assumptions:[rows,cols]", "assumptions:[rows]");
    for (fixture, text) in [ordinary, specialized, overlapping, disjoint.as_str()]
        .into_iter()
        .enumerate()
    {
        let source = SourceFile::new("file:///orders.den", 0, text);
        let p = load(
            &ProgramMembership::single("root", [source.uri.clone()]),
            &[source],
        )
        .unwrap();
        let l = Limits::default();
        let ops = (&l).into();
        let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &l).unwrap();
        let mut warm = Session::default();
        let mut reference = std::collections::BTreeMap::new();
        for order in [
            InputOrder::Key,
            InputOrder::ReverseKey,
            InputOrder::Structural,
            InputOrder::Key,
            InputOrder::Structural,
        ] {
            for (verification, mut request) in p.verification_requests(&l).unwrap() {
                request.backend = BackendIdentity::bdd_with_order(order);
                let run = |mut session: Option<&mut Session>, shared: bool| {
                    let prepared = match session.as_deref_mut() {
                        Some(session) => session
                            .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
                            .unwrap(),
                        None if shared => request
                            .prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None)
                            .unwrap(),
                        None => request.prepare(&p.corpus, &p.keys, &ops).unwrap(),
                    };
                    let RequestPreparation::Complete(prepared) = prepared else {
                        panic!("{fixture} {order:?}")
                    };
                    assert_eq!(prepared.program().input_order_report().requested, order);
                    if fixture == 1 {
                        assert_eq!(prepared.program().input_atoms().count(), 2);
                    }
                    let actual = prepared
                        .program()
                        .ordered_input_atoms()
                        .map(|a| AtomKey::from_atom(&p.keys, a).unwrap())
                        .collect::<Vec<_>>();
                    let mut sorted = actual.clone();
                    sorted.sort();
                    if order == InputOrder::Key {
                        assert_eq!(actual, sorted);
                    }
                    if order == InputOrder::ReverseKey {
                        sorted.reverse();
                        assert_eq!(actual, sorted);
                    }
                    if fixture < 2 {
                        let inputs = prepared
                            .program()
                            .input_atoms()
                            .cloned()
                            .collect::<Vec<_>>();
                        let context = prepared.program().condition_context(&l).unwrap();
                        for world in denotate_check::test_support::rewrites::subsets(&inputs) {
                            let expected = if request.constraints.is_empty() {
                                true
                            } else if fixture == 0 {
                                let has = |name: &str| {
                                    world.iter().any(|a| {
                                        p.corpus.relation(a.relation).unwrap().name == name
                                    })
                                };
                                !has("a") || has("b")
                            } else {
                                // Fixed specialization makes holds(a) always true;
                                // the selected bad() restriction forbids present(a).
                                !world
                                    .iter()
                                    .any(|a| p.corpus.constant(a.arguments[0]).unwrap().name == "a")
                            };
                            let accepted = context
                                .evaluate(&context.true_condition(), world, &l)
                                .is_ok();
                            assert_eq!(accepted, expected, "fixture {fixture}, order {order:?}");
                        }
                    }
                    if fixture >= 2 {
                        let inputs = prepared
                            .program()
                            .input_atoms()
                            .cloned()
                            .collect::<Vec<_>>();
                        let mut permitted = 0;
                        for world in denotate_check::test_support::rewrites::subsets(&inputs) {
                            let mut rows = std::collections::BTreeSet::new();
                            let mut cols = std::collections::BTreeSet::new();
                            let expected = world.iter().all(|a| {
                                a.arguments.is_empty()
                                    || (rows.insert(a.arguments[0])
                                        && (fixture == 3 || cols.insert(a.arguments[1])))
                            });
                            assert_eq!(prepared.program().evaluate(world, &l).is_ok(), expected);
                            permitted += usize::from(expected);
                        }
                        assert_eq!(permitted, if fixture == 2 { 28 } else { 36 });
                    }
                    let prepared = prepared.admit(&ops).unwrap();
                    let result = match session {
                        Some(session) => session.verify(&prepared, &ops).unwrap(),
                        None => prepared.verify_local(&ops).unwrap(),
                    };
                    let LocalCheckOutcome::Complete(result) = result else {
                        panic!()
                    };
                    for q in result.queries.values() {
                        assert_eq!(q.input.backend, request.backend);
                        let set = q
                            .input
                            .input_order
                            .iter()
                            .collect::<std::collections::BTreeSet<_>>();
                        assert_eq!(set.len(), q.input.input_order.len());
                        let filtered = actual
                            .iter()
                            .filter(|a| set.contains(a))
                            .cloned()
                            .collect::<Vec<_>>();
                        assert_eq!(filtered, q.input.input_order);
                    }
                    let status = presentation::present(&p, &result.checked).unwrap().status;
                    (result.checked.results.value, status["state"].clone())
                };
                let fresh = run(None, false);
                assert_eq!(fresh, run(None, true));
                assert_eq!(fresh, run(Some(&mut Session::default()), true));
                assert_eq!(fresh, run(Some(&mut warm), true));
                assert_eq!(fresh, run(Some(&mut warm), true));
                if let Some(expected) = reference.insert(verification.clone(), fresh.1.clone()) {
                    assert_eq!(fresh.1, expected, "{fixture} {order:?} {verification:?}");
                }
            }
        }
    }
}

#[test]
fn ordering_allowances_invalidate_preparation_and_report_before_assumptions() {
    use std::sync::{Arc, Mutex};
    for declared in ["", "at_most_one(group_by:())", "exactly_one(group_by:())"] {
        let text = format!(
            "sort S;const a,b:S; input i(x:S) {}; relation bad();bad():-i(a),i(b); assumption valid:empty(bad);obligation clear:empty(bad);verification checks{{assumptions:[valid];obligations:[clear];}}",
            declared
        );
        let source = SourceFile::new("file:///allowances.den", 0, text);
        let p = load(
            &ProgramMembership::single("root", [source.uri.clone()]),
            &[source],
        )
        .unwrap();
        let mut warm = Session::default();
        for (entries, work, expected) in [
            (0, 4_000_000, InputOrder::Key),
            (1_000_000, 4_000_000, InputOrder::Structural),
            (1_000_000, 0, InputOrder::Key),
            (0, 4_000_000, InputOrder::Key),
        ] {
            let limits = Limits {
                profile: Profile::new(|_| {}),
                max_input_order_entries: entries,
                max_input_order_work: work,
                ..Limits::default()
            };
            let mut request = p.verification_requests(&limits).unwrap().remove(0).1;
            request.backend = BackendIdentity::bdd_with_order(InputOrder::Structural);
            let events = Arc::new(Mutex::new(Vec::new()));
            let send = events.clone();
            limits.profile.observe_conditions(move |e| {
                if matches!(e.observation, ConditionObservation::AssumptionStep { .. }) {
                    send.lock().unwrap().push("assumption");
                }
            });
            let send = events.clone();
            let ops = OperationalLimits {
                progress: CheckingProgress::new(move |e| {
                    if matches!(e.target, Some(CheckingTarget::InputOrder(_))) {
                        send.lock().unwrap().push("order");
                    }
                }),
                ..(&limits).into()
            };
            let run = |session: &mut Session| {
                let RequestPreparation::Complete(prep) =
                    session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
                else {
                    panic!()
                };
                assert_eq!(prep.program().input_order_report().effective, expected);
                if expected == InputOrder::Key {
                    let r = prep.program().input_order_report();
                    assert_eq!(r.fallback_limit, Some(0));
                    assert!(r.fallback_observed.unwrap() > 0);
                }
                let order = prep
                    .program()
                    .ordered_input_atoms()
                    .map(|a| AtomKey::from_atom(&p.keys, a).unwrap())
                    .collect::<Vec<_>>();
                let prep = prep.admit(&ops).unwrap();
                let LocalCheckOutcome::Complete(report) = session.verify(&prep, &ops).unwrap()
                else {
                    panic!()
                };
                (
                    order,
                    presentation::present(&p, &report.checked).unwrap().status,
                )
            };
            let fresh = run(&mut Session::default());
            assert_eq!(fresh, run(&mut warm));
            assert_eq!(fresh, run(&mut warm));
            let e = events.lock().unwrap();
            assert_eq!(e.first(), Some(&"order"));
            assert!(e.contains(&"assumption"));
        }
    }
}

#[test]
fn recursive_worklist_results_agree_in_cold_warm_and_edited_sessions() {
    let mut warm = Session::default();
    for negated in [false, true, false] {
        let text = format!(
            "input x(); input y(); relation a(); relation b(); a():-b(); b():-a(); b():-x(),{}y(); relation bad(); bad():-a(),!x(); obligation clear:empty(bad); verification checks{{assumptions:[];obligations:[clear];}}",
            if negated { "!" } else { "" }
        );
        let source = SourceFile::new("file:///recursive.den", 0, text);
        let p = load(
            &ProgramMembership::single("root", [source.uri.clone()]),
            &[source],
        )
        .unwrap();
        let limits = Limits::default();
        let ops = (&limits).into();
        let (_, request) = p.verification_requests(&limits).unwrap().remove(0);
        let run = |session: &mut Session| {
            let RequestPreparation::Complete(prepared) =
                session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(result) = session.verify(&prepared, &ops).unwrap()
            else {
                panic!()
            };
            result.checked.results.value
        };
        let fresh = run(&mut Session::default());
        assert_eq!(fresh, run(&mut warm));
        assert_eq!(fresh, run(&mut warm));
    }
}
