use denotate_check::*;
use denotate_ir_text::*;

fn load_text(text: &str) -> LoadedProgram {
    let f = SourceFile::new("file:///probe.den", 0, text);
    load(&ProgramMembership::single("root", [f.uri.clone()]), &[f]).unwrap()
}

#[test]
fn component_probes_follow_three_successively_settled_providers() {
    let mut text = String::new();
    for i in 0..3 {
        if i == 0 {
            text.push_str("input perishable_0();");
        } else {
            text.push_str(&format!(
                "relation perishable_{i}();perishable_{i}():-cleared_{}();",
                i - 1
            ));
        }
        text.push_str(&format!(
            "
input docked_{i}();input priority_{i}();
relation booked_{i}();booked_{i}():-perishable_{i}(),cleared_{i}();
relation fails_{i}();fails_{i}():-docked_{i}(),!booked_{i}();
relation claim_{i}();claim_{i}():-!perishable_{i}(),!fails_{i}();
relation inspected_{i}();inspected_{i}():-perishable_{i}();inspected_{i}():-claim_{i}();
relation held_{i}();held_{i}():-priority_{i}(),inspected_{i}();
relation cleared_{i}();cleared_{i}():-docked_{i}(),!held_{i}();"
        ));
    }
    text.push_str("verification v{assumptions:[];obligations:[];}");
    let p = load_text(&text);
    let l = Limits::default();
    let ops = (&l).into();
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let prepare = || {
        let RequestPreparation::Complete(raw) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        raw
    };
    let ordinary = prepare().admit(&ops).unwrap();
    assert!(ordinary.program().is_admitted());
    let events = std::cell::RefCell::new(Vec::new());
    let observer = |e: SatProbeEvent<'_>| {
        if let Some(r) = e.report {
            let representative = &e.program.component(e.component).unwrap().atoms[0];
            let name = p
                .corpus
                .relation(representative.relation)
                .unwrap()
                .name
                .clone();
            events.borrow_mut().push((name, e.snapshot, r.clone()));
        }
    };
    let admitted = prepare()
        .admit_with_probes(
            &ops,
            None,
            None,
            Some((Default::default(), &observer)),
            None,
        )
        .unwrap();
    assert_eq!(admitted.receipts(), ordinary.receipts());
    assert!(admitted.program().is_admitted());
    let events = events.into_inner();
    let mut answered = Vec::new();
    for (name, snapshot, r) in &events {
        if r.answer == SatProbeAnswer::Unknown {
            assert!(r.reason.as_deref().unwrap().contains("upstream unresolved"));
        } else {
            assert_eq!(r.answer, SatProbeAnswer::Unsat);
            assert_eq!(
                r.existence.as_ref().unwrap().answer,
                SatExistenceAnswer::EveryWorld
            );
            let stage = name.chars().last().unwrap().to_digit(10).unwrap();
            if !answered.iter().any(|(s, _)| *s == stage) {
                answered.push((stage, *snapshot));
            }
        }
    }
    assert_eq!(
        answered.iter().map(|(s, _)| *s).collect::<Vec<_>>(),
        [0, 1, 2],
        "{events:?}"
    );
    assert!(answered.windows(2).all(|w| w[0].1 < w[1].1));
    assert!(
        events
            .iter()
            .any(|(_, _, r)| r.answer == SatProbeAnswer::Unknown)
    );
}

#[test]
fn unresolved_upstream_is_unknown_and_probe_results_are_not_cached() {
    let p = load_text(
        "input x();relation a();relation b();a():-x(),!b();b():-x(),!a();relation c();relation d();c():-a(),!d();d():-!c();verification v{assumptions:[];obligations:[];}",
    );
    let l = Limits::default();
    let ops = (&l).into();
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let mut session = denotate_check_session::Session::default();
    let events = std::cell::RefCell::new(Vec::new());
    let observer = |e: SatProbeEvent<'_>| {
        if let Some(r) = e.report {
            events.borrow_mut().push(r.clone());
        }
    };
    let mut outcomes = None;
    for _ in 0..2 {
        // cold/warm preparation; shared admission within each run
        let fixed = session
            .prepare_fixed(&p.corpus, &p.keys, &p.domains, &l)
            .unwrap();
        let mut receipts = None;
        for reused in [false, true] {
            events.borrow_mut().clear();
            let RequestPreparation::Complete(raw) = session
                .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
                .unwrap()
            else {
                panic!()
            };
            let admitted = raw
                .admit_with_probes(
                    &ops,
                    None,
                    None,
                    Some((Default::default(), &observer)),
                    None,
                )
                .unwrap();
            assert!(!admitted.program().is_admitted());
            if reused {
                assert!(
                    events.borrow().is_empty(),
                    "admission reuse must not re-run diagnostics"
                );
                assert_eq!(admitted.receipts(), receipts.as_ref().unwrap());
            } else {
                assert!(
                    events
                        .borrow()
                        .iter()
                        .any(|r| r.answer == SatProbeAnswer::Sat)
                );
                assert!(
                    events
                        .borrow()
                        .iter()
                        .any(|r| r.answer == SatProbeAnswer::Unknown
                            && r.reason.as_deref().unwrap().contains("upstream unresolved"))
                );
                receipts = Some(admitted.receipts().clone());
            }
            let LocalCheckOutcome::Complete(report) = session.verify(&admitted, &ops).unwrap()
            else {
                panic!()
            };
            if let Some(expected) = &outcomes {
                assert_eq!(&report.checked.results.value, expected);
            } else {
                outcomes = Some(report.checked.results.value);
            }
        }
    }
}

#[test]
fn component_probe_exhaustion_and_cancellation_do_not_become_checker_answers() {
    let p = load_text(include_str!("fixtures/guarded-settlement.den"));
    let l = Limits::default();
    let ops: OperationalLimits = (&l).into();
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let prepare = || {
        let RequestPreparation::Complete(raw) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        raw
    };
    let ordinary = prepare().admit(&ops).unwrap();
    let events = std::cell::RefCell::new(Vec::new());
    let observer = |e: SatProbeEvent<'_>| {
        if let Some(r) = e.report {
            events.borrow_mut().push(r.clone());
        }
    };
    let admitted = prepare()
        .admit_with_probes(
            &ops,
            None,
            None,
            Some((
                SatProbeLimits {
                    timeout: std::time::Duration::ZERO,
                    ..Default::default()
                },
                &observer,
            )),
            None,
        )
        .unwrap();
    assert!(admitted.program().is_admitted());
    assert_eq!(admitted.receipts(), ordinary.receipts());
    assert!(!events.borrow().is_empty());
    assert!(
        events
            .borrow()
            .iter()
            .all(|r| r.answer == SatProbeAnswer::Unknown && r.reason.is_some())
    );
    let observer = |_: SatProbeEvent<'_>| ops.cancellation.cancel();
    assert!(matches!(
        prepare().admit_with_probes(
            &ops,
            None,
            None,
            Some((Default::default(), &observer)),
            None
        ),
        Err(CheckError::Cancelled)
    ));
}
fn reports(text: &str) -> Vec<(String, Vec<SatProbeReport>)> {
    let p = load_text(text);
    let l = Limits::default();
    let ops = (&l).into();
    p.verification_requests(&l)
        .unwrap()
        .into_iter()
        .map(|(key, r)| {
            let RequestPreparation::Complete(raw) = r.prepare(&p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            let reports = raw
                .program()
                .components()
                .filter(|c| c.cycle.is_some())
                .map(|c| raw.sat_probe(c.id, &Default::default(), &ops).unwrap())
                .collect();
            (format!("{key:?}"), reports)
        })
        .collect()
}
#[test]
fn only_selected_assumptions_constrain_pairs_including_general_restrictions() {
    let text = "input x(); relation a(); relation b(); a():-x(),!b();b():-x(),!a();
relation forbidden(); forbidden():-x(); assumption no_x:empty(forbidden);
relation bad(); obligation clean:empty(bad);
verification free{assumptions:[];obligations:[clean];}
verification restricted{assumptions:[no_x];obligations:[clean];}";
    let r = reports(text);
    assert!(
        r.iter()
            .find(|(k, _)| k.contains("free"))
            .unwrap()
            .1
            .iter()
            .any(|r| r.answer == SatProbeAnswer::Sat)
    );
    assert!(
        r.iter()
            .find(|(k, _)| k.contains("restricted"))
            .unwrap()
            .1
            .iter()
            .all(|r| r.answer == SatProbeAnswer::Unsat)
    );
    for restriction in [
        "at_most_one(choice,group_by:())",
        "exactly_one(choice,group_by:())",
        "empty(both)",
    ] {
        let t=format!("sort S;const left,right:S;input choice(s:S);relation both();both():-choice(left),choice(right);
relation a();relation b();a():-both(),!b();b():-both(),!a();assumption exclusive:{restriction};
verification checks{{assumptions:[exclusive];obligations:[];}}");
        assert!(
            reports(&t)[0]
                .1
                .iter()
                .all(|r| r.answer == SatProbeAnswer::Unsat)
        );
    }
    // Coverage over an empty zero-arity relation makes W inconsistent.
    assert!(reports("relation a();relation b();a():-!b();b():-!a();relation missing();assumption impossible:at_least_one(missing,group_by:());verification v{assumptions:[impossible];obligations:[];}")[0].1.iter().all(|r|r.answer==SatProbeAnswer::Unsat));
}
#[test]
fn guarded_fixtures_and_four_guard_cycle_have_at_most_one_stable_model() {
    for text in [
        include_str!("fixtures/guarded-settlement.den"),
        include_str!("fixtures/guarded-settlement-boolean.den"),
        include_str!("fixtures/guarded-settlement-producers.den"),
        include_str!("fixtures/implied-guard.den"),
        include_str!("fixtures/guarded-chain.den"),
        "input x();input y();relation g0();relation g1();relation g2();relation g3();g0():-x();g0():-y();g1():-!x();g1():-y();g2():-x();g2():-!y();g3():-!x();g3():-!y();relation a();relation b();relation c();relation d();a():-g0(),!b();b():-g1(),!c();c():-g2(),!d();d():-g3(),!a();verification v{assumptions:[];obligations:[];}",
    ] {
        let rs = reports(text);
        assert!(!rs[0].1.is_empty());
        for (_, rs) in rs {
            for r in rs {
                assert_eq!(r.answer, SatProbeAnswer::Unsat, "{:?}", r.reason);
            }
        }
    }
}
#[test]
fn zoo_guards_are_unique_with_shared_upstream_completion() {
    let script =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/bench-den-zoo.mjs");
    let output=std::process::Command::new("node").args(["--input-type=module","-e","import {pathToFileURL} from 'node:url';const m=await import(pathToFileURL(process.argv[1]));console.log(JSON.stringify(['guarded-ring','guarded-fan-in','guarded-worlds'].map(f=>m.source(f,2)).concat([m.source('guarded-hub',2),m.source('guarded-hub',2,{hubReader:'merged'}),m.source('guarded-hub',2,{hubDecoys:2,hubRoutes:false}),m.source('guarded-hub',2,{hubDecoys:2,hubRoutes:false,hubDecoyShape:'near-full'})]))); "]).arg(script).output().unwrap();
    assert!(output.status.success());
    for text in serde_json::from_slice::<Vec<String>>(&output.stdout).unwrap() {
        let rs = reports(&text);
        assert!(!rs[0].1.is_empty());
        for (_, rs) in rs {
            for r in rs {
                assert_eq!(r.answer, SatProbeAnswer::Unsat, "{:?}", r.reason);
            }
        }
    }
}

#[test]
fn coverage_uses_resolved_domains_and_within_exclusions_with_fixed_facts() {
    for (domain, expected) in [
        ("domain S=[left];", SatProbeAnswer::Sat),
        ("", SatProbeAnswer::Unsat),
    ] {
        let text=format!("sort S;const left,right:S;{domain}
relation eligible(s:S);eligible(left);input choice(s:S) within eligible;
relation enabled();enabled();relation a();relation b();a():-enabled(),!b();b():-enabled(),!a();
assumption required:at_least_one(choice,group_by:(s));verification v{{assumptions:[required];obligations:[];}}");
        let rs = reports(&text);
        assert!(!rs[0].1.is_empty());
        for r in &rs[0].1 {
            assert_eq!(r.answer, expected, "{:?}", r.reason);
        }
    }
}

#[test]
fn candidate_probe_agrees_with_certificates_at_their_actual_snapshots() {
    let boolean = include_str!("fixtures/guarded-settlement-boolean.den");
    // The provider's real value is perishable, despite its positive self-loop.
    let upstream=boolean.replace("input perishable();", "input seed(); input extra(); relation perishable(); perishable():-seed();perishable():-extra(),perishable();");
    let early = format!(
        "{boolean}\nrelation unused(); unused():-docked();unused():-docked(),priority_call();"
    );
    let mut certificates = 0;
    let mut implied = 0;
    let mut revised = false;
    for text in [
        boolean,
        &upstream,
        &early,
        include_str!("fixtures/guarded-settlement.den"),
        include_str!("fixtures/implied-guard.den"),
        include_str!("fixtures/guarded-settlement-producers.den"),
    ] {
        let loaded = load_text(text);
        let l = Limits::default();
        let ops = (&l).into();
        let request = loaded.verification_requests(&l).unwrap().remove(0).1;
        let RequestPreparation::Complete(raw) =
            request.prepare(&loaded.corpus, &loaded.keys, &ops).unwrap()
        else {
            panic!()
        };
        let events = std::cell::RefCell::new(Vec::new());
        let observer = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
        let admitted = raw
            .admit_with_candidate_probe(
                &ops,
                Some(&observer),
                Some(CandidateProbeLimits {
                    max_candidates: 1000,
                    timeout: std::time::Duration::from_secs(60),
                    ..Default::default()
                }),
            )
            .unwrap();
        assert!(admitted.program().is_admitted());
        let events = events.into_inner();
        for event in events.iter().filter(|e| e.candidate_probe.is_some()) {
            assert!(
                event.guarded.as_ref().unwrap().position.is_some(),
                "diagnose the final iteration guard, never a lookahead preview"
            );
        }
        let reports = events
            .iter()
            .filter_map(|e| e.candidate_probe.as_ref())
            .collect::<Vec<_>>();
        for proof in admitted
            .program()
            .rewrite_proofs()
            .filter_map(|p| p.guarded_settlement())
        {
            let report = reports
                .iter()
                .find(|r| {
                    r.snapshot == proof.certificate.bounds().next().unwrap().cone.snapshot
                        && r.rule == proof.proof.candidate.rule.id
                        && r.occurrence == proof.occurrence
                })
                .expect("same-snapshot report for certificate");
            assert_eq!(report.answer, SatProbeAnswer::Unsat, "{report:?}");
            certificates += 1;
            implied += usize::from(proof.implied_guard.is_some());
            revised |= report.snapshot > 0;
        }
        let counts = events
            .iter()
            .filter_map(|e| e.candidate_probe_counts.as_ref())
            .last()
            .unwrap();
        assert_eq!(
            counts.candidates,
            counts.ruled_out + counts.not_ruled_out + counts.unknown + counts.unexamined
        );
        assert_eq!(counts.unknown, 0);
    }
    assert!(certificates >= 6);
    assert!(implied > 0);
    assert!(revised);
}

#[test]
fn candidate_probe_caps_exhaustion_and_cancellation_leave_admission_alone() {
    let text = "input x();relation h();relation p();h():-x(),!p();p():-x(),!h();verification v{assumptions:[];obligations:[];}";
    let loaded = load_text(text);
    let l = Limits::default();
    let ops = (&l).into();
    let request = loaded.verification_requests(&l).unwrap().remove(0).1;
    let prepare = || {
        let RequestPreparation::Complete(raw) =
            request.prepare(&loaded.corpus, &loaded.keys, &ops).unwrap()
        else {
            panic!()
        };
        raw
    };
    let ordinary = prepare().admit(&ops).unwrap();
    for config in [
        CandidateProbeLimits::default(),
        CandidateProbeLimits {
            max_candidates: 0,
            ..Default::default()
        },
        CandidateProbeLimits {
            max_candidates: 1,
            ..Default::default()
        },
        CandidateProbeLimits {
            max_work: 1,
            ..Default::default()
        },
        CandidateProbeLimits {
            timeout: std::time::Duration::ZERO,
            ..Default::default()
        },
    ] {
        let events = std::cell::RefCell::new(Vec::new());
        let observer = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
        let admitted = prepare()
            .admit_with_candidate_probe(&ops, Some(&observer), Some(config.clone()))
            .unwrap();
        assert_eq!(admitted.receipts(), ordinary.receipts());
        assert_eq!(
            admitted.program().is_admitted(),
            ordinary.program().is_admitted()
        );
        assert_eq!(
            admitted.program().admission_limit(),
            ordinary.program().admission_limit()
        );
        assert_eq!(
            admitted.program().rewrite_proofs().count(),
            ordinary.program().rewrite_proofs().count()
        );
        let events = events.into_inner();
        let counts = events
            .iter()
            .filter_map(|e| e.candidate_probe_counts.as_ref())
            .last()
            .unwrap();
        assert!(counts.candidates > 0);
        assert_eq!(
            counts.candidates,
            counts.ruled_out + counts.not_ruled_out + counts.unknown + counts.unexamined
        );
        if config.max_candidates == 0 || config.timeout.is_zero() {
            assert_eq!(counts.unexamined, counts.candidates);
        } else if config.max_work == 1 {
            assert!(counts.unknown > 0);
            assert!(counts.unexamined > 0);
        } else {
            assert!(counts.ruled_out > 0);
        }
    }
    let cancellation = ops.cancellation.clone();
    let observer = |e: &AdmissionProgress| {
        if e.candidate_probe.is_some() {
            cancellation.cancel();
        }
    };
    assert!(matches!(
        prepare().admit_with_candidate_probe(&ops, Some(&observer), Some(Default::default())),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn existence_uses_selected_assumptions_and_reports_empty_world_sets_separately() {
    for (restriction, extra) in [
        ("empty(enabled)", "relation enabled(); enabled():-x();"),
        (
            "at_least_one(off,group_by:())",
            "relation off(); off():-!x();",
        ),
    ] {
        let text=format!("input x(); relation a(); a():-x(),!a(); {extra} assumption safe:{restriction};
verification free{{assumptions:[];obligations:[];}} verification restricted{{assumptions:[safe];obligations:[];}}");
        let rs = reports(&text);
        for (key, reports) in rs {
            for r in reports {
                let e = r.existence.unwrap();
                assert_eq!(
                    e.answer,
                    if key.contains("free") {
                        SatExistenceAnswer::NoMeaning
                    } else {
                        SatExistenceAnswer::EveryWorld
                    }
                );
                if let Some(world) = e.world {
                    assert_eq!(world.len(), 1);
                }
            }
        }
    }
    // Eligibility leaves no input tuple for right, but the resolved grouping
    // domain still requires it. No permitted world is distinct from totality.
    let base="sort S; const left,right:S; relation eligible(s:S); eligible(left); input choice(s:S) within eligible;
relation a();a():-!a(); assumption required:at_least_one(choice,group_by:(s)); verification v{assumptions:[required];obligations:[];}";
    for (prefix, expected) in [
        ("", SatExistenceAnswer::InconsistentAssumptions),
        ("domain S=[left];", SatExistenceAnswer::NoMeaning),
    ] {
        let text = format!("{prefix}{base}");
        assert!(
            reports(&text)[0]
                .1
                .iter()
                .all(|r| r.existence.as_ref().unwrap().answer == expected)
        );
    }
}
