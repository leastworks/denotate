use denotate_check::*;
use denotate_ir_text::*;

fn load_text(text: &str) -> LoadedProgram {
    let f = SourceFile::new("file:///probe.den", 0, text);
    load(&ProgramMembership::single("root", [f.uri.clone()]), &[f]).unwrap()
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
                    r.snapshot == proof.bounds.cone.snapshot
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
