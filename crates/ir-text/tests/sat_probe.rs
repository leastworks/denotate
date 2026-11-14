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
