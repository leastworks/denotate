use denotate_check::{GroundAtom, Limits, completion_query::*};
use denotate_ir_text::*;
fn loaded(text: &str) -> LoadedProgram {
    let s = SourceFile::new("file:///scopes.den", 1, text);
    load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap()
}
fn engine(p: &LoadedProgram) -> Engine {
    let v = p.corpus.verifications().next().unwrap().id;
    let Preparation::Ready(e) = Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap() else {
        panic!()
    };
    e
}
fn checked(p: &LoadedProgram, options: &CheckOptions) -> Report {
    engine(p).check(&p.keys, options).unwrap()
}
#[test]
fn dead_and_nodead_leave_processing_contradictions_out_of_classification() {
    // A dead/nodead pair: including the dead edge in C(H)
    // would turn this into rejection (leaf off) instead of processing no-meaning.
    for dead in ["", "h():-bad(),absent();"] {
        let p = loaded(&format!(
            "relation leaf();leaf():-leaf();relation h();h():-leaf();relation absent();relation bad();bad():-h(),!bad();{dead}obligation total:no_rejections(h);verification v{{semantics:completion;hypothesis:h;decisions:[leaf];assumptions:[];obligations:[total];}}"
        ));
        let r = checked(&p, &Default::default());
        let c = r.classification.unwrap();
        assert!(c.accepted.exists());
        assert!(matches!(c.rejected, Search::None));
        assert!(matches!(c.no_meaning, Search::None));
        assert!(matches!(c.ambiguous, Search::None));
        assert!(r.meaning.no_meaning.exists());
        assert!(r.obligations.values().all(|o| o.complete() && !o.failed()));
    }
}
#[test]
fn dead_link_moves_ambiguity_to_processing_and_advisory_is_optional_non_gating() {
    let p = loaded(
        "relation h();h();relation p();p():-p();relation absent();h():-p(),absent();verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[];}",
    );
    let e = engine(&p);
    let plain = e.check(&p.keys, &Default::default()).unwrap();
    assert!(plain.classification.as_ref().unwrap().accepted.exists());
    assert!(matches!(
        plain.classification.as_ref().unwrap().ambiguous,
        Search::None
    ));
    assert!(plain.meaning.ambiguous.exists());
    let options = CheckOptions {
        dead_producers: true,
        ..Default::default()
    };
    for e in [&e, &engine(&p)] {
        let r = e.check(&p.keys, &options).unwrap();
        assert_eq!(r.has_failures(), plain.has_failures());
        assert_eq!(r.is_incomplete(), plain.is_incomplete());
        let DeadProducerAdvisory::Checked {
            findings,
            incomplete,
        } = &r.dead_producers
        else {
            panic!()
        };
        assert!(incomplete.is_none());
        assert_eq!(findings.len(), 1);
        let shown = presentation::present_completion(&p, &r).unwrap();
        let d = shown
            .diagnostics
            .iter()
            .find(|d| d.kind == denotate_presentation::Kind::DeadProducer)
            .unwrap();
        assert!(d.notes.iter().any(|n| n.contains("p()")));
        assert_eq!(d.evidence["kind"], "completion-dead-producer");
    }
    let cut = CheckOptions {
        advisory_limits: Limits {
            max_work: 0,
            ..Default::default()
        },
        ..options
    };
    let r = e.check(&p.keys, &cut).unwrap();
    assert_eq!(r.has_failures(), plain.has_failures());
    assert_eq!(r.is_incomplete(), plain.is_incomplete());
    assert!(matches!(
        r.dead_producers,
        DeadProducerAdvisory::Checked {
            incomplete: Some(_),
            ..
        }
    ));
}
#[test]
fn liveness_is_independent_of_w_h_and_decision_projection() {
    for decisions in ["", "h,p"] {
        let p = loaded(&format!(
            "input i();relation p();p():-p();relation h();h();h():-p(),i();assumption no_i:empty(i);verification v{{semantics:completion;hypothesis:h;decisions:[{decisions}];assumptions:[no_i];obligations:[];}}"
        ));
        let e = engine(&p);
        let h = p.corpus.relations().find(|r| r.name == "p").unwrap().id;
        match e.observation([]).unwrap() {
            ObservationOutcome::Accepted { classification, .. } => {
                assert!(classification.value(&GroundAtom::new(h, [])).is_some())
            }
            ObservationOutcome::Ambiguous { first, .. } => {
                assert!(first.value(&GroundAtom::new(h, [])).is_some())
            }
            other => panic!("{other:?}"),
        }
        let r = checked(
            &p,
            &CheckOptions {
                dead_producers: true,
                ..Default::default()
            },
        );
        let DeadProducerAdvisory::Checked { findings, .. } = r.dead_producers else {
            panic!()
        };
        assert!(findings.is_empty());
    }
}
#[test]
fn dead_contradictions_do_not_enter_assumption_provider_or_property_scopes() {
    for source in [
        "assumption a:at_least_one(yes,group_by:());",
        "input raw() within yes;",
    ] {
        let (assumptions, decisions) = if source.starts_with("assumption") {
            ("a", "")
        } else {
            ("", "raw")
        };
        let p = loaded(&format!(
            "relation yes();yes();relation absent();relation bad();bad():-!bad();yes():-bad(),absent();{source}obligation o:empty(yes);verification v{{semantics:completion;decisions:[{decisions}];assumptions:[{assumptions}];obligations:[o];}}"
        ));
        let r = checked(&p, &Default::default());
        assert!(!r.is_incomplete());
        assert!(r.assumptions.iter().all(AssumptionAnalysis::certified));
        assert!(r.obligations.values().all(|o| o.failed()));
        assert!(r.meaning.no_meaning.exists());
    }
}
