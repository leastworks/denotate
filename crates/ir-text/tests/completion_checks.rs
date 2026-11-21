use denotate_check::{Limits, completion_query::*};
use denotate_ir_text::*;
fn loaded(text: &str) -> LoadedProgram {
    let s = SourceFile::new("file:///program.den", 1, text);
    load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap()
}
fn checked(text: &str, options: CheckOptions) -> (LoadedProgram, Report) {
    let p = loaded(text);
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
    let r = e.check(&p.keys, &options).unwrap();
    (p, r)
}
#[test]
fn circular_empty_counterexample_keeps_completion_evidence_and_obligation_location() {
    let (p, r) = checked(
        "relation p();p():-p();relation h();h():-p();obligation clean:empty(p);verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[clean];}",
        Default::default(),
    );
    let s = presentation::present_completion(&p, &r).unwrap();
    assert_eq!(s.status["state"], "findings");
    assert_eq!(
        s.status["advisories"]["circularSupport"]["state"],
        "not-requested"
    );
    let d = s
        .diagnostics
        .iter()
        .find(|d| d.kind == denotate_presentation::Kind::Counterexample)
        .unwrap();
    assert_eq!(d.evidence["kind"], "completion-model");
    assert!(d.notes.iter().any(|s| s.contains("p()")));
    assert_eq!(d.evidence["examples"][0]["model"]["scope"], "property-cone");
    assert!(d.evidence["examples"][0]["model"]["scopeAtoms"].is_array());
    assert_eq!(
        d.evidence["examples"][0]["presentTuples"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(
        d.evidence["examples"][0]["model"]["interpretation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|a| a["value"] == true)
    );
    let obligation = p.corpus.obligations().next().unwrap();
    assert!(
        p.provenance
            .origins(obligation.id)
            .iter()
            .any(|o| o.span == d.primary)
    );
    assert!(!format!("{:?}", d.evidence).contains("replayed-counterexample"));
}
#[test]
fn fixed_cardinality_and_independent_errors_survive_processing_no_meaning() {
    let (p, r) = checked(
        "sort S;const a,b:S;relation r(x:S);r(a);r(b);relation missing(x:S);relation odd();odd():-!odd();obligation e:empty(r);obligation u:at_most_one(r,group_by:());obligation c:at_least_one(missing,group_by:(x));obligation x:exactly_one(r,group_by:());verification v{semantics:completion;assumptions:[];obligations:[e,u,c,x];}",
        Default::default(),
    );
    let s = presentation::present_completion(&p, &r).unwrap();
    assert!(!r.is_incomplete());
    assert!(r.meaning.no_meaning.exists());
    for o in s.status["obligations"].as_array().unwrap() {
        assert_eq!(o["state"], "counterexample");
    }
    assert_eq!(
        s.diagnostics
            .iter()
            .filter(|d| d.kind == denotate_presentation::Kind::Counterexample)
            .count(),
        4
    );
    let e = s
        .diagnostics
        .iter()
        .find(|d| matches!(d.identity, denotate_presentation::Identity::Emptiness(_)))
        .unwrap();
    assert_eq!(e.evidence["count"], 2);
    let coverage = s
        .diagnostics
        .iter()
        .find(|d| matches!(d.identity, denotate_presentation::Identity::Coverage(_)))
        .unwrap();
    for example in coverage.evidence["examples"].as_array().unwrap() {
        assert_eq!(example["group"].as_array().unwrap().len(), 1);
        assert!(example["presentTuples"].as_array().unwrap().is_empty());
    }
}
#[test]
fn symbolic_coverage_and_notices_are_explicitly_unanalysed() {
    let (p, r) = checked(
        "input i();obligation o:at_least_one(i,group_by:());notice n:varies(i);verification v{semantics:completion;assumptions:[];obligations:[o];notices:[n];}",
        Default::default(),
    );
    let s = presentation::present_completion(&p, &r).unwrap();
    assert!(r.is_incomplete());
    assert_eq!(s.status["obligations"][0]["state"], "not-analysed");
    assert_eq!(s.status["notices"][0]["state"], "not-analysed");
}
#[test]
fn inconsistent_context_never_reports_vacuous_proofs() {
    let (p, r) = checked(
        "input i();relation h();assumption a:empty(i);assumption b:at_least_one(i,group_by:());obligation total:no_rejections(h);verification v{semantics:completion;hypothesis:h;assumptions:[a,b];obligations:[total];}",
        Default::default(),
    );
    let s = presentation::present_completion(&p, &r).unwrap();
    assert!(r.has_failures());
    assert!(!r.all_rejected());
    assert!(!r.is_incomplete());
    assert_eq!(s.status["obligations"][0]["state"], "not-analysed");
    assert_eq!(s.status["obligations"][0]["vacuous"], false);
}
#[test]
fn ambiguity_models_and_rejection_evidence_are_distinct() {
    let (p, r) = checked(
        "input i();relation p();p():-p();relation h();h():-i(),p();h():-i(),!p();obligation total:no_rejections(h);verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[total];}",
        Default::default(),
    );
    let s = presentation::present_completion(&p, &r).unwrap();
    assert_eq!(s.status["classification"]["ambiguous"]["state"], "exists");
    assert_eq!(s.status["classification"]["rejected"]["state"], "exists");
    assert!(
        s.diagnostics
            .iter()
            .any(|d| d.evidence["kind"] == "rejected-observation")
    );
    assert!(
        s.diagnostics
            .iter()
            .any(|d| d.evidence["kind"] == "completion-ambiguity")
    );
}

#[test]
fn library_completion_findings_keep_labeled_fallback_and_upstream_hypothesis() {
    let lib = SourceFile::new(
        "file:///lib.den",
        1,
        "relation h();obligation total:no_rejections(h) message \"Recognize every input\";verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[total];}",
    );
    let app = SourceFile::new("file:///app.den", 1, "relation unrelated();");
    let mut membership = ProgramMembership::single("consumer", [app.uri.clone()]);
    // Use the same library membership form as the declaration fallback test.
    membership
        .roots
        .get_mut("consumer")
        .unwrap()
        .libraries
        .insert("lib".into());
    membership.roots.insert(
        "lib".into(),
        RootInfo {
            files: [lib.uri.clone()].into(),
            libraries: Default::default(),
        },
    );
    let p = load(&membership, &[lib, app]).unwrap();
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
    let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
    let s = presentation::present_completion(&p, &r).unwrap();
    let d = s
        .diagnostics
        .iter()
        .find(|d| d.kind == denotate_presentation::Kind::Counterexample)
        .unwrap();
    assert!(d.fallback);
    assert!(d.message.contains("in consumer:"));
    assert!(d.message.contains("Recognize every input"));
    assert!(
        d.related
            .iter()
            .any(|r| r.label == "condition being inspected")
    );
}

#[test]
fn classification_no_meaning_is_distinct_from_rejection_in_findings_and_summary() {
    let (p, r) = checked(
        "input i();relation h();h():-i(),!h();obligation total:no_rejections(h);verification v{semantics:completion;hypothesis:h;decisions:[];assumptions:[];obligations:[total];}",
        Default::default(),
    );
    let s = presentation::present_completion(&p, &r).unwrap();
    assert!(!r.all_rejected());
    assert_eq!(s.status["classification"]["noMeaning"]["state"], "exists");
    assert_eq!(s.status["classification"]["rejected"]["state"], "exists");
    let d = s
        .diagnostics
        .iter()
        .find(|d| d.kind == denotate_presentation::Kind::NoMeaning)
        .unwrap();
    assert_eq!(d.evidence["scope"], "classification-without-hypothesis");
    assert!(d.message.contains("even without the hypothesis"));
    let d = s
        .diagnostics
        .iter()
        .find(|d| d.evidence["kind"] == "rejected-observation")
        .unwrap();
    assert_eq!(d.evidence["confirmedNoInterpretation"], true);
    assert_eq!(d.evidence["withoutHypothesis"]["kind"], "completion-model");
    assert_eq!(
        d.evidence["withoutHypothesis"]["scope"],
        "classification-without-hypothesis"
    );
    assert!(d.evidence["withoutHypothesis"]["hypothesis"].is_null());
    assert_eq!(
        d.evidence["observation"],
        d.evidence["withoutHypothesis"]["observation"]
    );
    assert_eq!(
        s.status["classification"]["rejected"]["evidence"],
        d.evidence
    );
}

#[test]
fn decisions_compare_tuple_sets_not_cardinality_and_never_hide_contradictions() {
    for (rules, ambiguous, no_meaning) in [
        ("r(a);r(b);helper():-helper();", false, false),
        ("r(a):-!r(b);r(b):-!r(a);", true, false),
        ("r(a);helper():-!helper();", false, true),
    ] {
        let (p, r) = checked(
            &format!(
                "sort S;const a,b:S;relation r(x:S);relation helper();{rules}verification v{{semantics:completion;decisions:[r];assumptions:[];obligations:[];}}"
            ),
            Default::default(),
        );
        assert_eq!(r.meaning.ambiguous.exists(), ambiguous);
        assert_eq!(r.meaning.no_meaning.exists(), no_meaning);
        assert!(!r.is_incomplete());
        let s = presentation::present_completion(&p, &r).unwrap();
        assert_eq!(s.status["determinacy"]["kind"], "selected-relations");
        assert_eq!(
            s.status["determinacy"]["relations"]
                .as_array()
                .unwrap()
                .len(),
            1
        );
        if ambiguous {
            let d = s
                .diagnostics
                .iter()
                .find(|d| d.kind == denotate_presentation::Kind::AmbiguousMeaning)
                .unwrap();
            assert_eq!(d.evidence["determinacy"], s.status["determinacy"]);
        }
    }
}

#[test]
fn decision_edits_change_requests_and_repeated_preparations_agree() {
    let mut identities = Vec::new();
    for (decision, ambiguous) in [
        ("", true),
        ("decisions:[h];", false),
        ("decisions:[];", false),
        ("decisions:[helper];", true),
    ] {
        let text = format!(
            "relation helper();helper():-helper();relation h();h():-helper();h():-!helper();verification v{{semantics:completion;hypothesis:h;{decision}assumptions:[];obligations:[];}}"
        );
        let (p, r) = checked(&text, Default::default());
        let request = p
            .verification_requests(&Limits::default())
            .unwrap()
            .remove(0)
            .1;
        assert!(!identities.contains(&request));
        identities.push(request);
        assert_eq!(
            r.classification.as_ref().unwrap().ambiguous.exists(),
            ambiguous
        );
        let (_, again) = checked(&text, Default::default());
        assert_eq!(
            again.classification.as_ref().unwrap().ambiguous.exists(),
            ambiguous
        );
        assert_eq!(again.has_failures(), r.has_failures());
    }
}
