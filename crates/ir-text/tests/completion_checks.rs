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
fn evidence_model<'a>(
    status: &'a serde_json::Value,
    reference: &serde_json::Value,
) -> &'a serde_json::Value {
    &status["completionEvidence"]["models"][reference["modelRef"].as_str().unwrap()]
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
    let model = evidence_model(&s.status, &d.evidence["examples"][0]["model"]);
    assert_eq!(model["scope"], "property-cone");
    assert_eq!(model["scopeAtomsComplete"], false);
    assert_eq!(
        d.evidence["examples"][0]["presentTuples"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(
        model["interpretation"]
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
    let model = evidence_model(&s.status, &d.evidence["withoutHypothesis"]);
    assert_eq!(model["kind"], "completion-model");
    assert_eq!(model["scope"], "classification-without-hypothesis");
    assert!(model["hypothesis"].is_null());
    assert_eq!(d.evidence["observation"], model["observation"]);
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

#[test]
fn evidence_is_bounded_shared_and_explicitly_expandable_without_changing_findings() {
    let mut text = String::from("sort S;const ");
    text.push_str(
        &(0..150)
            .map(|i| format!("c{i}"))
            .collect::<Vec<_>>()
            .join(","),
    );
    text.push_str(":S;relation r(x:S);");
    for i in 0..150 {
        text.push_str(&format!("r(c{i});"));
    }
    text.push_str("obligation first:at_most_one(r,group_by:());obligation second:at_most_one(r,group_by:());verification v{semantics:completion;assumptions:[];obligations:[first,second];}");
    let (p, r) = checked(&text, Default::default());
    let bounded = presentation::present_completion(&p, &r).unwrap();
    let full = presentation::present_completion_with_options(
        &p,
        &r,
        denotate_presentation::CompletionEvidenceOptions {
            full_models: true,
            ..Default::default()
        },
    )
    .unwrap();
    let empty = presentation::present_completion_with_options(
        &p,
        &r,
        denotate_presentation::CompletionEvidenceOptions {
            max_atoms: 0,
            ..Default::default()
        },
    )
    .unwrap();
    for shown in [&bounded, &full, &empty] {
        assert_eq!(shown.status["state"], "findings");
        assert_eq!(
            shown
                .diagnostics
                .iter()
                .map(|d| &d.identity)
                .collect::<Vec<_>>(),
            bounded
                .diagnostics
                .iter()
                .map(|d| &d.identity)
                .collect::<Vec<_>>()
        );
    }
    let models = bounded.status["completionEvidence"]["models"]
        .as_object()
        .unwrap();
    assert_eq!(
        models.len(),
        1,
        "identical property models must be shared across obligations"
    );
    let model = models.values().next().unwrap();
    assert_eq!(model["interpretation"].as_array().unwrap().len(), 64);
    assert!(model["omittedAtoms"].as_u64().unwrap() > 0);
    assert_eq!(
        full.status["completionEvidence"]["models"]
            .as_object()
            .unwrap()
            .values()
            .next()
            .unwrap()["interpretation"]
            .as_array()
            .unwrap()
            .len(),
        150
    );
    assert!(
        empty.status["completionEvidence"]["models"]
            .as_object()
            .unwrap()
            .values()
            .all(|m| m["interpretation"].as_array().unwrap().is_empty())
    );
    for d in &bounded.diagnostics {
        if let Some(examples) = d.evidence["examples"].as_array() {
            for e in examples {
                assert!(e["presentTuples"].as_array().unwrap().len() <= 64);
            }
        }
    }
}

#[test]
fn projected_property_evidence_omits_unrelated_inputs_but_full_models_retain_them() {
    let (p, r) = checked(
        "input relevant();input unrelated();relation bad();bad():-relevant();obligation clean:empty(bad);verification v{semantics:completion;assumptions:[];obligations:[clean];}",
        Default::default(),
    );
    let shown = presentation::present_completion(&p, &r).unwrap();
    let text = shown.status["completionEvidence"].to_string();
    assert!(text.contains("relevant"));
    assert!(!text.contains("unrelated"));
    let full = presentation::present_completion_with_options(
        &p,
        &r,
        denotate_presentation::CompletionEvidenceOptions {
            full_models: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(
        full.status["completionEvidence"]
            .to_string()
            .contains("unrelated")
    );
}

#[test]
fn reused_property_queries_keep_tuple_pins_worlds_and_obligation_scopes_separate() {
    let (p, r) = checked(
        "sort S;const a,b,c:S;input i();relation bad(x:S);bad(a):-i();bad(b):-!i();bad(c):-bad(c);relation safe(x:S);obligation clean:empty(bad);obligation fine:empty(safe);verification v{semantics:completion;assumptions:[];obligations:[clean,fine];}",
        Default::default(),
    );
    let bad = p
        .corpus
        .obligations()
        .find(|o| o.name == "clean")
        .unwrap()
        .id;
    let safe = p
        .corpus
        .obligations()
        .find(|o| o.name == "fine")
        .unwrap()
        .id;
    assert!(r.obligations[&bad].complete());
    assert!(r.obligations[&safe].complete());
    assert!(!r.obligations[&safe].failed());
    let i = p.corpus.relations().find(|r| r.name == "i").unwrap().id;
    let mut worlds = std::collections::BTreeSet::new();
    for part in &r.obligations[&bad].parts {
        assert!(part.failed);
        let m = part.example.as_ref().unwrap();
        assert_eq!(m.value(&part.tuples[0]), Some(true));
        worlds.insert(m.value(&denotate_check::GroundAtom::new(i, [])).unwrap());
    }
    assert_eq!(
        worlds.len(),
        2,
        "opposite conditions require separate valid observations"
    );
}

#[test]
fn one_property_encoding_handles_many_parts_without_pooling_the_old_sat_allowances() {
    let text = format!(
        "sort S;const {}:S;input i();relation bad(x:S);{} obligation clean:empty(bad);verification v{{semantics:completion;assumptions:[];obligations:[clean];}}",
        (0..160)
            .map(|i| format!("a{i}"))
            .collect::<Vec<_>>()
            .join(","),
        (0..160)
            .map(|i| format!("bad(a{i}):-{}i();", if i % 2 == 0 { "" } else { "!" }))
            .collect::<String>()
    );
    let p = loaded(&text);
    let v = p.corpus.verifications().next().unwrap().id;
    let sink = denotate_check::CompletionSizes::default();
    let Preparation::Ready(e) = Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits {
            completion_sizes: Some(sink.clone()),
            ..Default::default()
        },
        QueryLimits {
            max_solves: 2,
            ..Default::default()
        },
    )
    .unwrap() else {
        panic!()
    };
    let r = e
        .check(
            &p.keys,
            &CheckOptions {
                max_failures: usize::MAX,
                ..Default::default()
            },
        )
        .unwrap();
    let o = r.obligations.values().next().unwrap();
    assert!(o.complete());
    assert!(o.parts.iter().all(|p| p.failed));
    let snapshot = sink.snapshot();
    let queries: Vec<_> = snapshot
        .searches
        .iter()
        .filter(|s| s.phase == "completion property")
        .collect();
    assert_eq!(queries.len(), 1, "one physical solver per obligation");
    assert_eq!(
        queries[0]
            .encoding_details
            .iter()
            .filter(|e| e.purpose == "model")
            .count(),
        1,
        "one property equation copy, regardless of tuple count"
    );
}

#[test]
fn reused_uniqueness_groups_do_not_keep_previous_group_constraints() {
    let (_p, r) = checked(
        "sort G;const a,b,c:G;sort V;const x,y:V;input i();relation r(g:G,v:V);r(a,x):-i();r(a,y):-!i();r(b,x);r(b,y);r(c,x);obligation one:at_most_one(r,group_by:(g));verification v{semantics:completion;assumptions:[];obligations:[one];}",
        Default::default(),
    );
    let o = r.obligations.values().next().unwrap();
    assert!(o.complete());
    assert_eq!(o.parts.iter().filter(|p| p.failed).count(), 1);
    assert!(o.parts.iter().any(|p| !p.failed));
}

#[test]
fn bounded_failure_triage_is_a_decided_failure_with_a_lower_bound_and_other_checks_continue() {
    let facts = (0..12).map(|i| format!("bad(a{i});")).collect::<String>();
    let names = (0..12)
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let text = format!(
        "sort S; const {names}:S; relation bad(x:S); {facts} relation safe(); obligation first:empty(bad); obligation last:empty(safe); verification v{{semantics:completion;assumptions:[];obligations:[first,last];}}"
    );
    for cap in [0, 2, 12, usize::MAX] {
        let (p, r) = checked(
            &text,
            CheckOptions {
                max_failures: cap,
                max_examples: 0,
                ..Default::default()
            },
        );
        assert!(!r.is_incomplete());
        assert!(r.has_failures());
        let bad = p
            .corpus
            .obligations()
            .find(|o| o.name == "first")
            .unwrap()
            .id;
        let safe = p
            .corpus
            .obligations()
            .find(|o| o.name == "last")
            .unwrap()
            .id;
        assert!(r.obligations[&safe].complete());
        assert!(!r.obligations[&safe].failed());
        let o = &r.obligations[&bad];
        assert!(o.complete());
        assert_eq!(
            o.parts.iter().filter(|p| p.failed).count(),
            cap.max(1).min(12)
        );
        assert_eq!(o.failures_truncated, cap.max(1) < 12);
        let shown = presentation::present_completion(&p, &r).unwrap();
        let row = shown.status["obligations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|o| o["name"] == "first")
            .unwrap();
        assert_eq!(row["state"], "counterexample");
        assert_eq!(
            row["failureCountKind"],
            if cap.max(1) < 12 { "at-least" } else { "exact" }
        );
    }
}

#[test]
fn completion_pruning_reports_head_context_and_source_without_an_edit() {
    let text = "input tag();\nrelation accepted();\nrelation profile();\naccepted():-tag();\naccepted():-profile();\nprofile():-tag(),accepted();\nverification v{semantics:completion;assumptions:[];obligations:[];}";
    let (p, r) = checked(
        text,
        CheckOptions {
            prune: true,
            ..Default::default()
        },
    );
    assert!(!r.has_failures());
    assert!(!r.is_incomplete());
    let shown = presentation::present_completion(&p, &r).unwrap();
    assert!(
        shown.status["simplifications"]["removedInstances"]
            .as_u64()
            .unwrap()
            > 0
    );
    let diagnostic = shown
        .diagnostics
        .iter()
        .find(|d| {
            d.kind == denotate_presentation::Kind::CompletionPruning
                && d.message.contains("accepted()")
        })
        .unwrap();
    assert_eq!(
        diagnostic.kind.severity(),
        denotate_presentation::Severity::Information
    );
    assert_eq!(diagnostic.evidence["context"], "W");
    assert!(diagnostic.message.contains("subsumption"));
    assert!(diagnostic.notes.iter().any(|n| n.contains("not edits")));
    let rule = p
        .corpus
        .rules()
        .find(|r| {
            p.provenance
                .origins(r.id)
                .iter()
                .any(|o| o.span == diagnostic.primary)
        })
        .unwrap();
    assert_eq!(
        p.corpus.relation(rule.head.relation()).unwrap().name,
        "accepted"
    );
    assert!(
        diagnostic.evidence["records"][0]["sources"]
            .as_array()
            .unwrap()
            .len()
            > 0
    );
}
