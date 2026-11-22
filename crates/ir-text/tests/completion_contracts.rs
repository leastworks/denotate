//! Input contracts are properties of their own completion cones, before W and H.
use denotate_check::{GroundAtom, Limits, completion_query::*};
use denotate_ir_text::*;
use denotate_presentation::Kind;
fn loaded(text: &str) -> LoadedProgram {
    let s = SourceFile::new("file:///contracts.den", 1, text);
    load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap()
}
fn prepare(p: &LoadedProgram, name: &str) -> Preparation {
    let v = p
        .corpus
        .verifications()
        .find(|v| v.name == name)
        .unwrap()
        .id;
    Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap()
}
fn engine(p: &LoadedProgram, name: &str) -> Engine {
    match prepare(p, name) {
        Preparation::Ready(e) => e,
        _ => panic!("not ready"),
    }
}
fn checked(p: &LoadedProgram) -> Report {
    engine(p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap()
}
fn input(p: &LoadedProgram, name: &str) -> GroundAtom {
    GroundAtom::new(
        p.corpus.relations().find(|r| r.name == name).unwrap().id,
        [],
    )
}
fn verification(selection: &str) -> String {
    format!(
        "verification v{{semantics:completion;decisions:[];assumptions:[a];obligations:[{selection}];}}"
    )
}

#[test]
fn invariant_cardinality_allows_varying_tuples_and_decisions_check_them_separately() {
    for decisions in ["", "r"] {
        let p = loaded(&format!(
            "sort S;const a,b:S;relation r(x:S);r(a):-!r(b);r(b):-!r(a);assumption a:exactly_one(r,group_by:());verification v{{semantics:completion;decisions:[{decisions}];assumptions:[a];obligations:[];}}"
        ));
        let e = engine(&p, "v");
        for e in [&e, &engine(&p, "v")] {
            let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
            assert!(r.assumptions.iter().all(AssumptionAnalysis::certified));
            assert_eq!(r.context, Context::Permitted);
            assert!(!r.is_incomplete());
            assert_eq!(r.meaning.ambiguous.exists(), !decisions.is_empty());
        }
    }
}
#[test]
fn whole_group_conjunction_not_individual_group_truth_is_the_contract() {
    let p = loaded(&format!(
        "sort G;const x,y:G;relation r(g:G);r(x):-r(x);assumption a:at_least_one(r,group_by:(g));{}",
        verification("")
    ));
    let r = checked(&p);
    assert!(r.assumptions[0].certified()); // y fails in every model, despite x varying.
    assert_eq!(r.context, Context::InconsistentAssumptions);
    let p = loaded(&format!(
        "sort G;const x,y:G;relation r(g:G);r(x):-r(x);r(y);assumption a:at_least_one(r,group_by:(g));{}",
        verification("")
    ));
    let r = checked(&p);
    let Search::Exists(a) = &r.assumptions[0].ambiguous else {
        panic!("{r:?}")
    };
    assert_eq!(p.corpus.constant(a.group[0]).unwrap().name, "x");
}
#[test]
fn undetermined_contract_never_becomes_empty_w_or_all_rejected_or_vacuous() {
    for body in ["p():-p();", "p():-!p();"] {
        let p = loaded(&format!(
            "relation p();{body}relation h();relation good();assumption a:empty(p);obligation o:empty(good);obligation total:no_rejections(h);verification v{{semantics:completion;hypothesis:h;decisions:[];assumptions:[a];obligations:[o,total];}}"
        ));
        let e = engine(&p, "v");
        let r = checked(&p);
        assert!(r.is_incomplete() && r.has_failures());
        assert_ne!(r.context, Context::InconsistentAssumptions);
        assert!(!r.all_rejected());
        assert!(
            r.obligations
                .values()
                .all(|o| !o.complete() && !o.vacuous && !o.failed())
        );
        assert!(matches!(
            e.worlds(&WorldQuery::default()).unwrap(),
            WorldAnswer::Inconclusive(_)
        ));
        assert!(matches!(
            e.observation([]).unwrap(),
            ObservationOutcome::UndeterminedAssumptions(_)
        ));
        let shown = presentation::present_completion(&p, &r).unwrap();
        assert_eq!(shown.status["inputContract"]["complete"], false);
        let d = shown
            .diagnostics
            .iter()
            .find(|d| d.kind == Kind::InvalidAssumption)
            .unwrap();
        assert!(d.message.contains("a"));
        assert!(
            d.notes
                .iter()
                .any(|n| n.contains("Example input observation"))
        );
        assert!(
            p.provenance
                .origins(p.corpus.assumptions().next().unwrap().id)
                .iter()
                .any(|o| o.span == d.primary)
        );
        assert!(
            !shown
                .diagnostics
                .iter()
                .flat_map(|d| &d.notes)
                .any(|n| n.contains("undetermined assumptions limit"))
        );
    }
}
#[test]
fn partial_contract_keeps_only_certified_counterexamples_and_cites_the_assumption() {
    for negation in ["", "!"] {
        let p = loaded(&format!(
            "input i();relation p();p():-{negation}p(),i();relation bad();bad():-!i();relation excluded();excluded():-i();assumption a:empty(p);obligation fails:empty(bad);obligation cannot_prove:empty(excluded);{}",
            verification("fails,cannot_prove")
        ));
        let r = checked(&p);
        let i = input(&p, "i");
        assert!(r.assumptions[0].failed());
        for (id, o) in &r.obligations {
            assert!(!o.complete());
            assert_eq!(
                o.failed(),
                p.corpus.obligation(*id).unwrap().name == "fails"
            );
            for part in &o.parts {
                for m in part.example.iter() {
                    assert!(!m.observation().present.contains(&i));
                }
            }
        }
        let shown = presentation::present_completion(&p, &r).unwrap();
        assert!(shown.diagnostics.iter().any(|d| {
            d.kind == Kind::Inconclusive
                && d.notes
                    .iter()
                    .any(|n| n == "Unvalidated input contract: a.")
        }));
        let e = engine(&p, "v");
        let WorldAnswer::World(w) = e.worlds(&WorldQuery::default()).unwrap() else {
            panic!()
        };
        assert!(w.absent.contains(&i));
    }
}
#[test]
fn overlapping_assumption_cones_do_not_share_helper_choices() {
    let p = loaded(
        "relation p();p():-p();relation a();a():-!a(),!p();a():-p();relation b();b():-!b(),p();b():-!p();assumption aa:at_least_one(a,group_by:());assumption bb:at_least_one(b,group_by:());verification v{semantics:completion;decisions:[];assumptions:[aa,bb];obligations:[];}",
    );
    let r = checked(&p);
    assert!(r.assumptions.iter().all(AssumptionAnalysis::certified));
    assert_eq!(r.context, Context::Permitted);
    assert!(r.meaning.no_meaning.exists());
}
#[test]
fn helpers_are_free_for_a_recursive_determined_provider() {
    let p = loaded(
        "relation p();relation q();p():-!q();q():-!p();relation eligible();eligible():-p();eligible():-q();input raw() within eligible;obligation o:empty(raw);verification v{semantics:completion;decisions:[raw,eligible];assumptions:[];obligations:[o];}",
    );
    let e = engine(&p, "v");
    assert!(matches!(
        e.observation([input(&p, "raw")]).unwrap(),
        ObservationOutcome::WholeProgram(Interpretations::Unique(_))
    ));
    let r = checked(&p);
    assert!(!r.is_incomplete());
    assert!(r.obligations.values().next().unwrap().failed());
}
#[test]
fn bad_static_providers_stop_only_dependent_verifications_and_keep_evidence() {
    for rule in ["eligible():-eligible();", "eligible():-!eligible();"] {
        let p = loaded(&format!(
            "relation eligible();{rule}input raw() within eligible;relation good();obligation o:empty(raw);obligation good:empty(good);verification bad{{semantics:completion;decisions:[];assumptions:[];obligations:[o];}}verification v{{semantics:completion;decisions:[];assumptions:[];obligations:[good];}}"
        ));
        let Preparation::InputDomains(issues) = prepare(&p, "bad") else {
            panic!()
        };
        assert_eq!(issues.len(), 1);
        assert!(matches!(
            issues[0].failure,
            InputDomainFailure::Ambiguous(_) | InputDomainFailure::NoMeaning
        ));
        let v = p
            .corpus
            .verifications()
            .find(|v| v.name == "bad")
            .unwrap()
            .id;
        let shown = presentation::completion_input_domain_failure(&p, v, &issues).unwrap();
        assert_eq!(shown.status["hasFailures"], true);
        assert!(
            shown
                .diagnostics
                .iter()
                .any(|d| d.kind == Kind::InvalidInputDomain)
        );
        if let InputDomainFailure::Ambiguous(pair) = &issues[0].failure {
            assert_eq!(pair.first.value(&input(&p, "raw")), None);
            assert_eq!(pair.second.value(&input(&p, "raw")), None);
            assert_ne!(
                pair.first.value(&input(&p, "eligible")),
                pair.second.value(&input(&p, "eligible"))
            );
            assert!(!shown.status["inputDomains"][0]["outcome"]["differingTuple"].is_null());
        }
        let r = checked(&p);
        assert!(r.obligations.values().all(|o| o.complete() && !o.failed()));
        assert_eq!(r.ignored_input_domains.len(), 1);
    }
}
#[test]
fn dead_reads_do_not_require_an_invalid_provider() {
    let p = loaded(
        "relation eligible();eligible():-eligible();input raw() within eligible;relation absent();relation good();good();good():-raw(),absent();obligation o:empty(absent);verification v{semantics:completion;decisions:[];assumptions:[];obligations:[o];}",
    );
    let r = checked(&p);
    assert!(r.obligations.values().all(|o| o.complete() && !o.failed()));
    assert_eq!(r.ignored_input_domains.len(), 1);
}
#[test]
fn input_dependent_provider_still_fails_loading_and_stable_keeps_stratification() {
    for body in [
        "input i();relation eligible();eligible():-i();input raw() within eligible;verification v{semantics:completion;assumptions:[];obligations:[];}",
        "relation eligible();eligible():-!eligible();input raw() within eligible;verification v{assumptions:[];obligations:[];}",
    ] {
        let s = SourceFile::new("file:///bad.den", 1, body);
        assert!(load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).is_err());
    }
}
#[test]
fn assumptions_with_input_independent_recursion_do_not_enumerate_irrelevant_inputs() {
    let mut text = (0..32)
        .map(|n| format!("input i{n}();"))
        .collect::<String>();
    text.push_str("relation p();relation q();p():-!q();q():-!p();relation valid();valid():-p();valid():-q();assumption a:at_least_one(valid,group_by:());");
    text.push_str(&verification(""));
    let p = loaded(&text);
    let e = engine(&p, "v");
    let r = e
        .check(
            &p.keys,
            &CheckOptions {
                max_worlds: 1,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(r.assumptions[0].certified());
    assert!(!r.is_incomplete());
}

#[test]
fn provider_cutoff_never_guesses_an_eligible_tuple_set() {
    let p = loaded(
        "relation eligible();eligible();input raw() within eligible;verification v{semantics:completion;decisions:[raw];assumptions:[];obligations:[];}",
    );
    let v = p.corpus.verifications().next().unwrap().id;
    for max_solves in [0, 1] {
        let Preparation::InputDomains(issues) = Engine::prepare(
            &p.corpus,
            &p.domains,
            &p.keys,
            v,
            &Limits::default(),
            QueryLimits {
                max_solves,
                ..Default::default()
            },
        )
        .unwrap() else {
            panic!()
        };
        assert!(matches!(
            issues[0].failure,
            InputDomainFailure::Inconclusive(_)
        ));
        let shown = presentation::completion_input_domain_failure(&p, v, &issues).unwrap();
        assert_eq!(shown.status["hasFailures"], false);
        assert_eq!(shown.status["incomplete"], true);
    }
}
#[test]
fn domain_and_provider_edits_rebuild_contracts_and_fresh_matches_repeated() {
    let text = "sort S;const a,b:S;relation eligible(x:S);eligible(a);eligible(X):-eligible(X);input raw(x:S) within eligible;obligation o:empty(raw);verification v{semantics:completion;decisions:[];assumptions:[];obligations:[o];}";
    for edit in [
        "domain S=[a];",
        "domain S=[a,b];",
        "domain S=[a,b];eligible(b);",
        "domain S=[a];",
    ] {
        let p = loaded(&format!("{text}{edit}"));
        for _ in 0..2 {
            match prepare(&p, "v") {
                Preparation::Ready(e) => {
                    assert_ne!(edit, "domain S=[a,b];");
                    let r = e.check(&p.keys, &Default::default()).unwrap();
                    assert!(!r.is_incomplete());
                    assert!(r.obligations.values().all(|o| o.failed()));
                }
                Preparation::InputDomains(issues) => {
                    assert_eq!(edit, "domain S=[a,b];");
                    assert!(matches!(
                        issues[0].failure,
                        InputDomainFailure::Ambiguous(_)
                    ));
                }
                _ => panic!(),
            }
        }
    }
}
#[test]
fn unused_bounded_input_is_unknown_in_models_and_refused_by_world_queries() {
    let p = loaded(
        "relation eligible();eligible():-eligible();input raw() within eligible;relation h();h();verification v{semantics:completion;hypothesis:h;decisions:[];assumptions:[];obligations:[];}",
    );
    let e = engine(&p, "v");
    let raw = input(&p, "raw");
    let ObservationOutcome::Accepted { classification, .. } = e.observation([]).unwrap() else {
        panic!()
    };
    assert_eq!(classification.value(&raw), None);
    assert!(
        classification
            .omitted_input_relations()
            .contains(&raw.relation)
    );
    assert!(
        e.worlds(&WorldQuery {
            pins: vec![(raw, true)],
            ..Default::default()
        })
        .is_err()
    );
}
