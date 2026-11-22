use denotate_check::{CompletionSizes, Limits, completion_query::*};
use denotate_ir_text::*;
fn loaded(text: &str) -> LoadedProgram {
    let s = SourceFile::new("file:///sizes.den", 1, text);
    load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap()
}
fn prepare(p: &LoadedProgram, limits: &Limits) -> Preparation {
    Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().next().unwrap().id,
        limits,
        Default::default(),
    )
    .unwrap()
}
const V: &str = "verification v{semantics:completion;decisions:[];assumptions:[];obligations:[];}";
#[test]
fn separates_seeded_and_circular_support_without_changing_meaning() {
    let p = loaded(&format!(
        "sort S;const a,b,c:S;relation loop(s:S);loop(X):-loop(X);loop(a);relation consumer(s:S);consumer(X):-loop(X);relation impossible();impossible();relation neg();neg():-!impossible();{V}"
    ));
    let sink = CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let Preparation::Ready(e) = prepare(&p, &limits) else {
        panic!()
    };
    let measured = e.check(&p.keys, &Default::default()).unwrap();
    let Preparation::Ready(plain) = prepare(&p, &Limits::default()) else {
        panic!()
    };
    let plain = plain.check(&p.keys, &Default::default()).unwrap();
    assert_eq!(
        denotate_presentation::completion_summary(&p.corpus, &p.keys, &measured).unwrap(),
        denotate_presentation::completion_summary(&p.corpus, &p.keys, &plain).unwrap()
    );
    let stats = sink.snapshot();
    let prep = stats.preparations.last().unwrap();
    assert!(prep.complete && prep.least_complete);
    for name in ["loop", "consumer"] {
        let r = p.corpus.relations().find(|r| r.name == name).unwrap();
        let row = &prep.relations[&r.id];
        assert_eq!(row.observed, 3);
        assert_eq!(row.least, 1);
        assert_eq!(row.circular, Some(2));
        let example = row.example.as_ref().unwrap();
        assert_ne!(p.corpus.constant(example.arguments[0]).unwrap().name, "a");
    }
    let neg = p.corpus.relations().find(|r| r.name == "neg").unwrap();
    assert_eq!(
        prep.relations[&neg.id].least, 1,
        "possibility ignores negation, unlike semantic truth"
    );
    assert!(
        stats
            .searches
            .iter()
            .any(|s| s.phase == "completion processing ambiguity" && s.encodings > 0)
    );
    assert!(
        stats
            .searches
            .iter()
            .all(|s| s.variables > 0 && s.clauses > 0)
    );
    let json = denotate_presentation::completion_sizes(&p.keys, &stats).unwrap();
    assert!(json["preparations"][0]["positiveRelationComponents"].is_array());
}
#[test]
fn cutoff_keeps_partial_round_counts_without_claiming_a_final_gfp() {
    let p = loaded(&format!(
        "sort S;const a,b,c,d,e,f:S;relation loop(s:S);loop(X):-loop(X);{V}"
    ));
    let sink = CompletionSizes::default();
    let limits = Limits {
        max_atoms: 3,
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    assert!(matches!(prepare(&p, &limits), Preparation::Inconclusive(_)));
    let stats = sink.snapshot();
    let prep = stats.preparations.last().unwrap();
    assert!(!prep.complete);
    assert!(prep.error.is_some());
    assert!(prep.peak_possibility_atoms > limits.max_atoms);
    assert!(prep.work_by_stage["possibility"] > 0);
    assert_eq!(prep.work, prep.work_by_stage.values().sum::<usize>());
    let row = prep.relations.values().find(|r| r.observed > 0).unwrap();
    assert!(!row.fixed);
    assert!(row.example.is_some());
    let json = denotate_presentation::completion_sizes(&p.keys, &stats).unwrap();
    assert!(json["preparations"][0]["error"].is_string());
    assert!(json["preparations"][0]["work"].as_u64().unwrap() > 0);
    let row = &json["preparations"][0]["relations"][0];
    assert_eq!(row["state"], "partial-round");
    assert!(row["circularOnly"].is_null());
}
#[test]
fn cnf_cutoff_keeps_the_partial_encoding() {
    let p = loaded(&format!(
        "input a();input b();input c();input d();relation h();h():-a();{V}"
    ));
    let sink = CompletionSizes::default();
    let limits = Limits {
        max_atoms: 6,
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let Preparation::Ready(e) = prepare(&p, &limits) else {
        panic!()
    };
    let report = e.check(&p.keys, &Default::default()).unwrap();
    assert!(report.is_incomplete());
    let stats = sink.snapshot();
    assert!(
        stats
            .searches
            .iter()
            .any(|s| s.variables > 0 && s.encodings > 0)
    );
    assert!(
        stats
            .searches
            .iter()
            .any(|s| { s.encoding_details.iter().any(|e| !e.complete) })
    );
}
#[test]
fn measurements_are_per_invocation_not_cached_or_shared_implicitly() {
    let p = loaded(&format!("relation a();a();{V}"));
    let sink = CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let Preparation::Ready(e) = prepare(&p, &limits) else {
        panic!()
    };
    e.check(&p.keys, &Default::default()).unwrap();
    let before = sink.snapshot();
    e.check(&p.keys, &Default::default()).unwrap();
    let after = sink.snapshot();
    assert_eq!(before.preparations.len(), after.preparations.len());
    assert!(after.searches.len() > before.searches.len());
    let fresh = CompletionSizes::default();
    assert!(fresh.snapshot().searches.is_empty());
}

#[test]
fn incomplete_least_analysis_does_not_label_unseen_support_circular() {
    let p = loaded(&format!(
        "sort S;const a,b,c,d,e,f:S;relation seeded(s:S);seeded(a);seeded(b);seeded(c);seeded(d);seeded(e);seeded(f);{V}"
    ));
    let sink = CompletionSizes::default();
    let limits = Limits {
        max_atoms: 3,
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    assert!(matches!(prepare(&p, &limits), Preparation::Inconclusive(_)));
    let stats = sink.snapshot();
    let prep = stats.preparations.last().unwrap();
    assert!(!prep.least_complete);
    assert!(prep.least_error.is_some());
    let data = denotate_presentation::completion_sizes(&p.keys, &stats).unwrap();
    for row in data["preparations"][0]["relations"].as_array().unwrap() {
        assert!(row["circularOnly"].is_null());
        assert_eq!(row["leastCountKind"], "at-least");
    }
}

#[test]
fn empty_eligible_inputs_have_exact_zero_circular_support() {
    let p = loaded(
        "relation eligible();input raw() within eligible;obligation absent:empty(raw);verification v{semantics:completion;decisions:[];assumptions:[];obligations:[absent];}",
    );
    let raw = p.corpus.relations().find(|r| r.name == "raw").unwrap().id;
    let sink = CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let Preparation::Ready(_) = prepare(&p, &limits) else {
        panic!()
    };
    let snapshot = sink.snapshot();
    assert!(!snapshot.preparations.is_empty());
    for prep in snapshot.preparations {
        let row = &prep.relations[&raw];
        assert!(row.fixed && prep.least_complete);
        assert_eq!(row.observed, 0);
        assert_eq!(row.least, 0);
        assert_eq!(row.circular, Some(0));
    }
}

#[test]
fn anchored_descent_avoids_the_old_transient_product_at_default_and_tight_limits() {
    let constants = (0..32)
        .map(|i| format!("v{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let p = loaded(&format!(
        "sort S;const {constants}:S;relation anchor(x:S,y:S);anchor(v0,v0);relation p(x:S,y:S);relation q(x:S,y:S);p(X,Y):-q(X,Y);q(X,Y):-p(X,Y),anchor(X,Y);{V}"
    ));
    for max_atoms in [100_000, 100] {
        let sink = CompletionSizes::default();
        let limits = Limits {
            max_atoms,
            completion_sizes: Some(sink.clone()),
            ..Default::default()
        };
        let result = prepare(&p, &limits);
        let sizes = sink.snapshot();
        let prep = sizes.preparations.last().unwrap();
        assert!(matches!(result, Preparation::Ready(_)));
        assert!(prep.peak_possibility_atoms < 100);
        assert!(prep.atoms < 100);
        assert!(prep.work > 0);
        assert_eq!(prep.work, prep.work_by_stage.values().sum::<usize>());
    }
}

#[test]
fn world_encoding_does_not_copy_unrelated_facts_for_each_input_assumption() {
    let mut observations = Vec::new();
    for facts in [0, 1000] {
        let facts = (0..facts)
            .map(|i| format!("relation fact{i}();fact{i}();"))
            .collect::<String>();
        let assumptions = (0..6)
            .map(|i| format!("assumption a{i}:empty(raw);"))
            .collect::<String>();
        let p = loaded(&format!(
            "input raw();{facts}{assumptions}verification v{{semantics:completion;decisions:[];assumptions:[a0,a1,a2,a3,a4,a5];obligations:[];}}"
        ));
        let sink = CompletionSizes::default();
        let limits = Limits {
            completion_sizes: Some(sink.clone()),
            ..Default::default()
        };
        let Preparation::Ready(e) = prepare(&p, &limits) else {
            panic!()
        };
        assert!(matches!(
            e.worlds(&WorldQuery::default()).unwrap(),
            WorldAnswer::World(_)
        ));
        let stats = sink.snapshot();
        let world = stats
            .searches
            .iter()
            .find(|s| s.phase == "completion worlds")
            .unwrap();
        assert!(
            world
                .encoding_details
                .iter()
                .all(|e| e.purpose == "input-universe")
        );
        observations.push((world.encodings, world.variables, world.clauses));
    }
    assert_eq!(
        observations[0], observations[1],
        "W must not scale with facts outside its scope"
    );
}

#[test]
fn sparse_recursive_static_provider_and_runtime_both_avoid_full_products() {
    let constants = (0..400)
        .map(|i| format!("v{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let p = loaded(&format!(
        "sort S;const {constants}:S;relation anchor(x:S,y:S);anchor(v0,v0);relation p(x:S,y:S);relation q(x:S,y:S);p(X,Y):-q(X,Y);q(X,Y):-p(X,Y),anchor(X,Y);q(X,Y):-anchor(X,Y);input raw(x:S,y:S) within p;relation used(x:S,y:S);used(X,Y):-raw(X,Y);{V}"
    ));
    let sink = CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let Preparation::Ready(e) = prepare(&p, &limits) else {
        panic!("{:?}", sink.snapshot());
    };
    let plain = prepare(&p, &Limits::default());
    assert!(matches!(plain, Preparation::Ready(_)));
    assert!(matches!(
        e.worlds(&WorldQuery::default()).unwrap(),
        WorldAnswer::World(_)
    ));
    let stats = sink.snapshot();
    assert!(stats.preparations.iter().any(|p| p.static_provider));
    assert!(stats.preparations.iter().any(|p| !p.static_provider));
    for prep in &stats.preparations {
        assert!(prep.complete, "{prep:?}");
        assert!(
            prep.peak_possibility_atoms < 400,
            "never materialize the 400 by 400 product"
        );
        assert!(prep.work > 0);
        assert_eq!(prep.work, prep.work_by_stage.values().sum::<usize>());
    }
}

#[test]
fn reverse_declared_provider_chain_uses_indexed_scope_discovery() {
    let n = 5000;
    let declarations = (0..=n)
        .map(|i| format!("relation p{i}();"))
        .collect::<String>();
    let rules = (0..n)
        .rev()
        .map(|i| format!("p{i}():-p{}();", i + 1))
        .collect::<String>();
    let p = loaded(&format!(
        "{declarations}{rules}p{n}();input raw() within p0;relation used();used():-raw();{V}"
    ));
    let sink = CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    assert!(matches!(prepare(&p, &limits), Preparation::Ready(_)));
    let stats = sink.snapshot();
    let provider = stats
        .preparations
        .iter()
        .find(|s| s.static_provider)
        .unwrap();
    assert!(provider.complete && provider.provider.is_some());
    assert!(provider.work_by_stage["provider-scope"] > 0);
}
