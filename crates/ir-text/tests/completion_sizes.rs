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
    let sink = CompletionSizes::with_least_analysis();
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
    let sink = CompletionSizes::with_least_analysis();
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
    // A property still needs an encoding; empty decisions no longer build an
    // otherwise unused pair merely to prove determinacy.
    let p = loaded(
        "input a();input b();input c();input d();relation h();h():-a();obligation none:empty(h);verification v{semantics:completion;decisions:[];assumptions:[];obligations:[none];}",
    );
    let sink = CompletionSizes::with_least_analysis();
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
    let sink = CompletionSizes::with_least_analysis();
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
    let fresh = CompletionSizes::with_least_analysis();
    assert!(fresh.snapshot().searches.is_empty());
}

#[test]
fn incomplete_least_analysis_does_not_label_unseen_support_circular() {
    let p = loaded(&format!(
        "sort S;const a,b,c,d,e,f:S;relation seeded(s:S);seeded(a);seeded(b);seeded(c);seeded(d);seeded(e);seeded(f);{V}"
    ));
    let sink = CompletionSizes::with_least_analysis();
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
    let sink = CompletionSizes::with_least_analysis();
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
        let sink = CompletionSizes::with_least_analysis();
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
        let sink = CompletionSizes::with_least_analysis();
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
    let sink = CompletionSizes::with_least_analysis();
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
    let sink = CompletionSizes::with_least_analysis();
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

#[test]
fn preparation_work_covers_common_provider_and_runtime_stages() {
    let constants = (0..2000)
        .map(|i| format!("v{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let facts = (0..2000)
        .map(|i| format!("candidate(v{i});"))
        .collect::<String>();
    let providers = (0..4).map(|i| format!("relation p{i}(x:S);p{i}(X):-candidate(X);input raw{i}(x:S) within p{i};relation use{i}(x:S);use{i}(X):-raw{i}(X);")).collect::<String>();
    let p = loaded(&format!(
        "sort S;const {constants}:S;relation candidate(x:S);{facts}{providers}{V}"
    ));
    let sink = CompletionSizes::with_least_analysis();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    assert!(matches!(prepare(&p, &limits), Preparation::Ready(_)));
    let stats = sink.snapshot();
    let work = stats.preparation_work.as_ref().unwrap();
    assert_eq!(work.work, work.by_stage.values().sum::<usize>());
    assert_eq!(work.work, work.by_phase.values().sum::<usize>());
    assert!(work.rejected_by_phase.is_empty());
    for stage in [
        "domains",
        "original-dependencies",
        "input-structure",
        "input-scope",
        "provider-scope",
        "provider-grounding",
        "provider-query",
        "runtime-grounding",
        "runtime-engine",
    ] {
        assert!(work.by_stage[stage] > 0, "{stage}");
    }
    let provider_work: usize = stats
        .preparations
        .iter()
        .filter(|p| p.static_provider)
        .map(|p| p.work)
        .sum();
    assert_eq!(
        provider_work,
        work.by_stage["provider-grounding"]
            + stats
                .preparations
                .iter()
                .map(|p| p.work_by_stage.get("provider-scope").copied().unwrap_or(0))
                .sum::<usize>()
    );
    assert_eq!(
        stats.preparations.last().unwrap().work,
        work.by_stage["runtime-grounding"]
    );
    let json = denotate_presentation::completion_sizes(&p.keys, &stats).unwrap();
    assert_eq!(
        json["preparationWork"]["work"].as_u64().unwrap() as usize,
        work.work
    );
    eprintln!(
        "four sparse providers: work {}, stages {:?}",
        work.work, work.by_stage
    );
}

#[test]
fn preparation_work_survives_exhaustion_before_the_first_attempt() {
    let p = loaded(&format!("sort S;const a,b:S;relation r(x:S);r(a);{V}"));
    let sink = CompletionSizes::with_least_analysis();
    let limits = Limits {
        max_work: 1,
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    assert!(matches!(prepare(&p, &limits), Preparation::Inconclusive(_)));
    let stats = sink.snapshot();
    assert!(stats.preparations.is_empty());
    let work = stats.preparation_work.as_ref().unwrap();
    assert_eq!(work.work, work.by_phase.values().sum::<usize>());
    assert_eq!(work.work, work.by_stage.values().sum::<usize>());
    assert_eq!(work.last_stage, "domains");
    assert!(!work.rejected_by_phase.is_empty());
    let json = denotate_presentation::completion_sizes(&p.keys, &stats).unwrap();
    assert_eq!(json["preparationWork"]["lastStage"], "domains");
}

#[test]
fn selective_bound_join_avoids_disconnected_cartesian_prefix() {
    let n = 3000;
    let constants = (0..n)
        .map(|i| format!("v{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let facts = (0..n)
        .map(|i| {
            format!(
                "left(v{i});right(v{i});edge(v{i},v{i});edge(v{i},v{});",
                (i + 1) % n
            )
        })
        .collect::<String>();
    for body in ["left(X),right(Y),edge(X,Y)", "edge(X,Y),right(Y),left(X)"] {
        let p = loaded(&format!(
            "sort S;const {constants}:S;relation left(x:S);relation right(x:S);relation edge(x:S,y:S);{facts}relation joined(x:S,y:S);joined(X,Y):-{body};{V}"
        ));
        let sink = CompletionSizes::default();
        let limits = Limits {
            completion_sizes: Some(sink.clone()),
            ..Default::default()
        };
        let Preparation::Ready(e) = prepare(&p, &limits) else {
            panic!("selective join must finish at defaults")
        };
        let r = p
            .corpus
            .relations()
            .find(|r| r.name == "joined")
            .unwrap()
            .id;
        let tuples: std::collections::BTreeSet<_> = e
            .original_program()
            .rules()
            .filter(|r0| r0.head.atom.relation == r)
            .map(|r| r.head.atom.arguments.clone())
            .collect();
        assert_eq!(tuples.len(), n * 2);
        let stats = sink.snapshot();
        assert!(!stats.preparations[0].least_enabled);
        assert!(stats.preparations[0].least_error.is_none());
        assert!(!stats.preparations[0].components.is_empty());
        let w = stats.preparation_work.as_ref().unwrap();
        assert_eq!(w.work, w.by_phase.values().sum::<usize>());
        assert_eq!(w.work, w.by_stage.values().sum::<usize>());
        assert!(!w.join_rules.is_empty());
        let json = denotate_presentation::completion_sizes(&p.keys, &stats).unwrap();
        assert!(
            !json["preparationWork"]["topJoinRules"]
                .as_array()
                .unwrap()
                .is_empty()
        );
        eprintln!(
            "selective join {body}: total work {}, join phases {:?}",
            w.work,
            w.by_phase
                .iter()
                .filter(|(k, _)| k.contains("join"))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn diagnostic_lfp_is_explicit_and_never_changes_prepared_rules_or_work() {
    let p = loaded(&format!(
        "sort S;const a,b:S;input i(s:S);relation p(s:S);p(X):-p(X);p(a):-i(a);{V}"
    ));
    let mut results = Vec::new();
    for sink in [
        CompletionSizes::default(),
        CompletionSizes::with_least_analysis(),
    ] {
        let limits = Limits {
            completion_sizes: Some(sink.clone()),
            ..Default::default()
        };
        let Preparation::Ready(e) = prepare(&p, &limits) else {
            panic!()
        };
        let snapshot = sink.snapshot();
        let prep = &snapshot.preparations[0];
        assert_eq!(prep.least_enabled, sink.least_analysis_enabled());
        assert_eq!(prep.least_complete, sink.least_analysis_enabled());
        let input = p.corpus.relations().find(|r| r.name == "i").unwrap().id;
        assert_eq!(prep.relations[&input].observed, 2);
        let work = snapshot.preparation_work.unwrap();
        results.push((
            e.original_program().atoms().cloned().collect::<Vec<_>>(),
            work.work,
            work.by_phase,
        ));
    }
    assert_eq!(results[0], results[1]);
}

#[test]
fn shrinking_reader_rejoins_are_counted_and_remain_bounded_on_sparse_cycle() {
    let constants = (0..2000)
        .map(|i| format!("v{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let p = loaded(&format!(
        "sort S;const {constants}:S;relation anchor(x:S);anchor(v0);relation p(x:S);relation q(x:S);relation r(x:S);p(X):-q(X);q(X):-r(X);r(X):-p(X),anchor(X);{V}"
    ));
    let sink = CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let Preparation::Ready(e) = prepare(&p, &limits) else {
        panic!()
    };
    for name in ["p", "q", "r"] {
        let relation = p.corpus.relations().find(|r| r.name == name).unwrap().id;
        assert_eq!(
            e.original_program()
                .atoms()
                .filter(|a| a.relation == relation)
                .count(),
            1
        );
    }
    let snapshot = sink.snapshot();
    let work = snapshot.preparation_work.unwrap();
    assert!(
        work.join_rules
            .iter()
            .any(|((_, stage), r)| *stage == "runtime-grounding" && r.calls > 0)
    );
    eprintln!(
        "sparse cycle reader re-joins: {:?}",
        work.join_rules
            .values()
            .map(|r| (r.calls, r.work))
            .collect::<Vec<_>>()
    );
}

#[test]
fn existence_reports_odd_cores_and_cumulative_work_separately_from_validation() {
    let p = loaded(
        "input guard(); relation conflict(); conflict():-guard(),!conflict(); relation h(); h():-!conflict(); verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[];}",
    );
    let sink = CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let Preparation::Ready(e) = prepare(&p, &limits) else {
        panic!()
    };
    let r = e.check(&p.keys, &Default::default()).unwrap();
    assert!(r.classification.as_ref().unwrap().no_meaning.exists());
    let stats = sink.snapshot();
    let json = denotate_presentation::completion_sizes(&p.keys, &stats).unwrap();
    let search = json["searches"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["phase"] == "completion classification existence")
        .unwrap();
    let components = search["existence"]["componentDetails"].as_array().unwrap();
    assert!(components.iter().any(|c| c["oddComponents"] == 1
        && c["state"] == "requires-upstream-search"
        && c["boundary"] == 1
        && c["relations"].to_string().contains("conflict")));
    let sum: u64 = search["workByPhase"]
        .as_object()
        .unwrap()
        .values()
        .map(|n| n.as_u64().unwrap())
        .sum();
    assert_eq!(search["work"], sum);
    assert!(
        search["workByPhase"]["completion call consistency"]
            .as_u64()
            .unwrap()
            > 0
    );
    // Candidate limit is reporting only: retain the current component on cutoff.
    let partial = e
        .check(
            &p.keys,
            &CheckOptions {
                max_worlds: 0,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(matches!(
        partial.classification.unwrap().no_meaning,
        Search::Inconclusive(_)
    ));
    let json = denotate_presentation::completion_sizes(&p.keys, &sink.snapshot()).unwrap();
    assert!(
        json["searches"]
            .as_array()
            .unwrap()
            .iter()
            .any(|s| s["phase"] == "completion classification existence"
                && s["existence"]["currentComponent"]["state"] == "incomplete")
    );
}

#[test]
fn determinacy_reports_component_queries_before_solving_and_keeps_their_scope() {
    use std::sync::{Arc, Mutex};
    let p = loaded(
        "input i(); relation p(); p():-i(); p():-p(),i(); relation q(); q():-!p(); verification v{semantics:completion;decisions:[q];assumptions:[];obligations:[];}",
    );
    let sink = CompletionSizes::default();
    let events = Arc::new(Mutex::new(Vec::new()));
    let out = events.clone();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        progress: denotate_check::CheckingProgress::new(move |e| {
            if let Some(denotate_check::CheckingTarget::CompletionExistence(s)) = e.target {
                if let Some(c) = s.current_component {
                    if !c.query.is_empty() {
                        out.lock().unwrap().push(c);
                    }
                }
            }
        }),
        ..Default::default()
    };
    let Preparation::Ready(e) = prepare(&p, &limits) else {
        panic!()
    };
    let r = e.check(&p.keys, &Default::default()).unwrap();
    assert!(matches!(r.meaning.ambiguous, Search::None));
    let events = events.lock().unwrap();
    let solving = events
        .iter()
        .position(|c| c.query == "local-uniqueness" && c.state == "solving")
        .unwrap();
    let unique = events
        .iter()
        .position(|c| c.query == "local-uniqueness" && c.state == "unique")
        .unwrap();
    assert!(solving < unique);
    assert!(events[solving].variables > 0 && events[solving].clauses > 0);
    let json = denotate_presentation::completion_sizes(&p.keys, &sink.snapshot()).unwrap();
    let search = json["searches"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["phase"] == "completion processing ambiguity")
        .unwrap();
    let details = search["existence"]["componentDetails"].as_array().unwrap();
    assert!(details.iter().any(|c| c["query"] == "local-uniqueness"
        && c["state"] == "unique"
        && c["oddComponents"].is_null()));
    assert!(search["existence"]["sharedAtoms"].as_u64().unwrap() > 0);
    assert!(search["existence"]["uniqueComponents"].as_u64().unwrap() > 0);
    let sum: u64 = search["workByPhase"]
        .as_object()
        .unwrap()
        .values()
        .map(|v| v.as_u64().unwrap())
        .sum();
    assert_eq!(search["work"], sum);
}
