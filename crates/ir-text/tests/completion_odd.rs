use denotate_check::{CompletionSizes, Limits, completion_query::*};
use denotate_ir_text::*;
use std::sync::{Arc, Mutex};

const SOURCE: &str = "sort S; const a,b:S;
input choice(s:S) at_most_one(group_by:());
relation admitted();
admitted() :- choice(a);
relation left();
relation right();
relation odd();
left() :- !right();
right() :- !left();
left() :- odd();
odd() :- !left(), admitted();
odd() :- !left(), admitted();
verification v { semantics:completion; assumptions:[]; obligations:[]; }
";
fn loaded() -> LoadedProgram {
    let s = SourceFile::new("file:///odd.den", 1, SOURCE);
    load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap()
}
fn prepare(p: &LoadedProgram, limits: &Limits) -> Engine {
    let Preparation::Ready(e) = Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().next().unwrap().id,
        limits,
        Default::default(),
    )
    .unwrap() else {
        panic!()
    };
    e
}
#[test]
fn explains_actual_odd_cycle_sources_alternatives_and_derived_guard_group_before_search() {
    let p = loaded();
    let sink = CompletionSizes::default();
    let events = Arc::new(Mutex::new(Vec::new()));
    let observed = events.clone();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        progress: denotate_check::CheckingProgress::new(move |event| {
            if let Some(denotate_check::CheckingTarget::CompletionExistence(s)) = event.target {
                if let Some(c) = s.current_component {
                    observed.lock().unwrap().push(c);
                }
            }
        }),
        ..Default::default()
    };
    let e = prepare(&p, &limits);
    let options = CheckOptions {
        max_worlds: 0,
        ..Default::default()
    };
    let report = e.check(&p.keys, &options).unwrap();
    let shape = events
        .lock()
        .unwrap()
        .iter()
        .find(|c| c.state == "searching" && c.odd_explanation.is_some())
        .cloned()
        .expect("explanation before SAT/cube exhaustion");
    let explanation = shape.odd_explanation.unwrap();
    assert!(!explanation.cycles.is_empty());
    for cycle in &explanation.cycles {
        assert_eq!(cycle.iter().filter(|e| e.negative).count() % 2, 1);
        for (i, edge) in cycle.iter().enumerate() {
            assert_eq!(edge.to, cycle[(i + 1) % cycle.len()].from);
            for producer in &edge.producers {
                let r = p.corpus.rule(producer.source.unwrap()).unwrap();
                assert_eq!(r.head.relation(), edge.from.relation);
                assert!(
                    r.body
                        .iter()
                        .any(|l| l.atom().relation() == edge.to.relation
                            && matches!(l, denotate_ir::Literal::Negative(_)) == edge.negative)
                );
            }
        }
    }
    let value = completion_output::explanations(&p)(&explanation).unwrap();
    assert_eq!(value["cycleCountKind"], "lower-bound");
    let all_edges = value["cycles"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|c| c.as_array().unwrap())
        .collect::<Vec<_>>();
    let guarded = all_edges.iter().find(|e| e["from"] == "odd()").unwrap();
    assert_eq!(guarded["producerCount"], 2);
    let lines = guarded["producers"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p["source"]["location"]["line"].as_u64().unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(lines, std::collections::BTreeSet::from([11, 12]));
    assert!(
        guarded["producers"]
            .as_array()
            .unwrap()
            .iter()
            .all(|p| p["guards"][0]["atom"] == "admitted()")
    );
    assert!(
        value["inputGroups"]
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r["group"]["relation"] == "choice" && r["group"]["declared"] == true)
    );
    let human = completion_output::odd_lines(&value).join("\n");
    assert!(human.contains("file:///odd.den:11:"));
    assert!(human.contains("--negative-->"));
    assert!(human.contains("ALL alternative producers"));
    let sizes = completion_output::sizes(&p, &sink.snapshot())
        .unwrap()
        .to_string();
    assert!(sizes.contains("oddExplanation") && sizes.contains("file:///odd.den"));
    // Plain, repeated and freshly prepared checks agree; telemetry never becomes a finding.
    let summary =
        |r: &Report| denotate_presentation::completion_summary(&p.corpus, &p.keys, r).unwrap();
    assert_eq!(
        summary(&report),
        summary(&e.check(&p.keys, &options).unwrap())
    );
    assert_eq!(
        summary(&report),
        summary(
            &prepare(&p, &Limits::default())
                .check(&p.keys, &options)
                .unwrap()
        )
    );
}
#[test]
fn even_loop_has_no_odd_explanation() {
    let s = SourceFile::new(
        "file:///even.den",
        1,
        "relation a();relation b();a():-!b();b():-!a();verification v{semantics:completion;assumptions:[];obligations:[];}",
    );
    let p = load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap();
    let sink = CompletionSizes::default();
    prepare(
        &p,
        &Limits {
            completion_sizes: Some(sink.clone()),
            ..Default::default()
        },
    )
    .check(&p.keys, &Default::default())
    .unwrap();
    assert!(
        sink.snapshot()
            .searches
            .iter()
            .flat_map(|s| &s.existence.component_details)
            .all(|c| c.odd_explanation.is_none())
    );
}

#[test]
fn every_component_record_identifies_its_scope_graph_context_and_view() {
    let source = SOURCE
        .replace(
            "semantics:completion;",
            "semantics:completion; hypothesis:left;",
        )
        .replace(
            "verification v",
            "relation independent(); independent() :- independent(); verification v",
        );
    let file = SourceFile::new("file:///contexts.den", 1, source);
    let p = load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap();
    for prune in [false, true] {
        let sink = CompletionSizes::default();
        let e = prepare(
            &p,
            &Limits {
                completion_sizes: Some(sink.clone()),
                ..Default::default()
            },
        );
        e.check(
            &p.keys,
            &CheckOptions {
                prune,
                ..Default::default()
            },
        )
        .unwrap();
        let snapshot = sink.snapshot();
        let records: Vec<_> = snapshot
            .searches
            .iter()
            .flat_map(|s| {
                s.existence
                    .component_details
                    .iter()
                    .chain(s.existence.current_component.iter())
            })
            .collect();
        assert!(!records.is_empty());
        for c in &records {
            assert!(matches!(c.scope, "classification" | "processing"));
            assert!(matches!(c.context, "W" | "W + H"));
            assert!(matches!(c.view, "pruned" | "unpruned"));
            if c.query == "hypothesis-model-coverage" {
                assert_eq!(
                    (c.scope, c.context, c.view),
                    (
                        "classification",
                        "W",
                        if prune { "pruned" } else { "unpruned" }
                    ),
                    "H-first shape records describe the W graph, not its H-pruned solver"
                );
            } else {
                assert_eq!(c.view, if prune { "pruned" } else { "unpruned" });
            }
        }
        assert!(records.iter().any(|c| c.context == "W"));
        assert!(records.iter().any(|c| c.context == "W + H"));
        let json = completion_output::sizes(&p, &snapshot).unwrap();
        assert!(
            json["searches"]
                .as_array()
                .unwrap()
                .iter()
                .flat_map(|s| s["existence"]["componentDetails"].as_array().unwrap())
                .all(|c| c["scope"].as_str().is_some_and(|s| !s.is_empty()))
        );
    }
}
