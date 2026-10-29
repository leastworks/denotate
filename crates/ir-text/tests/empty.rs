use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::top_level;
use denotate_ir_text::origins::{SourceIdentity, content_hash};
use denotate_ir_text::*;
use denotate_presentation::{Identity, Kind};
mod support;

fn load_text(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
const V: &str = "verification checks { assumptions: []; obligations: [one]; }";
fn run(
    p: &LoadedProgram,
    session: &mut Session,
    limits: &Limits,
) -> (ScopedResults, presentation::Presentation) {
    let ops = OperationalLimits::from(limits);
    let request = p.verification_requests(limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!("preparation incomplete")
    };
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
        panic!("checking incomplete")
    };
    let output = presentation::present(p, &report.checked).unwrap();
    assert_eq!(
        report.checked.verification.all_obligations_proved(),
        output.status["state"] == "proved"
    );
    (report.checked.results.value, output)
}
fn check(text: &str) -> (ScopedResults, presentation::Presentation) {
    run(
        &load_text(text),
        &mut Session::default(),
        &Limits::default(),
    )
}
#[test]
fn empty_relations_zero_arity_inputs_recursion_and_duplicate_derivations() {
    for (body, proved) in [
        ("sort S; relation p(x:S);", true),
        ("sort S; const a,b:S; relation p(x:S);", true),
        ("relation p();", true),
        ("relation p(); p(); p();", false),
        ("sort S; const a,b:S; input p(x:S);", false),
        ("sort S; const a,b:S; domain S=[]; input p(x:S);", true),
        ("relation p(); relation q(); p() :- q(); q() :- p();", true),
        (
            "relation p(); relation q(); p() :- q(); q() :- p(); q();",
            false,
        ),
    ] {
        let (r, out) = check(&format!("{body} obligation one: empty(p); {V}"));
        let e = r.emptiness.values().next().unwrap();
        assert!(e.complete(), "{body}");
        assert_eq!(e.proved(), proved, "{body}");
        assert!(r.groups.is_empty() && r.group_domains.is_empty() && r.coverage.is_empty());
        assert_eq!(out.status["state"] == "proved", proved);
        let diagnostics: Vec<_> = out
            .diagnostics
            .iter()
            .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
            .collect();
        assert_eq!(diagnostics.is_empty(), proved);
        assert!(
            diagnostics
                .iter()
                .all(|d| d.identity == diagnostics[0].identity)
        );
        if let Some(d) = diagnostics.first() {
            assert_eq!(d.evidence["kind"], "replayed-counterexample");
            assert_eq!(
                d.evidence["examples"].as_array().unwrap().len(),
                e.examples.len()
            );
            assert_eq!(d.evidence["component"], "emptiness");
        }
    }
}

#[test]
fn independent_small_world_oracle_and_replayed_presence_cold_warm_and_global() {
    for formula in 0..5 {
        for constrained in [false, true] {
            let rules = match formula {
                0 => "p(X) :- i(X);",
                1 => "p(a) :- !i(a); p(b) :- !i(b);",
                2 => "p(a) :- i(a), i(b);",
                3 => "p(a) :- i(a), !i(a);",
                _ => "p(a) :- i(a), !i(b); p(b) :- i(b), !i(a);",
            };
            let truth = |w: usize| match formula {
                0 => [w & 1 != 0, w & 2 != 0],
                1 => [w & 1 == 0, w & 2 == 0],
                2 => [w == 3, false],
                3 => [false, false],
                _ => [w == 1, w == 2],
            };
            let worlds: Vec<_> = (0..4).filter(|w| !constrained || *w != 3).collect();
            let expected = worlds.iter().all(|w| truth(*w) == [false, false]);
            let p = load_text(&format!(
                "sort S; const a,b:S; input i(x:S); relation p(x:S); {rules} assumption allowed: at_most_one(i, group_by: ()); obligation one: empty(p); verification checks {{ assumptions: [{}]; obligations: [one]; }}",
                if constrained { "allowed" } else { "" }
            ));
            let mut session = Session::default();
            let (cold, _) = run(&p, &mut session, &Limits::default());
            let (warm, _) = run(&p, &mut session, &Limits::default());
            assert_eq!(cold, warm);
            let e = cold.emptiness.values().next().unwrap();
            assert!(e.complete());
            assert_eq!(e.proved(), expected);
            assert_eq!(
                e.present,
                (0..2)
                    .filter(|column| worlds.iter().any(|w| truth(*w)[*column]))
                    .count()
            );
            for e in &e.examples {
                let a = p
                    .keys
                    .constant(p.corpus.constants().find(|c| c.name == "a").unwrap().id)
                    .unwrap();
                let w = e
                    .observation
                    .present
                    .iter()
                    .fold(0, |w, atom| w | if &atom.arguments[0] == a { 1 } else { 2 });
                assert!(worlds.contains(&w));
                assert!(truth(w)[usize::from(&e.tuple.arguments[0] != a)]);
            }
            let limits = Limits::default();
            let ops = OperationalLimits::from(&limits);
            let request = p.verification_requests(&limits).unwrap().remove(0).1;
            let RequestPreparation::Complete(prepared) =
                request.prepare(&p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            let CheckOutcome::Complete(global) = prepared.verify(&ops).unwrap() else {
                panic!()
            };
            assert_eq!(global.verification.all_obligations_proved(), expected);
            for e in &global
                .verification
                .emptiness
                .values()
                .next()
                .unwrap()
                .examples
            {
                let replay = prepared
                    .program()
                    .evaluate(e.observation.present.iter().cloned(), &limits)
                    .unwrap();
                assert!(matches!(
                    replay.fact(&e.tuple).unwrap(),
                    FactState::Settled(true)
                ));
            }
        }
    }
}

#[test]
fn unresolved_worlds_are_not_presence_or_a_proof_and_do_not_erase_known_failure() {
    for (body, failure) in [
        ("relation p(); p() :- !p();", false),
        (
            "relation p(); relation q(); p() :- !q(); q() :- !p();",
            false,
        ),
        (
            "sort S; const a,b:S; relation p(x:S); p(a); p(b) :- !p(b);",
            true,
        ),
        // One relation tuple, present in i=true, unresolved in i=false.
        (
            "input i(); relation p(); relation q(); p() :- i(); p() :- !q(), !i(); q() :- !p(), !i();",
            true,
        ),
    ] {
        let p = load_text(&format!("{body} obligation one: empty(p); {V}"));
        let mut session = Session::default();
        let (r, out) = run(&p, &mut session, &Limits::default());
        assert_eq!(r, run(&p, &mut session, &Limits::default()).0);
        let e = r.emptiness.values().next().unwrap();
        assert!(e.unresolved, "{body}: {e:?}");
        assert!(!e.complete() && !e.proved());
        assert_eq!(e.present, usize::from(failure), "{body}");
        let d = out
            .diagnostics
            .iter()
            .find(|d| matches!(d.identity, Identity::Emptiness(_)))
            .unwrap();
        assert_eq!(
            d.kind,
            if failure {
                Kind::Counterexample
            } else {
                Kind::Inconclusive
            }
        );
        assert!(d.message.contains("incomplete"));
    }
}

#[test]
fn limits_never_prove_unknown_facts_and_preserve_earlier_presence() {
    let names = (0..20)
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let conjunction = (0..20)
        .map(|i| format!("i(a{i})"))
        .collect::<Vec<_>>()
        .join(",");
    for fact in ["", "p(a0);"] {
        let p = load_text(&format!(
            "sort S; const {names}:S; input i(x:S); relation p(x:S); {fact} p(a1) :- {conjunction}; obligation one: empty(p); {V}"
        ));
        let limits = Limits {
            max_bdd_nodes: 16,
            ..Limits::default()
        };
        let mut session = Session::default();
        let (r, _) = run(&p, &mut session, &limits);
        assert_eq!(r, run(&p, &mut session, &limits).0);
        let e = r.emptiness.values().next().unwrap();
        assert!(e.inconclusive.is_some() && !e.proved(), "{e:?}");
        assert_eq!(e.examples.first().is_some(), !fact.is_empty());
    }
    // A second case forces bounded enumeration of unresolved worlds while an
    // independent fact already refutes the obligation.
    let p = load_text(&format!(
        "sort S; const {names}:S; input i(x:S); relation p(x:S); p(a0); p(a1) :- !p(a1); obligation one: empty(p); {V}"
    ));
    let limits = Limits {
        max_work: 2000,
        ..Limits::default()
    };
    let (r, out) = run(&p, &mut Session::default(), &limits);
    let e = r.emptiness.values().next().unwrap();
    assert!(
        e.examples.first().is_some() && e.inconclusive.is_some(),
        "{e:?}"
    );
    assert!(!e.complete());
    assert_eq!(out.status["state"], "findings");
    assert_eq!(
        out.status["emptiness"][0]["presentTuples"],
        serde_json::json!({"count":e.present,"exact":false})
    );
    let d = out
        .diagnostics
        .iter()
        .find(|d| matches!(d.identity, Identity::Emptiness(_)))
        .unwrap();
    assert_eq!(
        d.evidence["presentTuples"],
        out.status["emptiness"][0]["presentTuples"]
    );
    assert!(d.message.contains("at least"));
}

#[test]
fn sessions_refresh_kind_selection_facts_and_domains_with_stable_finding_identity() {
    let mut session = Session::default();
    let mut identity = None;
    for (contract, selection, domain, facts, proved) in [
        ("at_most_one(p, group_by: ())", "", "", "", true),
        ("empty(p)", "", "", "", false),
        ("empty(p)", "allowed", "", "", true),
        ("empty(p)", "allowed", "", "p(a);", false),
        ("empty(p)", "", "", "", false),
    ] {
        let p = load_text(&format!(
            "sort S; const a,b:S; input i(x:S); relation p(x:S); p(a) :- i(a), i(b); {domain} {facts} assumption allowed: at_most_one(i, group_by: ()); obligation one: {contract}; verification checks {{ assumptions: [{selection}]; obligations: [one]; }}"
        ));
        let (warm, out) = run(&p, &mut session, &Limits::default());
        assert_eq!(warm, run(&p, &mut Session::default(), &Limits::default()).0);
        assert_eq!(out.status["state"] == "proved", proved);
        if let Some(d) = out
            .diagnostics
            .iter()
            .find(|d| matches!(d.identity, Identity::Emptiness(_)))
        {
            let key = d
                .identity
                .data_in(&p.keys, warm.context.verification.as_ref())
                .unwrap();
            if let Some(old) = &identity {
                assert_eq!(old, &key);
            } else {
                identity = Some(key);
            }
        }
    }
    for domain in ["domain S=[];", "", "domain S=[];"] {
        let p = load_text(&format!(
            "sort S; const a,b:S; {domain} input i(x:S); relation p(x:S); p(X) :- i(X); obligation one: empty(p); {V}"
        ));
        let (warm, _) = run(&p, &mut session, &Limits::default());
        assert_eq!(warm, run(&p, &mut Session::default(), &Limits::default()).0);
        assert_eq!(
            warm.emptiness.values().next().unwrap().proved(),
            !domain.is_empty()
        );
    }
}

#[test]
fn round_trip_preserves_ungrouped_requirement_selection_and_origins() {
    let p = load_text(&format!(
        "namespace n {{ relation p(); p(); obligation one: empty(p); {V} }}"
    ));
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&p.corpus).into_iter().map(|id| (id, 0)).collect(),
    };
    let export = ExportProgram {
        corpus: &p.corpus,
        domains: &p.domains,
        sources: &p.sources,
        provenance: &p.provenance,
        layout: &layout,
    };
    for embedded_origins in [false, true] {
        let bundle = print(&export, PrintOptions { embedded_origins }).unwrap();
        assert!(bundle.files["program.den"].contains("empty(p)"));
        assert!(!bundle.files["program.den"].contains("group_by"));
        let (membership, documents) = bundle.documents("file:///export");
        let reloaded = load_with_resolver(&membership, &documents, Some(&mut &p.sources)).unwrap();
        support::compare(&export, &reloaded, "file:///export", embedded_origins);
        assert!(
            run(&reloaded, &mut Session::default(), &Limits::default())
                .0
                .emptiness
                .values()
                .next()
                .unwrap()
                .examples
                .first()
                .is_some()
        );
    }
}

#[test]
fn grouping_and_assumption_forms_are_rejected_by_loader_and_index() {
    for declaration in [
        "obligation one: empty(p, group_by: ());",
        "obligation one: empty(p, group_by: (x));",
        "assumption one: empty(p);",
        "obligation one: empty(missing);",
    ] {
        let source = SourceFile::new(
            "file:///invalid.den",
            1,
            format!("sort S; input p(x:S); {declaration}"),
        );
        let membership = ProgramMembership::single("root", [source.uri.clone()]);
        assert!(load(&membership, &[source.clone()]).is_err());
        let mut index = index::Index::default();
        let tree = parser().parse(source.text.as_ref(), None).unwrap();
        if declaration.contains("group_by") {
            assert!(tree.root_node().has_error());
            continue;
        }
        index.update(source.clone(), tree);
        index.set_membership(&membership).unwrap();
        assert!(
            index
                .diagnostics("root", &source.uri)
                .iter()
                .any(|d| !d.warning),
            "{declaration}"
        );
    }
}

#[test]
fn library_verifications_use_consumer_facts_and_domains_with_labeled_fallback() {
    use std::collections::{BTreeMap, BTreeSet};
    let roots = BTreeMap::from([
        (
            "lib".into(),
            RootInfo {
                files: BTreeSet::from(["file:///lib.den".into()]),
                libraries: BTreeSet::new(),
            },
        ),
        (
            "app".into(),
            RootInfo {
                files: BTreeSet::from(["file:///app.den".into()]),
                libraries: BTreeSet::from(["lib".into()]),
            },
        ),
    ]);
    let lib = "namespace lib; sort S; const a:S; input i(x:S); relation p(x:S); p(X) :- i(X); obligation one: empty(p); verification checks { assumptions: []; obligations: [one]; }";
    for (root, app, proved) in [
        ("lib", "", false),
        ("app", "domain lib::S=[];", true),
        ("app", "", false),
        ("app", "lib::p(lib::a);", false),
    ] {
        let documents = vec![
            SourceFile::new("file:///lib.den", 1, lib),
            SourceFile::new("file:///app.den", 1, app),
        ];
        let p = load(
            &ProgramMembership {
                root: root.into(),
                roots: roots.clone(),
            },
            &documents,
        )
        .unwrap();
        let (r, out) = run(&p, &mut Session::default(), &Limits::default());
        assert_eq!(r.emptiness.values().next().unwrap().proved(), proved);
        let ds: Vec<_> = out
            .diagnostics
            .iter()
            .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
            .collect();
        assert_eq!(ds.len(), usize::from(!proved));
        if let Some(d) = ds.first() {
            assert_eq!(d.fallback, root == "app" && app.is_empty());
            let key = d
                .identity
                .data_in(&p.keys, r.context.verification.as_ref())
                .unwrap();
            assert_eq!(key["component"], "emptiness");
            assert!(!key["verification"].is_null());
        }
    }
}

fn placement_snapshot(
    p: &LoadedProgram,
    out: &presentation::Presentation,
) -> Vec<serde_json::Value> {
    use serde_json::json;
    let span = |s: denotate_ir::SourceSpan| {
        json!({"uri":p.sources.snapshot(s.snapshot()).unwrap().uri,
            "range":[s.byte_range().start,s.byte_range().end]})
    };
    let mut values = out.diagnostics.iter().map(|d| json!({
        "data": d.data(&p.keys).unwrap(), "primary":span(d.primary),
        "related": d.related.iter().map(|r| json!({"span":span(r.span),"label":r.label})).collect::<Vec<_>>(),
        "message":d.message, "notes":d.notes,
    })).collect::<Vec<_>>();
    values.sort_by_key(|v| v.to_string());
    values
}

#[test]
fn emptiness_locations_follow_only_the_replayed_derivation_and_keep_negation_related() {
    let p = load_text(&format!(
        "input i(); input j(); input forbidden(); relation guard(); relation p();
         guard() :- i(); guard() :- j(); p() :- guard(), !forbidden();
         obligation one: empty(p); {V}"
    ));
    let mut session = Session::default();
    let (cold, out) = run(&p, &mut session, &Limits::default());
    let (warm, warm_out) = run(&p, &mut session, &Limits::default());
    assert_eq!(cold, warm);
    assert_eq!(
        placement_snapshot(&p, &out),
        placement_snapshot(&p, &warm_out)
    );
    let ds = out
        .diagnostics
        .iter()
        .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
        .collect::<Vec<_>>();
    assert_eq!(ds.len(), 2); // p's rule and the retained guard branch
    let example = cold
        .emptiness
        .values()
        .next()
        .unwrap()
        .examples
        .first()
        .unwrap();
    for d in ds {
        let text = p.sources.text(d.primary).unwrap();
        assert!(text.starts_with("p() :-") || text.starts_with("guard() :-"));
        if text.starts_with("guard() :-") {
            let input_name = if text.contains("i()") { "i" } else { "j" };
            let input = p.corpus.relations().find(|r| r.name == input_name).unwrap();
            assert!(
                example
                    .observation
                    .present
                    .iter()
                    .any(|a| &a.relation == p.keys.relation(input.id).unwrap())
            );
        }
        assert!(
            d.related
                .iter()
                .any(|r| r.label == "contributing occurrence"
                    && p.sources.text(r.span).unwrap().contains("forbidden"))
        );
        assert!(d.related.iter().any(|r| r.label == "checked obligation"));
        assert_eq!(
            d.evidence["examples"][0]["attribution"]["state"],
            "complete"
        );
    }
}

#[test]
fn certified_presence_uses_the_certified_derivation_not_the_blocked_replay() {
    let p = load_text(&format!(
        "input i(); relation p(); relation q(); relation out();
         p() :- i(), !p(); q() :- p(), !q(); out() :- !q();
         obligation one: empty(out); {V}"
    ));
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    let e = report.verification.emptiness.values().next().unwrap();
    let example = e.examples.first().unwrap();
    let replay = prepared
        .program()
        .evaluate(example.observation.present.iter().cloned(), &limits)
        .unwrap();
    assert!(matches!(
        replay.fact(&example.tuple).unwrap(),
        FactState::Blocked(_)
    ));
    assert!(matches!(
        e.examples[0].attribution,
        Some(Attribution::Complete(_))
    ));
    let out = presentation::present(&p, &report).unwrap();
    let d = out
        .diagnostics
        .iter()
        .find(|d| matches!(d.identity, Identity::Emptiness(_)))
        .unwrap();
    assert_eq!(p.sources.text(d.primary).unwrap(), "out() :- !q();");
    let mut session = Session::default();
    let (cold, cold_out) = run(&p, &mut session, &limits);
    let (warm, warm_out) = run(&p, &mut session, &limits);
    assert_eq!(cold, warm);
    assert_eq!(
        placement_snapshot(&p, &cold_out),
        placement_snapshot(&p, &warm_out)
    );
    assert_eq!(
        placement_snapshot(&p, &out),
        placement_snapshot(&p, &cold_out)
    );
}

#[test]
fn attribution_fallback_preserves_semantic_summary_and_uses_obligation_location() {
    let p = load_text(&format!("relation p(); p(); obligation one: empty(p); {V}"));
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let CheckOutcome::Complete(mut report) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    // The checker unit test forces real attribution exhaustion. Exercise its
    // reporting contract here independently of the provisional work allowance.
    let cause = Inconclusive {
        phase: "attribution",
        resource: "work",
    };
    for e in report.verification.emptiness.values_mut() {
        e.examples[0].attribution = Some(Attribution::Incomplete(cause));
    }
    for e in report.results.value.emptiness.values_mut() {
        e.examples[0].attribution = Some(Attribution::Incomplete(cause));
    }
    let out = presentation::present(&p, &report).unwrap();
    assert_eq!(out.status["state"], "findings");
    assert_eq!(out.status["emptiness"][0]["complete"], true);
    assert!(out.status["emptiness"][0]["reason"].is_null());
    let d = &out.diagnostics[0];
    assert_eq!(p.sources.text(d.primary).unwrap(), "one");
    assert_eq!(d.kind, Kind::Counterexample);
    assert_eq!(
        d.evidence["examples"][0]["attribution"]["state"],
        "incomplete"
    );
    assert!(
        d.notes
            .iter()
            .any(|n| n.contains("counterexample is unchanged"))
    );
}

#[test]
fn warm_fact_and_embedded_origin_edits_refresh_placement_without_changing_identity() {
    let mut session = Session::default();
    let mut prior = None;
    for (padding, column) in [("", 1), ("\n\n", 1), ("\n\n", 2)] {
        let text = format!(
            "relation p();{padding}\np() loc(#s 1:{column} to 1:{});\nobligation one: empty(p); {V}\n#s = source(\"file:///source.dsl\", view: \"dsl\", hash: \"{}\");",
            column + 1,
            content_hash("abc")
        );
        let doc = SourceFile::new("file:///program.den", 1, text.clone());
        let membership = ProgramMembership::single("root", [doc.uri.clone()]);
        let mut resolver = |_: &SourceIdentity| Ok(std::sync::Arc::<str>::from("abc"));
        let p = load_with_resolver(&membership, &[doc], Some(&mut resolver)).unwrap();
        let (warm, out) = run(&p, &mut session, &Limits::default());
        let (cold, cold_out) = run(&p, &mut Session::default(), &Limits::default());
        assert_eq!(cold, warm);
        assert_eq!(
            placement_snapshot(&p, &out),
            placement_snapshot(&p, &cold_out)
        );
        let d = &out.diagnostics[0];
        assert!(p.sources.text(d.primary).unwrap().starts_with("p() loc("));
        let upstream = d
            .related
            .iter()
            .find(|r| r.label == "upstream source origin")
            .unwrap();
        assert_eq!(upstream.span.byte_range(), column - 1..column);
        let origins = p.origins_at("file:///program.den", d.primary.byte_range().start);
        assert_eq!(origins.len(), 1);
        assert_eq!(origins[0].start.column, column);
        let identity = d.data(&p.keys).unwrap()["finding"].clone();
        let range = d.primary.byte_range();
        if let Some((old_identity, old_range, old_column)) = prior {
            assert_eq!(identity, old_identity);
            if column == old_column {
                assert_ne!(range, old_range)
            } else {
                assert_eq!(range, old_range)
            }
        }
        prior = Some((identity, range, column));
    }
}

#[test]
fn bounded_examples_are_key_ordered_and_count_all_distinct_tuples() {
    let count = EMPTINESS_EXAMPLE_LIMIT + 2;
    let names = (0..count).map(|i| format!("n{i}")).collect::<Vec<_>>();
    let facts = names
        .iter()
        .rev()
        .map(|n| format!("p({n}); p({n});"))
        .collect::<Vec<_>>()
        .join(
            "
",
        );
    let p = load_text(&format!(
        "sort S; const {}:S; relation p(x:S); {facts} obligation one: empty(p); {V}",
        names.iter().rev().cloned().collect::<Vec<_>>().join(",")
    ));
    let mut session = Session::default();
    let (cold, out) = run(&p, &mut session, &Limits::default());
    let (warm, warm_out) = run(&p, &mut session, &Limits::default());
    assert_eq!(cold, warm);
    assert_eq!(
        placement_snapshot(&p, &out),
        placement_snapshot(&p, &warm_out)
    );
    let e = cold.emptiness.values().next().unwrap();
    assert!(e.complete());
    assert_eq!(e.present, count);
    assert_eq!(e.examples.len(), EMPTINESS_EXAMPLE_LIMIT);
    let selected = e
        .examples
        .iter()
        .map(|e| &e.tuple.arguments[0])
        .collect::<Vec<_>>();
    let expected = names[..EMPTINESS_EXAMPLE_LIMIT]
        .iter()
        .map(|name| {
            p.keys
                .constant(p.corpus.constants().find(|c| &c.name == name).unwrap().id)
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(selected, expected);
    let ds = out
        .diagnostics
        .iter()
        .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
        .collect::<Vec<_>>();
    assert_eq!(ds.len(), EMPTINESS_EXAMPLE_LIMIT);
    for d in ds {
        let source = p.sources.text(d.primary).unwrap();
        let notes = d
            .notes
            .iter()
            .filter(|n| n.starts_with("Replayed present tuple:"))
            .collect::<Vec<_>>();
        assert_eq!(notes.len(), 1);
        assert!(notes[0].contains(source.trim_end_matches(';')));
        assert_eq!(
            d.evidence["presentTuples"],
            serde_json::json!({"count":count,"exact":true})
        );
        assert_eq!(d.evidence["examplesTruncated"], true);
        assert_eq!(
            d.evidence["examples"],
            out.status["emptiness"][0]["examples"]
        );
    }
}

#[test]
fn fixing_one_independent_error_leaves_other_locations_and_finding_identity() {
    let mut session = Session::default();
    let mut identity = None;
    for facts in ["p(a); p(b); p(c);", "p(b); p(c);"] {
        let p = load_text(&format!(
            "sort S; const a,b,c:S; relation p(x:S); {facts} obligation one: empty(p); {V}"
        ));
        let (warm, out) = run(&p, &mut session, &Limits::default());
        assert_eq!(warm, run(&p, &mut Session::default(), &Limits::default()).0);
        let ds = out
            .diagnostics
            .iter()
            .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
            .collect::<Vec<_>>();
        let located = ds
            .iter()
            .map(|d| p.sources.text(d.primary).unwrap())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(located, facts.split_inclusive(';').map(str::trim).collect());
        for d in ds {
            let key = d.data(&p.keys).unwrap()["finding"].clone();
            if let Some(prior) = &identity {
                assert_eq!(&key, prior);
            } else {
                identity = Some(key);
            }
        }
    }
}

#[test]
fn different_worlds_stay_with_their_own_tuples_and_shared_locations_merge_notes() {
    let p = load_text(&format!(
        "sort S; const a,b:S; input i(); relation seed(x:S); relation p(x:S);
         seed(a) :- i(); seed(b) :- !i(); p(X) :- seed(X);
         obligation one: empty(p); {V}"
    ));
    let (r, out) = run(&p, &mut Session::default(), &Limits::default());
    let e = r.emptiness.values().next().unwrap();
    assert_eq!(e.present, 2);
    assert!(e.complete());
    for example in &e.examples {
        assert_eq!(
            !example.observation.present.is_empty(),
            &example.tuple.arguments[0]
                == p.keys
                    .constant(p.corpus.constants().find(|c| c.name == "a").unwrap().id)
                    .unwrap()
        );
        assert_eq!(
            !example.observation.absent.is_empty(),
            &example.tuple.arguments[0]
                == p.keys
                    .constant(p.corpus.constants().find(|c| c.name == "b").unwrap().id)
                    .unwrap()
        );
    }
    let ds = out
        .diagnostics
        .iter()
        .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
        .collect::<Vec<_>>();
    assert_eq!(ds.len(), 3); // shared rule, plus each world-specific seed rule
    for d in ds {
        let source = p.sources.text(d.primary).unwrap();
        let notes = d
            .notes
            .iter()
            .filter(|n| n.starts_with("Replayed present tuple:"))
            .collect::<Vec<_>>();
        if source.starts_with("p(X)") {
            assert_eq!(notes.len(), 2);
        } else {
            assert_eq!(notes.len(), 1);
            assert!(notes[0].contains(if source.starts_with("seed(a)") {
                "p(a)"
            } else {
                "p(b)"
            }));
        }
    }
}

#[test]
fn one_attribution_fallback_is_not_hidden_by_another_tuples_derivation() {
    let p = load_text(&format!(
        "sort S; const a,b:S; relation p(x:S); p(a); p(b); obligation one: empty(p); {V}"
    ));
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let CheckOutcome::Complete(mut report) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    let cause = Inconclusive {
        phase: "attribution",
        resource: "work",
    };
    report
        .verification
        .emptiness
        .values_mut()
        .next()
        .unwrap()
        .examples[0]
        .attribution = Some(Attribution::Incomplete(cause));
    report
        .results
        .value
        .emptiness
        .values_mut()
        .next()
        .unwrap()
        .examples[0]
        .attribution = Some(Attribution::Incomplete(cause));
    let out = presentation::present(&p, &report).unwrap();
    let ds = out
        .diagnostics
        .iter()
        .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
        .collect::<Vec<_>>();
    assert_eq!(ds.len(), 2);
    for d in &ds {
        let source = p.sources.text(d.primary).unwrap();
        assert!(source == "one" || source == "p(b);");
        let tuple = if source == "one" { "p(a)" } else { "p(b)" };
        assert!(
            d.notes
                .iter()
                .any(|n| n.starts_with("Replayed present tuple:") && n.contains(tuple))
        );
        assert_eq!(d.evidence["complete"], true);
        assert_eq!(
            d.evidence["presentTuples"],
            serde_json::json!({"count":2,"exact":true})
        );
        assert_eq!(
            d.evidence["examples"][0]["attribution"]["state"],
            "incomplete"
        );
        assert_eq!(
            d.evidence["examples"][1]["attribution"]["state"],
            "complete"
        );
    }
    assert_eq!(
        ds[0].data(&p.keys).unwrap()["finding"],
        ds[1].data(&p.keys).unwrap()["finding"]
    );
}

#[test]
fn empty_notes_show_structural_dependency_inputs_including_derived_absences() {
    for (rules, expected_inputs) in [
        ("p();", None),
        ("relation allowed(); p() :- !allowed();", None),
        (
            "p() :- !excluded();",
            Some("present: (none); absent: excluded()"),
        ),
        (
            "p() :- selected(), !excluded();",
            Some("present: selected(); absent: excluded()"),
        ),
        (
            "relation guard(); guard() :- selected(); p() :- guard(), !excluded();",
            Some("present: selected(); absent: excluded()"),
        ),
        // A negative derived premise still depends on the inputs of its provider.
        (
            "relation guard(); guard() :- selected(); p() :- !guard();",
            Some("present: (none); absent: selected()"),
        ),
        (
            "input order(); input signed(); relation approved(); approved() :- signed(); p() :- order(), !approved();",
            Some("present: order(); absent: signed()"),
        ),
    ] {
        let p = load_text(&format!(
            "input selected(); input excluded(); input unrelated(); relation p();
             {rules} obligation one: empty(p); {V}"
        ));
        let mut session = Session::default();
        let (cold, out) = run(&p, &mut session, &Limits::default());
        let (warm, warm_out) = run(&p, &mut session, &Limits::default());
        assert_eq!(cold, warm);
        assert_eq!(
            placement_snapshot(&p, &out),
            placement_snapshot(&p, &warm_out)
        );
        for d in out
            .diagnostics
            .iter()
            .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
        {
            let note = d
                .notes
                .iter()
                .find(|n| n.starts_with("Replayed present tuple:"))
                .unwrap();
            if let Some(inputs) = expected_inputs {
                assert!(note.contains("Inputs in dependency cone"), "{note}");
                assert!(note.contains(inputs), "{note}");
            } else {
                assert_eq!(note, "Replayed present tuple: p().");
            }
            assert!(!note.contains("unrelated"));
            // Display filtering never shrinks the replayable observation.
            let observation = &d.evidence["examples"][0]["observation"];
            assert_eq!(
                observation["present"].as_array().unwrap().len()
                    + observation["absent"].as_array().unwrap().len(),
                p.corpus
                    .relations()
                    .filter(|r| r.role == denotate_ir::RelationRole::Input)
                    .count()
            );
            assert_eq!(
                d.evidence["examples"][0]["dependencyInputs"],
                out.status["emptiness"][0]["examples"][0]["dependencyInputs"]
            );
        }
    }
}

#[test]
fn empty_input_scope_is_structural_grounded_and_refreshed_after_warm_edits() {
    let mut session = Session::default();
    for input in ["selected", "excluded", "selected"] {
        let p = load_text(&format!(
            "sort S; const a,b:S; input selected(x:S); input excluded(x:S);
             relation p(x:S); p(a); p(a) :- {input}(a);
             obligation one: empty(p); {V}"
        ));
        let (warm, out) = run(&p, &mut session, &Limits::default());
        let (cold, cold_out) = run(&p, &mut Session::default(), &Limits::default());
        assert_eq!(cold, warm);
        assert_eq!(
            placement_snapshot(&p, &out),
            placement_snapshot(&p, &cold_out)
        );
        let example = &warm.emptiness.values().next().unwrap().examples[0];
        let Some(Attribution::Complete(inputs)) = &example.dependency_inputs else {
            panic!()
        };
        // Even when the retained proof is the unconditional fact, the alternative
        // producer belongs to the structural cone. Only its grounded a input does.
        assert_eq!(inputs.len(), 1);
        let atom = inputs.first().unwrap();
        assert_eq!(
            &atom.relation,
            p.keys
                .relation(p.corpus.relations().find(|r| r.name == input).unwrap().id)
                .unwrap()
        );
        assert_eq!(
            &atom.arguments[0],
            p.keys
                .constant(p.corpus.constants().find(|c| c.name == "a").unwrap().id)
                .unwrap()
        );
        for d in out
            .diagnostics
            .iter()
            .filter(|d| matches!(d.identity, Identity::Emptiness(_)))
        {
            let note = d
                .notes
                .iter()
                .find(|n| n.starts_with("Replayed present tuple:"))
                .unwrap();
            assert!(note.contains(&format!("{input}(a)")));
            assert!(!note.contains("(b)"));
        }
    }
}

#[test]
fn unavailable_empty_input_scope_falls_back_to_full_world_without_affecting_failure() {
    let p = load_text(&format!(
        "input selected(); relation p(); p(); obligation one: empty(p); {V}"
    ));
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let CheckOutcome::Complete(mut report) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    let cause = Inconclusive {
        phase: "dependency cones",
        resource: "work",
    };
    report
        .verification
        .emptiness
        .values_mut()
        .next()
        .unwrap()
        .examples[0]
        .dependency_inputs = Some(Attribution::Incomplete(cause));
    report
        .results
        .value
        .emptiness
        .values_mut()
        .next()
        .unwrap()
        .examples[0]
        .dependency_inputs = Some(Attribution::Incomplete(cause));
    let out = presentation::present(&p, &report).unwrap();
    let d = out
        .diagnostics
        .iter()
        .find(|d| matches!(d.identity, Identity::Emptiness(_)))
        .unwrap();
    assert!(
        d.notes
            .iter()
            .any(|n| n.contains("Dependency-cone inputs unavailable") && n.contains("selected()"))
    );
    assert_eq!(d.evidence["complete"], true);
    assert_eq!(
        d.evidence["examples"][0]["attribution"]["state"],
        "complete"
    );
    assert_eq!(
        d.evidence["examples"][0]["dependencyInputs"]["state"],
        "incomplete"
    );
    assert_eq!(
        out.status["emptiness"][0]["examples"][0]["dependencyInputs"],
        d.evidence["examples"][0]["dependencyInputs"]
    );
}
