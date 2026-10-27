use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::top_level;
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
        assert_eq!(diagnostics.len(), usize::from(!proved));
        if let Some(d) = diagnostics.first() {
            assert_eq!(d.evidence["kind"], "replayed-counterexample");
            assert_eq!(d.evidence["tuples"].as_array().unwrap().len(), 1);
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
            if let Some(e) = &e.example {
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
            if let Some(e) = &global
                .verification
                .emptiness
                .values()
                .next()
                .unwrap()
                .example
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
        assert_eq!(e.example.is_some(), failure, "{body}");
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
        assert_eq!(e.example.is_some(), !fact.is_empty());
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
    assert!(e.example.is_some() && e.inconclusive.is_some(), "{e:?}");
    assert!(!e.complete());
    assert_eq!(out.status["state"], "findings");
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
                .example
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
            assert_eq!(d.fallback, root == "app");
            let key = d
                .identity
                .data_in(&p.keys, r.context.verification.as_ref())
                .unwrap();
            assert_eq!(key["component"], "emptiness");
            assert!(!key["verification"].is_null());
        }
    }
}
