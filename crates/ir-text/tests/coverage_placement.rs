use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::{OccurrenceId, Origin, Provenance};
use denotate_ir_text::*;
use denotate_presentation::{Diagnostic, Identity};
use std::collections::{BTreeMap, BTreeSet};

fn program(library: &str, app: &str) -> LoadedProgram {
    load(
        &ProgramMembership {
            root: "app".into(),
            roots: BTreeMap::from([
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
            ]),
        },
        &[
            SourceFile::new("file:///lib.den", 1, library),
            SourceFile::new("file:///app.den", 1, app),
        ],
    )
    .unwrap()
}
fn run(p: &LoadedProgram, session: &mut Session) -> (ScopedResults, presentation::Presentation) {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let admitted = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&admitted, &ops).unwrap() else {
        panic!()
    };
    let out = presentation::present(p, &report.checked).unwrap();
    (report.checked.results.value, out)
}
fn coverage(out: &presentation::Presentation) -> Vec<&Diagnostic> {
    out.diagnostics
        .iter()
        .filter(|d| matches!(d.identity, Identity::Coverage(_)))
        .collect()
}
fn locations(p: &LoadedProgram, out: &presentation::Presentation) -> Vec<serde_json::Value> {
    let span = |s: denotate_ir::SourceSpan| {
        serde_json::json!({
            "uri":p.sources.snapshot(s.snapshot()).unwrap().uri,
            "range":[s.byte_range().start,s.byte_range().end],
        })
    };
    let mut entries = coverage(out).into_iter().map(|d| serde_json::json!({
        "data": d.data(&p.keys).unwrap(), "primary":span(d.primary), "message":d.message,
        "notes":d.notes, "fallback":d.fallback,
        "related":d.related.iter().map(|r| serde_json::json!({"span":span(r.span),"label":r.label})).collect::<Vec<_>>(),
    })).collect::<Vec<_>>();
    entries.sort_by_key(|v| v.to_string());
    entries
}
fn library(kind: &str) -> String {
    format!(
        "namespace lib; sort S; relation p(x:S); obligation covered: {kind}(p, group_by: (x)); verification checks {{ assumptions: []; obligations: [covered]; }}"
    )
}

#[test]
fn consumer_constant_is_primary_and_adding_the_missing_fact_clears_it() {
    for kind in ["at_least_one", "exactly_one"] {
        let mut session = Session::default();
        let mut identity = None;
        for (padding, name, fact) in [
            ("", "a", false),
            ("\n\n", "a", false),
            ("\n\n", "renamed", false),
            ("\n\n", "renamed", true),
            ("", "a", false),
        ] {
            let app = format!(
                "{padding}const {name}: lib::S; {}",
                if fact {
                    format!("lib::p({name});")
                } else {
                    String::new()
                }
            );
            let p = program(&library(kind), &app);
            let (warm, out) = run(&p, &mut session);
            let (cold, cold_out) = run(&p, &mut Session::default());
            assert_eq!(warm, cold);
            assert_eq!(locations(&p, &out), locations(&p, &cold_out));
            let ds = coverage(&out);
            assert_eq!(ds.len(), usize::from(!fact));
            if let Some(d) = ds.first() {
                assert_eq!(p.sources.text(d.primary).unwrap(), name);
                assert_eq!(d.primary.byte_range().start, padding.len() + "const ".len());
                assert_eq!(
                    p.sources.snapshot(d.primary.snapshot()).unwrap().uri,
                    "file:///app.den"
                );
                assert!(!d.fallback);
                assert!(d.related.iter().any(|r| r.label == "checked obligation"
                    && p.sources.text(r.span).unwrap() == "covered"));
                assert!(
                    d.notes
                        .iter()
                        .any(|n| n == &format!("Missing group ({name})."))
                );
                let data = d.data(&p.keys).unwrap()["finding"].clone();
                if let Some(prior) = &identity {
                    assert_eq!(&data, prior);
                } else {
                    identity = Some(data);
                }
            } else {
                assert_eq!(out.status["state"], "proved");
            }
        }
    }
}

#[test]
fn multiple_columns_union_locations_and_merge_only_their_groups_notes() {
    let lib = "namespace lib; sort N; sort L; relation p(n:N,l:L); obligation covered: at_least_one(p, group_by: (n,l)); verification checks { assumptions: []; obligations: [covered]; }";
    let p = program(lib, "const n:lib::N; const x,y:lib::L;");
    let (results, out) = run(&p, &mut Session::default());
    assert_eq!(results.coverage.values().next().unwrap().missing, 2);
    let ds = coverage(&out);
    assert_eq!(ds.len(), 3);
    for d in &ds {
        let name = p.sources.text(d.primary).unwrap();
        let expected = match name {
            "n" => vec!["Missing group (n, x).", "Missing group (n, y)."],
            "x" => vec!["Missing group (n, x)."],
            "y" => vec!["Missing group (n, y)."],
            _ => panic!("{name}"),
        };
        assert_eq!(d.notes, expected);
        assert!(d.related.iter().any(|r| r.label == "checked obligation"));
        assert_eq!(
            d.data(&p.keys).unwrap()["finding"],
            ds[0].data(&p.keys).unwrap()["finding"]
        );
    }
    assert_eq!(out.status["findings"].as_array().unwrap().len(), 1);
}

#[test]
fn library_only_and_global_groups_fall_back_and_do_not_hide_other_groups() {
    let lib = library("at_least_one").replace("sort S;", "sort S; const fixed:S;");
    let p = program(&lib, "const own:lib::S;");
    let (_, out) = run(&p, &mut Session::default());
    let ds = coverage(&out);
    assert_eq!(ds.len(), 2);
    let fallback = ds.iter().find(|d| d.fallback).unwrap();
    assert_eq!(p.sources.text(fallback.primary).unwrap(), "covered");
    assert_eq!(fallback.notes, ["Missing group (lib::fixed)."]);
    assert!(fallback.message.starts_with("in app:"));
    let own = ds.iter().find(|d| !d.fallback).unwrap();
    assert_eq!(p.sources.text(own.primary).unwrap(), "own");
    assert_eq!(own.notes, ["Missing group (own)."]);
    for lib in [
        lib,
        library("at_least_one").replace("group_by: (x)", "group_by: ()"),
    ] {
        let p = program(&lib, "");
        let (_, out) = run(&p, &mut Session::default());
        let ds = coverage(&out);
        assert_eq!(ds.len(), 1);
        assert!(ds[0].fallback);
        assert_eq!(p.sources.text(ds[0].primary).unwrap(), "covered");
    }
}

#[test]
fn mixed_ownership_group_uses_only_consumer_constants_as_primaries() {
    let lib = "namespace lib; sort N; sort L; const fixed:L; relation p(n:N,l:L); obligation covered: at_least_one(p, group_by: (n,l)); verification checks { assumptions: []; obligations: [covered]; }";
    let p = program(lib, "const n:lib::N;");
    let (_, out) = run(&p, &mut Session::default());
    let ds = coverage(&out);
    assert_eq!(ds.len(), 1);
    assert_eq!(p.sources.text(ds[0].primary).unwrap(), "n");
    assert!(!ds[0].fallback);
    assert!(
        ds[0]
            .related
            .iter()
            .any(|r| p.sources.text(r.span).unwrap() == "fixed")
    );
}

#[test]
fn missing_current_spans_fall_back_even_with_upstream_origins_and_shared_spans_merge() {
    let mut p = program(&library("at_least_one"), "const a,b:lib::S;");
    let constants = p.corpus.constants().map(|c| c.id).collect::<Vec<_>>();
    let a_span = p.provenance.origins(constants[0])[0].span;
    let mut current = Provenance::new();
    for (id, origins) in p.provenance.entries() {
        if constants.iter().any(|c| OccurrenceId::from(*c) == id) {
            p.embedded
                .provenance
                .attach(&p.corpus, &p.sources, id, origins.iter().cloned())
                .unwrap();
        } else {
            current
                .attach(&p.corpus, &p.sources, id, origins.iter().cloned())
                .unwrap();
        }
    }
    p.provenance = current;
    let (before, out) = run(&p, &mut Session::default());
    let ds = coverage(&out);
    assert_eq!(ds.len(), 1);
    assert!(ds[0].fallback);
    assert_eq!(p.sources.text(ds[0].primary).unwrap(), "covered");
    assert_eq!(ds[0].notes.len(), 2);

    // Two constants lowered from the same source occurrence: one primary, both notes.
    for id in constants {
        p.provenance
            .attach(&p.corpus, &p.sources, id, [Origin::new(a_span)])
            .unwrap();
    }
    let (after, out) = run(&p, &mut Session::default());
    assert_eq!(before, after); // provenance-only change never changes the checked results
    let ds = coverage(&out);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].primary, a_span);
    assert!(!ds[0].fallback);
    assert_eq!(ds[0].notes, ["Missing group (a).", "Missing group (b)."]);
}
