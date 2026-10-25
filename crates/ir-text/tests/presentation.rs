use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;
use denotate_presentation::{Kind, Severity};
use std::collections::{BTreeMap, BTreeSet};

fn checked(p: &LoadedProgram, backend: BackendIdentity) -> presentation::Presentation {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.request(&limits, backend).unwrap();
    let mut session = Session::default();
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
        panic!()
    };
    presentation::present(p, &report.checked).unwrap()
}
fn program(root: &str, app: &str, library: &str) -> LoadedProgram {
    let app_root = if root == "file:///lib/den.root" {
        "file:///app/den.root"
    } else {
        root
    };
    let app_uri = format!("{}/app.den", app_root.strip_suffix("/den.root").unwrap());
    let roots = BTreeMap::from([
        (
            app_root.into(),
            RootInfo {
                files: BTreeSet::from([app_uri.clone()]),
                libraries: BTreeSet::from(["file:///lib/den.root".into()]),
            },
        ),
        (
            "file:///lib/den.root".into(),
            RootInfo {
                files: BTreeSet::from(["file:///lib/lib.den".into()]),
                libraries: BTreeSet::new(),
            },
        ),
    ]);
    let documents = if root != "file:///lib/den.root" {
        vec![
            SourceFile::new(app_uri, 1, app),
            SourceFile::new("file:///lib/lib.den", 1, library),
        ]
    } else {
        vec![SourceFile::new("file:///lib/lib.den", 1, library)]
    };
    load(
        &ProgramMembership {
            root: root.into(),
            roots,
        },
        &documents,
    )
    .unwrap()
}
const LIB: &str =
    "sort S; const a,b: S; relation p(x:S); obligation unique: at_most_one(p, group_by: ());";

#[test]
fn consumer_locations_and_labeled_fallback_do_not_change_library_home() {
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        let app = program("file:///app/den.root", "p(a); p(b);", LIB);
        let out = checked(&app, backend.clone());
        let conflicts = out
            .diagnostics
            .iter()
            .filter(|d| d.kind == Kind::Counterexample)
            .collect::<Vec<_>>();
        assert_eq!(conflicts.len(), 2);
        for d in conflicts {
            assert!(!d.fallback);
            assert_eq!(
                app.sources.snapshot(d.primary.snapshot()).unwrap().uri,
                "file:///app/app.den"
            );
            assert!(
                d.related
                    .iter()
                    .any(|r| app.sources.snapshot(r.span.snapshot()).unwrap().uri
                        == "file:///lib/lib.den")
            );
            assert_eq!(
                d.data(&app.keys).unwrap()["program"],
                "file:///app/den.root"
            );
        }
        let second = program("file:///second/den.root", "p(a); p(b);", LIB);
        let second_out = checked(&second, backend.clone());
        assert!(
            second_out
                .diagnostics
                .iter()
                .filter(|d| d.kind == Kind::Counterexample)
                .all(
                    |d| second.sources.snapshot(d.primary.snapshot()).unwrap().uri
                        == "file:///second/app.den"
                        && !d.fallback
                )
        );
        let library = program("file:///lib/den.root", "", LIB);
        assert!(checked(&library, backend.clone()).diagnostics.is_empty());
        let bad_library = format!("{LIB} p(a); p(b);");
        let library = program("file:///lib/den.root", "", &bad_library);
        assert!(
            checked(&library, backend.clone())
                .diagnostics
                .iter()
                .filter(|d| d.kind == Kind::Counterexample)
                .all(|d| !d.fallback)
        );
        let consumer = program("file:///app/den.root", "relation unused();", &bad_library);
        let out = checked(&consumer, backend);
        let d = out
            .diagnostics
            .iter()
            .find(|d| d.kind == Kind::Counterexample)
            .unwrap();
        assert!(d.fallback);
        assert!(d.message.starts_with("in file:///app/den.root: "));
        assert_eq!(
            consumer.sources.snapshot(d.primary.snapshot()).unwrap().uri,
            "file:///lib/lib.den"
        );
        assert!(
            out.status["findings"]
                .as_array()
                .unwrap()
                .iter()
                .any(|f| f["fallback"] == true)
        );
        // Same library occurrence in two consumers is intentionally distinct.
        let second = program(
            "file:///second/den.root",
            "relation unused();",
            &bad_library,
        );
        let other = checked(&second, BackendIdentity::bdd());
        assert_ne!(
            d.data(&consumer.keys).unwrap()["program"],
            other.diagnostics[0].data(&second.keys).unwrap()["program"]
        );
    }
}

#[test]
fn current_and_embedded_denotate_views_stay_separate_and_missing_origins_do_not_hide_findings() {
    use denotate_ir::Origin;
    let mut p = program("file:///app/den.root", "p(a); p(b);", LIB);
    let upstream = p
        .sources
        .add("file:///dsl.den", 1, "denotate", "upstream")
        .unwrap();
    let span = p.sources.span(upstream, 0..8).unwrap();
    for rule in p.corpus.rules() {
        p.embedded
            .provenance
            .attach(&p.corpus, &p.sources, rule.id, [Origin::new(span)])
            .unwrap();
    }
    let out = checked(&p, BackendIdentity::bdd());
    for d in out
        .diagnostics
        .iter()
        .filter(|d| d.kind == Kind::Counterexample)
    {
        assert_ne!(d.primary.snapshot(), upstream);
        assert!(
            d.related
                .iter()
                .any(|r| r.span == span && r.label == "upstream source origin")
        );
    }
    p.embedded.provenance = denotate_ir::Provenance::new();
    assert_eq!(
        out.diagnostics.len(),
        checked(&p, BackendIdentity::bdd()).diagnostics.len()
    );
}

#[test]
fn no_meaning_and_unsupported_are_not_success_or_overlap() {
    for (rules, expected) in [
        ("relation x(); x() :- !x();", Kind::NoMeaning),
        (
            "relation x(); relation y(); x() :- !y(); y() :- !x();",
            Kind::UnsupportedRegion,
        ),
    ] {
        let p = program("file:///app/den.root", rules, LIB);
        let out = checked(&p, BackendIdentity::bdd());
        assert_ne!(out.status["state"], "proved");
        assert!(out.diagnostics.iter().any(|d| d.kind == expected));
        if expected == Kind::UnsupportedRegion {
            let diagnostics = out
                .diagnostics
                .iter()
                .filter(|d| d.kind == expected)
                .collect::<Vec<_>>();
            assert_eq!(diagnostics.len(), 1);
            let d = diagnostics[0];
            let texts = std::iter::once(d.primary)
                .chain(d.related.iter().map(|r| r.span))
                .map(|s| p.sources.text(s).unwrap())
                .collect::<Vec<_>>();
            assert!(texts.iter().any(|s| s.contains("x() :- !y()")));
            assert!(texts.iter().any(|s| s.contains("y() :- !x()")));
        }
        assert!(
            !out.diagnostics
                .iter()
                .any(|d| d.kind == Kind::Counterexample)
        );
        assert_eq!(
            expected.severity(),
            if expected == Kind::NoMeaning {
                Severity::Error
            } else {
                Severity::Warning
            }
        );
    }
}

#[test]
fn exhausted_request_keeps_backend_assumptions_and_reason_in_status() {
    let p = program(
        "file:///app/den.root",
        "input i(x:S); assumption w: at_most_one(i, group_by: ());",
        LIB,
    );
    let limits = Limits::default();
    let request = p.request(&limits, BackendIdentity::sat()).unwrap();
    let status = denotate_presentation::summary(&request.exhausted(Inconclusive {
        phase: "grounding",
        resource: "deadline",
    }));
    assert_eq!(status["state"], "incomplete");
    assert_eq!(status["backend"]["backend"], "sat");
    assert_eq!(status["activeAssumptions"].as_array().unwrap().len(), 1);
    assert_eq!(status["unfinished"]["resource"], "deadline");
}

#[test]
fn sat_unfounded_world_is_exposed_separately_from_replayed_counterexamples() {
    let cases = [
        "d(a) :- i(a); d(a) :- d(a); d(b) :- i(b);",
        "d(a) :- i(a); d(a) :- d(a); d(b) :- i(a), !d(a);",
        "d(a) :- i(a); d(b) :- d(a); d(a) :- d(b);",
    ];
    let mut unsupported = 0;
    for rules in cases {
        let text = format!(
            "sort S; const a,b:S; input i(x:S); relation d(x:S); {rules} obligation unique: at_most_one(d, group_by: ());"
        );
        let doc = SourceFile::new("file:///sat.den", 1, text);
        let p = load(
            &ProgramMembership::single("file:///den.root", [doc.uri.clone()]),
            &[doc],
        )
        .unwrap();
        let out = checked(&p, BackendIdentity::sat());
        for d in &out.diagnostics {
            if d.evidence["kind"] == "unfounded-support-world" {
                unsupported += 1;
                assert_eq!(d.kind, Kind::UnsupportedGroup);
                assert!(
                    d.notes
                        .iter()
                        .any(|s| s.contains("not an overlap counterexample"))
                );
                assert!(d.evidence.get("tuples").is_none());
                assert!(d.evidence.get("world").is_some());
            }
        }
    }
    assert!(unsupported > 0);
}

#[test]
fn phase_exhaustion_and_rewrite_proofs_remain_distinct() {
    let p = program(
        "file:///app/den.root",
        "relation x(); x() :- !x(); p(a); p(b);",
        LIB,
    );
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &p.domains, &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let meaning = ground.symbolic(&limits).unwrap();
    let exhausted = Limits {
        max_work: 0,
        ..limits.clone()
    };
    let report = meaning
        .verify_with_phase_limits(&limits, &exhausted, &limits)
        .unwrap();
    let findings = denotate_presentation::interpret(&p.corpus, &report, None).unwrap();
    assert!(
        findings
            .iter()
            .any(|f| f.kind == Kind::Inconclusive && f.message.contains("Consistency checking"))
    );
    assert!(findings.iter().any(|f| f.kind == Kind::Counterexample));
    let user_files = p
        .documents
        .iter()
        .filter(|d| d.ownership == "user")
        .map(|d| d.uri.clone())
        .collect();
    let placement = denotate_presentation::Placement {
        program: &p.root,
        user_files: &user_files,
        sources: &p.sources,
        current: &p.provenance,
        upstream: &p.embedded.provenance,
    };
    for finding in findings.iter().filter(|f| f.kind == Kind::Inconclusive) {
        assert_eq!(placement.finding(finding).unwrap().len(), 1);
    }
    let p = program(
        "file:///app/den.root",
        "input i(); relation x(); x() :- i(), !i(), !x();",
        LIB,
    );
    let out = checked(&p, BackendIdentity::bdd());
    assert!(out.diagnostics.iter().any(|f| f.kind == Kind::Rewrite));
    assert!(
        !out.diagnostics
            .iter()
            .any(|f| f.kind == Kind::Counterexample)
    );
    assert!(
        out.status["findings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["kind"] == "redundant")
    );
    let library_only = program(
        "file:///app/den.root",
        "relation unused();",
        &format!("{LIB} input i(); relation x(); x() :- i(), !i(), !x();"),
    );
    let fallback = checked(&library_only, BackendIdentity::bdd());
    assert!(
        fallback.status["findings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["kind"] == "redundant" && f["fallback"] == true)
    );
    // The generic adapter publishes proofs and locations, never inferred edits.
    for d in out.diagnostics {
        assert!(d.data(&p.keys).unwrap().get("edit").is_none());
    }
}

#[test]
fn a_consumers_participating_constant_declarations_are_valid_primaries() {
    let p = program(
        "file:///app/den.root",
        "const a,b:S;",
        "sort S; input i(x:S); relation p(x:S); p(X) :- i(X); obligation unique: at_most_one(p, group_by: ());",
    );
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        let out = checked(&p, backend);
        let conflicts = out
            .diagnostics
            .iter()
            .filter(|d| d.kind == Kind::Counterexample)
            .collect::<Vec<_>>();
        assert!(!conflicts.is_empty());
        for d in conflicts {
            assert!(!d.fallback);
            assert_eq!(
                p.sources.snapshot(d.primary.snapshot()).unwrap().uri,
                "file:///app/app.den"
            );
        }
    }
}
