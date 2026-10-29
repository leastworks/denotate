use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::Provenance;
use denotate_ir_text::*;
use denotate_presentation::Kind;
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
fn locations(p: &LoadedProgram, out: &presentation::Presentation) -> Vec<serde_json::Value> {
    let span = |s: denotate_ir::SourceSpan| {
        serde_json::json!({
            "uri":p.sources.snapshot(s.snapshot()).unwrap().uri,
            "range":[s.byte_range().start,s.byte_range().end],
        })
    };
    let mut entries = out.diagnostics.iter().map(|d| serde_json::json!({
        "data": d.data(&p.keys).unwrap(), "primary":span(d.primary), "message":d.message,
        "notes":d.notes, "fallback":d.fallback,
        "related":d.related.iter().map(|r| serde_json::json!({"span":span(r.span),"label":r.label})).collect::<Vec<_>>(),
    })).collect::<Vec<_>>();
    entries.sort_by_key(|v| v.to_string());
    entries
}
fn primaries(p: &LoadedProgram, out: &presentation::Presentation) -> BTreeSet<String> {
    out.diagnostics
        .iter()
        .filter(|d| d.kind == Kind::Counterexample)
        .map(|d| p.sources.text(d.primary).unwrap().to_owned())
        .collect()
}
fn related(p: &LoadedProgram, out: &presentation::Presentation, text: &str, label: &str) -> bool {
    out.diagnostics.iter().all(|d| {
        d.related
            .iter()
            .any(|r| p.sources.text(r.span).unwrap() == text && r.label == label)
    })
}
const EMPTY: &str =
    "obligation clean: empty(bad); verification checks { assumptions: []; obligations: [clean]; }";

#[test]
fn library_empty_stops_at_consumer_rule_and_local_obligation_keeps_full_derivation() {
    let declarations = "namespace lib; relation bad(); relation seed(); input forbidden();";
    let app =
        "use lib; relation guard(); guard() :- seed(); seed(); bad() :- guard(), !forbidden();";
    let mut session = Session::default();
    let mut identity = None;
    for padding in ["", "\n\n", ""] {
        let p = program(
            &format!("{declarations} {EMPTY}"),
            &format!("{padding}{app}"),
        );
        let (warm, out) = run(&p, &mut session);
        let (cold, cold_out) = run(&p, &mut Session::default());
        assert_eq!(warm, cold);
        assert_eq!(locations(&p, &out), locations(&p, &cold_out));
        assert_eq!(
            primaries(&p, &out),
            BTreeSet::from(["bad() :- guard(), !forbidden();".into()])
        );
        assert!(related(&p, &out, "guard() :- seed();", "producing rule"));
        assert!(related(&p, &out, "seed();", "producing rule"));
        assert!(
            out.diagnostics[0].related.iter().any(|r| p
                .sources
                .text(r.span)
                .unwrap()
                .contains("forbidden"))
        );
        let key = out.diagnostics[0].data(&p.keys).unwrap()["finding"].clone();
        if let Some(prior) = &identity {
            assert_eq!(&key, prior);
        } else {
            identity = Some(key);
        }
    }
    let p = program(declarations, &format!("{app} namespace lib {{ {EMPTY} }}"));
    let (_, out) = run(&p, &mut session);
    assert_eq!(
        primaries(&p, &out),
        BTreeSet::from([
            "bad() :- guard(), !forbidden();".into(),
            "guard() :- seed();".into(),
            "seed();".into()
        ])
    );
}

#[test]
fn uniqueness_and_exactly_one_keep_both_conflict_producers_with_helpers_related() {
    for contract in ["at_most_one", "exactly_one"] {
        let lib = format!(
            "namespace lib; sort S; const a,b:S; relation p(x:S); obligation unique: {contract}(p, group_by: ()); verification checks {{ assumptions: []; obligations: [unique]; }}"
        );
        let app = "use lib; relation seed(); relation g(); relation h(); seed(); g() :- seed(); h() :- g(); p(a) :- g(); p(b) :- h();";
        let p = program(&lib, app);
        let mut session = Session::default();
        let (cold, out) = run(&p, &mut session);
        let (warm, warm_out) = run(&p, &mut session);
        assert_eq!(cold, warm);
        assert_eq!(locations(&p, &out), locations(&p, &warm_out));
        assert_eq!(
            primaries(&p, &out),
            BTreeSet::from(["p(a) :- g();".into(), "p(b) :- h();".into()])
        );
        for helper in ["seed();", "g() :- seed();", "h() :- g();"] {
            assert!(related(&p, &out, helper, "producing rule"));
        }
        assert!(
            out.diagnostics
                .iter()
                .all(|d| d.identity == out.diagnostics[0].identity)
        );
    }
}

#[test]
fn frontier_is_unioned_across_roots_even_when_one_root_is_below_another() {
    let lib = "namespace lib; sort S; const a,b:S; relation p(x:S); obligation unique: at_most_one(p, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }";
    let p = program(
        lib,
        "use lib; relation seed(); seed(); p(b) :- seed(); p(a) :- p(b);",
    );
    let (_, out) = run(&p, &mut Session::default());
    assert_eq!(
        primaries(&p, &out),
        BTreeSet::from(["p(a) :- p(b);".into(), "p(b) :- seed();".into()])
    );
    assert!(related(&p, &out, "seed();", "producing rule"));
}

#[test]
fn library_rule_keeps_both_positive_consumer_premises_but_not_negative_support() {
    let lib = format!(
        "namespace lib; relation bad(); relation left(); relation right(); relation absent(); bad() :- left(), right(), !absent(); {EMPTY}"
    );
    let p = program(&lib, "use lib; left(); right();");
    let (_, out) = run(&p, &mut Session::default());
    assert_eq!(
        primaries(&p, &out),
        BTreeSet::from(["left();".into(), "right();".into()])
    );
    assert!(related(
        &p,
        &out,
        "bad() :- left(), right(), !absent();",
        "producing rule"
    ));
}

#[test]
fn a_tuple_without_consumer_producers_keeps_fallback_alongside_the_other_frontier() {
    let lib = "namespace lib; sort S; const a,b:S; input i(); relation p(x:S); p(b) :- i(); obligation unique: at_most_one(p, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }";
    let p = program(lib, "use lib; relation seed(); seed(); p(a) :- seed();");
    let (_, out) = run(&p, &mut Session::default());
    assert_eq!(
        primaries(&p, &out),
        BTreeSet::from(["p(a) :- seed();".into(), "p(b) :- i();".into()])
    );
    assert!(
        out.diagnostics
            .iter()
            .any(|d| d.fallback && d.message.starts_with("in app:"))
    );
    assert!(out.diagnostics.iter().any(|d| !d.fallback));
    // An input root has no producing rule and keeps the old declaration placement.
    let p = program(
        "namespace lib; input bad(); obligation clean: empty(bad); verification checks { assumptions: []; obligations: [clean]; }",
        "",
    );
    let (_, out) = run(&p, &mut Session::default());
    assert!(out.diagnostics.iter().all(|d| d.fallback));
    assert_eq!(primaries(&p, &out), BTreeSet::from(["bad".into()]));
}

#[test]
fn unlocated_rule_does_not_stop_at_its_locatable_literals_or_upstream_origin() {
    let lib = format!("namespace lib; relation bad(); {EMPTY}");
    let mut p = program(&lib, "use lib; relation seed(); seed(); bad() :- seed();");
    let mut current = Provenance::new();
    for (id, origins) in p.provenance.entries() {
        if origins
            .iter()
            .any(|o| p.sources.text(o.span).unwrap() == "bad() :- seed();")
        {
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
    let (_, out) = run(&p, &mut Session::default());
    assert_eq!(primaries(&p, &out), BTreeSet::from(["seed();".into()]));
    assert!(related(
        &p,
        &out,
        "bad() :- seed();",
        "upstream source origin"
    ));
}

#[test]
fn transitive_library_rules_do_not_stop_the_frontier() {
    let membership = ProgramMembership {
        root: "app".into(),
        roots: BTreeMap::from([
            (
                "base".into(),
                RootInfo {
                    files: BTreeSet::from(["file:///base.den".into()]),
                    libraries: BTreeSet::new(),
                },
            ),
            (
                "middle".into(),
                RootInfo {
                    files: BTreeSet::from(["file:///middle.den".into()]),
                    libraries: BTreeSet::from(["base".into()]),
                },
            ),
            (
                "app".into(),
                RootInfo {
                    files: BTreeSet::from(["file:///app.den".into()]),
                    libraries: BTreeSet::from(["middle".into()]),
                },
            ),
        ]),
    };
    let p = load(
        &membership,
        &[
            SourceFile::new(
                "file:///base.den",
                1,
                format!(
                    "namespace lib; relation bad(); relation middle(); bad() :- middle(); {EMPTY}"
                ),
            ),
            SourceFile::new(
                "file:///middle.den",
                1,
                "use lib; relation seed(); middle() :- seed();",
            ),
            SourceFile::new("file:///app.den", 1, "seed();"),
        ],
    )
    .unwrap();
    let (_, out) = run(&p, &mut Session::default());
    assert_eq!(primaries(&p, &out), BTreeSet::from(["seed();".into()]));
    for rule in ["bad() :- middle();", "middle() :- seed();"] {
        assert!(related(&p, &out, rule, "producing rule"));
    }
}

#[test]
fn unknown_obligation_ownership_keeps_legacy_placement_and_evidence_unchanged() {
    let lib = format!("namespace lib; relation bad(); {EMPTY}");
    let mut p = program(&lib, "use lib; relation seed(); seed(); bad() :- seed();");
    let mut session = Session::default();
    let (before, narrowed) = run(&p, &mut session);
    let mut current = Provenance::new();
    for (id, origins) in p.provenance.entries() {
        if origins
            .iter()
            .all(|o| p.sources.text(o.span).unwrap() != "clean")
        {
            current
                .attach(&p.corpus, &p.sources, id, origins.iter().cloned())
                .unwrap();
        }
    }
    p.provenance = current;
    let (after, legacy) = run(&p, &mut session);
    assert_eq!(before, after);
    assert_eq!(
        primaries(&p, &narrowed),
        BTreeSet::from(["bad() :- seed();".into()])
    );
    assert_eq!(
        primaries(&p, &legacy),
        BTreeSet::from(["bad() :- seed();".into(), "seed();".into()])
    );
    assert!(
        legacy
            .diagnostics
            .iter()
            .all(|d| d.identity == narrowed.diagnostics[0].identity
                && d.evidence == narrowed.diagnostics[0].evidence)
    );
    let (cold, cold_out) = run(&p, &mut Session::default());
    assert_eq!(cold, after);
    assert_eq!(locations(&p, &legacy), locations(&p, &cold_out));
}
