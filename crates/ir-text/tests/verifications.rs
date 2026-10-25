use denotate_check::{BackendIdentity, CheckOutcome, Limits, RequestPreparation, ScopedResult};
use denotate_ir::*;
use denotate_ir_text::*;
use std::collections::{BTreeMap, BTreeSet};

mod support;
const BODY: &str = "sort S; const x, y: S; input p(x: S); relation q(x: S); q(X) :- p(X); assumption a: at_most_one(p, group_by: ()); obligation o: at_most_one(q, group_by: ());";
fn single(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn checked(p: &LoadedProgram) -> Vec<(String, Vec<ScopedResult>)> {
    let limits = Limits::default();
    p.verification_requests(&limits, BackendIdentity::bdd())
        .unwrap()
        .into_iter()
        .map(|(key, request)| {
            let RequestPreparation::Complete(prepared) = request
                .prepare(&p.corpus, &p.keys, &(&limits).into())
                .unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&(&limits).into()).unwrap();
            let CheckOutcome::Complete(report) = prepared.verify(&(&limits).into()).unwrap() else {
                panic!()
            };
            assert_eq!(report.results.value.context.verification, Some(key.clone()));
            (
                key.0.name.to_string(),
                report.results.value.groups.into_values().collect(),
            )
        })
        .collect()
}
#[test]
fn explicit_selection_and_no_implicit_verification() {
    let unconfigured = single(BODY);
    assert!(
        unconfigured
            .verification_requests(&Limits::default(), BackendIdentity::bdd())
            .unwrap()
            .is_empty()
    );
    assert!(
        unconfigured
            .request(&Limits::default(), BackendIdentity::bdd())
            .unwrap()
            .verification
            .is_none()
    );
    let p = single(&format!(
        "verification restricted {{ assumptions: [a]; obligations: [o]; }} {BODY} verification unrestricted {{ assumptions: []; obligations: [o]; }} verification consistency {{ assumptions: [a]; obligations: []; }}"
    ));
    let results = checked(&p);
    assert_eq!(results[0].0, "consistency");
    assert!(results[0].1.is_empty());
    assert_eq!(
        results[1],
        ("restricted".into(), vec![ScopedResult::Proved])
    );
    assert_eq!(results[2].0, "unrestricted");
    assert!(matches!(
        results[2].1.as_slice(),
        [ScopedResult::Counterexample(..)]
    ));
    assert!(
        p.verification_requests(&Limits::default(), BackendIdentity::sat())
            .unwrap()
            .iter()
            .all(|(_, r)| r.backend == BackendIdentity::sat())
    );
}
#[test]
fn loader_and_index_reject_verification_errors() {
    for text in [
        "verification v { assumptions: [missing]; obligations: [o]; }",
        "verification v { assumptions: [o]; obligations: [o]; }",
        "verification v { assumptions: [a]; obligations: [a]; }",
        "verification v { assumptions: [a]; obligations: [missing]; }",
        "verification v { assumptions: [later]; obligations: []; } verification later { assumptions: []; obligations: []; }",
        "namespace left { assumption shared: at_most_one(p, group_by: ()); } namespace right { assumption shared: at_most_one(p, group_by: ()); } use left; use right; verification v { assumptions: [shared]; obligations: [o]; }",
        "namespace left { obligation shared: at_most_one(q, group_by: ()); } namespace right { obligation shared: at_most_one(q, group_by: ()); } use left; use right; verification v { assumptions: [a]; obligations: [shared]; }",
        "verification v { assumptions: [a, ::a]; obligations: [o]; }",
        "verification v { assumptions: [a]; obligations: [o, ::o]; }",
        "verification v { obligations: [o]; }",
        "verification v { assumptions: [a]; }",
        "verification v { obligations: [o]; assumptions: [a]; }",
        "verification v { assumptions: []; obligations: []; } verification v { assumptions: []; obligations: []; }",
    ] {
        let source = SourceFile::new("file:///program.den", 1, format!("{BODY} {text}"));
        let membership = ProgramMembership::single("root", [source.uri.clone()]);
        let errors = load(&membership, &[source.clone()]).unwrap_err();
        let tree = parser().parse(source.text.as_ref(), None).unwrap();
        let mut index = index::Index::default();
        index.update(source.clone(), tree);
        index.set_membership(&membership).unwrap();
        let diagnostics = index.diagnostics("root", &source.uri);
        assert!(
            diagnostics.iter().any(|d| !d.warning),
            "{text}: {diagnostics:?}"
        );
        if text.contains("missing")
            || text.contains("shared")
            || text.contains("later")
            || text.contains("[o]; obligations: [o]")
            || text.contains("[a]; obligations: [a]")
            || text.contains(", ::")
        {
            assert!(
                errors.iter().all(|e| diagnostics
                    .iter()
                    .any(|d| d.message == e.message && d.span == e.range)),
                "{errors:?} != {diagnostics:?}"
            );
        }
    }
}
#[test]
fn distinct_contract_kinds_and_field_words_can_share_names() {
    let text = "sort assumptions; input obligations(x: assumptions); assumption same: at_most_one(obligations, group_by: ()); obligation same: at_most_one(obligations, group_by: ()); verification same { assumptions: [same]; obligations: [same]; } verification 'verification' { assumptions: []; obligations: []; }";
    let p = single(text);
    assert_eq!(p.corpus.verifications().count(), 2);
    assert!(
        single(
            "sort S; input p(verification: S); verification v { assumptions: []; obligations: []; }"
        )
        .corpus
        .verifications()
        .next()
        .is_some()
    );
    assert!(
        load(
            &ProgramMembership::single("r", ["x".into()]),
            &[SourceFile::new("x", 1, "sort verification;")]
        )
        .is_err()
    );
    let mut index = index::Index::default();
    index.update(
        SourceFile::new("x", 1, text),
        parser().parse(text, None).unwrap(),
    );
    index
        .set_membership(&ProgramMembership::single("r", ["x".into()]))
        .unwrap();
    assert!(index.diagnostics("r", "x").is_empty());
}
#[test]
fn ir_contracts_round_trip_with_selected_keys_and_origins() {
    let text = format!(
        "namespace 'a::b' {{ {BODY} verification 'check name' {{ assumptions: [a]; obligations: [o]; }} }} namespace app {{ verification local {{ assumptions: ['a::b'::a]; obligations: ['a::b'::o]; }} }}"
    );
    let p = single(&text);
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
        let (membership, documents) = bundle.documents("file:///export");
        let q = load_with_resolver(&membership, &documents, Some(&mut &p.sources)).unwrap();
        support::compare(&export, &q, "file:///export", embedded_origins);
        let keys = |p: &LoadedProgram| {
            p.keys
                .bindings()
                .entries()
                .filter_map(|(key, _)| match key {
                    OccurrenceKey::Assumption(_)
                    | OccurrenceKey::Obligation(_)
                    | OccurrenceKey::Verification(_) => Some(key.clone()),
                    _ => None,
                })
                .collect::<BTreeSet<_>>()
        };
        assert_eq!(keys(&p), keys(&q));
        let selections = |p: &LoadedProgram| {
            p.corpus
                .verifications()
                .map(|v| {
                    (
                        p.keys.verification(v.id).unwrap().clone(),
                        (
                            v.assumptions
                                .iter()
                                .map(|id| p.keys.assumption(*id).unwrap().clone())
                                .collect::<Vec<_>>(),
                            v.obligations
                                .iter()
                                .map(|id| p.keys.obligation(*id).unwrap().clone())
                                .collect::<Vec<_>>(),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>()
        };
        assert_eq!(selections(&p), selections(&q));
        for v in q.corpus.verifications() {
            assert_eq!(
                !q.embedded.provenance.origins(v.id).is_empty(),
                embedded_origins
            );
        }
        assert_eq!(checked(&p), checked(&q));
    }
}
#[test]
fn closure_verifications_run_once_and_consumer_can_add_its_own() {
    let membership = ProgramMembership {
        root: "app".into(),
        roots: BTreeMap::from([
            (
                "app".into(),
                RootInfo {
                    files: BTreeSet::from(["app.den".into()]),
                    libraries: BTreeSet::from(["lib".into(), "bridge".into()]),
                },
            ),
            (
                "bridge".into(),
                RootInfo {
                    files: BTreeSet::new(),
                    libraries: BTreeSet::from(["lib".into()]),
                },
            ),
            (
                "lib".into(),
                RootInfo {
                    files: BTreeSet::from(["lib.den".into()]),
                    libraries: BTreeSet::new(),
                },
            ),
        ]),
    };
    let docs = [
        SourceFile::new(
            "lib.den",
            1,
            format!(
                "namespace lib; {BODY} verification v {{ assumptions: [a]; obligations: [o]; }}"
            ),
        ),
        SourceFile::new(
            "app.den",
            1,
            "namespace app; verification v { assumptions: []; obligations: [lib::o]; }",
        ),
    ];
    let p = load(&membership, &docs).unwrap();
    let requests = p
        .verification_requests(&Limits::default(), BackendIdentity::bdd())
        .unwrap();
    assert_eq!(requests.len(), 2);
    assert_ne!(requests[0].0, requests[1].0);
    assert_eq!(requests[0].1.obligations, requests[1].1.obligations);
    assert_ne!(requests[0].1.constraints, requests[1].1.constraints);
}
