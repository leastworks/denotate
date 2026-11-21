use denotate_check::{CheckError, Limits, stable_query};
use denotate_ir::*;
use denotate_ir_text::*;
mod support;

fn single(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}

#[test]
fn loaded_completion_queries_use_ground_hypothesis_cones_and_keep_processing_separate() {
    use denotate_check::{GroundAtom, completion_query::*};
    let p = single(
        "sort S; const a, b: S; input raw(); relation p(x:S); p(X):-p(X); relation recognized(); recognized():-p(a); relation broken(); broken():-!broken(); verification v{semantics:completion;hypothesis:recognized;assumptions:[];obligations:[];}",
    );
    let v = p.corpus.verifications().next().unwrap().id;
    let Preparation::Ready(engine) = Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap() else {
        panic!()
    };
    let relation = p.corpus.relations().find(|r| r.name == "p").unwrap().id;
    let a = p.corpus.constants().find(|c| c.name == "a").unwrap().id;
    let b = p.corpus.constants().find(|c| c.name == "b").unwrap().id;
    let ObservationOutcome::Accepted {
        classification,
        processing: Interpretations::NoMeaning,
    } = engine.observation([]).unwrap()
    else {
        panic!()
    };
    assert_eq!(
        classification.value(&GroundAtom::new(relation, [a])),
        Some(true)
    );
    assert_eq!(classification.value(&GroundAtom::new(relation, [b])), None);
    roundtrip(&p);
}

#[test]
fn loaded_recursive_within_provider_gets_completion_compatibility_refusal() {
    use denotate_check::completion_query::*;
    let p = single(
        "sort S; const a: S; relation candidates(x:S); candidates(X):-candidates(X); input raw(x:S) within candidates; verification v{semantics:completion;assumptions:[];obligations:[];}",
    );
    let v = p.corpus.verifications().next().unwrap().id;
    let Preparation::Unsupported(issue) = Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap() else {
        panic!()
    };
    assert!(matches!(
        issue.source,
        CompatibilitySource::InputDomain { .. }
    ));
    assert!(!issue.recursive_component.is_empty());
}
fn roundtrip(p: &LoadedProgram) {
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
        assert!(bundle.files["program.den"].contains("semantics: completion;"));
        assert!(!bundle.files["program.den"].contains("semantics: stable;"));
        let (membership, documents) = bundle.documents("file:///export");
        let loaded = load_with_resolver(&membership, &documents, Some(&mut &p.sources)).unwrap();
        support::compare(&export, &loaded, "file:///export", embedded_origins);
        assert_eq!(
            p.verification_requests(&Limits::default()).unwrap(),
            loaded.verification_requests(&Limits::default()).unwrap()
        );
    }
}

#[test]
fn completion_declarations_round_trip_references_selection_keys_and_origins() {
    let p = single(
        "namespace 'a::b' { input 'ready now'(); relation other(); obligation total:no_rejections('ready now') message \"Recognize every input\"; verification checks {semantics:completion; hypothesis:'ready now'; decisions:[other, 'ready now']; assumptions:[]; obligations:[total];} } namespace app { verification own {semantics:completion; hypothesis:'a::b'::'ready now'; decisions:[]; assumptions:[]; obligations:['a::b'::total];} verification ordinary { semantics:stable; assumptions:[]; obligations:[];} verification equations {semantics:completion; assumptions:[]; obligations:[];} }",
    );
    roundtrip(&p);
}

#[test]
fn construction_api_exports_the_same_completion_contract() {
    let mut corpus = Corpus::new();
    let h = corpus
        .declare_relation_in(
            Namespace::new(["lib"]).unwrap(),
            "recognized",
            RelationRole::Derived,
            [],
        )
        .unwrap();
    let o = corpus
        .require_no_rejections_in(Namespace::new(["lib"]).unwrap(), "total", h, "No rejection")
        .unwrap();
    let v = corpus
        .verification_with_options_in(
            Namespace::new(["app"]).unwrap(),
            "checks",
            [],
            [o],
            [],
            VerificationOptions {
                semantics: Semantics::Completion,
                hypothesis: Some(h),
                decisions: None,
            },
        )
        .unwrap();
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&corpus).into_iter().map(|id| (id, 0)).collect(),
    };
    let export = ExportProgram {
        corpus: &corpus,
        domains: &Default::default(),
        sources: &Sources::default(),
        provenance: &Provenance::default(),
        layout: &layout,
    };
    let bundle = print(
        &export,
        PrintOptions {
            embedded_origins: false,
        },
    )
    .unwrap();
    let (membership, documents) = bundle.documents("file:///export");
    let loaded = load(&membership, &documents).unwrap();
    support::compare(&export, &loaded, "file:///export", false);
    assert_eq!(
        loaded
            .corpus
            .verifications()
            .next()
            .unwrap()
            .options
            .semantics,
        corpus.verification(v).unwrap().options.semantics
    );
}

#[test]
fn invalid_completion_declarations_have_loader_and_index_errors() {
    let base = "sort S; input h(); relation other(); relation unary(x:S); obligation total:no_rejections(h);";
    for addition in [
        "verification v{semantics:completion; hypothesis:unary; assumptions:[];obligations:[];}",
        "obligation bad:no_rejections(unary);",
        "obligation bad:no_rejections(missing);",
        "verification v{semantics:completion; hypothesis:missing;assumptions:[];obligations:[];}",
        "verification v{semantics:completion; hypothesis:total;assumptions:[];obligations:[];}",
        "verification v{semantics:completion; hypothesis:other;assumptions:[];obligations:[total];}",
        "verification v{semantics:completion;assumptions:[];obligations:[total];}",
        "verification v{hypothesis:h;assumptions:[];obligations:[total];}",
        "assumption a:no_rejections(h);",
        "obligation bad:no_rejections(h,group_by:());",
        "verification v{semantics:typo;assumptions:[];obligations:[];}",
        "verification v{semantics:completion;decisions:[missing];assumptions:[];obligations:[];}",
        "verification v{semantics:completion;decisions:[total];assumptions:[];obligations:[];}",
        "verification v{semantics:completion;decisions:[];decisions:[];assumptions:[];obligations:[];}",
        "verification v{semantics:completion;semantics:stable;assumptions:[];obligations:[];}",
        "verification v{hypothesis:h;hypothesis:h;assumptions:[];obligations:[];}",
    ] {
        let source = SourceFile::new("file:///p.den", 1, format!("{base}{addition}"));
        let membership = ProgramMembership::single("root", [source.uri.clone()]);
        assert!(load(&membership, &[source.clone()]).is_err(), "{addition}");
        let tree = parser().parse(source.text.as_ref(), None).unwrap();
        if tree.root_node().has_error() {
            continue;
        }
        let mut index = index::Index::default();
        index.update(source.clone(), tree);
        index.set_membership(&membership).unwrap();
        assert!(
            index
                .diagnostics("root", &source.uri)
                .iter()
                .any(|d| !d.warning),
            "{addition}"
        );
    }
}

#[test]
fn stable_consumers_refuse_before_grounding_and_cannot_override_authored_semantics() {
    for options in [
        "semantics:completion; hypothesis:h;",
        "semantics:completion;",
        "hypothesis:h;",
        "decisions:[h];",
        "decisions:[];",
    ] {
        let p = single(&format!(
            "relation h();h():-h(); verification v{{{options} assumptions:[];obligations:[];}}"
        ));
        let limits = Limits {
            max_work: 0,
            ..Limits::default()
        };
        let (_, mut request) = p.verification_requests(&limits).unwrap().remove(0);
        let expected = request.unsupported_semantics().unwrap();
        assert!(
            matches!(request.prepare(&p.corpus,&p.keys,&(&limits).into()),Err(CheckError::InvalidRequest(reason)) if reason==expected)
        );
        let id = p.corpus.verifications().next().unwrap().id;
        assert!(
            matches!(stable_query::Engine::prepare(&p.corpus,&p.domains,&p.keys,id,&limits,Default::default()),Err(CheckError::InvalidRequest(reason)) if reason==expected)
        );
        assert!(
            matches!(denotate_plan::Planner::prepare(&p.corpus,&p.domains,&p.keys,id,&limits,Default::default()),Err(CheckError::InvalidRequest(reason)) if reason==expected)
        );
        let mut session = denotate_check_session::Session::default();
        assert!(
            matches!(session.prepare(&request,&p.corpus,&p.keys,&(&limits).into()),Err(CheckError::InvalidRequest(reason)) if reason==expected)
        );
        request.semantics = Semantics::Stable;
        request.hypothesis = None;
        request.decisions = None;
        assert!(
            matches!(request.prepare(&p.corpus,&p.keys,&(&limits).into()),Err(CheckError::InvalidRequest(reason)) if reason==expected)
        );
    }
}

#[test]
fn hypothesis_completion_uses_relation_resolution_including_incomplete_names() {
    use index::{Index, Kind, Lookup};
    let library = "namespace lib { input ready(); obligation total:no_rejections(ready); }";
    let mut index = Index::default();
    index.update(
        SourceFile::new("lib", 1, library),
        parser().parse(library, None).unwrap(),
    );
    index
        .set_membership(&ProgramMembership::single(
            "root",
            ["lib".into(), "app".into()],
        ))
        .unwrap();
    for prefix in [
        "verification v{semantics:completion;hypothesis:",
        "obligation o:no_rejections(",
        "verification v{semantics:completion; decisions:[",
    ] {
        for tail in ["", "lib::", "lib::ready"] {
            let text = format!("use lib; {prefix}{tail}");
            index.update(
                SourceFile::new("app", 1, text.clone()),
                parser().parse(&text, None).unwrap(),
            );
            let (lookup, scope, span) = index.files["app"].completion_context(text.len()).unwrap();
            assert_eq!(lookup, Lookup::Name(Kind::Relation));
            assert_eq!(&text[span], tail);
            let candidates = index.candidates("root", "app", &scope, &lookup, None);
            assert!(!candidates.is_empty());
            assert!(
                candidates
                    .iter()
                    .all(|c| index.declaration(c).unwrap().kind == Kind::Relation)
            );
        }
    }
}

#[test]
fn selecting_an_incompatible_rejection_query_highlights_the_reference() {
    let text = "input h(); input other(); obligation total:no_rejections(h); verification v{semantics:completion; hypothesis:other; assumptions:[]; obligations:[total];}";
    let s = SourceFile::new("file:///p.den", 1, text);
    let errors = load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|d| d.range == (text.rfind("total").unwrap()..text.rfind("total").unwrap() + 5)),
        "{errors:?}"
    );
}

#[test]
fn unselected_rejection_query_does_not_change_stable_checking() {
    let p = single(
        "input h(); relation bad(); obligation total:no_rejections(h); obligation clean:empty(bad); verification v{assumptions:[]; obligations:[clean];}",
    );
    let limits = Limits::default();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap(),
        denotate_check::RequestPreparation::Complete(_)
    ));
    stable_query::Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().next().unwrap().id,
        &limits,
        Default::default(),
    )
    .unwrap();
}

#[test]
fn unsupported_library_verification_has_a_labeled_fallback_and_related_hypothesis() {
    use std::collections::BTreeMap;
    let library = SourceFile::new(
        "file:///lib.den",
        1,
        "input h(); verification v{semantics:completion; hypothesis:h; assumptions:[]; obligations:[];}",
    );
    let app = SourceFile::new("file:///app.den", 1, "relation p();");
    let membership = ProgramMembership {
        root: "app".into(),
        roots: BTreeMap::from([
            (
                "app".into(),
                RootInfo {
                    files: [app.uri.clone()].into(),
                    libraries: ["lib".into()].into(),
                },
            ),
            (
                "lib".into(),
                RootInfo {
                    files: [library.uri.clone()].into(),
                    libraries: Default::default(),
                },
            ),
        ]),
    };
    let p = load(&membership, &[library, app]).unwrap();
    let shown = presentation::unsupported_semantics(
        &p,
        p.corpus.verifications().next().unwrap().id,
        "completion semantics not supported here",
    )
    .unwrap();
    assert_eq!(shown.status["state"], "incomplete");
    assert_eq!(shown.diagnostics.len(), 1);
    assert!(shown.diagnostics[0].fallback);
    assert_eq!(shown.diagnostics[0].related.len(), 1);
}
