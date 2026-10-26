use denotate_check::{
    Accounted, BackendIdentity, Limits, LocalCheckOutcome, OperationalLimits, RequestPreparation,
    ScopedResult, ScopedResults,
};
use denotate_check_session::Session;
use denotate_ir::{Literal, Namespace, Term};
use denotate_ir_text::{ActiveRoot, LoadedProgram, ProgramMembership, SourceFile, roots};

fn source(name: &str, text: &str) -> SourceFile {
    SourceFile::new(format!("file:///{name}.den"), 1, text.to_owned())
}
fn membership(root: &str, documents: &[SourceFile]) -> ProgramMembership {
    ProgramMembership::single(root, documents.iter().map(|s| s.uri.clone()))
}
fn load(root: &str, documents: &[SourceFile]) -> denotate_ir_text::Result<LoadedProgram> {
    denotate_ir_text::load(&membership(root, documents), documents)
}
fn single(text: &str) -> LoadedProgram {
    load("m", &[source("m", text)]).unwrap()
}
fn check(
    p: &LoadedProgram,
    session: &mut Session,
    backend: BackendIdentity,
) -> Accounted<ScopedResults> {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p
        .verification_requests(&limits, backend)
        .unwrap()
        .remove(0)
        .1;
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!("preparation exhausted")
    };
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(result) = session.verify(&prepared, &ops).unwrap() else {
        panic!("checking exhausted")
    };
    result.checked.results.clone()
}
fn counterexamples(result: &Accounted<ScopedResults>) -> usize {
    result
        .value
        .groups
        .values()
        .filter(|r| matches!(r, ScopedResult::Counterexample(..)))
        .count()
}
fn keys(p: &LoadedProgram) -> Vec<String> {
    p.keys
        .bindings()
        .entries()
        .map(|(k, _)| format!("{k:?}"))
        .collect()
}

#[test]
fn explicit_domains_preserve_worlds_and_unused_declarations() {
    let code = "module m; sort S; sort Empty; const a,b:S; input p(x:S); obligation unique: at_most_one(p, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }";
    let wide = single(code);
    let narrow = single(&format!("{code} domain S = [a];"));
    assert_eq!(wide.corpus.constants().count(), 2);
    assert_eq!(narrow.corpus.constants().count(), 2);
    assert!(narrow.domains.values().any(Vec::is_empty));
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        let mut session = Session::default();
        assert_eq!(
            counterexamples(&check(&wide, &mut session, backend.clone())),
            1
        );
        let edited = check(&narrow, &mut session, backend.clone());
        assert_eq!(
            edited,
            check(&narrow, &mut Session::default(), backend.clone())
        );
        assert_eq!(counterexamples(&edited), 0);
        assert_eq!(counterexamples(&check(&wide, &mut session, backend)), 1);
    }
}

#[test]
fn imported_assumptions_are_explicit_and_active() {
    let lib = source(
        "lib",
        "module lib; sort S; const a,b:S; input p(x:S); assumption one: at_most_one(p, group_by: ());",
    );
    let root = source(
        "root",
        "module root; use lib; obligation unique: at_most_one(lib::p, group_by: ()); verification checks { assumptions: [lib::one]; obligations: [unique]; }",
    );
    let docs = [root, lib];
    let p = load("root", &docs).unwrap();
    assert_eq!(p.corpus.assumptions().count(), 1);
    assert_eq!(
        p.keys
            .assumption(p.corpus.assumptions().next().unwrap().id)
            .unwrap()
            .0
            .namespace
            .as_ref(),
        "lib"
    );
    assert_eq!(
        p.documents
            .iter()
            .find(|m| m.uri == "file:///lib.den")
            .unwrap()
            .ownership,
        "user"
    );
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        let mut session = Session::default();
        let result = check(&p, &mut session, backend.clone());
        assert_eq!(result.value.context.constraints.len(), 1);
        assert_eq!(counterexamples(&result), 0);
        assert!(
            result
                .value
                .groups
                .values()
                .all(|r| matches!(r, ScopedResult::Proved))
        );
        let mut edited = docs.clone();
        edited[0].text = edited[0]
            .text
            .replace("assumptions: [lib::one]", "assumptions: []")
            .into();
        edited[0].revision += 1;
        let edited = load("root", &edited).unwrap();
        let reused = check(&edited, &mut session, backend.clone());
        assert_eq!(counterexamples(&reused), 1);
        assert_eq!(reused, check(&edited, &mut Session::default(), backend));
    }
}

#[test]
fn whole_export_root_sees_cross_module_conflicts_and_shared_constants() {
    let docs = vec![
        source(
            "lib",
            "module lib; sort S; relation r(x:S); obligation unique: at_most_one(r, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }",
        ),
        source("shared", "module shared; use lib; const a,b:lib::S;"),
        source("a", "module a; use lib; use shared; lib::r(shared::a);"),
        source("b", "module b; use lib; use shared; lib::r(shared::b);"),
        source("root", "module root; use a; use b; use shared;"),
    ];
    let p = load("root", &docs).unwrap();
    assert_eq!(p.corpus.rules().count(), 2);
    for rule in p.corpus.rules() {
        // A rule's lexical owner differs from the namespace of its head.
        assert_eq!(
            p.corpus.namespace(rule.id),
            Some(
                &Namespace::new([p.owners[&rule.id.into()]
                    .trim_start_matches("file:///")
                    .trim_end_matches(".den")])
                .unwrap()
            )
        );
        assert_eq!(
            p.corpus.namespace(rule.head.relation()),
            Some(&Namespace::new(["lib"]).unwrap())
        );
    }
    assert_eq!(p.documents.len(), 5);
    assert_eq!(
        counterexamples(&check(&p, &mut Session::default(), BackendIdentity::bdd())),
        1
    );
    let subset = [docs[0].clone(), docs[1].clone(), docs[2].clone()];
    let constituent = load("a", &subset).unwrap();
    assert_eq!(
        counterexamples(&check(
            &constituent,
            &mut Session::default(),
            BackendIdentity::bdd()
        )),
        0
    );
    let index = roots(&[membership("root", &docs)]).unwrap();
    assert_eq!(index["file:///a.den"], ActiveRoot::Selected("root".into()));
    let mut reordered = docs.clone();
    reordered.reverse();
    assert_eq!(keys(&p), keys(&load("root", &reordered).unwrap()));
    let mut two_roots = docs;
    two_roots.push(source("second", "module second; use a;"));
    assert_eq!(
        roots(&[
            membership("root", &reordered),
            membership("second", &two_roots)
        ])
        .unwrap()["file:///a.den"],
        ActiveRoot::NeedsSelection(vec!["root".into(), "second".into()])
    );
}

#[test]
fn cyclic_imports_install_once_and_visibility_stays_direct() {
    let docs = [
        source(
            "a",
            "module a; use b; sort S; const a:S; relation r(x:S); r(X) :- b::q(X);",
        ),
        source("b", "module b; use a; relation q(x:a::S); q(a::a);"),
    ];
    let p = load("a", &docs).unwrap();
    assert_eq!(p.corpus.sorts().count(), 1);
    assert_eq!(p.corpus.rules().count(), 2);
    let mut docs = docs.to_vec();
    docs.push(source("root", "module root; use a; domain b::S = [];"));
    assert!(
        load("root", &docs).unwrap_err()[0]
            .message
            .contains("Unknown sort")
    );
}

#[test]
fn module_qualification_and_expected_sorts_disambiguate_names() {
    let docs = [
        source("a", "module a; sort S; const same:S; relation r(x:S);"),
        source("b", "module b; sort S; const same:S; relation r(x:S);"),
        source("m", "module m; use a; use b; a::r(a::same); b::r(b::same);"),
    ];
    let p = load("m", &docs).unwrap();
    assert_eq!(
        p.corpus
            .sorts()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        vec!["S", "S"]
    );
    assert_eq!(
        p.corpus
            .relations()
            .map(|r| r.name.as_str())
            .collect::<Vec<_>>(),
        vec!["r", "r"]
    );
    let mut ambiguous = docs.to_vec();
    ambiguous[2] = source("m", "module m; use a; use b; r(same);");
    assert!(
        load("m", &ambiguous).unwrap_err()[0]
            .message
            .contains("Ambiguous relation")
    );
    let same = single(
        "module m; sort A; sort B; const same:A; const same:B; relation r(a:A,b:B); r(same,same);",
    );
    let arguments = same.corpus.rules().next().unwrap().head.arguments();
    assert_ne!(arguments[0].value(), arguments[1].value());
}

#[test]
fn generated_and_quoted_frontend_identity_do_not_alias() {
    for declarations in [
        "relation $condition_9(); relation '$condition_9'();",
        "relation '$condition_9'(); relation $condition_9();",
    ] {
        let p = single(&format!(
            "module m; {declarations} $condition_9(); '$condition_9'() :- !$condition_9();"
        ));
        let relations = p.corpus.relations().collect::<Vec<_>>();
        for relation in &relations {
            assert_eq!(
                p.corpus.namespace(relation.id),
                Some(&Namespace::new(["m"]).unwrap())
            );
        }
        for rule in p.corpus.rules() {
            assert_eq!(
                p.corpus.namespace(rule.id),
                Some(&Namespace::new(["m"]).unwrap())
            );
        }
        assert_eq!(relations[0].name, relations[1].name);
        assert_ne!(
            p.corpus.is_generated_relation(relations[0].id),
            p.corpus.is_generated_relation(relations[1].id)
        );
        assert_ne!(
            p.keys.relation(relations[0].id).unwrap(),
            p.keys.relation(relations[1].id).unwrap()
        );
        assert!(matches!(
            p.corpus.rules().nth(1).unwrap().body[0],
            Literal::Negative(_)
        ));
    }
}

#[test]
fn value_literals_and_quoted_names_keep_canonical_values_and_exact_spans() {
    let p = single(
        "module m; sort 'Integer Case'; const -01, 002, '🚀': 'Integer Case'; relation 'holds value'(x:'Integer Case'); 'holds value'(-1); 'holds value'(2); 'holds value'('🚀');",
    );
    assert_eq!(
        p.corpus
            .constants()
            .map(|c| c.name.as_str())
            .collect::<Vec<_>>(),
        vec!["-1", "2", "🚀"]
    );
    let last = p.corpus.rules().last().unwrap();
    let origin = p.provenance.origins(last.head.arguments()[0].id())[0].span;
    assert_eq!(p.sources.text(origin).unwrap(), "'🚀'");
}

#[test]
fn stable_keys_and_warm_answers_ignore_trivia_and_location_syntax() {
    let cold = single(
        "module m; sort S; const a,b:S; input p(x:S); relation r(x:S); r(X) :- p(X); r(X) :- p(X); obligation u: at_most_one(r, group_by: ()); verification checks { assumptions: []; obligations: [u]; }",
    );
    let warm = single(
        "// shifted\nmodule m; sort S; const a,b:S; input p(x:S); relation r(x:S); r( X ) :- p(X) loc(#map);\nr(X) :- p( X ); obligation u: at_most_one(r, group_by: ()); verification checks { assumptions: []; obligations: [u]; } #map = {head.0: loc(#dsl 1:1 to 1:2)}; #dsl = source(\"file:///original.dsl\", view: \"dsl\", hash: \"sha256:0000000000000000000000000000000000000000000000000000000000000000\");",
    );
    assert_eq!(keys(&cold), keys(&warm));
    let rules = cold
        .corpus
        .rules()
        .map(|r| cold.keys.rule(r.id).unwrap())
        .collect::<Vec<_>>();
    assert_ne!(rules[0], rules[1]);
    let mut session = Session::default();
    let a = check(&cold, &mut session, BackendIdentity::bdd());
    let b = check(&warm, &mut session, BackendIdentity::bdd());
    assert_eq!(a, b);
    assert!(session.stats().evaluation_hits > 0);
    assert_eq!(warm.documents[0].location_syntax.len(), 3);
    for (id, origins) in warm.provenance.entries() {
        assert_eq!(origins.len(), 1, "{id:?}");
        assert_eq!(
            warm.sources
                .snapshot(origins[0].span.snapshot())
                .unwrap()
                .view,
            "denotate"
        );
    }
}

#[test]
fn anonymous_terms_are_distinct_and_cannot_capture_authored_variables() {
    let p = single(
        "module m; sort S; input p(a:S,b:S); relation r(x:S); r(?'__den_anonymous_0') :- p(?'__den_anonymous_0', _), p(_, _);",
    );
    let rule = p.corpus.rules().next().unwrap();
    let variables = rule
        .body
        .iter()
        .flat_map(|a| a.atom().arguments())
        .map(|t| match t.value() {
            Term::Variable { name, .. } => name,
            _ => panic!(),
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(variables.len(), 4);
}

#[test]
fn invalid_programs_return_current_source_diagnostics_without_partial_ir() {
    for (code, expected) in [
        ("sort S; sort S;", "Duplicate sort name"),
        (
            "sort S; const a:S; domain S=[a,a];",
            "Duplicate domain member",
        ),
        (
            "sort S; domain S=[]; domain S=[];",
            "More than one explicit domain",
        ),
        (
            "sort S; const a:S; domain S=[]; relation p(x:S); p(a);",
            "outside its explicit domain",
        ),
        (
            "sort S; relation p(x:S); p(X);",
            "must occur in a positive body literal",
        ),
        (
            "sort S; input p(x:S); const a:S; p(a);",
            "cannot be defined by a rule",
        ),
        (
            "relation r(); assumption a: at_most_one(r, group_by: ());",
            "only input relations",
        ),
        (
            "input p(); obligation a: at_most_one(p, group_by: missing);",
            "Unknown grouping",
        ),
        (
            "sort S; input p(x:S); obligation a: at_most_one(p, group_by: (x,x));",
            "Duplicate grouping",
        ),
        ("input $bad();", "zero-arity derived"),
        ("sort S; const 9223372036854775808:S;", "64-bit"),
        ("sort S; const module:S;", "Reserved word"),
        ("relation r(); r( ;", "Expected"),
        ("use missing;", "Unknown namespace"),
    ] {
        let errors = load("m", &[source("m", &format!("module m; {code}"))]).unwrap_err();
        assert!(
            errors.iter().any(|e| e.message.contains(expected)),
            "{code}: {errors:?}"
        );
        assert_eq!(errors[0].uri, "file:///m.den");
    }
}

#[test]
fn unrelated_invalid_files_do_not_block_root_and_namespaces_can_span_files() {
    let docs = [
        source("m", "module m; relation r(); r();"),
        source("bad", "module bad; relation r(;"),
        source("broken", "not even a module"),
    ];
    let selected = membership("root", &docs[..1]);
    assert_eq!(
        denotate_ir_text::load(&selected, &docs)
            .unwrap()
            .corpus
            .rules()
            .count(),
        1
    );
    let reopened = source("elsewhere", "module m; r();");
    assert_eq!(
        load("m", &[docs[0].clone(), reopened])
            .unwrap()
            .corpus
            .rules()
            .count(),
        2
    );
}

#[test]
fn quoted_qualified_references_and_generated_references_decode_without_aliasing() {
    let docs = [
        source(
            "lib",
            "module 'lib::one'; sort 'Odd Sort'; const 'line\\nname', 01:'Odd Sort'; relation $condition_8(); relation '$condition_8'(); relation 'r::name'(x:'Odd Sort'); $condition_8();",
        ),
        source(
            "m",
            "module m; use 'lib::one'; 'lib::one'::'r::name'('lib::one'::'line\\nname') :- 'lib::one'::$condition_8(); 'lib::one'::'r::name'('lib::one'::1) :- !'lib::one'::'$condition_8'();",
        ),
    ];
    let p = load("m", &docs).unwrap();
    assert_eq!(p.corpus.rules().count(), 3);
    assert_eq!(p.corpus.constants().next().unwrap().name, "line\nname");
    let rule = p.corpus.rules().last().unwrap();
    assert!(
        !p.corpus
            .is_generated_relation(rule.body[0].atom().relation())
    );
}

#[test]
fn value_encoding_fixture_checks_and_rule_edits_refresh_answers() {
    let docs = [
        source("library", include_str!("../fixtures/library/library.den")),
        source("mappings", include_str!("../fixtures/mappings.den")),
        source("root", include_str!("../fixtures/root.den")),
    ];
    let p = load("root", &docs).unwrap();
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        let mut session = Session::default();
        let result = check(&p, &mut session, backend.clone());
        assert_eq!(counterexamples(&result), 1);
        assert_eq!(result.value.context.constraints.len(), 1);
        let mut edited = docs.clone();
        edited[1].text = edited[1].text.replace("mapped_to(j, a);", "").into();
        edited[1].revision += 1;
        let edited = load("root", &edited).unwrap();
        let result = check(&edited, &mut session, backend.clone());
        assert_eq!(counterexamples(&result), 0);
        assert_eq!(result, check(&edited, &mut Session::default(), backend));
    }
}

#[test]
fn declaration_keywords_require_quoting_and_quoted_names_are_usable() {
    for keyword in ["domain", "obligation", "assumption", "source", "namespace"] {
        let code = format!("module m; sort S; const a:S; relation {keyword}(x:S);");
        let errors = load("m", &[source("m", &code)]).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|e| e.message.contains("Reserved word must be quoted")),
            "{keyword}: {errors:?}"
        );
        assert_eq!(&code[errors[0].range.clone()], keyword);
        single(&format!(
            "module m; sort S; const a:S; relation '{keyword}'(x:S); '{keyword}'(a); m::'{keyword}'(a);"
        ));
        let qualified =
            format!("module m; sort S; const a:S; relation '{keyword}'(x:S); m::{keyword}(a);");
        assert!(
            load("m", &[source("m", &qualified)]).unwrap_err()[0]
                .message
                .contains("Reserved word must be quoted")
        );
        single(&format!(
            "module m; sort S; const '{keyword}':S; relation r(x:S); r('{keyword}');"
        ));
        assert!(
            load(
                "m",
                &[source(
                    "m",
                    &format!("module m; sort S; const {keyword}:S;")
                )]
            )
            .unwrap_err()[0]
                .message
                .contains("Reserved word must be quoted")
        );
    }
}

#[test]
fn reserved_words_are_allowed_as_parameter_and_grouping_names() {
    for word in [
        "input",
        "source",
        "domain",
        "obligation",
        "assumption",
        "module",
        "use",
        "sort",
        "const",
        "relation",
    ] {
        let program = single(&format!(
            "module m; sort S; const a,b:S; input p({word}:S); assumption w: at_most_one(p, group_by: {word}); obligation unique: at_most_one(p, group_by: ({word}));"
        ));
        assert_eq!(
            match &program.corpus.assumptions().next().unwrap().restriction {
                denotate_ir::Restriction::AtMostOne { group_by, .. } => group_by.clone(),
            },
            vec![0]
        );
        assert_eq!(
            program.corpus.relations().next().unwrap().parameters[0].name,
            word
        );
    }
}

#[test]
fn construction_diagnostics_name_sorts_instead_of_arena_handles() {
    let docs = [
        source("a", "module a; sort S; input p(x:S);"),
        source("b", "module b; sort S; input q(x:S);"),
        source(
            "m",
            "module m; use a; use b; relation r(); r() :- a::p(X), b::q(X);",
        ),
    ];
    let errors = load("m", &docs).unwrap_err();
    assert_eq!(
        errors[0].message,
        "Variable \"X\" has conflicting sorts \"a::S\" and \"b::S\""
    );
    assert_eq!(errors[0].uri, "file:///m.den");
    for bad in [
        "sort S; sort S;",
        "sort S; relation r(x:S); r(X);",
        "sort S; const a:S; input p(x:S); p(a);",
        "sort S; relation r(x:S,x:S);",
    ] {
        let errors = load("m", &[source("m", &format!("module m; {bad}"))]).unwrap_err();
        for e in errors {
            assert!(
                !e.message.contains("OccurrenceId")
                    && !e.message.contains("Arena(")
                    && !e.message.contains("SortId"),
                "{e:?}"
            );
        }
    }
}

#[test]
fn reserved_relation_diagnostic_survives_parser_recovery_contexts() {
    for keyword in ["domain", "obligation", "assumption", "source", "namespace"] {
        for parameters in ["", "x:S", "x:S,y:S"] {
            for suffix in [
                "",
                "relation other();",
                "domain(a);",
                "p(a);",
                "// comment\nrelation other(x:S);",
            ] {
                let code = format!(
                    "module m; sort S; const a:S; relation {keyword}({parameters}); {suffix}"
                );
                let errors = load("m", &[source("m", &code)]).unwrap_err();
                let start = code.find(&format!("relation {keyword}")).unwrap() + "relation ".len();
                assert!(
                    errors
                        .iter()
                        .any(|d| d.range == (start..start + keyword.len())
                            && d.message == "Reserved word must be quoted"),
                    "{code}\n{errors:?}\n{}",
                    denotate_ir_text::parser()
                        .parse(&code, None)
                        .unwrap()
                        .root_node()
                        .to_sexp()
                );
            }
        }
    }
}

#[test]
fn hierarchical_namespaces_reopen_across_files_and_keep_exact_origins() {
    let docs = [
        source(
            "one",
            "namespace billing { sort S; const a:S; namespace invoices { relation r(x:S); } }",
        ),
        source(
            "two",
            "namespace billing::invoices; r(a); relation $condition_1(); $condition_1();",
        ),
        source(
            "three",
            "namespace reports { billing::invoices::r(billing::a) :- billing::invoices::$condition_1(); }",
        ),
    ];
    let p = load("root", &docs).unwrap();
    let rules = p.corpus.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 3);
    for rule in &rules {
        let uri = &p.owners[&rule.id.into()];
        let expected = if uri.ends_with("three.den") {
            vec!["reports"]
        } else {
            vec!["billing", "invoices"]
        };
        assert_eq!(
            p.corpus.namespace(rule.id),
            Some(&Namespace::new(expected).unwrap())
        );
        let span = p.provenance.origins(rule.id)[0].span;
        assert_eq!(&p.sources.snapshot(span.snapshot()).unwrap().uri, uri);
        assert!(p.sources.text(span).unwrap().ends_with(';'));
    }
    let helper = p
        .corpus
        .relations()
        .find(|r| p.corpus.is_generated_relation(r.id))
        .unwrap();
    assert_eq!(
        p.corpus.namespace(helper.id),
        Some(&Namespace::new(["billing", "invoices"]).unwrap())
    );
}

#[test]
fn quoted_namespace_segments_are_not_nested_paths() {
    let p = single(
        "namespace a::b { relation r(); r(); } namespace 'a::b' { relation r(); r(); } namespace 'a\\'::b'::'3' { relation r(); r(); } namespace caller { a::b::r(); 'a::b'::r(); 'a\\'::b'::'3'::r(); }",
    );
    let namespaces = p
        .corpus
        .relations()
        .map(|r| p.corpus.namespace(r.id).unwrap().clone())
        .collect::<Vec<_>>();
    assert_eq!(
        namespaces,
        vec![
            Namespace::new(["a", "b"]).unwrap(),
            Namespace::new(["a::b"]).unwrap(),
            Namespace::new(["a'::b", "3"]).unwrap()
        ]
    );
    assert_eq!(p.corpus.rules().count(), 6);
    assert_eq!(p.keys.bindings().entries().count(), keys(&p).len());
}

#[test]
fn visibility_is_lexical_includes_ancestors_and_deduplicates_paths() {
    let p = single(
        "namespace library { relation p(); } namespace a { use library; sort S; const x:S; namespace b { use library; use a; relation r(x:S); r(x) :- p(); } } namespace c { library::p(); }",
    );
    assert_eq!(p.corpus.rules().count(), 2);
    for (code, expected) in [
        (
            "namespace lib { relation p(); } namespace a { use lib; } namespace b { p(); }",
            "Unknown relation",
        ),
        (
            "namespace lib { relation p(); } namespace a { use lib; } namespace b { use a; p(); }",
            "Unknown relation",
        ),
        (
            "namespace a { namespace b { relation p(); } } namespace c { use a; p(); }",
            "Unknown relation",
        ),
        (
            "relation p(); namespace a { relation p(); p(); }",
            "Ambiguous relation",
        ),
        (
            "namespace a { relation p(); namespace b { relation p(); p(); } }",
            "Ambiguous relation",
        ),
        (
            "namespace a { relation p(); } namespace b { relation p(); } namespace c { use a; use b; p(); }",
            "Ambiguous relation",
        ),
        ("namespace a::b; use missing;", "Unknown namespace"),
    ] {
        let errors = load("root", &[source("case", code)]).unwrap_err();
        assert!(errors[0].message.contains(expected), "{code}: {errors:?}");
    }
    let global = single("relation p(); namespace a { relation p(); ::p(); a::p(); }");
    let rules = global.corpus.rules().collect::<Vec<_>>();
    assert_ne!(rules[0].head.relation(), rules[1].head.relation());
}

#[test]
fn imports_are_file_local_and_do_not_supply_membership() {
    let docs = [
        source("a", "namespace shared; use lib; relation r(); r() :- p();"),
        source("b", "namespace shared; r() :- p();"),
        source("library", "namespace lib; relation p();"),
    ];
    assert!(
        load("root", &docs).unwrap_err()[0]
            .message
            .contains("Unknown relation")
    );
    let only_a = membership("root", &docs[..1]);
    assert!(
        denotate_ir_text::load(&only_a, &docs).unwrap_err()[0]
            .message
            .contains("Unknown namespace")
    );
    let valid = [
        docs[0].clone(),
        source("b", "namespace shared; r() :- lib::p();"),
        docs[2].clone(),
    ];
    assert_eq!(load("root", &valid).unwrap().corpus.rules().count(), 2);
}

#[test]
fn constant_keys_encode_namespaces_without_debug_text_or_separator_collisions() {
    let p = single(
        "sort S; const 'a::b::same':S; namespace a::b { const same:S; } namespace 'a::b' { const same:S; } namespace a { const 'b::same':S; }",
    );
    let names = p
        .corpus
        .constants()
        .map(|c| p.keys.constant(c.id).unwrap().name.as_ref())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        names,
        std::collections::BTreeSet::from([
            r#"["","a::b::same"]"#,
            r#"["a::b","same"]"#,
            r#"["'a::b'","same"]"#,
            r#"["a","b::same"]"#,
        ])
    );
}

#[test]
fn document_namespaces_omit_empty_implicit_scopes_and_retain_authored_ones() {
    for (code, paths) in [
        ("namespace a;", vec![vec!["a"]]),
        ("use lib; namespace a::b; sort S;", vec![vec!["a", "b"]]),
        ("module a; relation p(); p();", vec![vec!["a"]]),
        (
            "namespace a { namespace b {} } // trailing comment }",
            vec![vec!["a"], vec!["a", "b"]],
        ),
        ("sort S; namespace a {}", vec![vec![], vec!["a"]]),
        ("sort S;", vec![vec![]]),
        ("use lib;", vec![]),
        ("// empty document", vec![]),
        ("namespace 'a{' // not a block\n;", vec![vec!["a{"]]),
    ] {
        let p = load(
            "root",
            &[source("main", code), source("library", "namespace lib;")],
        )
        .unwrap();
        let document = p
            .documents
            .iter()
            .find(|d| d.uri == "file:///main.den")
            .unwrap();
        let expected = paths
            .into_iter()
            .map(|p| Namespace::new(p).unwrap())
            .collect();
        assert_eq!(document.namespaces, expected, "{code}");
    }
    let p = single("namespace 'ends}' { relation p(); p(); } // }");
    assert_eq!(
        p.corpus.namespace(p.corpus.rules().next().unwrap().id),
        Some(&Namespace::new(["ends}"]).unwrap())
    );
}

#[test]
fn file_scoped_namespaces_allow_only_imports_before_the_header_and_aliases_agree() {
    for header in ["namespace a::b;", "module a::b;"] {
        let code = format!(
            "\u{feff}// leading comment\nuse lib; // before header\n{header}\nrelation local(x:S); local(a);"
        );
        let file = load(
            "root",
            &[
                source("main", &code),
                source("library", "namespace lib; sort S; const a:S;"),
            ],
        )
        .unwrap();
        let rule = file.corpus.rules().next().unwrap();
        assert_eq!(
            file.corpus.namespace(rule.id),
            Some(&Namespace::new(["a", "b"]).unwrap())
        );
        for prefix in [
            "sort S;",
            "const a:S;",
            "relation p();",
            "input p();",
            "p();",
            "domain S=[];",
            "obligation w: at_most_one(p, group_by: ());",
            "assumption w: at_most_one(p, group_by: ());",
            "#s = source(\"file:///source\", view: \"dsl\", hash: \"sha256:0000000000000000000000000000000000000000000000000000000000000000\");",
            "#origin = loc(#s 1:1 to 1:2);",
        ] {
            let code = format!("use lib; {prefix} // before header\n{header} relation local();");
            // The shared grammar rejects it too, so B reports a syntax error.
            assert!(
                denotate_ir_text::parser()
                    .parse(&code, None)
                    .unwrap()
                    .root_node()
                    .has_error(),
                "{code}"
            );
            assert!(load("root", &[source("main", &code)]).is_err(), "{code}");
        }
    }
    let modern = single("namespace a::b; relation p(); p();");
    let legacy = single("module a::b; relation p(); p();");
    assert_eq!(keys(&modern), keys(&legacy));
    for code in [
        "namespace a; namespace b;",
        "namespace a; namespace b {}",
        "namespace a {} namespace b;",
        "namespace a { namespace b; }",
        "module a; namespace b {}",
        "module a ownership user;",
        "namespace a::1;",
        "namespace a::$helper;",
        "namespace ::a;",
    ] {
        assert!(load("root", &[source("case", code)]).is_err(), "{code}");
    }
}

#[test]
fn moving_constructs_between_files_preserves_resolved_keys_and_warm_answers() {
    let before = [
        source("a", "namespace lib; sort S; const a,b:S; input p(x:S);"),
        source(
            "b",
            "namespace n; use lib; relation r(x:S); r(X) :- p(X); r(X) :- p(X); obligation unique: at_most_one(r, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }",
        ),
    ];
    let after = [
        source(
            "x",
            "namespace lib { sort S; const a,b:S; input p(x:S); } namespace n { relation r(x:lib::S); r(X) :- lib::p(X); }",
        ),
        source(
            "y",
            "namespace n; r(X) :- lib::p(X); obligation unique: at_most_one(n::r, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }",
        ),
    ];
    let original = load("root", &before).unwrap();
    let moved = load("root", &after).unwrap();
    assert_eq!(keys(&original), keys(&moved));
    assert_eq!(moved.corpus.rules().count(), 2);
    assert_ne!(
        moved.corpus.rules().next().unwrap().id,
        moved.corpus.rules().last().unwrap().id
    );
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        let mut session = Session::default();
        let first = check(&original, &mut session, backend.clone());
        let warm = check(&moved, &mut session, backend.clone());
        assert_eq!(first.value, warm.value);
        assert_eq!(warm, check(&moved, &mut Session::default(), backend));
    }
}

#[test]
fn duplicate_declarations_and_contracts_are_checked_across_a_namespace() {
    for declaration in [
        "sort S;",
        "const a:shared::S;",
        "relation r();",
        "relation $helper();",
        "assumption w: at_most_one(shared::p, group_by: ());",
        "obligation w: at_most_one(shared::p, group_by: ());",
    ] {
        let docs = [
            source("types", "namespace shared; sort S; input p();"),
            source("a", &format!("namespace shared; {declaration}")),
            source("b", &format!("namespace shared; {declaration}")),
        ];
        assert!(
            load("root", &docs).unwrap_err()[0]
                .message
                .contains("Duplicate"),
            "{declaration}"
        );
    }
}
