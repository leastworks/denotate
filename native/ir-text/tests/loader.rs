use denotate_check::{
    Accounted, BackendIdentity, Limits, LocalCheckOutcome, OperationalLimits, RequestPreparation,
    ScopedResult, ScopedResults,
};
use denotate_check_session::Session;
use denotate_ir::{Literal, Term};
use denotate_ir_text::{ActiveRoot, LoadedProgram, SourceFile, load, roots};

fn source(name: &str, text: &str) -> SourceFile {
    SourceFile::new(format!("file:///{name}.den"), 1, text.to_owned())
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
    let request = p.request(&limits, backend).unwrap();
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
    let code = "module m; sort S; sort Empty; const a,b:S; input p(x:S); obligation unique: at_most_one(p, group_by: ());";
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
        "module lib ownership library; sort S; const a,b:S; input p(x:S); assumption one: at_most_one(p, group_by: ());",
    );
    let root = source(
        "root",
        "module root ownership root; use lib; obligation unique: at_most_one(lib::p, group_by: ());",
    );
    let docs = [root, lib];
    let p = load("root", &docs).unwrap();
    assert_eq!(p.assumptions.len(), 1);
    assert_eq!(p.assumptions[0].name.namespace.as_ref(), "lib");
    assert_eq!(
        p.modules
            .iter()
            .find(|m| m.name == "lib")
            .unwrap()
            .ownership,
        "library"
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
        edited[1].text = edited[1]
            .text
            .replace("assumption one: at_most_one(p, group_by: ());", "")
            .into();
        edited[1].revision += 1;
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
            "module lib ownership library; sort S; relation r(x:S); obligation unique: at_most_one(r, group_by: ());",
        ),
        source(
            "shared",
            "module shared ownership shared; use lib; const a,b:lib::S;",
        ),
        source("a", "module a; use lib; use shared; lib::r(shared::a);"),
        source("b", "module b; use lib; use shared; lib::r(shared::b);"),
        source(
            "root",
            "module root ownership root; use a; use b; use shared;",
        ),
    ];
    let p = load("root", &docs).unwrap();
    assert_eq!(p.corpus.rules().count(), 2);
    assert_eq!(p.modules.len(), 5);
    assert_eq!(
        counterexamples(&check(&p, &mut Session::default(), BackendIdentity::bdd())),
        1
    );
    let constituent = load("a", &docs).unwrap();
    assert_eq!(
        counterexamples(&check(
            &constituent,
            &mut Session::default(),
            BackendIdentity::bdd()
        )),
        0
    );
    let index = roots(&docs).unwrap();
    assert_eq!(index["file:///a.den"], ActiveRoot::Selected("root".into()));
    let mut reordered = docs.clone();
    reordered.reverse();
    assert_eq!(keys(&p), keys(&load("root", &reordered).unwrap()));
    let mut two_roots = docs;
    two_roots.push(source("second", "module second ownership root; use a;"));
    assert_eq!(
        roots(&two_roots).unwrap()["file:///a.den"],
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
            .contains("not directly imported")
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
        "module m; sort S; const a,b:S; input p(x:S); relation r(x:S); r(X) :- p(X); r(X) :- p(X); obligation u: at_most_one(r, group_by: ());",
    );
    let warm = single(
        "// shifted\nmodule m; sort S; const a,b:S; input p(x:S); relation r(x:S); r( X ) :- p(X) loc(#map);\nr(X) :- p( X ); obligation u: at_most_one(r, group_by: ()); #map = {head.0: loc(range(#dsl,1,1,1,2))}; source #dsl = \"file:///original.dsl\" view \"dsl\" hash \"sha256:pending\";",
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
    assert_eq!(warm.modules[0].location_syntax.len(), 3);
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
        ("use missing;", "Unknown module"),
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
fn unrelated_invalid_files_do_not_block_root_and_duplicate_modules_are_rejected() {
    let docs = [
        source("m", "module m; relation r(); r();"),
        source("bad", "module bad; relation r(;"),
        source("broken", "not even a module"),
    ];
    assert_eq!(load("m", &docs).unwrap().corpus.rules().count(), 1);
    let duplicate = source("elsewhere", "module m;");
    assert!(
        load("m", &[docs[0].clone(), duplicate]).unwrap_err()[0]
            .message
            .contains("Ambiguous module")
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
        source("library", include_str!("../fixtures/library.den")),
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
    for keyword in ["domain", "obligation", "assumption", "source"] {
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
        assert_eq!(program.assumptions[0].constraint.group_by, vec![0]);
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
