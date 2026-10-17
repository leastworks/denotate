//! Scripted edits compared with the uncached 5a pipeline, not another copy.
use super::*;
use denotate_test_dsl::lowering::incremental::{QueryCounts, Session};

const BASE: &str = "input i, x;\nslot a, b;\na <- i;\nb <- x when available(a);\n";

fn compare_cached(session: &mut Session, text: &str) -> (Sources, LoweringOutcome) {
    let (sources, ast) = parse(text);
    let cached = session.lower(&ast, &sources).unwrap();
    let fresh = lowering::lower(&ast, &sources).unwrap();
    match (&cached, &fresh) {
        (LoweringOutcome::Lowered(c), LoweringOutcome::Lowered(f)) => {
            assert_eq!(fingerprint(c, &sources), fingerprint(f, &sources), "{text}");
            assert_eq!(check(c), check(f), "{text}");
            for edit in c.attribution.rewrites.removals.values() {
                let mut edited = text.to_owned();
                edited.replace_range(edit.span.byte_range(), &edit.replacement);
                let (sources, ast) = parse(&edited);
                lowered(&ast, &sources);
            }
        }
        (LoweringOutcome::UserErrors(c), LoweringOutcome::UserErrors(f)) => {
            assert_eq!(c, f, "{text}")
        }
        _ => panic!("cached/fresh outcome differs: {text}"),
    }
    (sources, cached)
}

fn delta(before: QueryCounts, after: QueryCounts) -> QueryCounts {
    QueryCounts {
        recipe: after.recipe - before.recipe,
        declarations: after.declarations - before.declarations,
        resolve: after.resolve - before.resolve,
        validate: after.validate - before.validate,
    }
}

#[test]
fn comments_mapping_edits_and_unrelated_declarations_have_exact_dependencies() {
    let mut session = Session::new(true);
    compare_cached(&mut session, BASE);
    assert_eq!(
        session.stats().queries,
        QueryCounts {
            recipe: 4,
            declarations: 1,
            resolve: 4,
            validate: 2
        }
    );
    let before = session.stats();
    compare_cached(&mut session, &format!("// current ranges\n{BASE}"));
    assert_eq!(session.stats().queries, before.queries);
    assert_eq!(session.stats().declaration_updates, 1);
    assert_eq!(session.stats().assemblies, 2);

    let changed = BASE.replace("available(a)", "not not available(a)");
    compare_cached(&mut session, &changed);
    assert_eq!(
        delta(before.queries, session.stats().queries),
        QueryCounts {
            recipe: 1,
            validate: 1,
            ..Default::default()
        }
    );
    assert_eq!(session.stats().declaration_updates, 1);
    let before = session.stats().queries;
    compare_cached(
        &mut session,
        &changed.replace("input i, x;", "input i, x, unused;"),
    );
    assert_eq!(
        delta(before, session.stats().queries),
        QueryCounts {
            recipe: 1,
            declarations: 1,
            resolve: 4,
            validate: 0
        }
    );
    assert_eq!(session.stats().declaration_updates, 2);
}

#[test]
fn removed_forms_and_validation_results_survive_sixty_declaration_revisions() {
    let mut session = Session::new(true);
    compare_cached(&mut session, BASE);
    let invalid = BASE.replace("available(a)", "available(missing)");
    compare_cached(&mut session, &invalid);
    let before = session.stats();

    // Each edit changes the input and interns a new mapping; neither the valid
    // b mapping nor the invalid one is requested during these revisions.
    for revision in 0..60 {
        compare_cached(
            &mut session,
            &format!("input i, x;\nslot a, b, temp{revision};\na <- i;\ntemp{revision} <- x;\n"),
        );
    }
    assert_eq!(
        session.stats().declaration_updates,
        before.declaration_updates + 60
    );
    assert_eq!(
        session.stats().queries.validate,
        before.queries.validate + 60
    );

    let before_restore = session.stats().queries;
    compare_cached(
        &mut session,
        &format!("// restored at current ranges\n{BASE}"),
    );
    let restored = delta(before_restore, session.stats().queries);
    assert_eq!(restored.recipe, 0);
    assert_eq!(restored.validate, 0);

    let assemblies = session.stats().assemblies;
    let before_restore = session.stats().queries;
    let (_, result) = compare_cached(&mut session, &format!("// restored error\n{invalid}"));
    assert!(matches!(result, LoweringOutcome::UserErrors(_)));
    let restored = delta(before_restore, session.stats().queries);
    assert_eq!(restored.recipe, 0);
    assert_eq!(restored.validate, 0);
    assert_eq!(session.stats().assemblies, assemblies);
}

#[test]
fn changing_a_referenced_kind_invalidates_only_dependent_validation() {
    let mut session = Session::new(true);
    compare_cached(&mut session, BASE);
    let before = session.stats();
    let wrong = BASE.replace("input i, x;\nslot a, b;", "input i, x, b;\nslot a;");
    let (sources, result) = compare_cached(&mut session, &wrong);
    let LoweringOutcome::UserErrors(errors) = result else {
        panic!()
    };
    assert_eq!(errors.len(), 1);
    assert!(matches!(
        errors[0].kind,
        lowering::DiagnosticKind::WrongKind {
            expected: denotate_test_dsl::ast::Kind::Slot,
            found: denotate_test_dsl::ast::Kind::Input,
            ..
        }
    ));
    assert_eq!(sources.text(errors[0].related[0]).unwrap(), "b");
    assert_eq!(session.stats().assemblies, before.assemblies);
    assert_eq!(
        delta(before.queries, session.stats().queries),
        QueryCounts {
            declarations: 1,
            resolve: 4,
            validate: 1,
            recipe: 0,
        }
    );
    compare_cached(&mut session, &wrong.replace("slot a;", "slot a, b;"));
    assert_eq!(session.stats().assemblies, before.assemblies + 1);
    assert_eq!(
        session.stats().queries.validate,
        before.queries.validate + 2
    );
}

#[test]
fn ordinary_sessions_do_not_collect_measurements() {
    let mut session = Session::default();
    compare_cached(&mut session, BASE);
    compare_cached(&mut session, &format!("// edit\n{BASE}"));
    let stats = session.stats();
    assert_eq!(stats.queries, QueryCounts::default());
    assert_eq!(stats.assemblies, 0);
    assert_eq!(stats.declaration_updates, 0);
    assert_eq!(stats.last.projection_ns, 0);
    assert_eq!(stats.last.queries_ns, 0);
    assert_eq!(stats.last.assembly_attribution_ns, 0);
}

#[test]
fn missing_symbolic_related_declaration_is_a_creator_failure() {
    use denotate_test_dsl::ast::Kind;
    let (sources, ast) = parse(BASE);
    let projection = projection::project(&ast, &sources).unwrap();
    let (names, _) = semantic::Names::collect(&projection.keys());
    let diagnostics = [semantic::ValidationDiagnostic {
        kind: lowering::DiagnosticKind::WrongKind {
            name: "missing".into(),
            expected: Kind::Slot,
            found: Kind::Input,
        },
        primary: AstPath::Target,
        related: Some((Kind::Input, "missing".into())),
    }];
    assert!(matches!(
        names.bind(&projection.statements[2].key, &diagnostics),
        Err(lowering::LoweringFailure::InvalidAst(_))
    ));
}

#[test]
fn wrong_kind_result_ignores_declaration_identity_but_refreshes_related_location() {
    let mut session = Session::new(true);
    let original = "input x; slot a; a <- x when available(x);";
    compare_cached(&mut session, original);
    let before = session.stats();
    assert_eq!(before.queries.validate, 1);
    for (index, text) in [
        original.replace("input x;", "input unused, x;"),
        format!(
            "// comment\n{}",
            original.replace("input x;", "input unused, x;")
        ),
    ]
    .iter()
    .enumerate()
    {
        let (sources, result) = compare_cached(&mut session, text);
        let LoweringOutcome::UserErrors(errors) = result else {
            panic!()
        };
        assert_eq!(errors.len(), 1);
        assert_eq!(sources.text(errors[0].span).unwrap(), "x");
        assert_eq!(sources.text(errors[0].related[0]).unwrap(), "x");
        assert_eq!(
            errors[0].related[0].byte_range().start,
            text.find("x;").unwrap()
        );
        assert_eq!(session.stats().queries.validate, 1);
        assert_eq!(session.stats().assemblies, 0);
        assert_eq!(session.stats().queries.recipe, 0);
        if index == 1 {
            assert_eq!(session.stats().declaration_updates, 2);
        }
    }
    assert_eq!(
        delta(before.queries, session.stats().queries),
        QueryCounts {
            declarations: 1,
            resolve: 3,
            ..Default::default()
        }
    );
}

#[test]
fn every_current_error_gates_assembly_even_when_recipes_and_errors_are_cached() {
    let mut session = Session::new(true);
    compare_cached(&mut session, BASE);
    let valid = session.stats();
    let invalid = BASE.replace("b <- x", "b <- missing");
    compare_cached(&mut session, &invalid);
    assert_eq!(
        delta(valid.queries, session.stats().queries),
        QueryCounts {
            resolve: 1,
            validate: 1,
            ..Default::default()
        }
    );
    assert_eq!(session.stats().assemblies, valid.assemblies);
    let invalid_counts = session.stats().queries;
    compare_cached(&mut session, &format!("// moved error\n{invalid}"));
    assert_eq!(session.stats().queries, invalid_counts);
    assert_eq!(session.stats().assemblies, valid.assemblies);
    compare_cached(&mut session, &format!("{BASE}\nslot b;"));
    assert_eq!(session.stats().queries.recipe, valid.queries.recipe);
    assert_eq!(session.stats().assemblies, valid.assemblies);
    // Removing a declaration must invalidate the previously valid validation.
    compare_cached(&mut session, &BASE.replace("slot a, b", "slot a"));
    assert_eq!(session.stats().assemblies, valid.assemblies);
    compare_cached(&mut session, BASE);
    assert_eq!(session.stats().assemblies, valid.assemblies + 1);
    assert_eq!(session.stats().queries.recipe, valid.queries.recipe);
}

#[test]
fn duplicate_forms_share_queries_not_origins_or_error_locations() {
    let mut session = Session::new(true);
    let mapping = "b <- x when available(a);";
    let text = format!("{BASE}{mapping}\n");
    compare_cached(&mut session, &text);
    assert_eq!(session.stats().queries.recipe, 4);
    assert_eq!(session.stats().queries.validate, 2);
    let before = session.stats().queries;
    compare_cached(&mut session, BASE);
    compare_cached(
        &mut session,
        &format!("{BASE}// inserted\n{mapping}\n{mapping}\n"),
    );
    assert_eq!(session.stats().queries, before);
    let invalid = text.replace("b <- x", "b <- missing");
    let (_, result) = compare_cached(&mut session, &invalid);
    let LoweringOutcome::UserErrors(errors) = result else {
        panic!()
    };
    assert_eq!(errors.len(), 2);
    assert_ne!(errors[0].span, errors[1].span);
    assert_eq!(
        delta(before, session.stats().queries),
        QueryCounts {
            validate: 1,
            resolve: 1,
            ..Default::default()
        }
    );
}

#[test]
fn insertion_reordering_and_helpers_do_not_invalidate_surviving_forms() {
    let mut session = Session::new(true);
    let declarations = "input i, x; slot a, b;";
    let one = "a <- i when not (available(a) and present(x));";
    let two = "b <- x when (available(a) or present(i)) and not not present(x);";
    let three = "b <- i when not (not available(a) or present(x));";
    compare_cached(&mut session, &format!("{declarations} {one} {two}"));
    let before = session.stats().queries;
    compare_cached(&mut session, &format!("{declarations} {two} {one}"));
    assert_eq!(session.stats().queries, before);
    compare_cached(&mut session, &format!("{declarations} {three} {two} {one}"));
    assert_eq!(
        delta(before, session.stats().queries),
        QueryCounts {
            recipe: 1,
            validate: 1,
            ..Default::default()
        }
    );
    let before = session.stats().queries;
    compare_cached(
        &mut session,
        &format!("slot a, b; input i, x; {one} {three} {two} {one}"),
    );
    assert_eq!(
        delta(before, session.stats().queries),
        QueryCounts {
            declarations: 1,
            ..Default::default()
        }
    );
}

#[test]
fn duplicate_declaration_order_and_safe_edits_always_use_the_current_snapshot() {
    let mut session = Session::new(true);
    for text in [
        "input i, x; slot a; slot b, a; a <- i;",
        "input i, x; slot b, a; slot a; a <- i;",
        "// shifted\ninput i, x; slot b, a; slot a; a <- i;",
        "input i, x; slot a; a <- i when present(x) and not available(a);",
        "input i, x; slot a; a <- i when present(x) and // retain\n not available(a);",
        "input i, x; slot a; a <- i when present(x) and not available(a);",
    ] {
        compare_cached(&mut session, text);
    }
    assert_eq!(session.stats().queries.recipe, 3);
    assert_eq!(session.stats().assemblies, 3);
}

#[test]
fn cached_pipeline_covers_every_existing_fixture() {
    let mut session = Session::new(true);
    for fixture in [
        Fixture::overlap(),
        Fixture::exclusive(),
        Fixture::ambiguous(),
        Fixture::redundant(),
        Fixture::mixed(false, false),
        Fixture::mixed(true, false),
        Fixture::mixed(false, true),
    ] {
        let cached = session.lower(&fixture.ast, &fixture.sources).unwrap();
        let fresh = lowered(&fixture.ast, &fixture.sources);
        let LoweringOutcome::Lowered(cached) = cached else {
            panic!()
        };
        assert_eq!(
            fingerprint(&cached, &fixture.sources),
            fingerprint(&fresh, &fixture.sources)
        );
        assert_eq!(check(&cached), check(&fresh));
    }
    let fixture = include_str!("../../fixtures/lowering.txt");
    let declarations = fixture.lines().take(2).collect::<Vec<_>>().join("\n");
    for mapping in fixture.lines().skip(2).filter(|l| !l.is_empty()) {
        compare_cached(&mut session, &format!("{declarations}\n{mapping}"));
    }
}
