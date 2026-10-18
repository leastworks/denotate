use denotate_check::{FactState, GroundAtom, GroundProgram, Limits};
use denotate_editor::Document;
use denotate_ir::*;
use denotate_test_dsl::{
    attribution::{Attribution, AttributionError, SourceView},
    lowering::{self, LoweredProgram, LoweringFailure, LoweringOutcome},
    syntax::{self, ParseOutcome},
};

fn lower(text: &str) -> (Sources, LoweredProgram) {
    let mut sources = Sources::new();
    let snapshot = sources
        .add(
            "file:///origins.inputmapping",
            1,
            SourceView::TestDsl.as_str(),
            text,
        )
        .unwrap();
    let document = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
    let ParseOutcome::Parsed(ast) = syntax::project(&document, &sources, snapshot).unwrap() else {
        panic!()
    };
    let LoweringOutcome::Lowered(program) = lowering::lower(&ast, &sources).unwrap() else {
        panic!()
    };
    (sources, program)
}

fn quote<'a>(
    sources: &'a Sources,
    program: &LoweredProgram,
    id: impl Into<OccurrenceId>,
) -> &'a str {
    let origins = program.attribution.provenance.origins(id);
    assert_eq!(origins.len(), 1);
    sources.text(origins[0].span).unwrap()
}

#[test]
fn view_conversion_is_total_for_known_views_and_rejects_unknown_names() {
    for view in [SourceView::TestDsl, SourceView::Denotate] {
        assert_eq!(SourceView::try_from(view.as_str()).unwrap(), view);
    }
    for name in ["", "test_dsl", "Denotate", "typo"] {
        assert!(matches!(
            SourceView::try_from(name),
            Err(AttributionError::UnknownView(_))
        ));
    }
}

#[test]
fn ordinary_occurrences_use_their_construct_and_complete_guards_live_separately() {
    let statement = "b <- i when available(a) and not present(x);";
    let (sources, p) = lower(&format!("input i, x; slot a, b; {statement}"));
    let rule = p.corpus.rules().last().unwrap();
    for id in [rule.id.into(), rule.head.id()] {
        assert_eq!(quote(&sources, &p, id), statement);
    }
    assert_eq!(quote(&sources, &p, rule.head.arguments()[0].id()), "i");
    assert_eq!(quote(&sources, &p, rule.head.arguments()[1].id()), "b");
    assert_eq!(
        quote(&sources, &p, rule.body[0].atom().id()),
        "available(a)"
    );
    assert_eq!(
        quote(&sources, &p, rule.body[1].atom().id()),
        "not present(x)"
    );
    assert_eq!(
        quote(&sources, &p, rule.body[0].atom().arguments()[0].id()),
        "a"
    );
    assert_eq!(
        quote(&sources, &p, rule.body[1].atom().arguments()[0].id()),
        "x"
    );
    for constant in p.corpus.constants().filter(|c| c.sort != p.library.integer) {
        assert_eq!(quote(&sources, &p, constant.id), constant.name);
    }
    let guard = p.attribution.guards[&(rule.id, SourceView::TestDsl)];
    assert_eq!(
        sources.text(guard).unwrap(),
        "available(a) and not present(x)"
    );
    assert_eq!(p.attribution.guards.len(), 1);
    p.attribution.validate(&p.corpus, &sources).unwrap();
}

#[test]
fn nested_normalization_keeps_the_outer_authored_not_but_helpers_start_fresh() {
    for (guard, negative, helper) in [
        (
            "not ((available(a) and available(c)) or present(x))",
            vec![true, true],
            true,
        ),
        (
            "not (not available(a) or available(c))",
            vec![false, true],
            false,
        ),
        (
            "not not (available(a) and available(c))",
            vec![false, false],
            false,
        ),
        ("not not (available(a) or available(c))", vec![false], false),
    ] {
        let statement = format!("b <- i when {guard};");
        let (sources, p) = lower(&format!("input i, x; slot a, b, c; {statement}"));
        for rule in p
            .corpus
            .rules()
            .filter(|r| r.head.relation() == p.library.mapped_to)
        {
            assert_eq!(quote(&sources, &p, rule.id), statement);
            assert_eq!(rule.body.len(), negative.len());
            for (literal, expected_negative) in rule.body.iter().zip(&negative) {
                assert_eq!(matches!(literal, Literal::Negative(_)), *expected_negative);
                assert_eq!(quote(&sources, &p, literal.atom().id()), guard);
                for arg in literal.atom().arguments() {
                    let Term::Constant(id) = arg.value() else {
                        panic!()
                    };
                    assert_eq!(
                        quote(&sources, &p, arg.id()),
                        p.corpus.constant(*id).unwrap().name
                    );
                }
            }
        }
        if helper {
            let relation = p
                .corpus
                .relations()
                .find(|r| r.name == "$condition_1")
                .unwrap();
            assert_eq!(
                quote(&sources, &p, relation.id),
                "(available(a) and available(c))"
            );
            let rule = p
                .corpus
                .rules()
                .find(|r| r.head.relation() == relation.id)
                .unwrap();
            assert_eq!(
                quote(&sources, &p, rule.id),
                "(available(a) and available(c))"
            );
            assert_eq!(
                quote(&sources, &p, rule.head.id()),
                "(available(a) and available(c))"
            );
            assert_eq!(
                quote(&sources, &p, rule.body[0].atom().id()),
                "available(a)"
            );
            assert_eq!(
                quote(&sources, &p, rule.body[1].atom().id()),
                "available(c)"
            );
            assert!(
                !p.attribution
                    .guards
                    .contains_key(&(rule.id, SourceView::TestDsl))
            );
        }
    }
}

#[test]
fn validation_checks_unused_occurrences_allows_identical_repeats_and_separate_views() {
    let (mut sources, mut p) = lower("input i; slot a, unused; a <- i;");
    let unused = p
        .corpus
        .constants()
        .find(|c| c.name == "unused")
        .unwrap()
        .id;
    let original = p.attribution.provenance.origins(unused)[0].clone();
    p.attribution
        .provenance
        .attach(
            &p.corpus,
            &sources,
            unused,
            [original.clone(), original.clone()],
        )
        .unwrap();
    assert_eq!(p.attribution.provenance.origins(unused).len(), 1);
    let den = sources
        .add(
            "file:///origins.den",
            1,
            SourceView::Denotate.as_str(),
            "unused",
        )
        .unwrap();
    p.attribution
        .provenance
        .attach(
            &p.corpus,
            &sources,
            unused,
            [Origin::new(sources.span(den, 0..6).unwrap())],
        )
        .unwrap();
    p.attribution.validate(&p.corpus, &sources).unwrap();
    assert_eq!(
        p.attribution
            .origin(unused, &sources, SourceView::TestDsl)
            .unwrap(),
        Some(original.span)
    );
    let different = sources.span(original.span.snapshot(), 0..5).unwrap();
    p.attribution
        .provenance
        .attach(&p.corpus, &sources, unused, [Origin::new(different)])
        .unwrap();
    assert!(
        matches!(p.attribution.validate(&p.corpus, &sources), Err(AttributionError::MultipleOrigins { occurrence, view: SourceView::TestDsl }) if occurrence == unused.into())
    );
    assert!(matches!(
        p.attribution.origin(unused, &sources, SourceView::TestDsl),
        Err(AttributionError::MultipleOrigins { .. })
    ));
    // Even a report with no user diagnostic must validate unused attribution.
    let domains = p
        .corpus
        .sorts()
        .map(|sort| {
            (
                sort.id,
                p.corpus
                    .constants()
                    .filter(|c| c.sort == sort.id)
                    .map(|c| c.id)
                    .collect(),
            )
        })
        .collect();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains, &limits).unwrap();
    let report = ground
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    assert!(matches!(
        denotate_test_dsl::presentation::present(
            &p,
            &report,
            &sources,
            SourceView::TestDsl.as_str()
        ),
        Err(
            denotate_test_dsl::presentation::PresentationError::Attribution(
                AttributionError::MultipleOrigins { .. }
            )
        )
    ));
}

#[test]
fn zero_origins_are_valid_but_unknown_views_are_creator_errors_even_when_unused() {
    let (mut sources, p) = lower("input i; slot a; a <- i;");
    Attribution::default()
        .validate(&p.corpus, &sources)
        .unwrap();
    let snapshot = sources
        .add("file:///unknown", 1, "mistyped-view", "a")
        .unwrap();
    let mut attribution = Attribution::default();
    let id = p.corpus.constants().next().unwrap().id;
    attribution
        .provenance
        .attach(
            &p.corpus,
            &sources,
            id,
            [Origin::new(sources.span(snapshot, 0..1).unwrap())],
        )
        .unwrap();
    assert!(matches!(
        attribution.validate(&p.corpus, &sources),
        Err(AttributionError::UnknownView(_))
    ));
    // Even requesting a different view must not silently filter malformed data.
    assert!(matches!(
        attribution.origin(id, &sources, SourceView::Denotate),
        Err(AttributionError::UnknownView(_))
    ));
}

#[test]
fn lower_validates_unused_declaration_attribution_before_returning_success() {
    let text = "input unused;";
    let mut sources = Sources::new();
    let snapshot = sources
        .add("file:///unknown.inputmapping", 1, "mistyped-view", text)
        .unwrap();
    let document = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
    let ParseOutcome::Parsed(ast) = syntax::project(&document, &sources, snapshot).unwrap() else {
        panic!()
    };
    assert!(matches!(
        lowering::lower(&ast, &sources),
        Err(LoweringFailure::Attribution(AttributionError::UnknownView(
            _
        )))
    ));
}

#[test]
fn explicit_context_with_a_mismatched_view_is_a_creator_failure() {
    let (sources, mut p) = lower("input i; slot a; a <- i when present(i);");
    let rule = p.corpus.rules().last().unwrap().id;
    let span = p.attribution.guards[&(rule, SourceView::TestDsl)];
    p.attribution
        .guards
        .insert((rule, SourceView::Denotate), span);
    assert!(matches!(
        p.attribution.validate(&p.corpus, &sources),
        Err(AttributionError::InvalidMetadata(
            "guard has the wrong source view"
        ))
    ));
}

#[test]
fn classical_double_negation_self_loop_is_admitted_but_never_seeded() {
    let (_, p) = lower("input input_a; slot a; a <- input_a when not not available(a);");
    let domains = p
        .corpus
        .sorts()
        .map(|sort| {
            (
                sort.id,
                p.corpus
                    .constants()
                    .filter(|c| c.sort == sort.id)
                    .map(|c| c.id)
                    .collect(),
            )
        })
        .collect();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains, &limits).unwrap();
    assert!(ground.is_admitted());
    let input = p
        .corpus
        .constants()
        .find(|c| c.name == "input_a")
        .unwrap()
        .id;
    let slot = p.corpus.constants().find(|c| c.name == "a").unwrap().id;
    let present = GroundAtom::new(p.library.value, vec![input, p.library.other]);
    let replay = ground.evaluate([present.clone()], &limits).unwrap();
    assert_eq!(replay.fact(&present).unwrap(), FactState::Settled(true));
    assert_eq!(
        replay
            .fact(&GroundAtom::new(p.library.mapped_to, vec![input, slot]))
            .unwrap(),
        FactState::Settled(false)
    );
    assert_eq!(
        replay
            .fact(&GroundAtom::new(p.library.available, vec![slot]))
            .unwrap(),
        FactState::Settled(false)
    );
}
