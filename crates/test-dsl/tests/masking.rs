mod support;
use denotate_check::*;
use denotate_editor::Document;
use denotate_ir::*;
use denotate_test_dsl::{
    ast, attribution::SourceView, lowering::*, presentation, syntax, warnings,
};
use support::{atom, domains};

fn lower(text: &str) -> (LoweredProgram, Sources) {
    let mut sources = Sources::new();
    let snapshot = sources
        .add("file:///mask.testdsl", 1, "test-dsl", text)
        .unwrap();
    let doc = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
    let syntax::ParseOutcome::Parsed(ast) = syntax::project(&doc, &sources, snapshot).unwrap()
    else {
        panic!("{text}")
    };
    let LoweringOutcome::Lowered(p) = denotate_test_dsl::lowering::lower(&ast, &sources).unwrap()
    else {
        panic!("name error")
    };
    (p, sources)
}
fn prepare(p: &LoweredProgram) -> GroundProgram {
    GroundProgram::prepare(&p.corpus, &domains(p), &Limits::default())
        .unwrap()
        .admit(&Limits::default())
        .unwrap()
}
fn rule_text(c: &Corpus, r: &Rule) -> String {
    let atom = |a: &Atom| {
        format!(
            "{}({})",
            c.relation(a.relation()).unwrap().name,
            a.arguments()
                .iter()
                .map(|t| match t.value() {
                    Term::Constant(id) => c.constant(*id).unwrap().name.clone(),
                    Term::Variable { name, .. } => name.clone(),
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!(
        "{} :- {};",
        atom(&r.head),
        r.body
            .iter()
            .map(|l| format!(
                "{}{}",
                if matches!(l, Literal::Negative(_)) {
                    "!"
                } else {
                    ""
                },
                atom(l.atom())
            ))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

#[test]
fn conditional_masks_change_supply_not_mapping_or_inputs_and_multiple_masks_are_or() {
    let (p, _) = lower(
        "input i, j, x, y; slot a, b; a <- i; b <- i; b <- j; mask b when present(x); mask b when present(y);",
    );
    let ground = prepare(&p);
    assert!(ground.is_admitted());
    // Independent truth table for all sixteen permitted observations.
    let limits = Limits::default();
    let meaning = ground.symbolic(&limits).unwrap();
    for bits in 0u32..16 {
        let present = |n: usize| bits & (1u32 << n) != 0;
        let replay = ground
            .evaluate(
                ["i", "j", "x", "y"]
                    .into_iter()
                    .enumerate()
                    .filter(|(n, _)| present(*n))
                    .map(|(_, name)| atom(&p, "present", &[name])),
                &limits,
            )
            .unwrap();
        let masked = present(2) || present(3);
        for (relation, args, expected) in [
            ("masked", vec!["b"], masked),
            ("masked", vec!["a"], false),
            ("mapped_to", vec!["i", "b"], true),
            ("mapped_to", vec!["j", "b"], true),
            ("supplies", vec!["i", "a"], present(0)),
            ("supplies", vec!["i", "b"], present(0) && !masked),
            ("supplies", vec!["j", "b"], present(1) && !masked),
            (
                "available",
                vec!["b"],
                (present(0) || present(1)) && !masked,
            ),
        ] {
            assert_eq!(
                replay.fact(&atom(&p, relation, &args)).unwrap(),
                FactState::Settled(expected),
                "{relation}{args:?} in {bits}"
            );
        }
        assert_eq!(replay.present_inputs().count(), bits.count_ones() as usize);
    }
    let report = meaning.verify_at_most_one(&limits).unwrap();
    let example = report
        .groups
        .iter()
        .find_map(|g| match &g.outcome {
            VerifiedOutcome::Counterexample(e) => Some(e),
            _ => None,
        })
        .unwrap();
    assert!(
        example
            .observation
            .absent
            .contains(&atom(&p, "present", &["x"]))
    );
    assert!(
        example
            .observation
            .absent
            .contains(&atom(&p, "present", &["y"]))
    );
}

#[test]
fn unconditional_mask_removes_overlap_inactive_mask_is_not_a_contributor() {
    let base = "input i, j; slot a, b; b <- i; b <- j;";
    for (mask, conflict) in [("mask b;", false), ("mask b when available(a);", true)] {
        let (p, sources) = lower(&format!("{base} {mask}"));
        let ground = prepare(&p);
        let meaning = ground.symbolic(&Limits::default()).unwrap();
        let report = meaning.verify_at_most_one(&Limits::default()).unwrap();
        let diagnostics = presentation::present(&p, &report, &sources, "test-dsl").unwrap();
        assert_eq!(diagnostics.len(), if conflict { 2 } else { 0 });
        for d in diagnostics {
            assert_eq!(d.kind, presentation::DiagnosticKind::OverlappingMappings);
            assert!(
                d.related
                    .iter()
                    .all(|r| !sources.text(r.span).unwrap().contains("available(a)")
                        && !sources.text(r.span).unwrap().contains("mask"))
            );
        }
        assert!(warnings::covered_masks(&p, &sources).unwrap().is_empty());
        assert!(
            warnings::present_rewrites(&p, &ground, &sources, "test-dsl")
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn mixed_cycles_retain_authored_negations_and_specific_related_labels() {
    for (text, kind, targets, mask_conditions) in [
        (
            "input i, j; slot a, b; a <- i; b <- j when not available(a); mask a when available(b);",
            presentation::DiagnosticKind::UnsupportedCycle,
            vec!["not available(a)", "available(b)"],
            vec!["available(b)"],
        ),
        (
            "input i, j; slot a, b; a <- i; b <- j; mask a when available(b); mask b when not available(a);",
            presentation::DiagnosticKind::NoMeaning,
            vec!["available(b)", "not available(a)"],
            vec!["available(b)", "not available(a)"],
        ),
    ] {
        let (p, sources) = lower(text);
        let ground = prepare(&p);
        let meaning = ground.symbolic(&Limits::default()).unwrap();
        let report = meaning.verify_at_most_one(&Limits::default()).unwrap();
        let diagnostics = presentation::present(&p, &report, &sources, "test-dsl").unwrap();
        assert_eq!(diagnostics.len(), targets.len(), "{diagnostics:?}");
        for (d, target) in diagnostics.iter().zip(targets) {
            assert_eq!(d.kind, kind);
            assert_eq!(sources.text(d.primary).unwrap(), target);
            assert!(d.message.starts_with(
                "This dependency cycle involves masking and an authored negated condition"
            ));
            let spans: std::collections::BTreeSet<_> = d.related.iter().map(|r| r.span).collect();
            assert_eq!(spans.len(), d.related.len(), "{d:?}");
            for related in &d.related {
                let text = sources.text(related.span).unwrap();
                if mask_conditions.contains(&text) {
                    assert_eq!(related.label, "mask condition");
                }
                if text == "b <- j when not available(a);" {
                    assert_eq!(related.label, "cycle contributor");
                }
            }
            assert!(d.related.iter().any(|r| {
                sources.text(r.span).unwrap() == "a <- i;" && r.label == "supporting mapping"
            }));
            if kind == presentation::DiagnosticKind::UnsupportedCycle {
                assert!(
                    d.related.iter().any(|r| {
                        sources.text(r.span).unwrap() == "b <- j when not available(a);"
                    })
                );
            }
            for condition in &mask_conditions {
                if *condition != target {
                    assert!(d.related.iter().any(|r| {
                        sources.text(r.span).unwrap() == *condition && r.label == "mask condition"
                    }));
                }
            }
        }
    }
}

#[test]
fn masking_can_make_self_negation_harmless_without_a_dead_mapping_warning() {
    let (p, sources) =
        lower("input i; slot a; a <- i when not available(a); mask a when present(i);");
    let ground = prepare(&p);
    assert!(ground.is_admitted());
    for inputs in [vec![], vec![atom(&p, "present", &["i"])]] {
        let replay = ground.evaluate(inputs, &Limits::default()).unwrap();
        for (relation, args) in [("available", vec!["a"]), ("supplies", vec!["i", "a"])] {
            assert_eq!(
                replay.fact(&atom(&p, relation, &args)).unwrap(),
                FactState::Settled(false)
            );
        }
    }
    let meaning = ground.symbolic(&Limits::default()).unwrap();
    let report = meaning.verify_at_most_one(&Limits::default()).unwrap();
    assert!(
        presentation::present(&p, &report, &sources, "test-dsl")
            .unwrap()
            .is_empty()
    );
    assert!(warnings::covered_masks(&p, &sources).unwrap().is_empty());
    let rewrites = warnings::present_rewrites(&p, &ground, &sources, "test-dsl").unwrap();
    assert_eq!(rewrites.len(), 1);
    assert_eq!(rewrites[0].owner, warnings::Contribution::Program);
    assert_eq!(
        sources.text(rewrites[0].primary.unwrap()).unwrap(),
        "not available(a)"
    );
    assert_eq!(
        rewrites[0].message,
        "This negated condition is redundant: whenever its settled guard holds, the excluded condition cannot hold."
    );
}

#[test]
fn self_and_mutual_mask_cycles_use_masks_not_supporting_mappings_as_primary() {
    for (text, kind, expected, ranges) in [
        (
            "input i; slot a; a <- i; mask a when available(a);",
            presentation::DiagnosticKind::NoMeaning,
            "Masking Slot a depends on its own availability; no consistent result exists when Input i is present.",
            vec!["available(a)"],
        ),
        (
            "input i, j; slot a, b; a <- i; b <- j; mask a when available(b); mask b when available(a);",
            presentation::DiagnosticKind::UnsupportedCycle,
            "Masking Slots a and b depends cyclically on their availability. The checker could not establish a single result.",
            vec!["available(b)", "available(a)"],
        ),
        (
            "input i; slot a; a <- i; mask a when (available(a) or present(i)) and available(a);",
            presentation::DiagnosticKind::NoMeaning,
            "Masking Slot a depends on its own availability; no consistent result exists when Input i is present.",
            vec!["(available(a) or present(i)) and available(a)"],
        ),
    ] {
        let (p, sources) = lower(text);
        let ground = prepare(&p);
        assert!(!ground.is_admitted());
        let meaning = ground.symbolic(&Limits::default()).unwrap();
        let report = meaning.verify_at_most_one(&Limits::default()).unwrap();
        let ds = presentation::present(&p, &report, &sources, "test-dsl").unwrap();
        let cycles: Vec<_> = ds
            .iter()
            .filter(|d| {
                matches!(
                    d.kind,
                    presentation::DiagnosticKind::NoMeaning
                        | presentation::DiagnosticKind::UnsupportedCycle
                )
            })
            .collect();
        assert_eq!(cycles.len(), ranges.len(), "{ds:?}");
        for (d, range) in cycles.iter().zip(ranges) {
            assert_eq!(d.kind, kind);
            assert_eq!(d.message, expected);
            assert_eq!(sources.text(d.primary).unwrap(), range);
            assert!(
                d.related
                    .iter()
                    .any(|r| sources.text(r.span).unwrap().contains("a <- i;"))
            );
        }
        if kind == presentation::DiagnosticKind::UnsupportedCycle {
            assert!(
                ds.iter()
                    .all(|d| d.kind != presentation::DiagnosticKind::NoMeaning)
            );
        }
    }
}

#[test]
fn unconditional_coverage_warns_once_on_whole_mask_and_does_not_rewrite_rules() {
    let (p, sources) =
        lower("input i; slot a, b; a <- i; mask b; mask b when available(a) or present(i);");
    let ground = prepare(&p);
    let warnings = warnings::covered_masks(&p, &sources).unwrap();
    assert_eq!(warnings.len(), 1);
    assert_eq!(
        sources.text(warnings[0].primary).unwrap(),
        "mask b when available(a) or present(i);"
    );
    assert_eq!(
        warnings[0].message,
        "This mask adds no effect: Slot b is already masked unconditionally."
    );
    assert_eq!(
        sources.text(warnings[0].related[0].span).unwrap(),
        "mask b;"
    );
    assert!(ground.rewrite_proofs().next().is_none());
    assert_eq!(
        p.corpus
            .rules()
            .filter(|r| r.head.relation() == p.library.masked)
            .count(),
        3
    );
}

#[test]
fn library_discharge_keeps_creator_ownership_and_mask_failure_keeps_independent_findings() {
    let (p, sources) = lower(
        "input i, x; slot a; a <- i when not present(x); mask a when present(x) and available(a);",
    );
    let ground = prepare(&p);
    assert!(ground.is_admitted());
    let rewrites = warnings::present_rewrites(&p, &ground, &sources, "test-dsl").unwrap();
    assert!(
        rewrites
            .iter()
            .any(|w| w.owner == warnings::Contribution::Library
                && w.literal.is_some()
                && w.primary.is_none()
                && w.edit.is_none())
    );
    assert!(warnings::covered_masks(&p, &sources).unwrap().is_empty());
    let (p, sources) =
        lower("input i, j, x; slot b, c; b <- i; b <- j; c <- x; mask c when available(c);");
    let ground = prepare(&p);
    let meaning = ground.symbolic(&Limits::default()).unwrap();
    let report = meaning.verify_at_most_one(&Limits::default()).unwrap();
    assert!(!report.whole_program_admitted());
    let conflict = report
        .groups
        .iter()
        .find_map(|g| match &g.outcome {
            VerifiedOutcome::Counterexample(c) => Some(c),
            _ => None,
        })
        .unwrap();
    assert_eq!(conflict.replay_scope, ReplayScope::WholeProgram);
    assert!(
        conflict
            .observation
            .absent
            .contains(&atom(&p, "present", &["x"]))
    );
    let ds = presentation::present(&p, &report, &sources, "test-dsl").unwrap();
    assert_eq!(
        ds.iter()
            .filter(|d| d.kind == presentation::DiagnosticKind::OverlappingMappings)
            .count(),
        2
    );
    assert_eq!(
        ds.iter()
            .filter(|d| d.kind == presentation::DiagnosticKind::NoMeaning)
            .count(),
        1
    );
}

#[test]
fn masks_use_existing_boolean_recipes_and_exact_term_origins() {
    let text = "input i; slot a, b; mask b when not (available(a) and present(i));";
    let (p, sources) = lower(text);
    let rules: Vec<_> = p.corpus.rules().skip(4).collect();
    assert_eq!(
        rules
            .iter()
            .map(|r| rule_text(&p.corpus, r))
            .collect::<Vec<_>>(),
        [
            "$condition_1() :- available(a), present(i);",
            "masked(b) :- !$condition_1();"
        ]
    );
    let mask = rules[1];
    for (id, expected) in [
        (
            mask.id.into(),
            "mask b when not (available(a) and present(i));",
        ),
        (mask.head.arguments()[0].id(), "b"),
        (
            mask.body[0].atom().id(),
            "not (available(a) and present(i))",
        ),
        (rules[0].id.into(), "(available(a) and present(i))"),
    ] {
        let span = p
            .attribution
            .origin(id, &sources, SourceView::TestDsl)
            .unwrap()
            .unwrap();
        assert_eq!(sources.text(span).unwrap(), expected);
    }
    assert_eq!(
        p.attribution.masks.len(),
        2,
        "helper retains authored mask context"
    );
}

#[test]
fn mask_names_are_checked_at_the_target_and_keyword_is_reserved_everywhere() {
    for (statement, expected) in [
        ("mask missing;", ast::Kind::Slot),
        ("mask i;", ast::Kind::Slot),
        ("mask a when available(i);", ast::Kind::Slot),
        ("mask a when present(a);", ast::Kind::Input),
    ] {
        let mut sources = Sources::new();
        let text = format!("input i; slot a; a <- i; {statement}");
        let snap = sources
            .add("file:///error.testdsl", 1, "test-dsl", text.clone())
            .unwrap();
        let doc = Document::new(&mut syntax::parser().unwrap(), text, 1, true);
        let syntax::ParseOutcome::Parsed(ast) = syntax::project(&doc, &sources, snap).unwrap()
        else {
            panic!()
        };
        let LoweringOutcome::UserErrors(errors) =
            denotate_test_dsl::lowering::lower(&ast, &sources).unwrap()
        else {
            panic!()
        };
        assert_eq!(errors.len(), 1);
        match errors[0].kind {
            DiagnosticKind::UnknownName { expected: kind, .. }
            | DiagnosticKind::WrongKind { expected: kind, .. } => assert_eq!(kind, expected),
            _ => panic!(),
        }
    }
    for text in [
        "input mask; slot b; b <- mask;",
        "input i; slot mask;",
        "input i; slot a; mask <- i;",
        "input i; slot a; mask a when present(mask);",
        "input i; slot a; mask mask;",
    ] {
        let mut sources = Sources::new();
        let snap = sources
            .add("file:///error.testdsl", 1, "test-dsl", text)
            .unwrap();
        let doc = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
        assert!(
            matches!(
                syntax::project(&doc, &sources, snap).unwrap(),
                syntax::ParseOutcome::SyntaxErrors(_)
            ),
            "{text}"
        );
    }
}
