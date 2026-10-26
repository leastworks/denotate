use denotate_check::*;
use denotate_editor::Document;
use denotate_ir::*;
use denotate_test_dsl::{
    analysis,
    ast::Program,
    lowering::{self, LoweringOutcome, incremental::Session},
    presentation, syntax,
};
use lsp_types::{NumberOrString, Url};
use std::{collections::BTreeSet, sync::Arc};

fn parse(text: &str, revision: u64) -> (Program, Sources) {
    let mut s = Sources::new();
    let id = s
        .add("file:///values.testdsl", revision, "test-dsl", text)
        .unwrap();
    let doc = Document::new(
        &mut syntax::parser().unwrap(),
        text.into(),
        revision as i32,
        true,
    );
    let syntax::ParseOutcome::Parsed(ast) = syntax::project(&doc, &s, id).unwrap() else {
        panic!("syntax: {text}")
    };
    (ast, s)
}
fn lower(text: &str) -> lowering::LoweredProgram {
    let (ast, s) = parse(text, 1);
    let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &s).unwrap() else {
        panic!("validation: {text}")
    };
    p
}
fn diagnostics(text: &str) -> Vec<lsp_types::Diagnostic> {
    let doc = Arc::new(Document::new(
        &mut syntax::parser().unwrap(),
        text.into(),
        1,
        true,
    ));
    let p = analysis::prepare(
        &Url::parse("file:///values.testdsl").unwrap(),
        1,
        doc,
        &mut Session::default(),
    )
    .unwrap();
    if let Some(p) = p.program {
        p.check(&Limits::default(), || {}).unwrap().diagnostics
    } else {
        p.fast
    }
}
fn fact(p: &lowering::LoweredProgram, relation: RelationId, args: &[&str]) -> GroundAtom {
    let r = p.corpus.relation(relation).unwrap();
    GroundAtom::new(
        relation,
        args.iter().zip(&r.parameters).map(|(name, param)| {
            p.corpus
                .constants()
                .find(|c| c.name == *name && c.sort == param.sort)
                .unwrap()
                .id
        }),
    )
}
#[test]
fn overflow_is_validation_and_numeric_aliases_reuse_recipes_with_current_origins() {
    let mut session = Session::new(true);
    for literal in [
        "9223372036854775808",
        "-9223372036854775809",
        "999999999999999999999999999999999999999999999999999999999",
    ] {
        let text = format!("input i; slot a; a <- i when input_value(i) is {literal};");
        let (ast, s) = parse(&text, 1);
        let LoweringOutcome::UserErrors(errors) = session.lower(&ast, &s).unwrap() else {
            panic!("overflow lowered")
        };
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].kind, lowering::DiagnosticKind::InvalidInteger);
        assert_eq!(s.text(errors[0].span).unwrap(), literal);
        assert_eq!(session.stats().queries.recipe, 0);
        assert_eq!(session.stats().assemblies, 0);
        let ds = diagnostics(&text);
        assert!(
            ds.iter()
                .any(|d| d.code == Some(NumberOrString::String("literal".into())))
        );
    }
    for (first, second) in [
        ("1", "01"),
        ("0", "-0"),
        ("-9223372036854775808", "-09223372036854775808"),
        ("9223372036854775807", "09223372036854775807"),
    ] {
        let text = |n| format!("input i; slot a; a <- i when input_value(i) is {n};");
        let (ast, s) = parse(&text(first), 2);
        session.lower(&ast, &s).unwrap();
        let before = session.stats().queries;
        let (ast, s) = parse(&format!("// moved\n{}", text(second)), 3);
        let LoweringOutcome::Lowered(p) = session.lower(&ast, &s).unwrap() else {
            panic!()
        };
        assert_eq!(session.stats().queries, before);
        let leaf = p
            .corpus
            .rules()
            .flat_map(|r| &r.body)
            .map(Literal::atom)
            .find(|a| {
                a.relation() == p.library.value
                    && matches!(a.arguments()[0].value(), Term::Constant(_))
            })
            .unwrap();
        let origins = p.attribution.provenance.origins(leaf.arguments()[1].id());
        assert!(origins.iter().any(|o| s.text(o.span).unwrap() == second));
    }
    let mut session = Session::new(true);
    let (ast, s) = parse("input i; slot a; a <- i when input_value(i) is 1;", 4);
    session.lower(&ast, &s).unwrap();
    let before = session.stats().queries;
    let text = "input i; slot a; a <- i when input_value(i) is 1; mask a when input_value(i) is 2;";
    let (ast, s) = parse(text, 5);
    session.lower(&ast, &s).unwrap();
    assert_eq!(session.stats().queries.recipe, before.recipe + 1);
    assert_eq!(session.stats().queries.validate, before.validate + 1);
}
#[test]
fn copied_values_absence_other_and_masks_match_small_concrete_worlds() {
    let p = lower(
        "input i, j; slot a, b; a <- i; b <- j when slot_value(a) is 1; mask a when input_value(i) is 2;",
    );
    let limits = Limits::default();
    let ground = p.prepare(&limits).unwrap().admit(&limits).unwrap();
    assert!(ground.is_admitted());
    let choices = [None, Some("1"), Some("2"), Some("other_integer")];
    for i in choices {
        for j in choices {
            let world = [("i", i), ("j", j)]
                .into_iter()
                .filter_map(|(n, v)| v.map(|v| fact(&p, p.library.value, &[n, v])))
                .collect::<Vec<_>>();
            let replay = ground.evaluate(world.clone(), &limits).unwrap();
            for value in ["1", "2", "other_integer"] {
                assert_eq!(
                    replay
                        .fact(&fact(&p, p.library.slot_value, &["a", value]))
                        .unwrap(),
                    FactState::Settled(i == Some(value) && i != Some("2"))
                );
                assert_eq!(
                    replay
                        .fact(&fact(&p, p.library.slot_value, &["b", value]))
                        .unwrap(),
                    FactState::Settled(i == Some("1") && j == Some(value))
                );
            }
            let present = world.into_iter().collect::<BTreeSet<_>>();
            let observation = Observation {
                absent: ground
                    .input_atoms()
                    .filter(|a| !present.contains(*a))
                    .cloned()
                    .collect(),
                present,
            };
            let decoded = presentation::decode_observation(&p, &observation).unwrap();
            assert_eq!(
                decoded.values().filter(|v| v.is_some()).count(),
                i.is_some() as usize + j.is_some() as usize
            );
        }
    }
    assert!(
        ground
            .evaluate(
                [
                    fact(&p, p.library.value, &["i", "1"]),
                    fact(&p, p.library.value, &["i", "2"])
                ],
                &limits
            )
            .is_err()
    );
}
#[test]
fn negated_equality_includes_absence_and_input_uniqueness_still_counts_suppliers() {
    let p = lower("input i, j; slot a; a <- j when not input_value(i) is 1;");
    let limits = Limits::default();
    let g = p.prepare(&limits).unwrap().admit(&limits).unwrap();
    for i in [None, Some("1"), Some("other_integer")] {
        let mut world = vec![fact(&p, p.library.value, &["j", "other_integer"])];
        if let Some(v) = i {
            world.push(fact(&p, p.library.value, &["i", v]));
        }
        assert_eq!(
            g.evaluate(world, &limits)
                .unwrap()
                .fact(&fact(&p, p.library.available, &["a"]))
                .unwrap(),
            FactState::Settled(i != Some("1"))
        );
    }
    let text =
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(j) is 1;";
    let ds = diagnostics(text);
    assert_eq!(
        ds.iter()
            .filter(|d| d.message.contains("overlapping"))
            .count(),
        2
    );
    assert!(ds.iter().any(|d| d.message.contains("i: 1")));
    assert!(
        diagnostics(&text.replace("a <- j when input_value(j)", "a <- i when input_value(i)"))
            .is_empty()
    );
}
#[test]
fn w_sensitive_negation_warnings_and_cycles_keep_authored_locations() {
    let text = "input kind, first_input, second_input; slot first, second; first <- first_input when input_value(kind) is 1 and not (input_value(kind) is 2);";
    let ds = diagnostics(text);
    let d = ds
        .iter()
        .find(|d| d.code == Some(NumberOrString::String("redundant".into())))
        .unwrap();
    assert!(d.message.contains("cannot also have value 2"));
    assert_eq!(
        d.range.start.character as usize,
        text.find("not (").unwrap()
    );
    let text = "input kind, first_input, second_input; slot first, second; first <- first_input when input_value(kind) is 1 and not available(second); second <- second_input when input_value(kind) is 2 and not available(first);";
    let ds = diagnostics(text);
    assert_eq!(
        ds.iter()
            .filter(|d| d.code == Some(NumberOrString::String("redundant".into())))
            .count(),
        2
    );
    assert!(
        !ds.iter()
            .any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
    );
}
#[test]
fn value_no_meaning_reaches_presentation_with_valid_decoded_witnesses() {
    for condition in [
        "input_value(i) is 1",
        "not input_value(i) is 1",
        "input_value(i) is 2 and not input_value(i) is 1",
    ] {
        let text = format!("input i; slot a; a <- i when {condition} and not available(a);");
        let ds = diagnostics(&text);
        assert!(
            ds.iter()
                .any(|d| d.message.contains("no consistent result")),
            "{ds:?}"
        );
        assert!(
            ds.iter().any(|d| d.message.contains("Example observation")),
            "{ds:?}"
        );
        assert!(
            !ds.iter()
                .any(|d| d.code == Some(NumberOrString::String("creator-failure".into())))
        );
    }
}

#[test]
fn typed_value_names_safe_edits_and_budget_outcomes_keep_the_frontend_contract() {
    for condition in ["input_value(a) is 1", "slot_value(i) is 1"] {
        let ds = diagnostics(&format!("input i; slot a; a <- i when {condition};"));
        assert!(
            ds.iter()
                .any(|d| d.code == Some(NumberOrString::String("name".into())))
        );
    }
    let text = "input same; slot same; same <- same when input_value(same) is 1 and not input_value(same) is 2;";
    let (ast, sources) = parse(text, 1);
    let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &sources).unwrap() else {
        panic!()
    };
    let limits = Limits::default();
    let ground = p.prepare(&limits).unwrap().admit(&limits).unwrap();
    let warnings =
        denotate_test_dsl::warnings::present_rewrites(&p, &ground, &sources, "test-dsl").unwrap();
    let edit = warnings.iter().find_map(|w| w.edit.as_ref()).unwrap();
    let mut repaired = text.to_string();
    repaired.replace_range(edit.span.byte_range(), &edit.replacement);
    assert!(diagnostics(&repaired).is_empty());
    let doc = Arc::new(Document::new(
        &mut syntax::parser().unwrap(),
        text.into(),
        1,
        true,
    ));
    let program = analysis::prepare(
        &Url::parse("file:///budget.testdsl").unwrap(),
        1,
        doc,
        &mut Session::default(),
    )
    .unwrap()
    .program
    .unwrap();
    let out = program
        .check(
            &Limits {
                max_bdd_nodes: 2,
                ..limits
            },
            || {},
        )
        .unwrap();
    assert!(
        out.diagnostics
            .iter()
            .all(|d| d.code == Some(NumberOrString::String("inconclusive".into())))
    );
    assert!(!out.diagnostics.is_empty());
}

#[path = "support/normalization_fingerprint.rs"]
mod fingerprint;

#[test]
fn cached_value_edits_rebind_current_sources_and_match_uncached_lowering() {
    let base = "input i, j; slot a, b; a <- i when (input_value(j) is 1 or input_value(j) is 2) and not slot_value(b) is -1; b <- j;";
    let mut session = Session::new(true);
    for (revision, text) in [
        base.to_string(),
        format!("// moved\n{base}"),
        base.replace("is 1", "is 01"),
        format!("{base}mask b when input_value(i) is 3;"),
        base.replace("is 2", "is -2"),
        base.replace("is 2", "is 9223372036854775808"),
        base.replace("input_value(j)", "input_value(missing)"),
        base.to_string(),
        format!("{base}a <- i when input_value(j) is 1;"),
        base.replace("not slot_value(b) is -1", "not slot_value(b) is 1"),
    ]
    .into_iter()
    .enumerate()
    {
        let (ast, sources) = parse(&text, revision as u64 + 1);
        match (
            session.lower(&ast, &sources).unwrap(),
            lowering::lower(&ast, &sources).unwrap(),
        ) {
            (LoweringOutcome::Lowered(cached), LoweringOutcome::Lowered(fresh)) => assert_eq!(
                fingerprint::fingerprint(&cached, &sources),
                fingerprint::fingerprint(&fresh, &sources)
            ),
            (LoweringOutcome::UserErrors(cached), LoweringOutcome::UserErrors(fresh)) => {
                assert_eq!(cached, fresh)
            }
            _ => panic!("cached/fresh disagreement at {text}"),
        }
    }
}
