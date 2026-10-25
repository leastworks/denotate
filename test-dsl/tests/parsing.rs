use denotate_test_dsl::attribution::SourceView;
mod support;
use denotate_check::{GroundProgram, Limits};
use denotate_editor::Document;
use denotate_ir::{Literal, OccurrenceId, SourceSpan, Sources};
use denotate_test_dsl::{
    ast::*,
    lowering::{self, DiagnosticKind, LoweredProgram, LoweringOutcome},
    presentation,
    syntax::{self, ParseFailure, ParseOutcome},
};
use lsp_types::{Position, Range, TextDocumentContentChangeEvent};
use support::{Fixture, domains};

struct Parsed {
    sources: Sources,
    ast: Program,
}
fn parse(text: &str) -> Parsed {
    let mut sources = Sources::new();
    let snapshot = sources
        .add(
            "file:///example.testdsl",
            1,
            SourceView::TestDsl.as_str(),
            text,
        )
        .unwrap();
    let document = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
    let ParseOutcome::Parsed(ast) = syntax::project(&document, &sources, snapshot).unwrap() else {
        panic!(
            "unexpected syntax errors: {}",
            document.tree.root_node().to_sexp()
        );
    };
    Parsed { sources, ast }
}
fn lowered(p: &Parsed) -> LoweredProgram {
    let LoweringOutcome::Lowered(ir) = lowering::lower(&p.ast, &p.sources).unwrap() else {
        panic!("unexpected name errors");
    };
    ir
}
fn quotes(p: &Parsed, ir: &LoweredProgram, id: impl Into<OccurrenceId>) -> Vec<String> {
    ir.attribution
        .provenance
        .origins(id)
        .iter()
        .map(|o| p.sources.text(o.span).unwrap().into())
        .collect()
}

#[test]
fn parser_matches_independent_hand_built_fixtures_including_every_term_span() {
    for f in [
        Fixture::overlap(),
        Fixture::exclusive(),
        Fixture::ambiguous(),
        Fixture::redundant(),
        Fixture::mixed(false, false),
        Fixture::mixed(true, false),
        Fixture::mixed(false, true),
    ] {
        let document = Document::new(&mut syntax::parser().unwrap(), f.text.clone(), 1, true);
        assert_eq!(
            syntax::project(&document, &f.sources, f.snapshot).unwrap(),
            ParseOutcome::Parsed(f.ast)
        );
    }
}

fn shape(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::Value {
            kind,
            name,
            literal,
        } => format!("{kind:?}_value({}) is {}", name.text, literal.text),
        ExprKind::Available(n) => format!("a({})", n.text),
        ExprKind::Present(n) => format!("p({})", n.text),
        ExprKind::And(a, b) => format!("({}&{})", shape(a), shape(b)),
        ExprKind::Or(a, b) => format!("({}|{})", shape(a), shape(b)),
        ExprKind::Not { operand, .. } => format!("!{}", shape(operand)),
        ExprKind::Group(e) => format!("group({})", shape(e)),
    }
}

#[test]
fn precedence_associativity_parentheses_and_repeated_not_are_explicit() {
    for (condition, expected) in [
        (
            "not available(a) and available(b) or present(i)",
            "((!a(a)&a(b))|p(i))",
        ),
        (
            "available(a) or available(b) and present(i)",
            "(a(a)|(a(b)&p(i)))",
        ),
        (
            "available(a) and available(b) and present(i)",
            "((a(a)&a(b))&p(i))",
        ),
        (
            "available(a) or available(b) or present(i)",
            "((a(a)|a(b))|p(i))",
        ),
        (
            "not not (available(a) or present(i))",
            "!!group((a(a)|p(i)))",
        ),
    ] {
        let p = parse(&format!("input i; slot a, b; b <- i when {condition};"));
        let expr = p.ast.mappings[0].condition.as_ref().unwrap();
        assert_eq!(shape(expr), expected);
        assert_eq!(p.sources.text(expr.span).unwrap(), condition);
    }
}

#[test]
fn helper_and_negated_use_keep_different_origins_from_parsed_text() {
    let p = parse("input i; slot a, b, c; b <- i when not (available(a) and available(c));");
    let ir = lowered(&p);
    let helper = ir
        .corpus
        .relations()
        .find(|r| r.name == "$condition_1")
        .unwrap();
    assert_eq!(
        quotes(&p, &ir, helper.id),
        ["(available(a) and available(c))"]
    );
    let rule = ir
        .corpus
        .rules()
        .find(|r| r.head.relation() == helper.id)
        .unwrap();
    assert_eq!(
        quotes(&p, &ir, rule.id),
        ["(available(a) and available(c))"]
    );
    let use_rule = ir.corpus.rules().last().unwrap();
    let Literal::Negative(atom) = &use_rule.body[0] else {
        panic!("negative helper expected")
    };
    assert_eq!(
        quotes(&p, &ir, atom.id()),
        ["not (available(a) and available(c))"]
    );
}

#[test]
fn alternatives_and_duplicate_statements_keep_distinct_occurrences() {
    let p = parse(
        "input i; slot a, b, c;\nb <- i when available(a) or available(c);\nb <- i when available(a) or available(c);\n",
    );
    let ir = lowered(&p);
    let rules: Vec<_> = ir.corpus.rules().skip(4).collect();
    assert_eq!(rules.len(), 4);
    for (index, rule) in rules.iter().enumerate() {
        let mapping = &p.ast.mappings[index / 2];
        let origins = ir.attribution.provenance.origins(rule.id);
        assert_eq!(origins.len(), 1);
        assert_eq!(origins[0].span, mapping.span);
        assert_eq!(
            quotes(&p, &ir, rule.body[0].atom().id()),
            [if index % 2 == 0 {
                "available(a)"
            } else {
                "available(c)"
            }]
        );
        assert!(
            ir.attribution
                .provenance
                .origins(rule.head.arguments()[1].id())
                .iter()
                .any(|o| o.span == mapping.target.span)
        );
    }
    assert_ne!(rules[0].id, rules[1].id);
    assert_ne!(p.ast.mappings[0].target.span, p.ast.mappings[1].target.span);
}

#[test]
fn original_text_reaches_replayed_overlap_diagnostics_on_both_targets() {
    let p = parse(include_str!("../fixtures/overlapping-mappings.txt"));
    let ir = lowered(&p);
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&ir.corpus, &domains(&ir), &limits).unwrap();
    let report = ground
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    let diagnostics =
        presentation::present(&ir, &report, &p.sources, SourceView::TestDsl.as_str()).unwrap();
    assert_eq!(diagnostics.len(), 2);
    for mapping in &p.ast.mappings[1..] {
        let d = diagnostics
            .iter()
            .find(|d| d.primary == mapping.target.span)
            .unwrap();
        assert!(d.message.contains("input_b, input_bb"));
        assert!(d.related.iter().any(|o| o.span == mapping.input.span));
        assert!(
            d.related
                .iter()
                .any(|o| Some(o.span) == mapping.condition.as_ref().map(|e| e.span))
        );
    }
}

#[test]
fn names_are_checked_by_lowering_and_any_name_error_yields_no_ir() {
    for (text, expected, quoted) in [
        (
            "input i; slot a; a <- missing;",
            DiagnosticKind::UnknownName {
                name: "missing".into(),
                expected: Kind::Input,
            },
            "missing",
        ),
        (
            "input i; slot a; a <- i when available(i);",
            DiagnosticKind::WrongKind {
                name: "i".into(),
                expected: Kind::Slot,
                found: Kind::Input,
            },
            "i",
        ),
        (
            "input i; slot a; a <- i when present(a);",
            DiagnosticKind::WrongKind {
                name: "a".into(),
                expected: Kind::Input,
                found: Kind::Slot,
            },
            "a",
        ),
        (
            "input i, i; slot a; a <- i;",
            DiagnosticKind::DuplicateDeclaration {
                name: "i".into(),
                kind: Kind::Input,
            },
            "i",
        ),
    ] {
        let p = parse(text);
        let LoweringOutcome::UserErrors(errors) = lowering::lower(&p.ast, &p.sources).unwrap()
        else {
            panic!("must not lower a partial program")
        };
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].kind, expected);
        assert_eq!(p.sources.text(errors[0].span).unwrap(), quoted);
    }
    lowered(&parse("shared <- shared; input shared; slot shared;"));
    // The original lowering stress fixture includes three intentional name errors.
    let p = parse(include_str!("../fixtures/lowering.txt"));
    let LoweringOutcome::UserErrors(errors) = lowering::lower(&p.ast, &p.sources).unwrap() else {
        panic!()
    };
    assert_eq!(errors.len(), 3);
}

#[test]
fn malformed_source_never_projects_a_partial_program() {
    for broken in [
        "input i",
        "input i,;",
        "slot ;",
        "a <- ;",
        "a <- i when ;",
        "a <- i when available(a;",
        "a <- i when available();",
        "a <- i when available(a, b);",
        "a <- i when not;",
        "a <- i when present(i) and;",
        "a <- i when (present(i);",
        "a <- i when present(i) available(a);",
        "source i;",
        "/* block comment */",
        "input Upper;",
        "input _x;",
        "input $condition_1;",
        "input a-b;",
        "input café;",
        "input 1a;",
        "input i;\u{feff}slot a;",
    ] {
        // Even intact declarations/mappings around the error must not become an AST.
        let text = format!("input seed; slot kept; kept <- seed;\n{broken}\nslot after;");
        let mut sources = Sources::new();
        let snapshot = sources
            .add(
                "file:///broken.testdsl",
                1,
                SourceView::TestDsl.as_str(),
                text.as_str(),
            )
            .unwrap();
        let document = Document::new(&mut syntax::parser().unwrap(), text, 1, true);
        let ParseOutcome::SyntaxErrors(errors) =
            syntax::project(&document, &sources, snapshot).unwrap()
        else {
            panic!("accepted {broken:?}")
        };
        assert!(!errors.is_empty());
        for error in errors {
            assert!(sources.text(error.span).is_ok());
        }
    }
}

#[test]
fn keywords_are_reserved_in_every_identifier_position_but_prefixes_are_names() {
    for keyword in [
        "input",
        "slot",
        "when",
        "available",
        "present",
        "and",
        "or",
        "not",
    ] {
        for text in [
            format!("input {keyword};"),
            format!("slot {keyword};"),
            format!("{keyword} <- i;"),
            format!("a <- {keyword};"),
            format!("a <- i when present({keyword});"),
            format!("a <- i when available({keyword});"),
        ] {
            let mut sources = Sources::new();
            let snapshot = sources
                .add(
                    "file:///reserved.testdsl",
                    1,
                    SourceView::TestDsl.as_str(),
                    text.as_str(),
                )
                .unwrap();
            let document = Document::new(&mut syntax::parser().unwrap(), text, 1, true);
            assert!(
                matches!(
                    syntax::project(&document, &sources, snapshot).unwrap(),
                    ParseOutcome::SyntaxErrors(_)
                ),
                "accepted {keyword}: {}",
                document.text
            );
        }
        lowered(&parse(&format!(
            "input {keyword}_1; slot {keyword}2; {keyword}2 <- {keyword}_1;"
        )));
    }
}

#[test]
fn comments_line_endings_and_bom_preserve_bytes_and_exact_not_spans() {
    for newline in ["\n", "\r\n", "\r"] {
        let text = format!(
            "\u{feff}// 😀 café{newline}input i;{newline}slot a;{newline}a <- i when not // 🦀{newline} present(i); // end"
        );
        let p = parse(&text);
        let mapping = &p.ast.mappings[0];
        let ExprKind::Not { keyword, operand } = &mapping.condition.as_ref().unwrap().kind else {
            panic!()
        };
        assert_eq!(p.sources.text(*keyword).unwrap(), "not");
        assert_eq!(p.sources.text(operand.span).unwrap(), "present(i)");
        let document = Document::new(&mut syntax::parser().unwrap(), text, 1, true);
        assert_eq!(
            document.position(mapping.target.span.byte_range().start),
            Position::new(3, 0)
        );
        assert_eq!(
            document.position(keyword.byte_range().start),
            Position::new(3, 12)
        );
        lowered(&p);
    }
    assert_eq!(parse("// empty draft\n").ast, Program::default());
}

#[test]
fn missing_tokens_have_insertion_spans_and_snapshot_mismatch_is_a_creator_failure() {
    let text = "input i";
    let mut sources = Sources::new();
    let snapshot = sources
        .add("file:///a.testdsl", 1, SourceView::TestDsl.as_str(), text)
        .unwrap();
    let document = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
    let ParseOutcome::SyntaxErrors(errors) =
        syntax::project(&document, &sources, snapshot).unwrap()
    else {
        panic!()
    };
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].message, "Expected ';'.");
    assert_eq!(errors[0].span.byte_range(), text.len()..text.len());
    let newer = sources
        .add(
            "file:///a.testdsl",
            2,
            SourceView::TestDsl.as_str(),
            "input input_long;",
        )
        .unwrap();
    assert!(matches!(
        syntax::project(&document, &sources, newer),
        Err(ParseFailure::SnapshotMismatch)
    ));
}

#[test]
fn incremental_damage_and_repair_match_fresh_projection_at_the_current_snapshot() {
    let text = include_str!("../fixtures/overlapping-mappings.txt");
    let mut parser = syntax::parser().unwrap();
    let mut document = Document::new(&mut parser, text.into(), 1, true);
    let mut sources = Sources::new();
    let initial = sources
        .add(
            "file:///edit.testdsl",
            1,
            SourceView::TestDsl.as_str(),
            text,
        )
        .unwrap();
    let ParseOutcome::Parsed(old_ast) = syntax::project(&document, &sources, initial).unwrap()
    else {
        panic!()
    };
    let old_target: SourceSpan = old_ast.mappings[1].target.span;
    for (version, range, replacement, valid) in [
        (
            2,
            Range::new(Position::new(0, 0), Position::new(0, 0)),
            "// 😀 comment\r\n",
            true,
        ),
        (
            3,
            Range::new(Position::new(1, 32), Position::new(1, 33)),
            "",
            false,
        ),
        (
            4,
            Range::new(Position::new(1, 32), Position::new(1, 32)),
            ";",
            true,
        ),
        (
            5,
            Range::new(Position::new(5, 0), Position::new(5, 1)),
            "a",
            true,
        ),
    ] {
        document = document
            .changed(
                &mut parser,
                &[TextDocumentContentChangeEvent {
                    range: Some(range),
                    range_length: None,
                    text: replacement.into(),
                }],
                version,
            )
            .unwrap();
        let snapshot = sources
            .add(
                "file:///edit.testdsl",
                version as u64,
                SourceView::TestDsl.as_str(),
                document.text.as_str(),
            )
            .unwrap();
        let actual = syntax::project(&document, &sources, snapshot).unwrap();
        let fresh = Document::new(
            &mut syntax::parser().unwrap(),
            document.text.clone(),
            version,
            true,
        );
        assert_eq!(actual, syntax::project(&fresh, &sources, snapshot).unwrap());
        assert_eq!(
            matches!(actual, ParseOutcome::Parsed(_)),
            valid,
            "version {version}: {}",
            document.text
        );
        if let ParseOutcome::Parsed(ast) = actual {
            let target = ast.mappings[1].target.span;
            assert_eq!(target.snapshot(), snapshot);
            assert_eq!(
                document.position(target.byte_range().start),
                Position::new(5, 0)
            );
            assert_ne!(target, old_target);
            let LoweringOutcome::Lowered(ir) = lowering::lower(&ast, &sources).unwrap() else {
                panic!()
            };
            let rule = ir.corpus.rules().nth(5).unwrap();
            assert!(
                ir.attribution
                    .provenance
                    .origins(rule.head.arguments()[1].id())
                    .iter()
                    .any(|o| o.span == target)
            );
        }
    }
    assert_eq!(sources.text(old_target).unwrap(), "b"); // Old evidence still quotes the old snapshot.
}
