use denotate_ir::*;
use denotate_test_dsl::attribution::{Attribution, SourceView};
use denotate_test_dsl::library::{self, MappingLibrary};

const DSL: &str = include_str!("../fixtures/overlapping-mappings.txt");

struct Example {
    corpus: Corpus,
    library: MappingLibrary,
    mappings: Vec<RuleId>,
    sources: Sources,
    attribution: Attribution,
}

// Deliberate direct construction, not a parser or DSL AST lowerer. Test-owned
// source associations are explicit so slice 2 can assert the same output.
fn example() -> Example {
    let mut corpus = Corpus::new();
    let library = library::build(&mut corpus).unwrap();
    let a = corpus.declare_constant("a", library.slot).unwrap();
    let b = corpus.declare_constant("b", library.slot).unwrap();
    let input_a = corpus.declare_constant("input_a", library.input).unwrap();
    let input_b = corpus.declare_constant("input_b", library.input).unwrap();
    let input_bb = corpus.declare_constant("input_bb", library.input).unwrap();
    let mut sources = Sources::new();
    let document = sources
        .add(
            "file:///overlapping-mappings.flow",
            1,
            SourceView::TestDsl.as_str(),
            DSL,
        )
        .unwrap();
    let mut provenance = Provenance::new();
    let mut mappings = Vec::new();
    for (statement, input_name, input, slot, conditional) in [
        ("a <- input_a;", "input_a", input_a, a, false),
        (
            "b <- input_b  when available(a);",
            "input_b",
            input_b,
            b,
            true,
        ),
        (
            "b <- input_bb when available(a);",
            "input_bb",
            input_bb,
            b,
            true,
        ),
    ] {
        let start = DSL.find(statement).unwrap();
        let span = |offset, length| {
            sources
                .span(document, start + offset..start + offset + length)
                .unwrap()
        };
        let head = corpus
            .atom(library.mapped_to, [input.into(), slot.into()])
            .unwrap();
        let head_id = head.id();
        let input_id = head.arguments()[0].id();
        let slot_id = head.arguments()[1].id();
        let mut body = Vec::new();
        let mut condition_origins = Vec::new();
        if conditional {
            let condition = corpus.atom(library.available, [a.into()]).unwrap();
            let at = statement.find("available(a)").unwrap();
            condition_origins.push((condition.id(), Origin::new(span(at, 12))));
            condition_origins.push((condition.arguments()[0].id(), Origin::new(span(at + 10, 1))));
            body.push(Literal::Positive(condition));
        }
        let rule = corpus.add_rule(head, body).unwrap();
        provenance
            .attach(
                &corpus,
                &sources,
                rule,
                [Origin::new(span(0, statement.len()))],
            )
            .unwrap();
        let input_at = statement.find(input_name).unwrap();
        provenance
            .attach(
                &corpus,
                &sources,
                head_id,
                [Origin::new(span(0, input_at + input_name.len()))],
            )
            .unwrap();
        provenance
            .attach(
                &corpus,
                &sources,
                input_id,
                [Origin::new(span(input_at, input_name.len()))],
            )
            .unwrap();
        provenance
            .attach(&corpus, &sources, slot_id, [Origin::new(span(0, 1))])
            .unwrap();
        for (occurrence, origin) in condition_origins {
            provenance
                .attach(&corpus, &sources, occurrence, [origin])
                .unwrap();
        }
        mappings.push(rule);
    }
    let attribution = Attribution {
        provenance,
        ..Default::default()
    };
    attribution.validate(&corpus, &sources).unwrap();
    Example {
        corpus,
        library,
        mappings,
        sources,
        attribution,
    }
}

// A test-only readable projection of semantic fields. No generated source map
// or Denotate printer is implemented by this helper.
fn atom_text(corpus: &Corpus, atom: &Atom) -> String {
    let arguments: Vec<_> = atom
        .arguments()
        .iter()
        .map(|term| match term.value() {
            Term::Constant(id) => corpus.constant(*id).unwrap().name.clone(),
            Term::Variable { name, .. } => name.clone(),
        })
        .collect();
    format!(
        "{}({})",
        corpus.relation(atom.relation()).unwrap().name,
        arguments.join(", ")
    )
}

fn rule_text(corpus: &Corpus, rule: &Rule) -> String {
    let head = atom_text(corpus, &rule.head);
    if rule.is_fact() {
        return format!("{head};");
    }
    let body: Vec<_> = rule
        .body
        .iter()
        .map(|literal| match literal {
            Literal::Positive(atom) => atom_text(corpus, atom),
            Literal::Negative(atom) => format!("!{}", atom_text(corpus, atom)),
        })
        .collect();
    format!("{head} :- {};", body.join(", "))
}

#[test]
fn constructs_the_example_and_library_via_the_public_api() {
    let e = example();
    assert_eq!(
        e.corpus
            .sorts()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["Slot", "Input"]
    );
    assert_eq!(e.corpus.constants().count(), 5);
    assert_eq!(e.corpus.relations().count(), 4);
    assert_eq!(
        e.corpus.relation(e.library.present).unwrap().role,
        RelationRole::Input
    );
    assert_eq!(
        e.corpus
            .rules()
            .map(|r| rule_text(&e.corpus, r))
            .collect::<Vec<_>>(),
        [
            "supplies(I, D) :- mapped_to(I, D), present(I);",
            "available(D) :- supplies(I, D);",
            "mapped_to(input_a, a);",
            "mapped_to(input_b, b) :- available(a);",
            "mapped_to(input_bb, b) :- available(a);",
        ]
    );
    let obligation = e.corpus.obligation(e.library.unique_input).unwrap();
    assert_eq!(
        obligation.requirement,
        Requirement::AtMostOne {
            relation: e.library.supplies,
            group_by: vec![1],
        }
    );
    assert_eq!(
        obligation.message_template,
        "Slot {slot} has overlapping InputMappings from {inputs}."
    );
    // No present facts have been fixed. This constructs an obligation; it does
    // not evaluate it, establish the conflict or require missing slots to exist.
    assert!(
        e.corpus
            .rules()
            .all(|r| r.head.relation() != e.library.present)
    );
}

#[test]
fn equal_slot_values_retain_precise_distinct_occurrences_and_conditions() {
    let e = example();
    let first = e.corpus.rule(e.mappings[1]).unwrap();
    let second = e.corpus.rule(e.mappings[2]).unwrap();
    let b1 = &first.head.arguments()[1];
    let b2 = &second.head.arguments()[1];
    assert_eq!(b1.value(), b2.value());
    assert_ne!(b1.id(), b2.id());
    let guard1 = first.body[0].atom();
    let guard2 = second.body[0].atom();
    assert_eq!(guard1.relation(), guard2.relation());
    assert_ne!(guard1.id(), guard2.id());
    assert_eq!(guard1.arguments()[0].value(), guard2.arguments()[0].value());
    assert_ne!(guard1.arguments()[0].id(), guard2.arguments()[0].id());
    assert_ne!(
        e.attribution.provenance.origins(guard1.id())[0].span,
        e.attribution.provenance.origins(guard2.id())[0].span
    );
    let first_span = e.attribution.provenance.origins(b1.id())[0].span;
    let second_span = e.attribution.provenance.origins(b2.id())[0].span;
    assert_ne!(first_span, second_span);
    assert_eq!(
        first_span.byte_range().start,
        DSL.find("b <- input_b ").unwrap()
    );
    assert_eq!(
        second_span.byte_range().start,
        DSL.find("b <- input_bb").unwrap()
    );
    for (rule, input) in [(first, "input_b"), (second, "input_bb")] {
        let quote = |id| {
            e.sources
                .text(e.attribution.provenance.origins(id)[0].span)
                .unwrap()
        };
        assert_eq!(quote(rule.head.arguments()[0].id()), input);
        assert_eq!(quote(rule.head.arguments()[1].id()), "b");
        assert_eq!(quote(rule.body[0].atom().id()), "available(a)");
        assert_eq!(quote(rule.body[0].atom().arguments()[0].id()), "a");
        assert_eq!(
            quote(rule.id.into()),
            if input == "input_b" {
                "b <- input_b  when available(a);"
            } else {
                "b <- input_bb when available(a);"
            }
        );
    }
}

#[test]
fn adding_a_denotate_view_does_not_replace_dsl_term_origins() {
    let mut e = example();
    let rule = e.corpus.rule(e.mappings[1]).unwrap();
    let target = rule.head.arguments()[1].id();
    let original = e.attribution.provenance.origins(target).to_vec();
    let generated_text = "mapped_to(input_b, b) :- available(a);";
    let doc = e
        .sources
        .add(
            "file:///generated.den",
            1,
            SourceView::Denotate.as_str(),
            generated_text,
        )
        .unwrap();
    let start = generated_text.find(", b").unwrap() + 2;
    e.attribution
        .provenance
        .attach(
            &e.corpus,
            &e.sources,
            target,
            [Origin::new(e.sources.span(doc, start..start + 1).unwrap())],
        )
        .unwrap();
    assert_eq!(
        e.attribution
            .provenance
            .in_view(target, &e.sources, SourceView::TestDsl.as_str())
            .unwrap(),
        original.iter().collect::<Vec<_>>()
    );
    let denotate_origins = e
        .attribution
        .provenance
        .in_view(target, &e.sources, SourceView::Denotate.as_str())
        .unwrap();
    assert_eq!(denotate_origins.len(), 1);
    assert_eq!(e.sources.text(denotate_origins[0].span).unwrap(), "b");
}

#[test]
fn wrong_sort_from_a_lowerer_is_a_construction_error_not_a_user_diagnostic() {
    let mut e = example();
    let slot_value = e
        .corpus
        .declare_constant("wrong_input", e.library.slot)
        .unwrap();
    let slot = e.corpus.declare_constant("c", e.library.slot).unwrap();
    let before = e.corpus.rules().count();
    assert!(
        matches!(e.corpus.atom(e.library.mapped_to, [slot_value.into(), slot.into()]),
        Err(ConstructionError::SortMismatch { argument: 0, expected, actual, .. })
            if expected == e.library.input && actual == e.library.slot)
    );
    assert_eq!(e.corpus.rules().count(), before);
}
