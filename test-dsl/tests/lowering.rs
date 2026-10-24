use denotate_ir::*;
use denotate_test_dsl::attribution::SourceView;
use denotate_test_dsl::{ast::*, lowering::*};

const CASES: &str = include_str!("../fixtures/lowering.txt");
const OVERLAP: &str = include_str!("../fixtures/overlapping-mappings.txt");

/// Hand-written fixture builder, not a parser: every declaration, mapping,
/// operator and operand is specified by each test. Searches locate exact spans.
struct Fixture {
    sources: Sources,
    snapshot: SnapshotId,
    text: &'static str,
    program: Program,
}
impl Fixture {
    fn new(text: &'static str) -> Self {
        let mut sources = Sources::new();
        let snapshot = sources
            .add("file:///case.flow", 1, SourceView::TestDsl.as_str(), text)
            .unwrap();
        Self {
            sources,
            snapshot,
            text,
            program: Program::default(),
        }
    }
    fn span(&self, start: usize, end: usize) -> SourceSpan {
        self.sources.span(self.snapshot, start..end).unwrap()
    }
    fn occurrence(&self, text: &str, nth: usize) -> SourceSpan {
        let start = self.text.match_indices(text).nth(nth).unwrap().0;
        self.span(start, start + text.len())
    }
    fn name_in(&self, container: SourceSpan, text: &str) -> Name {
        let at = self.sources.text(container).unwrap().find(text).unwrap()
            + container.byte_range().start;
        Name {
            text: text.into(),
            span: self.span(at, at + text.len()),
        }
    }
    fn declare(&mut self, text: &str, nth: usize, kind: Kind, names: &[&str]) {
        let span = self.occurrence(text, nth);
        self.program.declarations.push(Declaration {
            kind,
            span,
            names: names.iter().map(|n| self.name_in(span, n)).collect(),
        });
    }
    fn cases() -> Self {
        let mut f = Self::new(CASES);
        f.declare(
            "input input_a, input_b, input_bb, input_x;",
            0,
            Kind::Input,
            &["input_a", "input_b", "input_bb", "input_x"],
        );
        f.declare("slot a, b, c;", 0, Kind::Slot, &["a", "b", "c"]);
        f
    }
    fn atom(&self, statement: SourceSpan, name: &str, input: bool) -> Expr {
        let call = format!("{}({name})", if input { "present" } else { "available" });
        let at = statement.byte_range().start
            + self.sources.text(statement).unwrap().find(&call).unwrap();
        let span = self.span(at, at + call.len());
        // Search only inside the parentheses, not the predicate's spelling.
        let arg = self.span(at + call.find('(').unwrap() + 1, at + call.len() - 1);
        let name = Name {
            text: name.into(),
            span: arg,
        };
        Expr {
            span,
            kind: if input {
                ExprKind::Present(name)
            } else {
                ExprKind::Available(name)
            },
        }
    }
    fn binary(&self, a: Expr, b: Expr, or: bool) -> Expr {
        let span = self.span(a.span.byte_range().start, b.span.byte_range().end);
        Expr {
            span,
            kind: if or {
                ExprKind::Or(Box::new(a), Box::new(b))
            } else {
                ExprKind::And(Box::new(a), Box::new(b))
            },
        }
    }
    fn group(&self, inner: Expr) -> Expr {
        let span = self.span(
            inner.span.byte_range().start - 1,
            inner.span.byte_range().end + 1,
        );
        assert!(self.sources.text(span).unwrap().starts_with('('));
        assert!(self.sources.text(span).unwrap().ends_with(')'));
        Expr {
            span,
            kind: ExprKind::Group(Box::new(inner)),
        }
    }
    fn not(&self, inner: Expr) -> Expr {
        let start = inner.span.byte_range().start - 4;
        let keyword = self.span(start, start + 3);
        assert_eq!(self.sources.text(keyword).unwrap(), "not");
        Expr {
            span: self.span(start, inner.span.byte_range().end),
            kind: ExprKind::Not {
                keyword,
                operand: Box::new(inner),
            },
        }
    }
    fn mapping(&mut self, span: SourceSpan, target: &str, input: &str, condition: Option<Expr>) {
        self.program.mappings.push(Mapping {
            target: self.name_in(span, target),
            input: self.name_in(span, input),
            condition,
            span,
        });
    }
    fn lower(&self) -> LoweredProgram {
        match lower(&self.program, &self.sources).unwrap() {
            LoweringOutcome::Lowered(p) => p,
            LoweringOutcome::UserErrors(errors) => panic!("unexpected user errors: {errors:?}"),
        }
    }
}

fn atom_text(c: &Corpus, atom: &Atom) -> String {
    let args: Vec<_> = atom
        .arguments()
        .iter()
        .map(|t| match t.value() {
            Term::Constant(id) => c.constant(*id).unwrap().name.clone(),
            Term::Variable { name, .. } => name.clone(),
        })
        .collect();
    format!(
        "{}({})",
        c.relation(atom.relation()).unwrap().name,
        args.join(", ")
    )
}
fn rules(p: &LoweredProgram) -> Vec<String> {
    p.corpus
        .rules()
        .skip(4)
        .map(|r| {
            let head = atom_text(&p.corpus, &r.head);
            if r.is_fact() {
                return format!("{head};");
            }
            let body: Vec<_> = r
                .body
                .iter()
                .map(|lit| match lit {
                    Literal::Positive(a) => atom_text(&p.corpus, a),
                    Literal::Negative(a) => format!("!{}", atom_text(&p.corpus, a)),
                })
                .collect();
            format!("{head} :- {};", body.join(", "))
        })
        .collect()
}
fn quotes<'a>(f: &'a Fixture, p: &LoweredProgram, id: impl Into<OccurrenceId>) -> Vec<&'a str> {
    p.attribution
        .provenance
        .origins(id)
        .iter()
        .map(|o| f.sources.text(o.span).unwrap())
        .collect()
}
fn assert_terms_have_origins(f: &Fixture, p: &LoweredProgram) {
    for rule in p.corpus.rules().skip(4) {
        for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
            assert!(!p.attribution.provenance.origins(atom.id()).is_empty());
            for arg in atom.arguments() {
                let Term::Constant(id) = arg.value() else {
                    panic!("DSL generated a variable")
                };
                let origins = p.attribution.provenance.origins(arg.id());
                assert_eq!(origins.len(), 1);
                assert_eq!(
                    f.sources.text(origins[0].span).unwrap(),
                    p.corpus.constant(*id).unwrap().name
                );
            }
        }
    }
}

#[test]
fn existing_overlap_lowers_through_the_api_with_exact_term_origins() {
    let mut f = Fixture::new(OVERLAP);
    f.declare(
        "input input_a, input_b, input_bb;",
        0,
        Kind::Input,
        &["input_a", "input_b", "input_bb"],
    );
    f.declare("slot a, b;", 0, Kind::Slot, &["a", "b"]);
    let first = f.occurrence("a <- input_a;", 0);
    f.mapping(first, "a", "input_a", None);
    for (text, input) in [
        ("b <- input_b  when available(a);", "input_b"),
        ("b <- input_bb when available(a);", "input_bb"),
    ] {
        let span = f.occurrence(text, 0);
        let guard = f.atom(span, "a", false);
        f.mapping(span, "b", input, Some(guard));
    }
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "mapped_to(input_a, a);",
            "mapped_to(input_b, b) :- available(a);",
            "mapped_to(input_bb, b) :- available(a);"
        ]
    );
    assert_eq!(
        p.corpus
            .obligation(p.library.unique_input)
            .unwrap()
            .requirement,
        Requirement::AtMostOne {
            relation: p.library.supplies,
            group_by: vec![1]
        }
    );
    assert_terms_have_origins(&f, &p);
    let mappings: Vec<_> = p.corpus.rules().skip(4).collect();
    for (rule, mapping) in mappings.iter().zip(&f.program.mappings) {
        assert_eq!(
            p.attribution.provenance.origins(rule.id)[0].span,
            mapping.span
        );
        assert_eq!(
            p.attribution
                .provenance
                .origins(rule.head.arguments()[0].id())[0]
                .span,
            mapping.input.span
        );
        assert_eq!(
            p.attribution
                .provenance
                .origins(rule.head.arguments()[1].id())[0]
                .span,
            mapping.target.span
        );
        assert_eq!(
            quotes(&f, &p, rule.head.id()),
            [f.sources.text(mapping.span).unwrap()]
        );
    }
    let b1 = &mappings[1].head.arguments()[1];
    let b2 = &mappings[2].head.arguments()[1];
    assert_eq!(b1.value(), b2.value());
    assert_ne!(b1.id(), b2.id());
    assert_ne!(
        p.attribution.provenance.origins(b1.id()),
        p.attribution.provenance.origins(b2.id())
    );
}

#[test]
fn top_level_or_splits_heads_with_shared_statement_origins() {
    let mut f = Fixture::cases();
    let span = f.occurrence("b <- input_b when available(a) or available(c);", 0);
    let condition = f.binary(f.atom(span, "a", false), f.atom(span, "c", false), true);
    f.mapping(span, "b", "input_b", Some(condition));
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "mapped_to(input_b, b) :- available(a);",
            "mapped_to(input_b, b) :- available(c);"
        ]
    );
    let rs: Vec<_> = p.corpus.rules().skip(4).collect();
    for (r, alt) in rs.iter().zip(["available(a)", "available(c)"]) {
        assert_eq!(quotes(&f, &p, r.id), [f.sources.text(span).unwrap()]);
        assert_eq!(quotes(&f, &p, r.body[0].atom().id()), [alt]);
    }
    assert_eq!(
        rs[0].head.arguments()[1].value(),
        rs[1].head.arguments()[1].value()
    );
    assert_ne!(
        rs[0].head.arguments()[1].id(),
        rs[1].head.arguments()[1].id()
    );
    assert_eq!(
        p.attribution
            .provenance
            .origins(rs[0].head.arguments()[1].id()),
        p.attribution
            .provenance
            .origins(rs[1].head.arguments()[1].id())
    );
    assert_terms_have_origins(&f, &p);
}

#[test]
fn complementary_guards_and_self_negative_mapping_are_not_admissibility_checked() {
    let mut f = Fixture::cases();
    let s = f.occurrence("b <- input_b when available(a);", 0);
    f.mapping(s, "b", "input_b", Some(f.atom(s, "a", false)));
    for (line, target, input) in [
        ("b <- input_bb when not available(a);", "b", "input_bb"),
        ("a <- input_a when not available(a);", "a", "input_a"),
    ] {
        let s = f.occurrence(line, 0);
        f.mapping(s, target, input, Some(f.not(f.atom(s, "a", false))));
    }
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "mapped_to(input_b, b) :- available(a);",
            "mapped_to(input_bb, b) :- !available(a);",
            "mapped_to(input_a, a) :- !available(a);"
        ]
    );
    for r in p.corpus.rules().skip(5) {
        assert_eq!(quotes(&f, &p, r.body[0].atom().id()), ["not available(a)"]);
    }
    assert_terms_have_origins(&f, &p);
}

#[test]
fn fixed_input_negation_is_a_negative_present_atom() {
    let mut f = Fixture::cases();
    let s = f.occurrence("b <- input_b when not present(input_x);", 0);
    f.mapping(s, "b", "input_b", Some(f.not(f.atom(s, "input_x", true))));
    let p = f.lower();
    assert_eq!(rules(&p), ["mapped_to(input_b, b) :- !present(input_x);"]);
    assert_terms_have_origins(&f, &p);
    let atom = p.corpus.rules().last().unwrap().body[0].atom();
    assert_eq!(quotes(&f, &p, atom.id()), ["not present(input_x)"]);
}

#[test]
fn negated_conjunction_uses_a_helper_and_keeps_full_negation_origins() {
    let mut f = Fixture::cases();
    let s = f.occurrence("b <- input_b when not (available(a) and available(c));", 0);
    let and = f.binary(f.atom(s, "a", false), f.atom(s, "c", false), false);
    let operand = f.group(and);
    let operand_span = operand.span;
    let condition = f.not(operand);
    f.mapping(s, "b", "input_b", Some(condition));
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "$condition_1() :- available(a), available(c);",
            "mapped_to(input_b, b) :- !$condition_1();"
        ]
    );
    let helper = p.corpus.relations().last().unwrap();
    assert_eq!(
        p.attribution.provenance.origins(helper.id)[0].span,
        operand_span
    );
    let rs: Vec<_> = p.corpus.rules().skip(4).collect();
    assert_eq!(
        quotes(&f, &p, rs[0].id),
        ["(available(a) and available(c))"]
    );
    let atom = rs[1].body[0].atom();
    assert_eq!(
        quotes(&f, &p, atom.id()),
        ["not (available(a) and available(c))"]
    );
    assert_terms_have_origins(&f, &p);
}

#[test]
fn nested_or_uses_a_helper_without_distributing_the_outer_conjunction() {
    let mut f = Fixture::cases();
    let s = f.occurrence(
        "b <- input_b when (available(a) or available(c)) and present(input_b);",
        0,
    );
    let or = f.group(f.binary(f.atom(s, "a", false), f.atom(s, "c", false), true));
    let condition = f.binary(or, f.atom(s, "input_b", true), false);
    f.mapping(s, "b", "input_b", Some(condition));
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "$condition_1() :- available(a);",
            "$condition_1() :- available(c);",
            "mapped_to(input_b, b) :- $condition_1(), present(input_b);"
        ]
    );
    assert_terms_have_origins(&f, &p);
    let helpers: Vec<_> = p.corpus.rules().skip(4).take(2).collect();
    for (r, alt) in helpers.iter().zip(["available(a)", "available(c)"]) {
        assert_eq!(quotes(&f, &p, r.body[0].atom().id()), [alt]);
        assert_eq!(quotes(&f, &p, r.id), ["(available(a) or available(c))"]);
    }
}

#[test]
fn identical_statements_keep_distinct_occurrences_and_source_spans() {
    let mut f = Fixture::cases();
    for nth in 0..2 {
        let s = f.occurrence("b <- input_b when available(a);", nth);
        f.mapping(s, "b", "input_b", Some(f.atom(s, "a", false)));
    }
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "mapped_to(input_b, b) :- available(a);",
            "mapped_to(input_b, b) :- available(a);"
        ]
    );
    let rs: Vec<_> = p.corpus.rules().skip(4).collect();
    assert_ne!(rs[0].id, rs[1].id);
    assert_ne!(
        p.attribution.provenance.origins(rs[0].id),
        p.attribution.provenance.origins(rs[1].id)
    );
    let a = rs[0].body[0].atom();
    let b = rs[1].body[0].atom();
    assert_eq!(a.relation(), b.relation());
    assert_ne!(a.id(), b.id());
    assert_eq!(a.arguments()[0].value(), b.arguments()[0].value());
    assert_ne!(a.arguments()[0].id(), b.arguments()[0].id());
    assert_ne!(
        p.attribution.provenance.origins(a.id()),
        p.attribution.provenance.origins(b.id())
    );
}

#[test]
fn name_errors_are_all_or_nothing_at_the_name_and_distinct_from_creator_failures() {
    let mut f = Fixture::cases();
    for (line, name, input) in [
        ("b <- input_b when available(missing);", "missing", false),
        ("b <- input_b when available(input_a);", "input_a", false),
        ("b <- input_b when present(a);", "a", true),
    ] {
        let s = f.occurrence(line, 0);
        f.mapping(s, "b", "input_b", Some(f.atom(s, name, input)));
    }
    let LoweringOutcome::UserErrors(errors) = lower(&f.program, &f.sources).unwrap() else {
        panic!("invalid program produced IR")
    };
    assert_eq!(errors.len(), 3);
    assert_eq!(
        errors
            .iter()
            .map(|e| f.sources.text(e.span).unwrap())
            .collect::<Vec<_>>(),
        ["missing", "input_a", "a"]
    );
    assert_eq!(
        errors[0].kind,
        DiagnosticKind::UnknownName {
            name: "missing".into(),
            expected: Kind::Slot
        }
    );
    assert_eq!(
        errors[1].kind,
        DiagnosticKind::WrongKind {
            name: "input_a".into(),
            expected: Kind::Slot,
            found: Kind::Input
        }
    );
    assert_eq!(
        errors[2].kind,
        DiagnosticKind::WrongKind {
            name: "a".into(),
            expected: Kind::Input,
            found: Kind::Slot
        }
    );
    assert!(!errors[1].related.is_empty());
    f.program.mappings[0].target.text = "not_the_spanned_name".into();
    assert!(matches!(
        lower(&f.program, &f.sources),
        Err(LoweringFailure::InvalidAst(_))
    ));
}

#[test]
fn mapping_head_errors_prevent_output_even_alongside_valid_statements() {
    let mut f = Fixture::new(
        "input input_a;\nslot a;\na <- input_a;\nmissing <- missing_input;\ninput_a <- a;\n",
    );
    f.declare("input input_a;", 0, Kind::Input, &["input_a"]);
    f.declare("slot a;", 0, Kind::Slot, &["a"]);
    for (line, target, input) in [
        ("a <- input_a;", "a", "input_a"),
        ("missing <- missing_input;", "missing", "missing_input"),
        ("input_a <- a;", "input_a", "a"),
    ] {
        let span = f.occurrence(line, 0);
        f.mapping(span, target, input, None);
        // The last Input name is also a suffix of the target: specify that use.
        if input == "a" {
            let start = span.byte_range().end - 2;
            f.program.mappings.last_mut().unwrap().input.span =
                f.sources.span(f.snapshot, start..start + 1).unwrap();
        }
    }
    let LoweringOutcome::UserErrors(errors) = lower(&f.program, &f.sources).unwrap() else {
        panic!("invalid program produced IR")
    };
    assert_eq!(
        errors.iter().map(|e| &e.kind).collect::<Vec<_>>(),
        [
            &DiagnosticKind::UnknownName {
                name: "missing".into(),
                expected: Kind::Slot
            },
            &DiagnosticKind::UnknownName {
                name: "missing_input".into(),
                expected: Kind::Input
            },
            &DiagnosticKind::WrongKind {
                name: "input_a".into(),
                expected: Kind::Slot,
                found: Kind::Input
            },
            &DiagnosticKind::WrongKind {
                name: "a".into(),
                expected: Kind::Input,
                found: Kind::Slot
            },
        ]
    );
    assert_eq!(
        errors
            .iter()
            .map(|e| f.sources.text(e.span).unwrap())
            .collect::<Vec<_>>(),
        ["missing", "missing_input", "input_a", "a"]
    );
}

#[test]
fn foreign_source_snapshots_are_creator_failures_not_dsl_diagnostics() {
    let f = Fixture::cases();
    assert!(matches!(
        lower(&f.program, &Sources::new()),
        Err(LoweringFailure::Provenance(
            ProvenanceError::UnknownSnapshot(_)
        ))
    ));
}

#[test]
fn negated_or_pushes_not_to_both_atoms_without_a_helper() {
    let mut f = Fixture::cases();
    let s = f.occurrence("b <- input_b when not (available(a) or available(c));", 0);
    let or = f.group(f.binary(f.atom(s, "a", false), f.atom(s, "c", false), true));
    f.mapping(s, "b", "input_b", Some(f.not(or)));
    let p = f.lower();
    assert_eq!(
        rules(&p),
        ["mapped_to(input_b, b) :- !available(a), !available(c);"]
    );
    let r = p.corpus.rules().last().unwrap();
    for lit in &r.body {
        assert_eq!(
            quotes(&f, &p, lit.atom().id()),
            ["not (available(a) or available(c))"]
        );
    }
    assert_eq!(
        p.attribution.provenance.origins(r.body[0].atom().id())[0].span,
        p.attribution.provenance.origins(r.body[1].atom().id())[0].span
    );
    assert_terms_have_origins(&f, &p);
}

#[test]
fn duplicate_declarations_error_but_cross_kind_names_resolve_by_expected_kind() {
    let text =
        "input shared;\nslot shared;\nshared <- shared when present(shared);\ninput shared;\n";
    let mut f = Fixture::new(text);
    f.declare("input shared;", 0, Kind::Input, &["shared"]);
    f.declare("slot shared;", 0, Kind::Slot, &["shared"]);
    let s = f.occurrence("shared <- shared when present(shared);", 0);
    f.mapping(s, "shared", "shared", Some(f.atom(s, "shared", true)));
    // Both spellings are equal; their source occurrences must still be precise.
    let input_at = s.byte_range().start + "shared <- ".len();
    f.program.mappings[0].input.span = f.span(input_at, input_at + 6);
    let p = f.lower();
    assert_eq!(rules(&p), ["mapped_to(shared, shared) :- present(shared);"]);
    let r = p.corpus.rules().last().unwrap();
    assert_ne!(r.head.arguments()[0].value(), r.head.arguments()[1].value());
    assert_terms_have_origins(&f, &p);
    f.declare("input shared;", 1, Kind::Input, &["shared"]);
    let LoweringOutcome::UserErrors(errors) = lower(&f.program, &f.sources).unwrap() else {
        panic!("duplicate produced IR")
    };
    assert_eq!(errors.len(), 1);
    assert_eq!(
        errors[0].kind,
        DiagnosticKind::DuplicateDeclaration {
            name: "shared".into(),
            kind: Kind::Input
        }
    );
    assert_eq!(errors[0].related, [f.program.declarations[0].names[0].span]);
    assert_ne!(errors[0].span, errors[0].related[0]);
}

#[test]
fn double_negation_normalizes_with_one_full_expression_origin() {
    let mut f = Fixture::cases();
    let s = f.occurrence("b <- input_b when not not available(a);", 0);
    f.mapping(s, "b", "input_b", Some(f.not(f.not(f.atom(s, "a", false)))));
    let p = f.lower();
    assert_eq!(rules(&p), ["mapped_to(input_b, b) :- available(a);"]);
    let a = p.corpus.rules().last().unwrap().body[0].atom();
    assert_eq!(quotes(&f, &p, a.id()), ["not not available(a)"]);
}

#[test]
fn nested_demorgan_retains_the_outer_not_on_a_generated_helper_use() {
    let mut f = Fixture::cases();
    let s = f.occurrence(
        "b <- input_b when not (available(a) or (available(c) and present(input_x)));",
        0,
    );
    let and = f.group(f.binary(f.atom(s, "c", false), f.atom(s, "input_x", true), false));
    let or = f.group(f.binary(f.atom(s, "a", false), and, true));
    f.mapping(s, "b", "input_b", Some(f.not(or)));
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "$condition_1() :- available(c), present(input_x);",
            "mapped_to(input_b, b) :- !available(a), !$condition_1();"
        ]
    );
    let r = p.corpus.rules().last().unwrap();
    for literal in &r.body {
        assert_eq!(
            quotes(&f, &p, literal.atom().id()),
            ["not (available(a) or (available(c) and present(input_x)))"]
        );
    }
    assert_terms_have_origins(&f, &p);
}

#[test]
fn two_nested_ors_have_linear_helpers_and_repeatable_numbering_and_origins() {
    let mut f = Fixture::cases();
    let s = f.occurrence("b <- input_b when (available(a) or available(c)) and (present(input_b) or present(input_x));", 0);
    let left = f.group(f.binary(f.atom(s, "a", false), f.atom(s, "c", false), true));
    let right = f.group(f.binary(f.atom(s, "input_b", true), f.atom(s, "input_x", true), true));
    f.mapping(s, "b", "input_b", Some(f.binary(left, right, false)));
    let p = f.lower();
    assert_eq!(
        rules(&p),
        [
            "$condition_1() :- available(a);",
            "$condition_1() :- available(c);",
            "$condition_2() :- present(input_b);",
            "$condition_2() :- present(input_x);",
            "mapped_to(input_b, b) :- $condition_1(), $condition_2();"
        ]
    );
    let again = f.lower();
    assert_eq!(rules(&p), rules(&again));
    for (a, b) in p.corpus.rules().zip(again.corpus.rules()) {
        assert_eq!(
            p.attribution.provenance.origins(a.id),
            again.attribution.provenance.origins(b.id)
        );
        for (a, b) in std::iter::once(&a.head)
            .chain(a.body.iter().map(Literal::atom))
            .zip(std::iter::once(&b.head).chain(b.body.iter().map(Literal::atom)))
        {
            assert_eq!(
                p.attribution.provenance.origins(a.id()),
                again.attribution.provenance.origins(b.id())
            );
            for (a, b) in a.arguments().iter().zip(b.arguments()) {
                assert_eq!(
                    p.attribution.provenance.origins(a.id()),
                    again.attribution.provenance.origins(b.id())
                );
            }
        }
    }
    assert_terms_have_origins(&f, &p);
}
