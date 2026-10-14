use crate::*;
use denotate_ir::*;
use denotate_test_dsl::{ast::*, lowering::*};
use std::collections::BTreeSet;

// Source-spanned AST fixtures, not a parser. Each mapping and expression is
// built explicitly; the real lowerer and library produce the checked corpus.
struct Fixture {
    sources: Sources,
    snapshot: SnapshotId,
    text: &'static str,
    ast: Program,
}
impl Fixture {
    fn new(text: &'static str, inputs: &[&str], slots: &[&str]) -> Self {
        let mut sources = Sources::new();
        let snapshot = sources
            .add("file:///replay.flow", 1, "test-dsl", text)
            .unwrap();
        let mut f = Self {
            sources,
            snapshot,
            text,
            ast: Program::default(),
        };
        for (line, kind, names) in [
            (text.lines().next().unwrap(), Kind::Input, inputs),
            (text.lines().nth(1).unwrap(), Kind::Slot, slots),
        ] {
            let span = f.span(line);
            f.ast.declarations.push(Declaration {
                kind,
                names: names.iter().map(|name| f.name(span, name)).collect(),
                span,
            });
        }
        f
    }
    fn span(&self, text: &str) -> SourceSpan {
        let at = self.text.find(text).unwrap();
        self.sources
            .span(self.snapshot, at..at + text.len())
            .unwrap()
    }
    fn name(&self, span: SourceSpan, name: &str) -> Name {
        let at = span.byte_range().start + self.sources.text(span).unwrap().find(name).unwrap();
        Name {
            text: name.into(),
            span: self
                .sources
                .span(self.snapshot, at..at + name.len())
                .unwrap(),
        }
    }
    fn available(&self, line: SourceSpan, slot: &str) -> Expr {
        let text = format!("available({slot})");
        let start = line.byte_range().start + self.sources.text(line).unwrap().find(&text).unwrap();
        let span = self
            .sources
            .span(self.snapshot, start..start + text.len())
            .unwrap();
        let name_span = self
            .sources
            .span(self.snapshot, start + 10..start + text.len() - 1)
            .unwrap();
        Expr {
            span,
            kind: ExprKind::Available(Name {
                text: slot.into(),
                span: name_span,
            }),
        }
    }
    fn not(&self, inner: Expr) -> Expr {
        let start = inner.span.byte_range().start - 4;
        let keyword = self.sources.span(self.snapshot, start..start + 3).unwrap();
        assert_eq!(self.sources.text(keyword).unwrap(), "not");
        Expr {
            span: self
                .sources
                .span(self.snapshot, start..inner.span.byte_range().end)
                .unwrap(),
            kind: ExprKind::Not {
                keyword,
                operand: Box::new(inner),
            },
        }
    }
    fn mapping(&mut self, line: &str, slot: &str, input: &str, guard: Option<(&str, bool)>) {
        let span = self.span(line);
        let condition = guard.map(|(slot, negative)| {
            let expr = self.available(span, slot);
            if negative { self.not(expr) } else { expr }
        });
        self.ast.mappings.push(Mapping {
            target: self.name(span, slot),
            input: self.name(span, input),
            condition,
            span,
        });
    }
    fn lower(&self) -> LoweredProgram {
        match lower(&self.ast, &self.sources).unwrap() {
            LoweringOutcome::Lowered(p) => p,
            LoweringOutcome::UserErrors(e) => panic!("{e:?}"),
        }
    }
}
fn prepare(p: &LoweredProgram) -> GroundProgram {
    // Explicit client choice: the declared identifiers are the exhaustive
    // domains for this test DSL. The generic checker does not infer this policy.
    let domains: Domains = p
        .corpus
        .sorts()
        .map(|s| {
            (
                s.id,
                p.corpus
                    .constants()
                    .filter(|c| c.sort == s.id)
                    .map(|c| c.id)
                    .collect(),
            )
        })
        .collect();
    let prepared = GroundProgram::prepare(&p.corpus, &domains, &Limits::default()).unwrap();
    super::sparse::assert_equivalent(&p.corpus, &domains, &prepared);
    super::symbolic::assert_symbolic_agrees(&prepared);
    prepared
}
fn atom(p: &LoweredProgram, name: &str, args: &[&str]) -> GroundAtom {
    let relation = p.corpus.relations().find(|r| r.name == name).unwrap();
    GroundAtom::new(
        relation.id,
        args.iter()
            .zip(&relation.parameters)
            .map(|(name, parameter)| {
                p.corpus
                    .constants()
                    .find(|c| c.name == *name && c.sort == parameter.sort)
                    .unwrap()
                    .id
            }),
    )
}

#[test]
fn lowered_complementary_guards_are_locally_stratified_for_all_input_observations() {
    let mut f = Fixture::new(
        "input input_a, input_b, input_bb;\nslot a, b;\na <- input_a;\nb <- input_b when available(a);\nb <- input_bb when not available(a);\n",
        &["input_a", "input_b", "input_bb"],
        &["a", "b"],
    );
    f.mapping("a <- input_a;", "a", "input_a", None);
    f.mapping(
        "b <- input_b when available(a);",
        "b",
        "input_b",
        Some(("a", false)),
    );
    f.mapping(
        "b <- input_bb when not available(a);",
        "b",
        "input_bb",
        Some(("a", true)),
    );
    let lowered = f.lower();
    let p = prepare(&lowered);
    assert!(p.is_admitted());
    assert_eq!(p.rules().count(), 9); // two library rules per possible mapping, plus mappings
    for bits in 0..8 {
        let inputs = ["input_a", "input_b", "input_bb"]
            .into_iter()
            .enumerate()
            .filter(|(i, _)| bits & (1 << i) != 0)
            .map(|(_, name)| atom(&lowered, "present", &[name]));
        let replay = p.evaluate(inputs, &Limits::default()).unwrap();
        let left = bits & 1 != 0 && bits & 2 != 0;
        let right = bits & 1 == 0 && bits & 4 != 0;
        assert!(replay.is_complete());
        assert_eq!(
            replay
                .fact(&atom(&lowered, "supplies", &["input_b", "b"]))
                .unwrap(),
            FactState::Settled(left)
        );
        assert_eq!(
            replay
                .fact(&atom(&lowered, "supplies", &["input_bb", "b"]))
                .unwrap(),
            FactState::Settled(right)
        );
        assert_eq!(
            replay.fact(&atom(&lowered, "available", &["b"])).unwrap(),
            FactState::Settled(left || right)
        );
        assert!(!(left && right));
    }
}

#[test]
fn unresolved_c_blocks_d_but_not_b_and_preserves_the_dsl_negative_premise() {
    let mut f = Fixture::new(
        "input input_a, input_b, input_bb, input_c, input_d;\nslot a, b, c, d;\na <- input_a;\nb <- input_b when available(a);\nb <- input_bb when available(a);\nc <- input_c when not available(c);\nd <- input_d when not available(c);\n",
        &["input_a", "input_b", "input_bb", "input_c", "input_d"],
        &["a", "b", "c", "d"],
    );
    f.mapping("a <- input_a;", "a", "input_a", None);
    f.mapping(
        "b <- input_b when available(a);",
        "b",
        "input_b",
        Some(("a", false)),
    );
    f.mapping(
        "b <- input_bb when available(a);",
        "b",
        "input_bb",
        Some(("a", false)),
    );
    f.mapping(
        "c <- input_c when not available(c);",
        "c",
        "input_c",
        Some(("c", true)),
    );
    f.mapping(
        "d <- input_d when not available(c);",
        "d",
        "input_d",
        Some(("c", true)),
    );
    let lowered = f.lower();
    let p = prepare(&lowered);
    assert!(!p.is_admitted());
    let c = p
        .component_for(&atom(&lowered, "available", &["c"]))
        .unwrap();
    let cycle = c.cycle.as_ref().unwrap();
    assert_eq!(cycle.edges.len(), 3);
    let heads: BTreeSet<_> = cycle
        .edges
        .iter()
        .map(|e| {
            lowered
                .corpus
                .relation(e.consumer.relation)
                .unwrap()
                .name
                .as_str()
        })
        .collect();
    assert_eq!(
        heads,
        BTreeSet::from(["mapped_to", "supplies", "available"])
    );
    let negative = cycle
        .edges
        .iter()
        .find(|e| e.polarity == Polarity::Negative)
        .unwrap();
    let origins = lowered.provenance.origins(negative.premise);
    assert_eq!(
        f.sources
            .text(origins.iter().find(|o| o.role == "not").unwrap().span)
            .unwrap(),
        "not"
    );
    assert_eq!(
        f.sources
            .text(origins.iter().find(|o| o.role == "condition").unwrap().span)
            .unwrap(),
        "available(c)"
    );
    let source_rule = lowered
        .corpus
        .rule(p.rule(negative.rule).unwrap().source)
        .unwrap();
    assert_eq!(source_rule.body[0].atom().id(), negative.premise);
    for include_c in [false, true] {
        let mut inputs = vec!["input_a", "input_b", "input_bb", "input_d"];
        if include_c {
            inputs.push("input_c");
        }
        let replay = p
            .evaluate(
                inputs.iter().map(|name| atom(&lowered, "present", &[name])),
                &Limits::default(),
            )
            .unwrap();
        assert!(!replay.is_complete()); // no observation-specific cycle pruning in 3a
        assert_eq!(
            replay
                .fact(&atom(&lowered, "present", &["input_c"]))
                .unwrap(),
            FactState::Settled(include_c)
        );
        for input in ["input_b", "input_bb"] {
            let fact = atom(&lowered, "supplies", &[input, "b"]);
            assert_eq!(replay.fact(&fact).unwrap(), FactState::Settled(true));
            assert!(replay.derivation(&fact).is_some());
        }
        for slot in ["c", "d"] {
            assert_eq!(
                replay.fact(&atom(&lowered, "available", &[slot])).unwrap(),
                FactState::Blocked(BTreeSet::from([c.id]))
            );
        }
        assert_eq!(
            replay
                .fact(&atom(&lowered, "mapped_to", &["input_d", "d"]))
                .unwrap(),
            FactState::Blocked(BTreeSet::from([c.id]))
        );
        // The two contributions are facts, not yet an at_most_one result: 3b.
    }
}

#[test]
fn generated_zero_argument_helper_replays_and_retains_its_negative_use_origin() {
    let mut f = Fixture::new(
        "input input_a, input_b, input_c;\nslot a, b, c;\na <- input_a;\nc <- input_c;\nb <- input_b when not (available(a) and available(c));\n",
        &["input_a", "input_b", "input_c"],
        &["a", "b", "c"],
    );
    f.mapping("a <- input_a;", "a", "input_a", None);
    f.mapping("c <- input_c;", "c", "input_c", None);
    let span = f.span("b <- input_b when not (available(a) and available(c));");
    let conjunction_span = f.span("available(a) and available(c)");
    let conjunction = Expr {
        span: conjunction_span,
        kind: ExprKind::And(
            Box::new(f.available(span, "a")),
            Box::new(f.available(span, "c")),
        ),
    };
    let group = Expr {
        span: f.span("(available(a) and available(c))"),
        kind: ExprKind::Group(Box::new(conjunction)),
    };
    f.ast.mappings.push(Mapping {
        target: f.name(span, "b"),
        input: f.name(span, "input_b"),
        condition: Some(f.not(group)),
        span,
    });
    let lowered = f.lower();
    let p = prepare(&lowered);
    assert!(p.is_admitted());
    let helper = atom(&lowered, "$condition_1", &[]);
    for bits in 0..8 {
        let inputs = ["input_a", "input_b", "input_c"]
            .into_iter()
            .enumerate()
            .filter(|(i, _)| bits & (1 << i) != 0)
            .map(|(_, name)| atom(&lowered, "present", &[name]));
        let replay = p.evaluate(inputs, &Limits::default()).unwrap();
        let both = bits & 1 != 0 && bits & 4 != 0;
        assert_eq!(replay.fact(&helper).unwrap(), FactState::Settled(both));
        assert_eq!(
            replay.fact(&atom(&lowered, "available", &["b"])).unwrap(),
            FactState::Settled(bits & 2 != 0 && !both)
        );
        if !both {
            let mapping = atom(&lowered, "mapped_to", &["input_b", "b"]);
            let Evidence::Derived { premises, .. } = &replay.derivation(&mapping).unwrap().evidence
            else {
                panic!()
            };
            let PremiseEvidence::Absent {
                fact,
                occurrence,
                provider,
            } = &premises[0]
            else {
                panic!()
            };
            assert_eq!(*fact, helper);
            assert_eq!(
                *provider,
                CompletedProvider::Component(p.component_for(&helper).unwrap().id)
            );
            let origin = lowered
                .provenance
                .origins(*occurrence)
                .iter()
                .find(|o| o.role == "not")
                .unwrap();
            assert_eq!(f.sources.text(origin.span).unwrap(), "not");
        }
    }
}

#[test]
fn impossible_guards_prune_positive_mappings_and_explain_negative_mappings() {
    for self_guarded in [false, true] {
        let mut f = Fixture::new(
            "input input_a, input_b, input_c;\nslot a, b, c;\na <- input_a when available(c);\nb <- input_b when not available(c);\nc <- input_c when available(c);\n",
            &["input_a", "input_b", "input_c"],
            &["a", "b", "c"],
        );
        f.mapping(
            "a <- input_a when available(c);",
            "a",
            "input_a",
            Some(("c", false)),
        );
        f.mapping(
            "b <- input_b when not available(c);",
            "b",
            "input_b",
            Some(("c", true)),
        );
        if self_guarded {
            f.mapping(
                "c <- input_c when available(c);",
                "c",
                "input_c",
                Some(("c", false)),
            );
        }
        let lowered = f.lower();
        let p = prepare(&lowered); // every observation and legal atom against full grounding
        assert_eq!(p.rules().count(), 3);
        assert!(
            !p.is_possible(&atom(&lowered, "mapped_to", &["input_a", "a"]))
                .unwrap()
        );
        assert!(!p.is_possible(&atom(&lowered, "available", &["c"])).unwrap());
        let replay = p
            .evaluate(
                [atom(&lowered, "present", &["input_b"])],
                &Limits::default(),
            )
            .unwrap();
        assert_eq!(
            replay.fact(&atom(&lowered, "available", &["a"])).unwrap(),
            FactState::Settled(false)
        );
        assert_eq!(
            replay.fact(&atom(&lowered, "available", &["b"])).unwrap(),
            FactState::Settled(true)
        );
        let mapping = atom(&lowered, "mapped_to", &["input_b", "b"]);
        let Evidence::Derived { premises, .. } = &replay.derivation(&mapping).unwrap().evidence
        else {
            panic!()
        };
        let PremiseEvidence::Absent {
            fact,
            occurrence,
            provider,
        } = &premises[0]
        else {
            panic!()
        };
        assert_eq!(*fact, atom(&lowered, "available", &["c"]));
        assert_eq!(*provider, CompletedProvider::NoPossibleProducer);
        let origin = lowered
            .provenance
            .origins(*occurrence)
            .iter()
            .find(|o| o.role == "not")
            .unwrap();
        assert_eq!(f.sources.text(origin.span).unwrap(), "not");
    }
}
