#![allow(dead_code)] // Shared by integration tests and the small CLI example.
use denotate_check::*;
use denotate_ir::*;
use denotate_test_dsl::{ast::*, lowering::*};

/// Builds explicit ASTs against fixture text. This is not a parser.
pub struct Fixture {
    pub sources: Sources,
    pub snapshot: SnapshotId,
    pub text: String,
    pub ast: Program,
}
impl Fixture {
    pub fn new(text: &str, inputs: &[&str], slots: &[&str]) -> Self {
        let mut sources = Sources::new();
        let snapshot = sources
            .add("file:///example.inputmapping", 1, "test-dsl", text)
            .unwrap();
        let mut f = Self {
            sources,
            snapshot,
            text: text.into(),
            ast: Program::default(),
        };
        for (line, kind, names) in [(0, Kind::Input, inputs), (1, Kind::Slot, slots)] {
            let span = f.span(text.lines().nth(line).unwrap());
            f.ast.declarations.push(Declaration {
                kind,
                span,
                names: names.iter().map(|name| f.name(span, name)).collect(),
            });
        }
        f
    }
    pub fn span(&self, text: &str) -> SourceSpan {
        self.nth_span(text, 0)
    }
    pub fn nth_span(&self, text: &str, nth: usize) -> SourceSpan {
        let at = self.text.match_indices(text).nth(nth).unwrap().0;
        self.sources
            .span(self.snapshot, at..at + text.len())
            .unwrap()
    }
    pub fn within(&self, parent: SourceSpan, text: &str) -> SourceSpan {
        let at = parent.byte_range().start + self.sources.text(parent).unwrap().find(text).unwrap();
        self.sources
            .span(self.snapshot, at..at + text.len())
            .unwrap()
    }
    pub fn name(&self, parent: SourceSpan, name: &str) -> Name {
        Name {
            text: name.into(),
            span: self.within(parent, name),
        }
    }
    pub fn atom(&self, parent: SourceSpan, predicate: &str, name: &str) -> Expr {
        let span = self.within(parent, &format!("{predicate}({name})"));
        let argument = self
            .sources
            .span(
                self.snapshot,
                span.byte_range().start + predicate.len() + 1..span.byte_range().end - 1,
            )
            .unwrap();
        let name = Name {
            text: name.into(),
            span: argument,
        };
        Expr {
            span,
            kind: match predicate {
                "available" => ExprKind::Available(name),
                "present" => ExprKind::Present(name),
                _ => panic!("fixture predicate"),
            },
        }
    }
    pub fn not(&self, operand: Expr) -> Expr {
        let start = operand.span.byte_range().start - 4;
        let keyword = self.sources.span(self.snapshot, start..start + 3).unwrap();
        assert_eq!(self.sources.text(keyword).unwrap(), "not");
        Expr {
            span: self
                .sources
                .span(self.snapshot, start..operand.span.byte_range().end)
                .unwrap(),
            kind: ExprKind::Not {
                keyword,
                operand: Box::new(operand),
            },
        }
    }
    pub fn binary(&self, a: Expr, b: Expr, and: bool) -> Expr {
        let span = self
            .sources
            .span(
                self.snapshot,
                a.span.byte_range().start..b.span.byte_range().end,
            )
            .unwrap();
        Expr {
            span,
            kind: if and {
                ExprKind::And(Box::new(a), Box::new(b))
            } else {
                ExprKind::Or(Box::new(a), Box::new(b))
            },
        }
    }
    pub fn mapping(&mut self, span: SourceSpan, slot: &str, input: &str, condition: Option<Expr>) {
        self.ast.mappings.push(Mapping {
            target: self.name(span, slot),
            input: self.name(span, input),
            condition,
            span,
        });
    }
    pub fn lower(&self) -> LoweredProgram {
        match lower(&self.ast, &self.sources).unwrap() {
            LoweringOutcome::Lowered(p) => p,
            LoweringOutcome::UserErrors(e) => panic!("{e:?}"),
        }
    }
    pub fn overlap() -> Self {
        let mut f = Self::new(
            include_str!("../../fixtures/overlapping-mappings.txt"),
            &["input_a", "input_b", "input_bb"],
            &["a", "b"],
        );
        let span = f.span("a <- input_a;");
        f.mapping(span, "a", "input_a", None);
        for (line, input) in [
            ("b <- input_b  when available(a);", "input_b"),
            ("b <- input_bb when available(a);", "input_bb"),
        ] {
            let span = f.span(line);
            f.mapping(span, "b", input, Some(f.atom(span, "available", "a")));
        }
        f
    }
    pub fn ambiguous() -> Self {
        let text = "input input_a, input_b;\nslot a, b;\na <- input_a when not available(b);\nb <- input_b when not available(a);\n";
        let mut f = Self::new(text, &["input_a", "input_b"], &["a", "b"]);
        for (line, target, input, other) in [(2, "a", "input_a", "b"), (3, "b", "input_b", "a")] {
            let span = f.span(text.lines().nth(line).unwrap());
            let guard = f.not(f.atom(span, "available", other));
            f.mapping(span, target, input, Some(guard));
        }
        f
    }

    pub fn exclusive() -> Self {
        let mut f = Self::new(
            "input input_a, input_b, input_x;\nslot a, b;\na <- input_a when present(input_x) and not available(b);\nb <- input_b when not present(input_x) and not available(a);\n",
            &["input_a", "input_b", "input_x"],
            &["a", "b"],
        );
        for (slot, input, other, neg_input) in
            [("a", "input_a", "b", false), ("b", "input_b", "a", true)]
        {
            let line = f
                .text
                .lines()
                .find(|s| s.starts_with(&format!("{slot} <-")))
                .unwrap()
                .to_owned();
            let span = f.span(&line);
            let t = f.atom(span, "present", "input_x");
            let t = if neg_input { f.not(t) } else { t };
            let condition = f.binary(t, f.not(f.atom(span, "available", other)), true);
            f.mapping(span, slot, input, Some(condition));
        }
        f
    }
    pub fn redundant() -> Self {
        let mut f = Self::new(
            "input input_a;\nslot a;\na <- input_a;\na <- input_a when not available(a);\n",
            &["input_a"],
            &["a"],
        );
        f.mapping(f.span("a <- input_a;"), "a", "input_a", None);
        let span = f.span("a <- input_a when not available(a);");
        f.mapping(
            span,
            "a",
            "input_a",
            Some(f.not(f.atom(span, "available", "a"))),
        );
        f
    }
    pub fn mixed(require_c: bool, fix_c: bool) -> Self {
        let guard = if require_c {
            "available(a) and present(input_c)"
        } else {
            "available(a)"
        };
        let c = if fix_c {
            "c <- input_c;"
        } else {
            "c <- input_c when not available(c);"
        };
        let text = format!(
            "input input_a, input_b, input_bb, input_c, input_d, input_dd;\nslot a, b, c, d;\na <- input_a;\nb <- input_b when available(a);\nb <- input_bb when {guard};\n{c}\nd <- input_d when not available(c);\nd <- input_dd;\n"
        );
        let mut f = Self::new(
            &text,
            &[
                "input_a", "input_b", "input_bb", "input_c", "input_d", "input_dd",
            ],
            &["a", "b", "c", "d"],
        );
        f.mapping(f.span("a <- input_a;"), "a", "input_a", None);
        let span = f.span("b <- input_b when available(a);");
        f.mapping(span, "b", "input_b", Some(f.atom(span, "available", "a")));
        let span = f.span(&format!("b <- input_bb when {guard};"));
        let a = f.atom(span, "available", "a");
        let expr = if require_c {
            f.binary(a, f.atom(span, "present", "input_c"), true)
        } else {
            a
        };
        f.mapping(span, "b", "input_bb", Some(expr));
        let span = f.span(c);
        let expr = (!fix_c).then(|| f.not(f.atom(span, "available", "c")));
        f.mapping(span, "c", "input_c", expr);
        let span = f.span("d <- input_d when not available(c);");
        f.mapping(
            span,
            "d",
            "input_d",
            Some(f.not(f.atom(span, "available", "c"))),
        );
        f.mapping(f.span("d <- input_dd;"), "d", "input_dd", None);
        f
    }
}
pub fn domains(p: &LoweredProgram) -> Domains {
    p.corpus
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
        .collect()
}
pub fn atom(p: &LoweredProgram, relation: &str, values: &[&str]) -> GroundAtom {
    let r = p.corpus.relations().find(|r| r.name == relation).unwrap();
    GroundAtom::new(
        r.id,
        values.iter().zip(&r.parameters).map(|(name, param)| {
            p.corpus
                .constants()
                .find(|c| c.name == *name && c.sort == param.sort)
                .unwrap()
                .id
        }),
    )
}
