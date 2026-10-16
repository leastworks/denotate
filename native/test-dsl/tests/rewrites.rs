mod support;
use denotate_check::*;
use denotate_ir::*;
use denotate_test_dsl::{
    ast::*,
    presentation::{self, DiagnosticKind},
    warnings::*,
};
use support::*;

fn group(f: &Fixture, inner: Expr) -> Expr {
    let span = f
        .sources
        .span(
            f.snapshot,
            inner.span.byte_range().start - 1..inner.span.byte_range().end + 1,
        )
        .unwrap();
    assert_eq!(
        f.sources.text(span).unwrap(),
        format!("({})", f.sources.text(inner.span).unwrap())
    );
    Expr {
        span,
        kind: ExprKind::Group(Box::new(inner)),
    }
}

#[test]
fn direct_dsl_condition_warns_at_exact_negation_and_offers_whole_condition_edit() {
    let text = "input input_a, input_x;\nslot a;\na <- input_a when present(input_x) and not present(input_x) and not available(a);\n";
    let mut f = Fixture::new(text, &["input_a", "input_x"], &["a"]);
    let span = f.span(text.lines().nth(2).unwrap());
    let positive = f.atom(span, "present", "input_x");
    let negative = f.not(f.atom(f.within(span, "not present(input_x)"), "present", "input_x"));
    let guard = f.binary(
        f.binary(positive, negative, true),
        f.not(f.atom(span, "available", "a")),
        true,
    );
    f.mapping(span, "a", "input_a", Some(guard));
    let p = f.lower();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert!(ground.is_admitted());
    let warnings = present_rewrites(&p, &ground, &f.sources, "test-dsl").unwrap();
    assert_eq!(warnings.len(), 1);
    let mut edited = f.text.clone();
    let mut edits: Vec<_> = warnings
        .iter()
        .map(|w| {
            assert_eq!(w.owner, Contribution::Program);
            assert_eq!(f.sources.text(w.primary.unwrap()).unwrap(), "not");
            let edit = w.edit.as_ref().unwrap();
            assert!(
                f.sources
                    .text(edit.span)
                    .unwrap()
                    .starts_with(" and not available(")
            );
            edit
        })
        .collect();
    edits.sort_by_key(|e| std::cmp::Reverse(e.span.byte_range().start));
    for edit in edits {
        edited.replace_range(edit.span.byte_range(), &edit.replacement);
    }
    assert_eq!(
        edited,
        "input input_a, input_x;\nslot a;\na <- input_a when present(input_x) and not present(input_x);\n"
    );
    // Independently authored post-edit AST, not mutation of the lowered rules.
    let mut after = Fixture::new(&edited, &["input_a", "input_x"], &["a"]);
    let span = after.span(edited.lines().nth(2).unwrap());
    let t = after.atom(span, "present", "input_x");
    let not_t = after.not(after.atom(
        after.within(span, "not present(input_x)"),
        "present",
        "input_x",
    ));
    after.mapping(span, "a", "input_a", Some(after.binary(t, not_t, true)));
    let after = after.lower();
    let after_ground = GroundProgram::prepare(&after.corpus, &domains(&after), &limits).unwrap();
    for bits in 0..4 {
        let names = ["input_a", "input_x"];
        let before = ground
            .evaluate(
                names
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits & (1 << i) != 0)
                    .map(|(_, n)| atom(&p, "present", &[n])),
                &limits,
            )
            .unwrap();
        let after_replay = after_ground
            .evaluate(
                names
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits & (1 << i) != 0)
                    .map(|(_, n)| atom(&after, "present", &[n])),
                &limits,
            )
            .unwrap();
        for (slot, expected) in [("a", false)] {
            assert_eq!(
                before.fact(&atom(&p, "available", &[slot])).unwrap(),
                FactState::Settled(expected)
            );
            assert_eq!(
                after_replay
                    .fact(&atom(&after, "available", &[slot]))
                    .unwrap(),
                FactState::Settled(expected)
            );
        }
    }
    assert!(
        presentation::present(
            &p,
            &ground
                .symbolic(&limits)
                .unwrap()
                .verify_at_most_one(&limits)
                .unwrap(),
            &f.sources,
            "test-dsl"
        )
        .unwrap()
        .is_empty()
    );
}

#[test]
fn transformed_negations_and_generated_helpers_warn_without_edits() {
    for shape in ["demorgan", "double", "helper"] {
        let rhs_text = match shape {
            "demorgan" => "not (available(a) or available(c))",
            "double" => "not not not available(a)",
            _ => "not (available(a) and present(input_x))",
        };
        let text = format!(
            "input input_a, input_x;\nslot a, c;\na <- input_a when present(input_x) and not present(input_x) and {rhs_text};\n"
        );
        let mut f = Fixture::new(&text, &["input_a", "input_x"], &["a", "c"]);
        let span = f.span(text.lines().nth(2).unwrap());
        let t = f.binary(
            f.atom(span, "present", "input_x"),
            f.not(f.atom(f.within(span, "not present(input_x)"), "present", "input_x")),
            true,
        );
        let a = f.atom(span, "available", "a");
        let rhs = match shape {
            "demorgan" => f.not(group(
                &f,
                f.binary(a, f.atom(span, "available", "c"), false),
            )),
            "double" => f.not(f.not(f.not(a))),
            _ => {
                let later = f.within(span, "(available(a) and present(input_x))");
                f.not(group(
                    &f,
                    f.binary(a, f.atom(later, "present", "input_x"), true),
                ))
            }
        };
        f.mapping(span, "a", "input_a", Some(f.binary(t, rhs, true)));
        let p = f.lower();
        let limits = Limits::default();
        let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
            .unwrap()
            .admit(&limits)
            .unwrap();
        assert!(ground.is_admitted(), "{shape}");
        let warnings = present_rewrites(&p, &ground, &f.sources, "test-dsl").unwrap();
        let a = warnings.iter().find(|w| p.corpus.rule(w.rule).unwrap().head.arguments().iter().any(|t| matches!(t.value(),Term::Constant(id) if p.corpus.constant(*id).unwrap().name=="a"))).unwrap();
        assert_eq!(a.owner, Contribution::Program);
        assert!(
            a.edit.is_none(),
            "transformed {shape} must not offer an edit"
        );
        assert!(a.related.iter().any(|o| o.role == "negated expression"));
        for r in p.corpus.rules().filter(|r| {
            p.corpus
                .relation(r.head.relation())
                .unwrap()
                .name
                .starts_with('$')
        }) {
            assert_eq!(p.rewrite_metadata.owners[&r.id], Contribution::Program);
        }
    }
}

#[test]
fn library_warnings_do_not_borrow_user_locations_or_change_owner_with_view() {
    let f = Fixture::exclusive();
    let mut p = f.lower();
    let mut sources = f.sources;
    let mut rules = Vec::new();
    let t = p
        .corpus
        .declare_relation("switch", RelationRole::Input, [])
        .unwrap();
    let a = p
        .corpus
        .declare_relation("left", RelationRole::Derived, [])
        .unwrap();
    let b = p
        .corpus
        .declare_relation("right", RelationRole::Derived, [])
        .unwrap();
    for (head, other, negative) in [(a, b, false), (b, a, true)] {
        let head = p.corpus.atom(head, []).unwrap();
        let guard = p.corpus.atom(t, []).unwrap();
        let other = p.corpus.atom(other, []).unwrap();
        let occurrence = other.id();
        let r = p
            .corpus
            .add_rule(
                head,
                [
                    if negative {
                        Literal::Negative(guard)
                    } else {
                        Literal::Positive(guard)
                    },
                    Literal::Negative(other),
                ],
            )
            .unwrap();
        p.rewrite_metadata.owners.insert(r, Contribution::Library);
        rules.push((r, occurrence));
    }
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let warnings = present_rewrites(&p, &ground, &sources, "test-dsl").unwrap();
    assert_eq!(
        warnings
            .iter()
            .filter(|w| w.owner == Contribution::Library)
            .count(),
        2
    );
    assert!(
        warnings
            .iter()
            .filter(|w| w.owner == Contribution::Library)
            .all(|w| w.primary.is_none() && w.edit.is_none())
    );
    let snapshot = sources
        .add("file:///library.den", 1, "denotate", "!right()")
        .unwrap();
    let span = sources.span(snapshot, 0..1).unwrap();
    p.provenance
        .attach(&p.corpus, &sources, rules[0].1, [Origin::new(span, "not")])
        .unwrap();
    let warnings = present_rewrites(&p, &ground, &sources, "denotate").unwrap();
    let warning = warnings.iter().find(|w| w.rule == rules[0].0).unwrap();
    assert_eq!(warning.owner, Contribution::Library);
    assert_eq!(warning.primary, Some(span));
    assert!(warning.edit.is_none());
}

#[test]
fn exhausted_admission_reports_inconclusive_but_keeps_independent_overlap() {
    let f = Fixture::mixed(false, false);
    let p = f.lower();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&Limits {
            max_work: 0,
            ..limits.clone()
        })
        .unwrap();
    let report = ground
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    assert!(!report.all_obligations_proved());
    let ds = presentation::present(&p, &report, &f.sources, "test-dsl").unwrap();
    assert_eq!(
        ds.iter()
            .filter(|d| d.kind == DiagnosticKind::OverlappingMappings)
            .count(),
        2
    );
    assert!(
        ds.iter()
            .filter(|d| d.kind == DiagnosticKind::Inconclusive)
            .count()
            >= 2
    );
    // Completion has a separate allowance: exhausted admission does not erase
    // the independently established no-meaning finding on the cycle itself.
    let failure = ds
        .iter()
        .find(|d| d.kind == DiagnosticKind::NoMeaning)
        .unwrap();
    assert!(
        failure
            .notes
            .iter()
            .any(|n| n.contains("Admission remains inconclusive"))
    );
    assert!(ds.iter().all(|d| d.kind != DiagnosticKind::UnsupportedGroup
        && d.kind != DiagnosticKind::UnsupportedCycle));
    assert!(
        present_rewrites(&p, &ground, &f.sources, "test-dsl")
            .unwrap()
            .is_empty()
    );
}

#[test]
fn redundant_mapping_warns_on_the_dropped_statement_not_a_fake_derivation() {
    let text = "input input_a;\nslot a;\na <- input_a;\na <- input_a when not available(a);\n";
    let mut f = Fixture::new(text, &["input_a"], &["a"]);
    f.mapping(f.span("a <- input_a;"), "a", "input_a", None);
    let span = f.span("a <- input_a when not available(a);");
    f.mapping(
        span,
        "a",
        "input_a",
        Some(f.not(f.atom(span, "available", "a"))),
    );
    let p = f.lower();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert!(ground.is_admitted());
    let warnings = present_rewrites(&p, &ground, &f.sources, "test-dsl").unwrap();
    assert_eq!(warnings.len(), 1);
    let w = &warnings[0];
    assert_eq!(w.owner, Contribution::Program);
    assert_eq!(w.literal, None);
    assert_eq!(w.primary, Some(span));
    assert!(w.edit.is_none());
    let replay = ground
        .evaluate([atom(&p, "present", &["input_a"])], &limits)
        .unwrap();
    let Evidence::Derived { rule, .. } = replay
        .derivation(&atom(&p, "mapped_to", &["input_a", "a"]))
        .unwrap()
        .evidence
    else {
        panic!()
    };
    assert_ne!(ground.rule(rule).unwrap().source, w.rule);
}

#[test]
fn a_partial_ground_discharge_never_offers_an_authored_edit() {
    let f = Fixture::exclusive();
    let mut p = f.lower();
    let limits = Limits::default();
    let s = p.library.slot;
    let values: Vec<_> = p
        .corpus
        .constants()
        .filter(|c| c.sort == s)
        .map(|c| c.id)
        .collect();
    let t = p
        .corpus
        .declare_relation("t", RelationRole::Input, [])
        .unwrap();
    let gate = p
        .corpus
        .declare_relation("gate", RelationRole::Input, [Parameter::new("slot", s)])
        .unwrap();
    let left = p
        .corpus
        .declare_relation("left", RelationRole::Derived, [Parameter::new("slot", s)])
        .unwrap();
    let right = p
        .corpus
        .declare_relation("right", RelationRole::Derived, [Parameter::new("slot", s)])
        .unwrap();
    let x = Term::variable("X", s);
    let head = p.corpus.atom(left, [x.clone()]).unwrap();
    let bind = p.corpus.atom(gate, [x.clone()]).unwrap();
    let guard = p.corpus.atom(t, []).unwrap();
    let negative = p.corpus.atom(right, [x]).unwrap();
    let occurrence = negative.id();
    let rule = p
        .corpus
        .add_rule(
            head,
            [
                Literal::Positive(bind),
                Literal::Positive(guard),
                Literal::Negative(negative),
            ],
        )
        .unwrap();
    p.rewrite_metadata
        .owners
        .insert(rule, Contribution::Program);
    // A frontend-supplied edit is still insufficient without all instances.
    let edit = p.rewrite_metadata.removals.values().next().unwrap().clone();
    p.rewrite_metadata.removals.insert(occurrence, edit);
    p.provenance
        .attach(
            &p.corpus,
            &f.sources,
            occurrence,
            [Origin::new(
                f.span("not available(b)"),
                "negated expression",
            )],
        )
        .unwrap();
    for (i, value) in values.iter().enumerate() {
        let head = p.corpus.atom(right, [(*value).into()]).unwrap();
        let guard = p.corpus.atom(t, []).unwrap();
        let negative = p.corpus.atom(left, [(*value).into()]).unwrap();
        let id = p
            .corpus
            .add_rule(
                head,
                [
                    if i == 0 {
                        Literal::Negative(guard)
                    } else {
                        Literal::Positive(guard)
                    },
                    Literal::Negative(negative),
                ],
            )
            .unwrap();
        p.rewrite_metadata.owners.insert(id, Contribution::Library);
    }
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert_eq!(
        ground.original_rules().filter(|r| r.source == rule).count(),
        2
    );
    let warnings = present_rewrites(&p, &ground, &f.sources, "test-dsl").unwrap();
    let w = warnings.iter().find(|w| w.rule == rule).unwrap();
    assert_eq!(w.proofs.len(), 1);
    assert_eq!(w.literal, Some(occurrence));
    assert!(w.edit.is_none());
}

#[test]
fn exclusivity_through_library_forwarding_discharges_and_warns_at_both_nots() {
    let f = Fixture::exclusive();
    let p = f.lower();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert!(ground.is_admitted());
    assert!(ground.admission_limit().is_none());
    assert_eq!(ground.rewrite_proofs().count(), 2);
    let warnings = present_rewrites(&p, &ground, &f.sources, "test-dsl").unwrap();
    assert_eq!(warnings.len(), 2);
    let mut edited = f.text.clone();
    let mut edits = Vec::new();
    for (warning, negation) in warnings
        .iter()
        .zip(["not available(b)", "not available(a)"])
    {
        assert_eq!(warning.owner, Contribution::Program);
        let expected = f.within(f.span(negation), "not");
        assert_eq!(warning.primary, Some(expected));
        edits.push(warning.edit.as_ref().unwrap());
    }
    edits.sort_by_key(|e| std::cmp::Reverse(e.span.byte_range().start));
    for edit in edits {
        edited.replace_range(edit.span.byte_range(), &edit.replacement);
    }
    assert_eq!(
        edited,
        "input input_a, input_b, input_x;\nslot a, b;\na <- input_a when present(input_x);\nb <- input_b when not present(input_x);\n"
    );
    for bits in 0..8 {
        let world = ["input_a", "input_b", "input_x"]
            .iter()
            .enumerate()
            .filter(|(i, _)| bits & (1 << i) != 0)
            .map(|(_, name)| atom(&p, "present", &[name]))
            .collect::<Vec<_>>();
        let replay = ground.evaluate(world, &limits).unwrap();
        for (input, slot, enabled) in [
            ("input_a", "a", bits & 4 != 0),
            ("input_b", "b", bits & 4 == 0),
        ] {
            let mapping = atom(&p, "mapped_to", &[input, slot]);
            assert_eq!(replay.fact(&mapping).unwrap(), FactState::Settled(enabled));
            if enabled {
                let Evidence::Derived { premises, .. } =
                    &replay.derivation(&mapping).unwrap().evidence
                else {
                    panic!()
                };
                assert!(
                    premises
                        .iter()
                        .any(|p| matches!(p, PremiseEvidence::Discharged { .. }))
                );
            }
        }
    }
    let report = ground
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    assert!(report.all_obligations_proved());
    assert!(report.unresolved.is_empty());
}
