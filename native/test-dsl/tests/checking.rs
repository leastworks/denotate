use denotate_test_dsl::attribution::SourceView;
mod support;
use denotate_check::*;
use denotate_ir::*;
use denotate_test_dsl::{
    ast::*,
    presentation::{self, DiagnosticKind, DiagnosticSeverity, PresentationError},
};
use std::collections::BTreeSet;
use support::*;

fn counterexample(group: &VerifiedGroup) -> &Counterexample {
    match &group.outcome {
        VerifiedOutcome::Counterexample(e) => e,
        other => panic!("{other:?}"),
    }
}

#[test]
fn moving_the_second_mapping_to_another_slot_clears_the_conflict() {
    let mut f = Fixture::new(
        "input input_a, input_b, input_bb;\nslot a, b, c;\na <- input_a;\nb <- input_b when available(a);\nc <- input_bb when available(a);\n",
        &["input_a", "input_b", "input_bb"],
        &["a", "b", "c"],
    );
    f.mapping(f.span("a <- input_a;"), "a", "input_a", None);
    for (line, slot, input) in [
        ("b <- input_b when available(a);", "b", "input_b"),
        ("c <- input_bb when available(a);", "c", "input_bb"),
    ] {
        let span = f.span(line);
        f.mapping(span, slot, input, Some(f.atom(span, "available", "a")));
    }
    let p = f.lower();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
    let meaning = ground.symbolic(&limits).unwrap();
    let report = meaning.verify_at_most_one(&limits).unwrap();
    assert!(report.all_obligations_proved());
    assert!(
        presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str())
            .unwrap()
            .is_empty()
    );
}

#[test]
fn fixture_overlap_has_replayed_ground_evidence_and_exact_term_locations() {
    let f = Fixture::overlap();
    let p = f.lower();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
    let symbolic = ground.symbolic(&limits).unwrap();
    let report = symbolic.verify_at_most_one(&limits).unwrap();
    assert!(!report.all_obligations_proved());
    assert!(report.whole_program_admitted());
    let example = counterexample(&report.groups[0]);
    assert_eq!(example.replay_scope, ReplayScope::WholeProgram);
    assert_eq!(
        example.tuples,
        BTreeSet::from([
            atom(&p, "supplies", &["input_b", "b"]),
            atom(&p, "supplies", &["input_bb", "b"])
        ])
    );
    let replay = ground
        .evaluate(example.observation.present.iter().cloned(), &limits)
        .unwrap();
    for tuple in &example.tuples {
        assert_eq!(replay.fact(tuple).unwrap(), FactState::Settled(true));
    }
    assert_eq!(
        example.observation.present.len() + example.observation.absent.len(),
        3
    );
    let messages =
        presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str()).unwrap();
    assert_eq!(messages.len(), 2);
    let expected: BTreeSet<_> = f.ast.mappings[1..].iter().map(|m| m.target.span).collect();
    assert_eq!(
        messages.iter().map(|d| d.primary).collect::<BTreeSet<_>>(),
        expected
    );
    for diagnostic in &messages {
        assert_eq!(diagnostic.kind, DiagnosticKind::OverlappingMappings);
        assert_eq!(
            diagnostic.message,
            "Slot b has overlapping InputMappings from input_b, input_bb. Mapping conditions: `available(a)`."
        );
        for mapping in &f.ast.mappings[1..] {
            assert!(
                diagnostic
                    .related
                    .iter()
                    .any(|o| o.label == "conflicting Input" && o.span == mapping.input.span)
            );
            assert!(
                diagnostic
                    .related
                    .iter()
                    .any(|o| o.label == "mapping condition"
                        && o.span == mapping.condition.as_ref().unwrap().span)
            );
        }
    }
    // Origins on each ground argument remain the original term occurrence IDs.
    for input in ["input_b", "input_bb"] {
        let fact = atom(&p, "mapped_to", &[input, "b"]);
        let GroundEvidence::Derived { rule, .. } = &example.evidence[&fact].evidence else {
            panic!()
        };
        assert_eq!(
            f.sources
                .text(p.attribution.provenance.origins(rule.head.arguments[0])[0].span)
                .unwrap(),
            input
        );
        assert_eq!(
            f.sources
                .text(p.attribution.provenance.origins(rule.head.arguments[1])[0].span)
                .unwrap(),
            "b"
        );
        assert_eq!(ground.rule(rule.id), Some(rule));
    }
}

#[test]
fn unresolved_region_never_restricts_the_overlap_witness_or_hides_independent_results() {
    for require_c in [false, true] {
        for fix_c in [false, true] {
            let f = Fixture::mixed(require_c, fix_c);
            let p = f.lower();
            let limits = Limits::default();
            let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
            let symbolic = ground.symbolic(&limits).unwrap();
            let report = symbolic.verify_at_most_one(&limits).unwrap();
            let b = atom(&p, "available", &["b"]).arguments;
            let group = report.groups.iter().find(|g| g.group.key == b).unwrap();
            let example = counterexample(group);
            assert_eq!(
                example
                    .observation
                    .present
                    .contains(&atom(&p, "present", &["input_c"])),
                require_c
            );
            assert_eq!(
                example.replay_scope,
                if fix_c || !require_c {
                    ReplayScope::WholeProgram
                } else {
                    ReplayScope::ConeOnly
                }
            );
            assert_eq!(report.whole_program_admitted(), fix_c);
            if !fix_c {
                assert!(if require_c {
                    matches!(
                        example.certification,
                        Some(CertificationOutcome::NotCertified)
                    )
                } else {
                    matches!(
                        example.certification,
                        Some(CertificationOutcome::Certified(_))
                    )
                });
            }
            assert!(!report.all_obligations_proved());
            let d = atom(&p, "available", &["d"]).arguments;
            let group = report.groups.iter().find(|g| g.group.key == d).unwrap();
            if !fix_c {
                assert!(matches!(group.outcome, VerifiedOutcome::Unsupported));
            }
            let messages =
                presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str())
                    .unwrap();
            assert_eq!(
                example.confined_to_no_meaning.len(),
                usize::from(require_c && !fix_c)
            );
            for message in messages
                .iter()
                .filter(|m| m.kind == DiagnosticKind::OverlappingMappings)
            {
                assert_eq!(
                    message
                        .notes
                        .iter()
                        .any(|n| n.starts_with("This conflict only occurs")),
                    require_c && !fix_c
                );
                if !require_c && !fix_c {
                    assert!(
                        message
                            .notes
                            .iter()
                            .any(|n| n.contains("for this observation only")
                                && n.contains("remains incomplete"))
                    );
                }
            }
            assert_eq!(
                messages
                    .iter()
                    .filter(|m| m.message.starts_with("Slot b "))
                    .count(),
                2
            );
            let skipped: Vec<_> = messages
                .iter()
                .filter(|m| m.kind == DiagnosticKind::UnsupportedGroup)
                .collect();
            if !fix_c {
                let d_targets: BTreeSet<_> = f
                    .ast
                    .mappings
                    .iter()
                    .filter(|m| m.target.text == "d")
                    .map(|m| m.target.span)
                    .collect();
                assert_eq!(skipped.len(), 2);
                assert_eq!(
                    skipped.iter().map(|m| m.primary).collect::<BTreeSet<_>>(),
                    d_targets
                );
                assert_eq!(report.unresolved.len(), 1);
                let cycle = &report.unresolved[0];
                assert_eq!(cycle.rules.len(), 3);
                assert_eq!(
                    cycle.rules.iter().map(|r| r.id).collect::<BTreeSet<_>>(),
                    cycle.cycle.edges.iter().map(|e| e.rule).collect()
                );
                let diagnostic = messages
                    .iter()
                    .find(|d| d.kind == DiagnosticKind::NoMeaning)
                    .unwrap();
                assert_eq!(
                    f.sources.text(diagnostic.primary).unwrap(),
                    "not available(c)"
                );
                assert_eq!(diagnostic.kind.severity(), DiagnosticSeverity::Error);
                assert_eq!(
                    diagnostic.message,
                    "These rules have no consistent result whenever input_c is present."
                );
                let CompletionOutcome::NoMeaning(failure) = &cycle.completion else {
                    panic!()
                };
                assert!(
                    failure
                        .observation
                        .present
                        .contains(&atom(&p, "present", &["input_c"]))
                );
                assert!(
                    diagnostic
                        .notes
                        .iter()
                        .any(|n| n.contains("Other observations remain unsupported"))
                );
                assert!(
                    diagnostic
                        .notes
                        .iter()
                        .any(|n| n.starts_with("Example observation") && n.contains("input_c"))
                );
                assert_eq!(diagnostic.cycle_rules.len(), 3);
                for notice in skipped {
                    assert_eq!(notice.kind.severity(), DiagnosticSeverity::Information);
                    assert_eq!(
                        notice.message,
                        "Overlap check for slot d was skipped: it depends on a region with a no-consistent-result finding. See related locations."
                    );
                    assert_eq!(
                        notice.notes,
                        ["No proof or counterexample is available for this slot."]
                    );
                    assert!(
                        notice
                            .related
                            .iter()
                            .any(|o| o.label == "blocking no-meaning finding"
                                && o.span == diagnostic.primary)
                    );
                    assert_eq!(
                        notice.cycle_rules.iter().copied().collect::<BTreeSet<_>>(),
                        diagnostic.cycle_rules.iter().copied().collect()
                    );
                }
                assert_eq!(
                    f.sources.text(diagnostic.primary).unwrap(),
                    "not available(c)"
                );
            } else {
                assert!(
                    skipped.is_empty(),
                    "Fixing the cycle must clear skipped-check notices"
                );
            }
        }
    }
}

#[test]
fn unlocated_library_negation_falls_back_without_hiding_other_findings() {
    let mut f = Fixture::new(
        "input input_a, input_b, input_bb, input_c, input_d, input_dd;\nslot a, b, c, d;\na <- input_a;\nb <- input_b when available(a);\nb <- input_bb when available(a);\nc <- input_c when available(c);\nd <- input_d when not available(c);\nd <- input_dd;\n",
        &[
            "input_a", "input_b", "input_bb", "input_c", "input_d", "input_dd",
        ],
        &["a", "b", "c", "d"],
    );
    f.mapping(f.span("a <- input_a;"), "a", "input_a", None);
    for (line, slot, input, guard, negative) in [
        (
            "b <- input_b when available(a);",
            "b",
            "input_b",
            "a",
            false,
        ),
        (
            "b <- input_bb when available(a);",
            "b",
            "input_bb",
            "a",
            false,
        ),
        (
            "c <- input_c when available(c);",
            "c",
            "input_c",
            "c",
            false,
        ),
        (
            "d <- input_d when not available(c);",
            "d",
            "input_d",
            "c",
            true,
        ),
    ] {
        let span = f.span(line);
        let condition = f.atom(span, "available", guard);
        f.mapping(
            span,
            slot,
            input,
            Some(if negative {
                f.not(condition)
            } else {
                condition
            }),
        );
    }
    f.mapping(f.span("d <- input_dd;"), "d", "input_dd", None);
    let mut p = f.lower();
    let mapping = atom(&p, "mapped_to", &["input_c", "c"]);
    let available = atom(&p, "available", &["c"]);
    // A library-generated negative dependency closes a cycle through the user's
    // positive mapping. It has no negative-premise origin in the DSL view.
    let head = p
        .corpus
        .atom(
            available.relation,
            available.arguments.iter().copied().map(Term::from),
        )
        .unwrap();
    let negative = p
        .corpus
        .atom(
            mapping.relation,
            mapping.arguments.iter().copied().map(Term::from),
        )
        .unwrap();
    let negative_id = negative.id();
    p.corpus
        .add_rule(head, [Literal::Negative(negative)])
        .unwrap();
    let library_text = "available(c) :- !mapped_to(input_c, c);";
    let library_snapshot = f
        .sources
        .add(
            "file:///library.den",
            1,
            SourceView::Denotate.as_str(),
            library_text,
        )
        .unwrap();
    p.attribution
        .provenance
        .attach(
            &p.corpus,
            &f.sources,
            negative_id,
            [Origin::new(
                f.sources
                    .span(
                        library_snapshot,
                        library_text.find('!').unwrap()..library_text.len() - 1,
                    )
                    .unwrap(),
            )],
        )
        .unwrap();

    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
    let meaning = ground.symbolic(&limits).unwrap();
    let report = meaning.verify_at_most_one(&limits).unwrap();
    assert_eq!(report.unresolved.len(), 1);
    let cycle = &report.unresolved[0];
    assert!(
        cycle
            .cycle
            .edges
            .iter()
            .any(|e| e.polarity == Polarity::Negative && e.premise == negative_id)
    );
    let messages =
        presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str()).unwrap();
    let user_mapping = f
        .ast
        .mappings
        .iter()
        .find(|m| m.target.text == "c")
        .unwrap();
    let expected_rule_locations = BTreeSet::from([user_mapping.span]);
    assert_eq!(
        messages
            .iter()
            .filter(|d| d.kind == DiagnosticKind::NoMeaning)
            .map(|d| d.primary)
            .collect::<BTreeSet<_>>(),
        expected_rule_locations
    );
    assert_eq!(
        messages
            .iter()
            .filter(|d| d.kind == DiagnosticKind::OverlappingMappings)
            .count(),
        2
    );
    let skipped: Vec<_> = messages
        .iter()
        .filter(|d| d.kind == DiagnosticKind::UnsupportedGroup)
        .collect();
    assert_eq!(skipped.len(), 2);
    for diagnostic in skipped {
        assert_eq!(
            diagnostic
                .related
                .iter()
                .map(|o| o.span)
                .collect::<BTreeSet<_>>(),
            expected_rule_locations
        );
    }
    assert!(messages.iter().all(|d| d.primary.snapshot() == f.snapshot
        && d.related.iter().all(|o| o.span.snapshot() == f.snapshot)));

    // Even term-only attribution is a location. With no cycle attribution at
    // all, keep the creator error rather than blaming an unrelated statement.
    let occurrences = |rule: &denotate_ir::Rule| {
        std::iter::once(rule.id.into())
            .chain(
                std::iter::once(&rule.head)
                    .chain(rule.body.iter().map(|l| l.atom()))
                    .flat_map(|a| {
                        std::iter::once(a.id()).chain(a.arguments().iter().map(|arg| arg.id()))
                    }),
            )
            .collect::<Vec<OccurrenceId>>()
    };
    let cycle_occurrences: BTreeSet<_> = cycle
        .rules
        .iter()
        .flat_map(|r| occurrences(p.corpus.rule(r.source).unwrap()))
        .collect();
    let target = cycle
        .rules
        .iter()
        .find(|r| r.head.atom == mapping)
        .unwrap()
        .head
        .arguments[1];
    let mut term_only = Provenance::new();
    let mut no_cycle = Provenance::new();
    for occurrence in p.corpus.rules().flat_map(occurrences) {
        let origins = p.attribution.provenance.origins(occurrence).iter().cloned();
        if !cycle_occurrences.contains(&occurrence) {
            no_cycle
                .attach(&p.corpus, &f.sources, occurrence, origins.clone())
                .unwrap();
        }
        if !cycle_occurrences.contains(&occurrence) || occurrence == target {
            term_only
                .attach(&p.corpus, &f.sources, occurrence, origins)
                .unwrap();
        }
    }
    p.attribution.provenance = term_only;
    let messages =
        presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str()).unwrap();
    assert_eq!(
        messages
            .iter()
            .filter(|d| d.kind == DiagnosticKind::NoMeaning)
            .map(|d| d.primary)
            .collect::<Vec<_>>(),
        [user_mapping.target.span]
    );
    assert_eq!(
        messages
            .iter()
            .filter(|d| d.kind == DiagnosticKind::OverlappingMappings)
            .count(),
        2
    );
    p.attribution.provenance = no_cycle;
    assert!(matches!(
        presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str()),
        Err(PresentationError::MissingOrigin { .. })
    ));
}

#[test]
fn complementary_guards_duplicates_or_paths_and_one_input_to_two_slots_do_not_conflict() {
    let cases = [
        (
            "input input_a, input_b, input_bb;\nslot a, b;\na <- input_a;\nb <- input_b when available(a);\nb <- input_bb when not available(a);\n",
            0,
        ),
        (
            "input input_a, input_b, input_bb;\nslot a, b;\na <- input_a;\nb <- input_b;\nb <- input_b;\n",
            1,
        ),
        (
            "input input_a, input_b, input_bb;\nslot a, b;\na <- input_a;\nb <- input_b when available(a) or present(input_bb);\n",
            2,
        ),
        (
            "input input_a, input_b, input_bb;\nslot a, b;\na <- input_a;\nb <- input_a;\n",
            3,
        ),
    ];
    for (text, kind) in cases {
        let mut f = Fixture::new(text, &["input_a", "input_b", "input_bb"], &["a", "b"]);
        f.mapping(f.span("a <- input_a;"), "a", "input_a", None);
        match kind {
            0 => {
                for (line, input, negative) in [
                    ("b <- input_b when available(a);", "input_b", false),
                    ("b <- input_bb when not available(a);", "input_bb", true),
                ] {
                    let span = f.span(line);
                    let a = f.atom(span, "available", "a");
                    f.mapping(span, "b", input, Some(if negative { f.not(a) } else { a }));
                }
            }
            1 => {
                for n in 0..2 {
                    f.mapping(f.nth_span("b <- input_b;", n), "b", "input_b", None);
                }
            }
            2 => {
                let span = f.span("b <- input_b when available(a) or present(input_bb);");
                f.mapping(
                    span,
                    "b",
                    "input_b",
                    Some(f.binary(
                        f.atom(span, "available", "a"),
                        f.atom(span, "present", "input_bb"),
                        false,
                    )),
                );
            }
            _ => f.mapping(f.span("b <- input_a;"), "b", "input_a", None),
        }
        let p = f.lower();
        let limits = Limits::default();
        let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
        let meaning = ground.symbolic(&limits).unwrap();
        let report = meaning.verify_at_most_one(&limits).unwrap();
        assert!(report.all_obligations_proved());
        assert!(
            presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str())
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn helper_and_input_absence_keep_references_and_quote_the_original_negative_guard() {
    for guard in [
        "not present(input_a)",
        "not (available(a) and available(c))",
        "not available(c)",
    ] {
        let text = format!(
            "input input_a, input_b, input_bb, input_c;\nslot a, b, c;\na <- input_a;\nc <- input_c;\nb <- input_b when {guard};\nb <- input_bb;\n"
        );
        let mut f = Fixture::new(
            &text,
            &["input_a", "input_b", "input_bb", "input_c"],
            &["a", "b", "c"],
        );
        f.mapping(f.span("a <- input_a;"), "a", "input_a", None);
        if guard != "not available(c)" {
            f.mapping(f.span("c <- input_c;"), "c", "input_c", None);
        }
        let span = f.span(&format!("b <- input_b when {guard};"));
        let inner = if guard.contains("present") {
            f.atom(span, "present", "input_a")
        } else if guard.contains("and") {
            Expr {
                span: f.within(span, "(available(a) and available(c))"),
                kind: ExprKind::Group(Box::new(f.binary(
                    f.atom(span, "available", "a"),
                    f.atom(span, "available", "c"),
                    true,
                ))),
            }
        } else {
            f.atom(span, "available", "c")
        };
        f.mapping(span, "b", "input_b", Some(f.not(inner)));
        f.mapping(f.span("b <- input_bb;"), "b", "input_bb", None);
        let p = f.lower();
        let limits = Limits::default();
        let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
        let meaning = ground.symbolic(&limits).unwrap();
        let report = meaning.verify_at_most_one(&limits).unwrap();
        let example = counterexample(&report.groups[0]);
        let replay = ground
            .evaluate(example.observation.present.iter().cloned(), &limits)
            .unwrap();
        let mut absences = 0;
        for step in example.evidence.values() {
            if let GroundEvidence::Derived { premises, .. } = &step.evidence {
                for premise in premises {
                    if let PremiseEvidence::Absent {
                        fact,
                        occurrence,
                        provider,
                    } = premise
                    {
                        if fact.relation == p.library.masked {
                            assert_eq!(*provider, CompletedProvider::NoPossibleProducer);
                            assert!(p.attribution.provenance.origins(*occurrence).is_empty());
                            continue; // New library absence is not an authored guard.
                        }
                        absences += 1;
                        assert_eq!(
                            replay.absence_provider(fact).unwrap().as_ref(),
                            Some(provider)
                        );
                        assert_eq!(replay.fact(fact).unwrap(), FactState::Settled(false));
                        assert!(!example.evidence.contains_key(fact)); // no why-not expansion
                        let origins = p.attribution.provenance.origins(*occurrence);
                        assert_eq!(origins.len(), 1);
                        assert_eq!(f.sources.text(origins[0].span).unwrap(), guard);
                        if guard.contains("present") {
                            assert_eq!(*provider, CompletedProvider::InputSnapshot);
                        } else if guard.contains("and") {
                            assert!(matches!(provider, CompletedProvider::Component(_)));
                        } else {
                            assert_eq!(*provider, CompletedProvider::NoPossibleProducer);
                        }
                    }
                }
            }
        }
        assert_eq!(absences, 1);
        let messages =
            presentation::present(&p, &report, &f.sources, SourceView::TestDsl.as_str()).unwrap();
        assert!(
            messages
                .iter()
                .all(|d| d.message.contains(&format!("`{guard}`")))
        );
    }
}

#[test]
fn denotate_view_selects_supplied_term_origins_and_missing_origins_are_creator_failures() {
    let mut f = Fixture::overlap();
    let mut p = f.lower();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
    let meaning = ground.symbolic(&limits).unwrap();
    let report = meaning.verify_at_most_one(&limits).unwrap();
    assert!(matches!(
        presentation::present(&p, &report, &f.sources, SourceView::Denotate.as_str()),
        Err(PresentationError::MissingOrigin { .. })
    ));
    let text = "mapped_to(input_b, b) :- available(a);\nmapped_to(input_bb, b) :- available(a);\n";
    let snapshot = f
        .sources
        .add(
            "file:///example.den",
            7,
            SourceView::Denotate.as_str(),
            text,
        )
        .unwrap();
    let mut targets = BTreeSet::new();
    for (input, start) in [("input_b", 0), ("input_bb", text.find('\n').unwrap() + 1)] {
        let fact = atom(&p, "mapped_to", &[input, "b"]);
        let GroundEvidence::Derived { rule, .. } =
            &counterexample(&report.groups[0]).evidence[&fact].evidence
        else {
            panic!()
        };
        let input_span = f
            .sources
            .span(snapshot, start + 10..start + 10 + input.len())
            .unwrap();
        let target_at = start + 10 + input.len() + 2;
        let target = f.sources.span(snapshot, target_at..target_at + 1).unwrap();
        targets.insert(target);
        let guard_at = start + text[start..].find("available(a)").unwrap();
        let guard = f
            .sources
            .span(snapshot, guard_at..guard_at + "available(a)".len())
            .unwrap();
        for (id, origin) in [
            (rule.head.arguments[0], Origin::new(input_span)),
            (rule.head.arguments[1], Origin::new(target)),
        ] {
            p.attribution
                .provenance
                .attach(&p.corpus, &f.sources, id, [origin])
                .unwrap();
        }
        p.attribution
            .guards
            .insert((rule.source, SourceView::Denotate), guard);
    }
    let messages =
        presentation::present(&p, &report, &f.sources, SourceView::Denotate.as_str()).unwrap();
    assert_eq!(
        messages.iter().map(|d| d.primary).collect::<BTreeSet<_>>(),
        targets
    );
    for d in messages {
        assert_eq!(f.sources.text(d.primary).unwrap(), "b");
        assert!(d.related.iter().all(|o| o.span.snapshot() == snapshot));
    }
    let other_fixture = Fixture::overlap();
    let other = other_fixture.lower();
    assert!(matches!(
        presentation::present(
            &other,
            &report,
            &other_fixture.sources,
            SourceView::TestDsl.as_str()
        ),
        Err(PresentationError::InvalidFinding(_))
    ));
}
