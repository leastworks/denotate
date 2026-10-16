mod support;
use denotate_check::*;
use denotate_test_dsl::presentation::{self, DiagnosticKind, DiagnosticSeverity};
use support::*;

#[test]
fn exact_conjunction_is_worded_as_a_condition_not_a_complete_witness() {
    let text = "input input_c, input_x, input_y, unrelated;\nslot c;\nc <- input_c when present(input_x) and not present(input_y) and not available(c);\n";
    let mut f = Fixture::new(
        text,
        &["input_c", "input_x", "input_y", "unrelated"],
        &["c"],
    );
    let span = f.span(text.lines().nth(2).unwrap());
    let guard = f.binary(
        f.binary(
            f.atom(span, "present", "input_x"),
            f.not(f.atom(span, "present", "input_y")),
            true,
        ),
        f.not(f.atom(span, "available", "c")),
        true,
    );
    f.mapping(span, "c", "input_c", Some(guard));
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let report = g
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    let diagnostics = presentation::present(&p, &report, &f.sources, "test-dsl").unwrap();
    let failure = diagnostics
        .iter()
        .find(|d| d.kind == DiagnosticKind::NoMeaning)
        .unwrap();
    assert_eq!(
        failure.message,
        "These rules have no consistent result whenever input_c is present and input_x is present and input_y is absent."
    );
    assert!(
        failure
            .notes
            .iter()
            .any(|n| n.starts_with("Example observation") && n.contains("unrelated"))
    );
    assert!(
        failure
            .notes
            .iter()
            .any(|n| n.contains("Other observations remain unsupported"))
    );
}

#[test]
fn disjunctive_failure_keeps_example_wording_instead_of_generalizing_a_witness() {
    use denotate_test_dsl::ast::{Expr, ExprKind};
    let text = "input input_c, input_x, input_y;\nslot c;\nc <- input_c when (present(input_x) or present(input_y)) and not available(c);\n";
    let mut f = Fixture::new(text, &["input_c", "input_x", "input_y"], &["c"]);
    let span = f.span(text.lines().nth(2).unwrap());
    let alternative = Expr {
        span: f.within(span, "(present(input_x) or present(input_y))"),
        kind: ExprKind::Group(Box::new(f.binary(
            f.atom(span, "present", "input_x"),
            f.atom(span, "present", "input_y"),
            false,
        ))),
    };
    let guard = f.binary(alternative, f.not(f.atom(span, "available", "c")), true);
    f.mapping(span, "c", "input_c", Some(guard));
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let report = g
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    let diagnostics = presentation::present(&p, &report, &f.sources, "test-dsl").unwrap();
    let failure = diagnostics
        .iter()
        .find(|d| d.kind == DiagnosticKind::NoMeaning)
        .unwrap();
    assert_eq!(
        failure.message,
        "These rules have no consistent result in the example input observation."
    );
    assert!(
        failure
            .notes
            .iter()
            .any(|n| n.starts_with("Example observation"))
    );
}

#[test]
fn ambiguity_is_still_a_warning_not_a_contradiction_error() {
    let f = Fixture::ambiguous();
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let report = g
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    let diagnostics = presentation::present(&p, &report, &f.sources, "test-dsl").unwrap();
    assert!(!diagnostics.is_empty());
    assert!(
        diagnostics
            .iter()
            .all(|d| d.kind == DiagnosticKind::UnsupportedCycle)
    );
    assert!(
        diagnostics
            .iter()
            .all(|d| d.kind.severity() == DiagnosticSeverity::Warning)
    );
    assert!(
        diagnostics
            .iter()
            .all(|d| d.message.contains("does not establish meaning"))
    );
}

#[test]
fn deferred_cycle_cites_upstream_failure_without_inventing_its_own_witness() {
    let text = "input input_c, input_d;\nslot c, d;\nc <- input_c when not available(c);\nd <- input_d when available(c) and not available(d);\n";
    let mut f = Fixture::new(text, &["input_c", "input_d"], &["c", "d"]);
    let c = f.span(text.lines().nth(2).unwrap());
    f.mapping(c, "c", "input_c", Some(f.not(f.atom(c, "available", "c"))));
    let d = f.span(text.lines().nth(3).unwrap());
    f.mapping(
        d,
        "d",
        "input_d",
        Some(f.binary(
            f.atom(d, "available", "c"),
            f.not(f.atom(d, "available", "d")),
            true,
        )),
    );
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let report = g
        .symbolic(&limits)
        .unwrap()
        .verify_at_most_one(&limits)
        .unwrap();
    let diagnostics = presentation::present(&p, &report, &f.sources, "test-dsl").unwrap();
    assert_eq!(diagnostics.len(), 2);
    let failure = diagnostics
        .iter()
        .find(|d| d.kind == DiagnosticKind::NoMeaning)
        .unwrap();
    assert_eq!(failure.primary, f.within(c, "not"));
    let deferred = diagnostics
        .iter()
        .find(|d| d.kind == DiagnosticKind::UnsupportedCycle)
        .unwrap();
    assert_eq!(deferred.primary, f.within(d, "not"));
    assert!(
        deferred
            .message
            .contains("upstream component is not settled")
    );
    assert!(
        deferred
            .related
            .iter()
            .any(|o| o.span == failure.primary && o.role == "upstream no-meaning finding")
    );
    assert!(
        !deferred
            .notes
            .iter()
            .any(|n| n.starts_with("Example observation"))
    );
}

#[test]
fn completion_exhaustion_is_informational_and_keeps_the_overlap_errors() {
    let f = Fixture::mixed(false, false);
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &domains(&p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let m = g.symbolic(&limits).unwrap();
    let report = m
        .verify_with_completion_limits(
            &limits,
            &Limits {
                max_work: 0,
                ..limits.clone()
            },
        )
        .unwrap();
    let diagnostics = presentation::present(&p, &report, &f.sources, "test-dsl").unwrap();
    assert_eq!(
        diagnostics
            .iter()
            .filter(|d| d.kind == DiagnosticKind::OverlappingMappings)
            .count(),
        2
    );
    assert!(
        !diagnostics
            .iter()
            .any(|d| d.kind == DiagnosticKind::NoMeaning)
    );
    let exhausted = diagnostics
        .iter()
        .find(|d| d.kind == DiagnosticKind::Inconclusive)
        .unwrap();
    assert_eq!(exhausted.kind.severity(), DiagnosticSeverity::Information);
    assert!(exhausted.message.contains("Consistency checking"));
}

#[test]
fn certification_exhaustion_keeps_cone_errors_and_separate_no_meaning_error() {
    let f = Fixture::mixed(false, false);
    let p = f.lower();
    let limits = Limits::default();
    let g = GroundProgram::prepare(&p.corpus, &domains(&p), &limits).unwrap();
    let m = g.symbolic(&limits).unwrap();
    let report = m
        .verify_with_phase_limits(
            &limits,
            &limits,
            &Limits {
                max_work: 0,
                ..limits.clone()
            },
        )
        .unwrap();
    let diagnostics = presentation::present(&p, &report, &f.sources, "test-dsl").unwrap();
    let conflicts: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.kind == DiagnosticKind::OverlappingMappings)
        .collect();
    assert_eq!(conflicts.len(), 2);
    for d in conflicts {
        assert!(
            d.notes
                .iter()
                .any(|n| n.contains("certification is inconclusive"))
        );
        assert!(d.notes.iter().any(|n| n.contains("dependency cone only")));
        assert!(
            !d.notes
                .iter()
                .any(|n| n.starts_with("This conflict only occurs"))
        );
    }
    assert!(
        diagnostics
            .iter()
            .any(|d| d.kind == DiagnosticKind::NoMeaning)
    );
}
