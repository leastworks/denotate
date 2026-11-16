use super::*;
use crate::test_support::rewrites::{atom, rel, rule};

fn fixture() -> (GroundProgram, GroundAtom) {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let allowed = rel(&mut c, "allowed", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(x, false), (b, true)]);
    rule(&mut c, b, &[(x, true), (a, true)]);
    let limits = Limits::default();
    let mut p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    // W excludes worlds, without fixing the split candidate x.
    p.assumption_condition = Some(
        p.condition_context(&limits)
            .unwrap()
            .input(&atom(allowed), &limits)
            .unwrap(),
    );
    (p, atom(a))
}

#[test]
fn profiling_reports_raw_and_restricted_sizes_without_changing_admission_work() {
    let (p, head) = fixture();
    let defaults = Limits::default();
    let meaning = p.symbolic(&defaults).unwrap();
    let summaries = crate::test_support::rewrites::summaries(&p, &meaning, &defaults);
    let run = |profile| {
        let limits = Limits {
            profile,
            ..defaults.clone()
        };
        let mut budget = Budget::tracked(&limits);
        let events = std::cell::RefCell::new(Vec::new());
        let observer = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
        let proofs = p
            .structural_splits(
                p.component_for(&head).unwrap(),
                &summaries,
                &meaning,
                &mut 0,
                &mut budget,
                &AdmissionReporter::new(Some(&observer)),
                &mut false,
            )
            .unwrap();
        (proofs, budget.snapshot(), events.into_inner())
    };
    let (plain, charges, quiet_events) = run(Profile::default());
    let (profiled, observed_charges, events) = run(Profile::new(|_| {}));
    assert!(!plain.is_empty());
    assert_eq!(charges, observed_charges);
    assert_eq!(
        plain.iter().map(|p| &p.replacement).collect::<Vec<_>>(),
        profiled.iter().map(|p| &p.replacement).collect::<Vec<_>>()
    );
    assert!(quiet_events.iter().all(|e| {
        e.structural_split
            .as_ref()
            .is_none_or(|s| s.replacement_sizes.is_none())
    }));
    let report = events
        .iter()
        .filter_map(|e| e.structural_split.as_ref()?.replacement_sizes.as_ref())
        .last()
        .unwrap();
    assert_eq!(report.state, "complete");
    assert_eq!(report.replacements, profiled.len());
    assert_eq!(
        report.measured_expressions,
        report.distinct_expressions.unwrap()
    );
    assert!(report.max_domain_restricted_bdd_nodes > report.max_unrestricted_bdd_nodes);
    assert!(report.expression_nodes.unwrap() > 0);

    let failed = measure_with_limits(
        &profiled,
        &meaning,
        &Limits {
            max_work: 0,
            ..defaults.clone()
        },
    )
    .unwrap();
    assert_eq!(failed.state, "incomplete");
    assert_eq!(failed.failure.unwrap().resource, "work");
    assert!(failed.unrestricted_bdd.is_none());
    for (limited, resource) in [
        (
            Limits {
                max_condition_nodes: 0,
                ..defaults.clone()
            },
            "condition nodes",
        ),
        (
            Limits {
                max_bdd_nodes: 0,
                ..defaults.clone()
            },
            "BDD nodes",
        ),
        (
            Limits {
                timeout: Duration::ZERO,
                ..defaults.clone()
            },
            "deadline",
        ),
    ] {
        let limited = measure_with_limits(&profiled, &meaning, &limited).unwrap();
        assert_eq!(limited.state, "incomplete");
        assert_eq!(limited.failure.unwrap().resource, resource);
        assert!(limited.unrestricted_bdd.is_none() && limited.domain_restricted_bdd.is_none());
    }
    let duplicated: Vec<_> = profiled.iter().chain(&profiled).cloned().collect();
    let duplicate_sizes = measure_with_limits(&duplicated, &meaning, &defaults).unwrap();
    assert_eq!(duplicate_sizes.state, "complete");
    assert_eq!(duplicate_sizes.replacements, report.replacements * 2);
    assert_eq!(
        duplicate_sizes.distinct_expressions,
        report.distinct_expressions
    );
    assert_eq!(duplicate_sizes.expression_nodes, report.expression_nodes);
    let cancelled = Limits::default();
    cancelled.cancellation.cancel();
    assert!(matches!(
        measure_with_limits(&profiled, &meaning, &cancelled),
        Err(CheckError::Cancelled)
    ));
}
