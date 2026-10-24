//! Frontend use of the neutral contract and the explicit witness-order boundary.
use denotate_check::*;
use denotate_editor::Document;
use denotate_test_dsl::{
    analysis, attribution::SourceView, lowering::incremental::Session, presentation, syntax,
};
use lsp_types::Url;
use serde_json::Value;
use std::{collections::BTreeSet, sync::Arc, time::Duration};

fn program(text: &str) -> analysis::Program {
    analysis::prepare(
        &Url::parse("file:///request.inputmapping").unwrap(),
        1,
        Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            text.into(),
            1,
            true,
        )),
        &mut Session::default(),
    )
    .unwrap()
    .program
    .unwrap()
}
#[test]
fn affected_fixtures_keep_status_and_diagnostic_summaries() {
    let report: Value = serde_json::from_str(include_str!(
        "../../native/check-session/fixtures/regression/outcomes.json"
    ))
    .unwrap();
    let mut sources = BTreeSet::new();
    for row in report["cases"].as_array().unwrap() {
        sources.insert(row["source"].as_str().unwrap());
    }
    // Nonalphabetical declarations exercise summary decoding as well as witnesses.
    sources.insert("input z, a, m, unrelated; slot s; s <- z when present(a) and not present(m) and not available(s);");
    let limits = Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    for text in sources {
        let p = program(text);
        let old = GroundProgram::prepare_with_input_groups(
            &p.lowered.corpus,
            &p.lowered.domains(),
            &[InputAtMostOne {
                relation: p.lowered.library.value,
                group_by: vec![0],
            }],
            &limits,
        )
        .unwrap()
        .admit(&limits)
        .unwrap();
        let old = old
            .symbolic(&limits)
            .unwrap()
            .verify_at_most_one(&limits)
            .unwrap();
        let request = p.lowered.request(&limits).unwrap();
        let RequestPreparation::Complete(new) = request
            .prepare(&p.lowered.corpus, &p.lowered.keys, &(&limits).into())
            .unwrap()
        else {
            panic!()
        };
        let new = new.admit(&(&limits).into()).unwrap();
        let CheckOutcome::Complete(new) = new.verify(&(&limits).into()).unwrap() else {
            panic!()
        };
        let summary = |r: &Verification<'_>| {
            presentation::present(&p.lowered, r, &p.sources, SourceView::TestDsl.as_str())
                .unwrap()
                .into_iter()
                .map(|d| (d.kind, d.message, d.primary))
                .collect::<Vec<_>>()
        };
        assert_eq!(summary(&old), summary(&new.verification), "{text}");
        let output = p.check(&limits, || {}).unwrap();
        assert_eq!(
            output.results, new.results,
            "frontend must return the neutral checked result"
        );
    }
}
#[test]
fn interruption_never_returns_a_semantic_result() {
    let p = program("input i; slot a; a <- i;");
    let deadline = Limits {
        timeout: Duration::ZERO,
        ..Limits::default()
    };
    assert!(matches!(
        p.check(&deadline, || {}),
        Err(analysis::Failure::Deadline)
    ));
    let cancelled = Limits::default();
    cancelled.cancellation.cancel();
    assert!(matches!(
        p.check(&cancelled, || {}),
        Err(analysis::Failure::Cancelled)
    ));
    let ample = Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    assert!(
        p.check(&ample, || {})
            .unwrap()
            .results
            .value
            .unfinished
            .is_none()
    );
}
