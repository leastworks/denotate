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
fn requests_and_direct_preparation_follow_the_selected_assumptions() {
    use denotate_ir::{Namespace, QualifiedKey, VerificationKey};

    let mut p = program(
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
    );
    let p = &mut p.lowered;
    let limits = Limits::default();
    let default = p.library.default_checks;
    let unrestricted = p
        .corpus
        .verification_in(
            Namespace::default(),
            "unrestricted",
            [],
            [p.library.unique_input],
        )
        .unwrap();
    p.keys
        .bind_verification(
            &p.corpus,
            unrestricted,
            VerificationKey(QualifiedKey::new("test", "unrestricted")),
        )
        .unwrap();

    // The guards are exclusive only when the selected assumption forbids two
    // values for i. The unselected declaration remains in the corpus.
    for (verification, proved) in [(default, true), (unrestricted, false)] {
        p.library.default_checks = verification;
        let direct = p.prepare(&limits).unwrap().admit(&limits).unwrap();
        let direct = direct
            .symbolic(&limits)
            .unwrap()
            .verify_at_most_one(&limits)
            .unwrap();
        assert_eq!(direct.all_obligations_proved(), proved);

        let request = p.request(&limits).unwrap();
        assert_eq!(
            request.verification.as_ref(),
            Some(p.keys.verification(verification).unwrap())
        );
        let RequestPreparation::Complete(prepared) = request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap()
        else {
            panic!("unexpected preparation exhaustion")
        };
        let admitted = prepared.admit(&(&limits).into()).unwrap();
        let CheckOutcome::Complete(checked) = admitted.verify(&(&limits).into()).unwrap() else {
            panic!("unexpected checking exhaustion")
        };
        assert_eq!(checked.verification.all_obligations_proved(), proved);
    }
}

#[test]
fn affected_fixtures_keep_status_and_diagnostic_summaries() {
    let report: Value = serde_json::from_str(include_str!(
        "../../crates/check-session/fixtures/regression/outcomes.json"
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
            &verification_constraints(&p.lowered.corpus, p.lowered.library.default_checks).unwrap(),
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
