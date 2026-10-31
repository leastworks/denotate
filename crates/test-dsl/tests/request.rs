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
        &Url::parse("file:///request.testdsl").unwrap(),
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
        "../../check-session/fixtures/regression/outcomes.json"
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

#[test]
fn selected_notice_findings_reach_both_editor_adapters_with_the_same_identity() {
    use denotate_ir::*;
    use denotate_ir_text::{ExportFile, ExportLayout, ExportProgram, Ownership, PrintOptions};

    // The test DSL has no notice syntax. Exercise the editor path by attaching a
    // notice through the construction API, as a lowerer would for this guard.
    let mut p = program("input i; slot a; a <- i when not available(a);");
    let span = p.sources.span(p.snapshot, 28..44).unwrap();
    let c = &mut p.lowered.corpus;
    let relation = c
        .declare_relation_in(
            Namespace::new(["test"]).unwrap(),
            "observed",
            RelationRole::Derived,
            [],
        )
        .unwrap();
    let head = c.atom(relation, []).unwrap();
    let body = c
        .atom(
            p.lowered.library.available,
            [Term::variable("S", p.lowered.library.slot)],
        )
        .unwrap();
    let rule = c.add_rule(head, [Literal::Positive(body)]).unwrap();
    let notice = c
        .notice_varies_in(
            Namespace::new(["test"]).unwrap(),
            "guard",
            relation,
            None,
            "Guard",
        )
        .unwrap();
    let verification = c
        .verification_with_notices_in(
            Namespace::new(["test"]).unwrap(),
            "checks",
            [p.lowered.library.one_value_per_input],
            [p.lowered.library.unique_input],
            [notice],
        )
        .unwrap();
    p.lowered.library.default_checks = verification;
    let keys = &mut p.lowered.keys;
    keys.bind_relation(
        c,
        relation,
        RelationKey::Named(QualifiedKey::new("test", "observed")),
    )
    .unwrap();
    keys.bind_notice(c, notice, NoticeKey(QualifiedKey::new("test", "guard")))
        .unwrap();
    keys.bind_verification(
        c,
        verification,
        VerificationKey(QualifiedKey::new("test", "checks")),
    )
    .unwrap();
    let key = RuleKey::Library(QualifiedKey::new("test", "observer"));
    keys.bind_rule(c, rule, key.clone()).unwrap();
    let rule_data = c.rule(rule).unwrap();
    for (atom, occurrence) in std::iter::once(&rule_data.head)
        .chain(rule_data.body.iter().map(Literal::atom))
        .enumerate()
    {
        keys.bind_occurrence(
            c,
            occurrence.id(),
            OccurrenceKey::Library {
                rule: key.clone(),
                atom,
                argument: None,
            },
        )
        .unwrap();
        for (argument, term) in occurrence.arguments().iter().enumerate() {
            keys.bind_occurrence(
                c,
                term.id(),
                OccurrenceKey::Library {
                    rule: key.clone(),
                    atom,
                    argument: Some(argument),
                },
            )
            .unwrap();
        }
    }
    for id in [
        OccurrenceId::from(relation),
        rule.into(),
        notice.into(),
        verification.into(),
    ] {
        p.lowered
            .attribution
            .provenance
            .attach(c, &p.sources, id, [Origin::new(span)])
            .unwrap();
    }
    p.lowered.attribution.validate(c, &p.sources).unwrap();
    let limits = Limits::default();
    let mut session = denotate_check_session::Session::default();
    let cold = p.check(&limits, || {}).unwrap();
    for _ in 0..2 {
        let warm = p.check_cached(&limits, || {}, &mut session).unwrap();
        assert_eq!(cold.diagnostics, warm.diagnostics);
    }
    let notice_diagnostics = cold
        .diagnostics
        .iter()
        .filter(|d| d.data.as_ref().unwrap()["kind"] == "unanalysed-condition")
        .collect::<Vec<_>>();
    assert_eq!(notice_diagnostics.len(), 1);
    let d = notice_diagnostics[0];
    assert_eq!(d.severity, Some(lsp_types::DiagnosticSeverity::INFORMATION));
    assert_eq!(d.range.start.character, 28);
    assert!(
        d.related_information
            .as_ref()
            .unwrap()
            .iter()
            .any(|r| r.message == "blocking dependency cycle")
    );

    // Export the same construction and compare the actual .den adapter result.
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&p.lowered.corpus)
            .into_iter()
            .map(|id| (id, 0))
            .collect(),
    };
    let bundle = denotate_ir_text::print(
        &ExportProgram {
            corpus: &p.lowered.corpus,
            domains: &p.lowered.domains(),
            sources: &p.sources,
            provenance: &p.lowered.attribution.provenance,
            layout: &layout,
        },
        PrintOptions::default(),
    )
    .unwrap();
    let (membership, documents) = bundle.documents("file:///notice-export");
    let loaded = denotate_ir_text::load(&membership, &documents).unwrap();
    let (_, request) = loaded
        .verification_requests(&limits)
        .unwrap()
        .into_iter()
        .find(|(key, _)| key.0.name.as_ref() == "checks")
        .unwrap();
    let ops = (&limits).into();
    let RequestPreparation::Complete(prepared) =
        request.prepare(&loaded.corpus, &loaded.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    let presented = denotate_ir_text::presentation::present(&loaded, &report).unwrap();
    let notices = presented
        .diagnostics
        .iter()
        .filter(|d| d.kind == denotate_presentation::Kind::UnanalysedCondition)
        .collect::<Vec<_>>();
    assert_eq!(notices.len(), 1);
    assert_eq!(notices[0].message, d.message);
    assert_eq!(
        notices[0].data(&loaded.keys).unwrap()["finding"],
        d.data.as_ref().unwrap()["finding"]
    );
    assert_eq!(notices[0].evidence["reason"]["kind"], "unsupported");
    assert!(
        notices[0]
            .related
            .iter()
            .any(|r| r.label == "blocking dependency cycle")
    );
}
