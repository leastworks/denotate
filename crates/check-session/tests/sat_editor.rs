#[path = "../../test-dsl/tests/support/corpus.rs"]
mod corpus;
use denotate_check::{
    BackendIdentity, CertificationScope, Limits, ScopedResult, UnsupportedReason,
};
use denotate_editor::Document;
use denotate_test_dsl::{analysis, lowering, syntax};
use std::{sync::Arc, time::Duration};

#[test]
fn sat_editor_spurious_completion_is_an_unsupported_diagnostic() {
    let source = "input i,j,k; slot a,b; a <- i when available(b); a <- j when available(b); b <- i when available(a); b <- k;";
    let doc = Arc::new(Document::new(
        &mut syntax::parser().unwrap(),
        source.into(),
        1,
        true,
    ));
    let program = analysis::prepare(
        &"file:///sat-loop.testdsl".parse().unwrap(),
        1,
        doc,
        &mut lowering::incremental::Session::default(),
    )
    .unwrap()
    .program
    .unwrap();
    let l = Limits::default();
    let mut session = denotate_check_session::Session::default();
    let result = program
        .check_with_backend(&l, || {}, BackendIdentity::sat(), Some(&mut session))
        .unwrap();
    assert!(result.results.value.groups.values().any(|r| matches!(
        r,
        ScopedResult::Unsupported(UnsupportedReason::UnfoundedSupport(_))
    )));
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.message.contains("unsupported by the selected checker"))
    );
    assert!(result.creator_warnings.is_empty());
    let warm = program
        .check_with_backend(&l, || {}, BackendIdentity::sat(), Some(&mut session))
        .unwrap();
    assert_eq!(result.results, warm.results);
    assert_eq!(result.diagnostics, warm.diagnostics);
}

#[test]
fn sat_editor_corpus_fresh_cached_and_current_diagnostics() {
    let mut checked = 0;
    let mut unfounded = 0;
    let mut diagnostic_differences = 0;
    for source in corpus::texts() {
        let source = source.as_str();
        let mut session = denotate_check_session::Session::default();
        let mut lower = lowering::incremental::Session::default();
        for (version, source) in [source.to_owned(), format!("// shifted\n{source}")]
            .into_iter()
            .enumerate()
        {
            let document = Arc::new(Document::new(
                &mut syntax::parser().unwrap(),
                source.clone(),
                version as i32 + 1,
                true,
            ));
            let frontend = analysis::prepare(
                &"file:///sat-corpus.testdsl".parse().unwrap(),
                version as u64 + 1,
                document,
                &mut lower,
            )
            .unwrap();
            let Some(program) = frontend.program else {
                continue;
            };
            let l = Limits {
                timeout: Duration::from_secs(60),
                ..Limits::default()
            };
            let bdd = program.check(&l, || {}).unwrap();
            let fresh = program
                .check_with_backend(&l, || {}, BackendIdentity::sat(), None)
                .unwrap();
            let cached = program
                .check_with_backend(&l, || {}, BackendIdentity::sat(), Some(&mut session))
                .unwrap();
            assert_eq!(fresh.results, cached.results, "{source}");
            assert_eq!(fresh.diagnostics, cached.diagnostics, "{source}");
            assert_eq!(fresh.creator_warnings, cached.creator_warnings);
            checked += 1;
            let mut identical = true;
            for (key, result) in &cached.results.value.groups {
                match result {
                    ScopedResult::Unsupported(UnsupportedReason::UnfoundedSupport(_)) => {
                        unfounded += 1;
                        identical = false;
                    }
                    ScopedResult::Counterexample(c, _)
                        if c.scope == CertificationScope::ConeOnly =>
                    {
                        assert!(matches!(
                            bdd.results.value.groups[key],
                            ScopedResult::Counterexample(_, _)
                        ));
                        identical = false;
                    }
                    _ => assert_eq!(result, &bdd.results.value.groups[key], "{source}"),
                }
            }
            assert_eq!(
                cached.results.value.regions, bdd.results.value.regions,
                "{source}"
            );
            if identical {
                assert_eq!(cached.diagnostics, bdd.diagnostics, "{source}");
            }
            diagnostic_differences += usize::from(cached.diagnostics != bdd.diagnostics);
            if cached.diagnostics != bdd.diagnostics && version == 0 {
                println!(
                    "SAT_DIAGNOSTIC_DELTA={}",
                    serde_json::json!({
                        "source":source,
                        "bdd":format!("{:?}", bdd.diagnostics),
                        "sat":format!("{:?}", cached.diagnostics),
                        "reason":"SAT retains the validated cone finding without the BDD alternate-world retry or universal confinement annotation"
                    })
                );
            }
            if version == 1 {
                assert_eq!(
                    session.stats().verdict_misses + session.stats().completion_misses,
                    0
                );
            }
        }
    }
    println!(
        "SAT_EDITOR_INVENTORY checked={checked} unfounded={unfounded} diagnostic_differences={diagnostic_differences}"
    );
    assert!(checked > 0);
}
