#[path = "../../test-dsl/tests/support/corpus.rs"]
mod corpus;
use denotate_check::{Limits, ScopedResult};
use denotate_editor::Document;
use denotate_test_dsl::{analysis, lowering, syntax};
use std::{sync::Arc, time::Duration};

#[test]
fn bdd_editor_recursive_support_requires_replayed_facts() {
    let source = "input i,j,k; slot a,b; a <- i when available(b); a <- j when available(b); b <- i when available(a); b <- k;";
    let doc = Arc::new(Document::new(
        &mut syntax::parser().unwrap(),
        source.into(),
        1,
        true,
    ));
    let program = analysis::prepare(
        &"file:///bdd-loop.testdsl".parse().unwrap(),
        1,
        doc,
        &mut lowering::incremental::Session::default(),
    )
    .unwrap()
    .program
    .unwrap();
    let l = Limits::default();
    let mut session = denotate_check_session::Session::default();
    let result = program.check_cached(&l, || {}, &mut session).unwrap();
    assert!(
        result
            .results
            .value
            .groups
            .values()
            .any(|r| matches!(r, ScopedResult::Counterexample(..)))
    );
    assert!(
        result
            .results
            .value
            .groups
            .values()
            .all(|r| !matches!(r, ScopedResult::Unsupported(_)))
    );
    assert!(result.creator_warnings.is_empty());
    let warm = program.check_cached(&l, || {}, &mut session).unwrap();
    assert_eq!(result.results, warm.results);
    assert_eq!(result.diagnostics, warm.diagnostics);
}

#[test]
fn bdd_editor_corpus_fresh_cached_and_current_diagnostics() {
    let mut checked = 0;
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
                &"file:///bdd-corpus.testdsl".parse().unwrap(),
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
            // Use the same local evaluator with retention disabled. The global
            // reference has a different query/receipt graph.
            let mut fresh_session =
                denotate_check_session::Session::new(denotate_check_session::Retention {
                    max_entries: 0,
                    max_bytes: 0,
                    max_condition_nodes: 0,
                });
            let fresh = program.check_cached(&l, || {}, &mut fresh_session).unwrap();
            let cached = program.check_cached(&l, || {}, &mut session).unwrap();
            assert_eq!(fresh.results, cached.results, "{source}");
            assert_eq!(fresh.diagnostics, cached.diagnostics, "{source}");
            assert_eq!(fresh.creator_warnings, cached.creator_warnings);
            checked += 1;
            if version == 1 {
                assert_eq!(
                    session.stats().verdict_misses + session.stats().completion_misses,
                    0
                );
            }
        }
    }
    assert!(checked > 0);
}
