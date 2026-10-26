#[path = "../../test-dsl/tests/support/corpus.rs"]
mod corpus;
use denotate_check::Limits;
use denotate_editor::Document;
use denotate_test_dsl::{lowering, syntax};
fn limits() -> Limits {
    Limits {
        timeout: std::time::Duration::from_secs(60),
        ..Limits::default()
    }
}
#[test]
fn grounding_matches_fresh_checks_on_the_corpus() {
    for source in corpus::texts() {
        let source = source.as_str();
        let document = std::sync::Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            source.into(),
            1,
            true,
        ));
        let frontend = denotate_test_dsl::analysis::prepare(
            &"file:///grounding-corpus.testdsl".parse().unwrap(),
            1,
            document,
            &mut lowering::incremental::Session::default(),
        )
        .unwrap();
        if let Some(program) = frontend.program {
            let l = limits();
            let a = program.check(&l, || {}).unwrap();
            let mut session = denotate_check_session::Session::with_grounding();
            for _ in 0..2 {
                let b = program.check_cached(&l, || {}, &mut session).unwrap();
                assert_eq!(a.results.value, b.results.value);
                assert_eq!(a.diagnostics, b.diagnostics);
                assert_eq!(a.creator_warnings, b.creator_warnings);
            }
        }
    }
}
