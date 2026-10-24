use denotate_check::Limits;
use denotate_editor::Document;
use denotate_test_dsl::{lowering, syntax};
use serde_json::Value;
fn limits() -> Limits {
    Limits {
        timeout: std::time::Duration::from_secs(60),
        ..Limits::default()
    }
}
#[test]
fn grounding_all_valid_frontend_frozen_sources_match() {
    for text in [
        include_str!("../../../test-dsl/fixtures/pre-mask.json"),
        include_str!("../../../test-dsl/fixtures/pre-normalize.json"),
        include_str!("../../../test-dsl/fixtures/pre-integration-fingerprints.json"),
    ] {
        let data: Value = serde_json::from_str(text).unwrap();
        for row in data["cases"].as_array().unwrap() {
            let source = row["text"].as_str().unwrap();
            let document = std::sync::Arc::new(Document::new(
                &mut syntax::parser().unwrap(),
                source.into(),
                1,
                true,
            ));
            let frontend = denotate_test_dsl::analysis::prepare(
                &"file:///grounding-frozen.inputmapping".parse().unwrap(),
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
}
