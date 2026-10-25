use super::rewrites::dsl_fixture;
use denotate_check::test_support::certification::compare;
#[test]
fn lowered_mapping_certificates_match_the_independent_oracle() {
    // Keep head counts within the oracle's deliberate exponential bound.
    for f in [
        dsl_fixture::Fixture::ambiguous(),
        dsl_fixture::Fixture::exclusive(),
    ] {
        let p = f.lower();
        for admit in [false, true] {
            assert!(compare(&p.corpus, &dsl_fixture::domains(&p), admit) > 0);
        }
    }
    let text = "input input_c;\nslot c;\nc <- input_c when not available(c);\n";
    let mut f = dsl_fixture::Fixture::new(text, &["input_c"], &["c"]);
    let span = f.span(text.lines().nth(2).unwrap());
    f.mapping(
        span,
        "c",
        "input_c",
        Some(f.not(f.atom(span, "available", "c"))),
    );
    let p = f.lower();
    assert_eq!(compare(&p.corpus, &dsl_fixture::domains(&p), true), 1);
}
