use crate::Session;
use denotate_check::*;
use denotate_ir_text::{ProgramMembership, SourceFile, load};
use std::ops::Deref;

#[test]
fn checking_mode_invalidates_only_checking_and_agrees_cold_warm() {
    for restriction in ["at_most_one", "exactly_one"] {
        let source = SourceFile::new(
            "file:///mode.den",
            0,
            format!(
                "sort S; const x,y:S; input i(s:S); relation r(s:S); r(X):-i(X); assumption a:{restriction}(i,group_by:()); obligation u:at_most_one(r,group_by:()); obligation e:empty(r); obligation c:at_least_one(r,group_by:()); relation any(); any():-r(X); notice n:varies(any); verification v{{assumptions:[a];obligations:[u,e,c];notices:[n];}}"
            ),
        );
        let p = load(
            &ProgramMembership::single("root", [source.uri.clone()]),
            &[source],
        )
        .unwrap();
        let limits = Limits::default();
        let ops = (&limits).into();
        let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
        let mut request = p.verification_requests(&limits).unwrap().remove(0).1;
        assert!(!request.checking_within_w);
        let mut warm = Session::default();
        let mut last_core: Option<GroundProgram> = None;
        let mut last_mode = None;
        for mode in [false, false, true, true, false, false] {
            request.checking_within_w = mode;
            let RequestPreparation::Complete(prepared) = warm
                .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
                .unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            if let Some(previous) = &last_core {
                // Reuse the actual graph/W/admission, not just equal results.
                assert!(std::ptr::eq(previous.deref(), prepared.program().deref()));
            }
            last_core = Some(prepared.program().clone());
            let LocalCheckOutcome::Complete(actual) = warm.verify(&prepared, &ops).unwrap() else {
                panic!()
            };
            let RequestPreparation::Complete(fresh) =
                request.prepare(&p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            let fresh = fresh.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(expected) = fresh.verify_local(&ops).unwrap() else {
                panic!()
            };
            assert_eq!(actual.checked.results.value, expected.checked.results.value);
            assert_eq!(actual.queries, expected.queries);
            for q in actual.queries.values() {
                assert_eq!(q.input.checking_within_w, mode);
            }
            if restriction == "at_most_one" {
                assert!(!actual.queries.is_empty());
                assert_eq!(warm.stats().evaluation_misses == 0, last_mode == Some(mode));
                assert_eq!(warm.stats().verdict_misses == 0, last_mode == Some(mode));
            }
            last_mode = Some(mode);
        }
    }
}
