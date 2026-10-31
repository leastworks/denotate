use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load};

const SOURCE: &str = r#"
namespace probe;
input trigger();
input release();
relation blocked();
relation result();
relation unrelated();
blocked() :- trigger(), !blocked();
result() :- !blocked();
unrelated() :- !release(), !unrelated();
relation mismatch();
mismatch() :- trigger(), !release();
mismatch() :- release(), !trigger();
assumption linked: empty(mismatch);
obligation absent: empty(result);
obligation covered: at_least_one(result, group_by: ());
verification checks { assumptions: []; obligations: [absent, covered]; }
"#;

fn program(text: &str) -> LoadedProgram {
    let file = SourceFile::new("file:///search.den", 1, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}

fn check(p: &LoadedProgram, session: Option<&mut Session>) -> ScopedResults {
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
    if let Some(session) = session {
        let RequestPreparation::Complete(prepared) =
            session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!("preparation exhausted")
        };
        let prepared = prepared.admit(&ops).unwrap();
        let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
            panic!("verification exhausted")
        };
        report.checked.results.value
    } else {
        let RequestPreparation::Complete(prepared) =
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!("preparation exhausted")
        };
        let prepared = prepared.admit(&ops).unwrap();
        let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
            panic!("verification exhausted")
        };
        report.results.value
    }
}

#[test]
fn certification_search_agrees_cold_warm_and_after_context_and_blocker_edits() {
    let mut session = Session::default();
    for (text, expected_present, unresolved) in [
        (SOURCE.to_owned(), 1, true),
        (format!("// new source snapshot\n{SOURCE}"), 1, true),
        (
            SOURCE.replace("assumptions: []", "assumptions: [linked]"),
            0,
            true,
        ),
        (
            SOURCE.replace(
                "unrelated() :- !release(), !unrelated();",
                "unrelated() :- !unrelated();",
            ),
            0,
            true,
        ),
        (SOURCE.to_owned(), 1, true),
        (
            SOURCE
                .replace(
                    "blocked() :- trigger(), !blocked();",
                    "blocked() :- trigger();",
                )
                .replace(
                    "unrelated() :- !release(), !unrelated();",
                    "unrelated() :- !release();",
                ),
            1,
            false,
        ),
    ] {
        let p = program(&text);
        let warm = check(&p, Some(&mut session));
        let fresh = check(&p, Some(&mut Session::default()));
        let global = check(&p, None);
        // Same-snapshot equality includes replay validity/identity. No chosen
        // witness, resource receipt or timing is stored as a golden.
        assert_eq!(warm, fresh);
        assert_eq!(warm, global);
        assert!(!warm.inconsistent_assumptions);
        assert!(warm.unfinished.is_none() && warm.incomplete.is_empty());
        let empty = warm.emptiness.values().next().unwrap();
        assert!(empty.inconclusive.is_none());
        assert_eq!(
            (empty.present, empty.unresolved),
            (expected_present, unresolved)
        );
        let coverage = warm.coverage.values().next().unwrap();
        assert!(coverage.inconclusive.is_none());
        assert_eq!(coverage.unsupported, usize::from(unresolved));
        assert_eq!(coverage.missing, usize::from(!unresolved));
    }
}
