use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load, presentation};

const SOURCE: &str = r#"
sort Field;
const service: Field;
input present(field: Field);
input chosen(field: Field);
relation mandatory(field: Field);
mandatory(service);
relation kept(field: Field);
relation term(field: Field);
kept(F) :- mandatory(F);
kept(F) :- term(F);
term(F) :- chosen(F), !kept(F);
relation missing();
missing() :- !kept(service);
assumption available: at_least_one(present, group_by: (field));
obligation service_kept: empty(missing);
verification checks { assumptions: []; obligations: [service_kept]; }
"#;

fn check(
    p: &LoadedProgram,
    session: Option<&mut Session>,
) -> (bool, ScopedResults, serde_json::Value) {
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
    if let Some(session) = session {
        let fixed = session
            .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
            .unwrap();
        let RequestPreparation::Complete(prepared) = session
            .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
            .unwrap()
        else {
            panic!("preparation exhausted")
        };
        let prepared = prepared.admit(&ops).unwrap();
        assert!(prepared.program().admission_limit().is_none());
        let admitted = prepared.program().is_admitted();
        let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
            panic!("verification exhausted")
        };
        let status = presentation::present(p, &report.checked).unwrap().status;
        (admitted, report.checked.results.value, status)
    } else {
        let RequestPreparation::Complete(prepared) =
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!("preparation exhausted")
        };
        let prepared = prepared.admit(&ops).unwrap();
        assert!(prepared.program().admission_limit().is_none());
        let admitted = prepared.program().is_admitted();
        let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
            panic!("verification exhausted")
        };
        let status = presentation::present(p, &report).unwrap().status;
        (admitted, report.results.value, status)
    }
}

#[test]
fn producer_removals_agree_fresh_cold_warm_and_after_support_and_context_edits() {
    let conditional = SOURCE.replace("mandatory(service);", "mandatory(F) :- present(F);");
    let mut session = Session::default();
    for (revision, (text, expected)) in [
        (SOURCE.to_owned(), true),
        (format!("// new snapshot\n{SOURCE}"), true),
        (conditional.clone(), false),
        (
            conditional.replace("assumptions: []", "assumptions: [available]"),
            true,
        ),
        (conditional, false),
        (SOURCE.to_owned(), true),
    ]
    .into_iter()
    .enumerate()
    {
        let file = SourceFile::new("file:///producer-removals.den", revision as u64, text);
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let fresh = check(&p, None);
        let cold = check(&p, Some(&mut Session::default()));
        let warm = check(&p, Some(&mut session));
        let repeated = check(&p, Some(&mut session));
        // Same-source comparisons include keyed findings, replay evidence and
        // presented rewrite identities, without witness or resource goldens.
        assert_eq!(cold, warm);
        assert_eq!(warm, repeated);
        assert_eq!(fresh, warm);
        assert_eq!(warm.0, expected);
        assert!(!warm.1.inconsistent_assumptions);
        assert!(warm.1.incomplete.is_empty() && warm.1.unfinished.is_none());
        assert_eq!(warm.1.emptiness.values().next().unwrap().proved(), expected);
    }
}
