use crate::{Retention, Session};
use denotate_check::*;
use denotate_ir_text::*;

fn program() -> LoadedProgram {
    let source = SourceFile::new(
        "file:///fixed.den",
        1,
        "relation fixed(); fixed(); input i(); relation r(); r():-fixed(),i(); obligation o:empty(r); verification v{assumptions:[];obligations:[o];}",
    );
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}

fn check(p: &LoadedProgram, session: &mut Session, with_validation: bool) {
    let limits = Limits::default();
    let ops = (&limits).into();
    let validated =
        validate_assumption_cones_for_run(&p.corpus, &p.domains, &p.keys, &limits).unwrap();
    let fixed = if with_validation {
        session.prepare_fixed_with_validation(&validated, &limits)
    } else {
        session.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
    }
    .unwrap();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = session
        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!("preparation failed")
    };
    let prepared = prepared.admit(&ops).unwrap();
    let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
        panic!("checking failed")
    };
    let RequestPreparation::Complete(fresh) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!("fresh preparation failed")
    };
    let fresh = fresh.admit(&ops).unwrap();
    let CheckOutcome::Complete(control) = fresh.verify(&ops).unwrap() else {
        panic!("fresh checking failed")
    };
    assert_eq!(
        presentation::present(p, &report).unwrap().status,
        presentation::present(p, &control).unwrap().status
    );
}

#[test]
fn completed_folds_ignore_byte_budgets_and_do_not_shrink_other_pools() {
    let p = program();
    for max_bytes in [0, 1, Retention::default().max_bytes] {
        let mut session = Session::new(Retention {
            max_bytes,
            ..Retention::default()
        });
        check(&p, &mut session, false);
        assert!(session.fixed_stats().retained_bytes > 0);
        assert_eq!(session.local_retention_for_test().max_bytes, max_bytes);
        let before = session.fixed_stats();
        check(&p, &mut session, true);
        assert!(session.fixed_stats().reused > before.reused);
        assert_eq!(session.fixed_stats().executed, before.executed);
        assert_eq!(session.fixed_stats().bypassed, 0);
        assert_eq!(session.local_retention_for_test().max_bytes, max_bytes);
    }
}

#[test]
fn disabled_retention_prepares_directly_with_or_without_validation() {
    let p = program();
    // Even a large byte allowance cannot enable retention when entries are off.
    let mut session = Session::new(Retention {
        max_entries: 0,
        ..Retention::default()
    });
    for validated in [false, true, false] {
        let before = session.fixed_stats();
        check(&p, &mut session, validated);
        assert_eq!(session.fixed_stats().retained_bytes, 0);
        assert_eq!(session.fixed_stats().reused, 0);
        assert!(session.fixed_stats().bypassed > before.bypassed);
    }
}
