use denotate_check::*;
use denotate_check_session::{Retention, Session};
use denotate_ir_text::*;

fn parse(uri: &str, text: &str) -> LoadedProgram {
    let file = SourceFile::new(uri, 1, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}

fn compare(p: &LoadedProgram, session: &mut Session) {
    let limits = Limits::default();
    let ops = (&limits).into();
    let fixed = session
        .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
        .unwrap();
    let requests = p.verification_requests(&limits).unwrap();
    // Prepare all before admitting any: neither order nor the first request's
    // selection can decide what the other requests check.
    let prepared: Vec<_> = requests
        .iter()
        .map(|(_, request)| {
            let RequestPreparation::Complete(p) = session
                .prepare_with_fixed(request, &p.corpus, &p.keys, &ops, &fixed)
                .unwrap()
            else {
                panic!("incomplete preparation")
            };
            p
        })
        .collect();
    for (prepared, (_, request)) in prepared.into_iter().zip(requests).rev() {
        let prepared = prepared.admit(&ops).unwrap();
        let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
            panic!("incomplete check")
        };
        let RequestPreparation::Complete(fresh) =
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!("incomplete fresh preparation")
        };
        let fresh = fresh.admit(&ops).unwrap();
        let CheckOutcome::Complete(control) = fresh.verify(&ops).unwrap() else {
            panic!("incomplete fresh check")
        };
        assert_eq!(report.checked.results.value.context, request);
        let actual = presentation::present(p, &report.checked).unwrap();
        let expected = presentation::present(p, &control).unwrap();
        assert_eq!(actual.status, expected.status);
        // Compare current locations as well as finding identities. These cases
        // deliberately have no interchangeable witness/producer choices.
        assert_eq!(
            actual
                .diagnostics
                .iter()
                .map(|d| (
                    d.kind,
                    d.identity
                        .data_in(&p.keys, d.verification.as_ref())
                        .unwrap(),
                    &d.message,
                    &d.primary,
                    &d.related
                ))
                .collect::<Vec<_>>(),
            expected
                .diagnostics
                .iter()
                .map(|d| (
                    d.kind,
                    d.identity
                        .data_in(&p.keys, d.verification.as_ref())
                        .unwrap(),
                    &d.message,
                    &d.primary,
                    &d.related
                ))
                .collect::<Vec<_>>()
        );
    }
}

const PROGRAM: &str = "sort S; const a,b:S;
relation fixed(s:S); fixed(a); relation absent(s:S); absent(X):-fixed(X),!fixed(X);
input i(s:S) within fixed;
relation r(s:S); r(X):-i(X); r(b):-!i(a);
assumption none:empty(i); assumption impossible:empty(fixed);
obligation empty_r:empty(r); obligation unique_r:at_most_one(r,group_by:());
obligation covered:at_least_one(fixed,group_by:s); obligation exactly:exactly_one(r,group_by:());
relation n(); n():-r(a); notice condition:varies(n);
verification first{assumptions:[];obligations:[empty_r];}
verification second{assumptions:[];obligations:[unique_r,covered,exactly];notices:[condition];}
verification third{assumptions:[none];obligations:[empty_r,exactly];notices:[condition];}
verification consistency{assumptions:[];obligations:[];}
verification inconsistent{assumptions:[impossible];obligations:[empty_r];}";

#[test]
fn selections_stay_separate_and_current_across_edits() {
    let mut session = Session::default();
    for (step, (uri, text)) in [
        ("file:///program.den", PROGRAM.to_owned()),
        (
            "file:///moved.den",
            format!("// trivia and a move\n\n{PROGRAM}"),
        ),
        (
            "file:///moved.den",
            PROGRAM.replace("const a,b:S", "const b,a:S"),
        ),
        // Same fixed projection, different input-dependent behavior.
        (
            "file:///moved.den",
            PROGRAM.replace("r(b):-!i(a)", "r(b):-i(a)"),
        ),
        (
            "file:///moved.den",
            PROGRAM.replace("fixed(a);", "fixed(b);"),
        ),
        (
            "file:///moved.den",
            PROGRAM
                .replace("relation fixed(s:S); fixed(a);", "input fixed(s:S);")
                .replace(" within fixed", ""),
        ),
        ("file:///moved.den", PROGRAM.to_owned()),
    ]
    .into_iter()
    .enumerate()
    {
        let p = parse(uri, &text);
        let before = session.fixed_stats();
        compare(&p, &mut session);
        if (1..=3).contains(&step) {
            assert_eq!(
                session.fixed_stats().executed,
                before.executed,
                "trivia, arena order and residual rules do not invalidate fixed facts"
            );
            assert!(session.fixed_stats().reused > before.reused);
        }
        compare(&p, &mut session);
        compare(&p, &mut Session::default());
    }
    assert!(session.fixed_stats().reused > 0);
}

#[test]
fn fold_failure_eviction_and_bypass_recover() {
    let p = parse("file:///program.den", PROGRAM);
    let mut session = Session::default();
    let limits = Limits::default();
    compare(&p, &mut session);
    let exhausted = Limits {
        max_atoms: 0,
        ..limits.clone()
    };
    assert!(matches!(
        session.prepare_fixed(&p.corpus, &p.keys, &p.domains, &exhausted),
        Err(CheckError::LimitExceeded { .. })
    ));
    assert_eq!(session.fixed_stats().retained_bytes, 0);
    compare(&p, &mut session);
    let cancelled = limits.clone();
    cancelled.cancellation.cancel();
    assert!(matches!(
        session.prepare_fixed(&p.corpus, &p.keys, &p.domains, &cancelled),
        Err(CheckError::Cancelled)
    ));
    assert_eq!(session.fixed_stats().retained_bytes, 0);
    compare(&p, &mut session);
    let expired = Limits {
        timeout: std::time::Duration::ZERO,
        ..Limits::default()
    };
    assert!(matches!(
        session.prepare_fixed(&p.corpus, &p.keys, &p.domains, &expired),
        Err(CheckError::Deadline { .. })
    ));
    assert_eq!(session.fixed_stats().retained_bytes, 0);
    compare(&p, &mut session);
    session.evict_values();
    assert_eq!(session.fixed_stats().retained_bytes, 0);
    compare(&p, &mut session);
    session.reset();
    assert_eq!(session.fixed_stats().retained_bytes, 0);
    compare(&p, &mut session);
    let mut bypass = Session::new(Retention {
        max_entries: 0,
        max_bytes: 0,
        max_condition_nodes: 0,
    });
    compare(&p, &mut bypass);
    compare(&p, &mut bypass);
    assert_eq!(bypass.fixed_stats().retained_bytes, 0);
    assert!(bypass.fixed_stats().bypassed > 0);
}

#[test]
fn fixed_false_negation_and_blocked_recursion_keep_their_evidence() {
    for rules in [
        "relation truth(); truth(); relation absent(); absent():-!truth(); relation r(); r():-!absent();",
        "relation truth(); truth(); relation f(); f():-!truth(); relation r(); r():-f(),!s(); relation s(); s():-!r();",
        "relation r(); relation s(); r():-s(); s():-r();",
    ] {
        let p = parse(
            "file:///evidence.den",
            &format!(
                "{rules} obligation o:empty(r); notice n:varies(r); verification v{{assumptions:[];obligations:[o];notices:[n];}}"
            ),
        );
        let mut session = Session::default();
        compare(&p, &mut session);
        compare(&p, &mut session);
    }
}

#[test]
fn shared_preparation_keeps_example_policy_and_operational_interruptions_local() {
    let p = parse(
        "file:///examples.den",
        "sort S; const a,b,c,d:S; relation r(s:S); r(a); r(b); r(c); r(d); obligation o:empty(r); verification v{assumptions:[];obligations:[o];}",
    );
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let mut session = Session::default();
    let fixed = session
        .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
        .unwrap();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    for (policy, count) in [
        (EmptinessExamples::Limited(1.try_into().unwrap()), 1),
        (EmptinessExamples::All, 4),
    ] {
        let RequestPreparation::Complete(prepared) = session
            .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
            .unwrap()
        else {
            panic!()
        };
        let prepared = prepared
            .admit(&ops)
            .unwrap()
            .with_emptiness_examples(policy);
        let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
            panic!()
        };
        let finding = report
            .checked
            .results
            .value
            .emptiness
            .values()
            .next()
            .unwrap();
        assert!(finding.complete());
        assert_eq!(finding.present, 4);
        assert_eq!(finding.examples.len(), count);
    }
    let expired = OperationalLimits {
        timeout: std::time::Duration::ZERO,
        ..ops.clone()
    };
    assert!(matches!(
        session.prepare_with_fixed(&request, &p.corpus, &p.keys, &expired, &fixed),
        Err(CheckError::Deadline { .. })
    ));
    let RequestPreparation::Complete(prepared) = session
        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!()
    };
    assert!(matches!(
        prepared.admit(&expired),
        Err(CheckError::Deadline { .. })
    ));
    let mut forged = request.clone();
    forged.obligations.clear();
    assert!(matches!(
        session.prepare_with_fixed(&forged, &p.corpus, &p.keys, &ops, &fixed),
        Err(CheckError::InvalidRequest(_))
    ));
    compare(&p, &mut session);
}
