//! Abstract mostly-fixed workload. Counts/times are measurements, never goldens.
use denotate_check::*;
use denotate_check_session::{Retention, Session};
use denotate_ir_text::*;
use serde_json::json;
use std::time::{Duration, Instant};

fn main() {
    let mut args = std::env::args().skip(1);
    let n: usize = args
        .next()
        .expect("ITEMS [VERIFICATIONS=4] [--ground-assumption]")
        .parse()
        .unwrap();
    let verifications: usize = args.next().map(|n| n.parse().unwrap()).unwrap_or(4);
    let flags = args.collect::<Vec<_>>();
    assert!(flags.iter().all(|f| matches!(
        f.as_str(),
        "--ground-assumption" | "--two-selections" | "--no-retention"
    )));
    let ground_assumption = flags.iter().any(|f| f == "--ground-assumption");
    let two_selections = flags.iter().any(|f| f == "--two-selections");
    let retention_disabled = flags.iter().any(|f| f == "--no-retention");
    let new_session = || {
        if retention_disabled {
            Session::new(Retention {
                max_entries: 0,
                max_bytes: 0,
                max_condition_nodes: 0,
            })
        } else {
            Session::default()
        }
    };
    assert!(n > 0 && verifications > 0);
    let mut source = String::from(
        "sort S; relation item(s:S); relation tagged(s:S); relation off(s:S); input flag(); relation error(s:S); relation left(); relation right();\n",
    );
    for i in 0..n {
        source.push_str(&format!("const k{i}:S; item(k{i});\n"));
    }
    source.push_str("tagged(X):-item(X); off(X):-item(X),!tagged(X); error(X):-off(X),flag(); left():-flag(),!right(); right():-!flag(),!left(); assumption fixed_absence:empty(off); obligation clean:empty(error);\n");
    if ground_assumption {
        // Relation-level negation cycle, stratified after grounding. Exercises
        // both ground-validation entry points without changing the obligation.
        source.push_str("sort Side; const a,b:Side; input present(s:Side); relation guarded(s:Side); guarded(a); relation gives(s:Side); gives(b); relation holds(s:Side); holds(X):-present(X); holds(X):-guarded(X),!supplied(X); relation supplied(s:Side); supplied(X):-gives(X),!holds(X); relation broken(); broken():-!holds(a); assumption valid:empty(broken);\n");
    }
    if two_selections {
        source.push_str("assumption fixed_coverage:at_least_one(item,group_by:());\n");
    }
    for i in 0..verifications {
        source.push_str(&format!(
            "verification v{i}{{assumptions:[{}{}];obligations:[clean];}}\n",
            if two_selections && i % 2 == 1 {
                "fixed_coverage"
            } else {
                "fixed_absence"
            },
            if ground_assumption { ",valid" } else { "" }
        ));
    }
    let limits = Limits {
        timeout: Duration::from_secs(120),
        ..Limits::default()
    };
    let operations = (&limits).into();
    let mut controls = Vec::new();
    let mut session = new_session();
    for (folded, warm, edited) in [
        (false, false, false),
        (true, false, false),
        (true, true, false),
        (true, true, true),
    ] {
        let text = if edited {
            source.replace("error(X):-off(X),flag()", "error(X):-off(X),!flag()")
        } else {
            source.clone()
        };
        let file = SourceFile::new("file:///benchmark.den", 1, text);
        let p = load(
            &ProgramMembership::single("benchmark", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let requests = p.verification_requests(&limits).unwrap();
        if !warm {
            session = new_session();
        }
        let start = Instant::now();
        let validated =
            validate_assumption_cones_using(&p.corpus, &p.domains, &p.keys, &limits, || {
                if folded {
                    session.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
                } else {
                    FixedPreparation::prepare(&p.corpus, &p.domains, &limits)
                }
            })
            .unwrap();
        assert!(validated.result().is_valid());
        let validation = start.elapsed();
        let start = Instant::now();
        let fixed = folded.then(|| {
            session
                .prepare_fixed_with_validation(&validated, &limits)
                .unwrap()
        });
        let fold = start.elapsed();
        let mut preparation = fold;
        let mut admission = Duration::ZERO;
        let mut checking = Duration::ZERO;
        let mut sizes = json!(null);
        for (i, (_, request)) in requests.iter().enumerate() {
            let start = Instant::now();
            let result = match &fixed {
                Some(fixed) => {
                    session.prepare_with_fixed(request, &p.corpus, &p.keys, &operations, fixed)
                }
                None => session.prepare(request, &p.corpus, &p.keys, &operations),
            }
            .unwrap();
            let RequestPreparation::Complete(prepared) = result else {
                panic!("preparation exhausted")
            };
            preparation += start.elapsed();
            let (atoms, rules, components) = prepared.program().residual_size();
            let (fixed_atoms, present, fixed_rules, fixed_components, dependencies) =
                prepared.program().fixed_size();
            sizes = json!({"residual":{"atoms":atoms,"rule_instances":rules,"components":components},
                "retained_fixed_evidence":{"atoms":fixed_atoms,"present_facts":present,"rule_instances":fixed_rules,"components":fixed_components,"dependencies":dependencies}});
            let start = Instant::now();
            let prepared = prepared.admit(&operations).unwrap();
            admission += start.elapsed();
            let start = Instant::now();
            let LocalCheckOutcome::Complete(report) =
                session.verify(&prepared, &operations).unwrap()
            else {
                panic!("checking exhausted")
            };
            checking += start.elapsed();
            let result = denotate_presentation::summary(&report.checked.results.value);
            assert_eq!(result["state"], "proved", "{result}");
            if folded {
                assert_eq!(result, controls[i]);
            } else {
                controls.push(result);
            }
        }
        println!(
            "{}",
            json!({"folded":folded,"warm":warm,"edited":edited,"two_selections":two_selections,"fixed_cache":{"executed":session.fixed_stats().executed,"reused":session.fixed_stats().reused,"bypassed":session.fixed_stats().bypassed,"retained_bytes":session.fixed_stats().retained_bytes},"items":n,"verifications":verifications,
            "retention_disabled":retention_disabled,"ground_assumption":ground_assumption,"validation_ms":validation.as_secs_f64()*1000.,
            "fixed_ms":fold.as_secs_f64()*1000., "preparation_ms":preparation.as_secs_f64()*1000.,
            "admission_ms":admission.as_secs_f64()*1000.,"checking_ms":checking.as_secs_f64()*1000.,"size":sizes})
        );
    }
}
