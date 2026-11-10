use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;
use denotate_presentation::{Diagnostic, Kind};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

const DECLARATIONS: &str = "namespace 'odd-space'; sort S; const 'F2', 'F3':S; relation eligible(x:S); eligible('F2'); eligible('F3'); relation p(x:S); relation q(x:S); relation bridge(x:S);";
const UNSUPPORTED: &str = "p(X):-eligible(X),!q(X); q(X):-bridge(X); bridge(X):-eligible(X),!p(X);";
const VERIFY: &str = "relation clear(); obligation independent:empty(clear); verification checks { assumptions:[]; obligations:[independent]; }";

fn program(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///cycles.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn checked<T>(
    p: &LoadedProgram,
    session: &mut Session,
    f: impl FnOnce(&CheckedReport<'_>) -> T,
) -> T {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
        panic!()
    };
    f(&report.checked)
}
fn cycle_notes(d: &Diagnostic) -> Vec<&str> {
    d.notes
        .iter()
        .filter(|n| n.starts_with("Ground dependency cycle "))
        .map(String::as_str)
        .collect()
}
fn closed_cycle(cycle: &Value) {
    let edges = cycle.as_array().unwrap();
    assert!(!edges.is_empty());
    assert!(edges.iter().any(|e| e["polarity"] == "negative"));
    for (edge, next) in edges.iter().zip(edges.iter().cycle().skip(1)) {
        assert_eq!(edge["provider"], next["consumer"]);
    }
}
fn instance(p: &LoadedProgram, cycle: &Value) -> String {
    closed_cycle(cycle);
    let names = cycle
        .as_array()
        .unwrap()
        .iter()
        .map(|e| e["consumer"]["arguments"][0]["name"].as_str().unwrap())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        names.len(),
        1,
        "cycle must not combine different ground instances"
    );
    p.corpus
        .constants()
        .find(|c| p.keys.constant(c.id).unwrap().name.as_ref() == *names.first().unwrap())
        .unwrap()
        .name
        .clone()
}

#[test]
fn generic_rules_report_separate_concrete_cycles_with_both_edge_polarities() {
    let p = program(&format!("{DECLARATIONS}{UNSUPPORTED}{VERIFY}"));
    checked(&p, &mut Session::default(), |report| {
        let out = presentation::present(&p, report).unwrap();
        let mut instances = BTreeSet::new();
        for d in out
            .diagnostics
            .iter()
            .filter(|d| d.kind == Kind::UnsupportedRegion)
        {
            let cycles = d.evidence["cycles"].as_array().unwrap();
            assert_eq!(cycles.len(), 1);
            let name = instance(&p, &cycles[0]);
            assert!(
                cycles[0]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|e| e["polarity"] == "positive")
            );
            let notes = cycle_notes(d);
            assert_eq!(notes.len(), 1);
            assert!(notes[0].contains(&format!("'odd-space'::p('odd-space'::'{name}')")));
            assert!(notes[0].contains(" -not-> ") && notes[0].contains(" -> "));
            let other = if name == "F2" { "F3" } else { "F2" };
            assert!(!notes[0].contains(other));
            assert!(
                !d.notes
                    .iter()
                    .any(|n| n.starts_with("Example input observation"))
            );
            instances.insert(name);
        }
        assert_eq!(instances, BTreeSet::from(["F2".into(), "F3".into()]));
        assert!(report.results.value.emptiness.values().all(|r| r.proved()));
    });
}

#[test]
fn no_meaning_keeps_the_observation_separate_from_its_structural_cycle() {
    let p = program(&format!(
        "{DECLARATIONS} input enabled(x:S); p(X):-eligible(X),enabled(X),!p(X); {VERIFY}"
    ));
    checked(&p, &mut Session::default(), |report| {
        let out = presentation::present(&p, report).unwrap();
        let mut instances = BTreeSet::new();
        for d in out.diagnostics.iter().filter(|d| d.kind == Kind::NoMeaning) {
            let cycle = &d.evidence["cycles"][0];
            let name = instance(&p, cycle);
            let notes = cycle_notes(d);
            assert_eq!(notes.len(), 1);
            assert!(notes[0].contains(&format!("p('odd-space'::'{name}')")));
            assert!(!notes[0].contains("enabled"));
            assert!(
                d.notes
                    .iter()
                    .any(|n| n.starts_with("Example input observation") && n.contains("enabled"))
            );
            assert_eq!(d.evidence["kind"], "no-meaning-observation");
            assert!(
                d.evidence["observation"]["present"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|a| a["arguments"][0] == cycle[0]["consumer"]["arguments"][0])
            );
            instances.insert(name);
        }
        assert_eq!(instances, BTreeSet::from(["F2".into(), "F3".into()]));
    });
}

#[test]
fn warm_edits_clear_only_the_removed_instance_and_rebind_remaining_cycles() {
    let mut session = Session::with_grounding();
    let mut before = None;
    for remove in [false, true, false] {
        let text = format!("{DECLARATIONS}{UNSUPPORTED}{VERIFY}");
        let text = if remove {
            text.replace("eligible('F2');", "")
        } else {
            text
        };
        let p = program(&text);
        let snapshot = |report: &CheckedReport<'_>| {
            let out = presentation::present(&p, report).unwrap();
            let traces = out
                .diagnostics
                .iter()
                .filter(|d| d.kind == Kind::UnsupportedRegion)
                .map(|d| {
                    let name = instance(&p, &d.evidence["cycles"][0]);
                    (
                        name,
                        (
                            d.identity.data(&p.keys).unwrap(),
                            d.evidence["cycles"].clone(),
                            cycle_notes(d)
                                .into_iter()
                                .map(str::to_owned)
                                .collect::<Vec<_>>(),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            (report.results.value.clone(), traces)
        };
        let warm = checked(&p, &mut session, &snapshot);
        let cold = checked(&p, &mut Session::default(), &snapshot);
        assert_eq!(warm, cold);
        assert_eq!(warm.1.contains_key("F2"), !remove);
        let remaining = &warm.1["F3"];
        if let Some(before) = &before {
            assert_eq!(remaining, before);
        }
        before = Some(remaining.clone());
    }
}

#[test]
fn displayed_names_do_not_change_identity_or_structured_cycle_evidence() {
    let p = program(&format!("{DECLARATIONS}{UNSUPPORTED}{VERIFY}"));
    checked(&p, &mut Session::default(), |report| {
        let names = presentation::diagnostic_names(&p.corpus);
        let findings =
            denotate_presentation::interpret(&p.corpus, &report.verification, &names).unwrap();
        for f in findings
            .iter()
            .filter(|f| f.kind == Kind::UnsupportedRegion)
        {
            let before = (
                f.identity.data(&p.keys).unwrap(),
                denotate_presentation::evidence_data(f, &p.keys).unwrap(),
            );
            let actual = denotate_presentation::generic_details(&p.corpus, f, &names).unwrap();
            let renamed =
                denotate_presentation::generic_details(&p.corpus, f, &|_| "different".into())
                    .unwrap();
            assert_ne!(actual, renamed);
            assert_eq!(
                before,
                (
                    f.identity.data(&p.keys).unwrap(),
                    denotate_presentation::evidence_data(f, &p.keys).unwrap()
                )
            );
        }
    });
}

#[test]
fn invalid_assumptions_show_all_retained_cycles_and_keep_helper_names_distinct() {
    let p = program(&format!(
        "{DECLARATIONS}{UNSUPPORTED} assumption invalid:empty(p);"
    ));
    let validation =
        validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &Limits::default()).unwrap();
    let out = presentation::present_assumption_validation(&p, &validation).unwrap();
    assert_eq!(out.diagnostics.len(), 1);
    let d = &out.diagnostics[0];
    assert_eq!(d.kind, Kind::InvalidAssumption);
    assert_eq!(cycle_notes(d).len(), 2);
    assert_eq!(
        d.evidence["cycles"]
            .as_array()
            .unwrap()
            .iter()
            .map(|c| instance(&p, c))
            .collect::<BTreeSet<_>>(),
        BTreeSet::from(["F2".into(), "F3".into()])
    );
    for name in ["F2", "F3"] {
        assert!(
            cycle_notes(d)
                .iter()
                .any(|n| n.contains(&format!("'odd-space'::p('odd-space'::'{name}')")))
        );
    }
    let p = program(
        "namespace 'odd-space' { relation $helper(); relation '$helper'(); $helper():-!'$helper'(); '$helper'():-$helper(); assumption invalid:empty($helper); }",
    );
    let validation =
        validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &Limits::default()).unwrap();
    let out = presentation::present_assumption_validation(&p, &validation).unwrap();
    let note = cycle_notes(&out.diagnostics[0])[0];
    assert!(note.contains("'odd-space'::$helper()"), "{note}");
    assert!(note.contains("'odd-space'::'$helper'()"), "{note}");
}
