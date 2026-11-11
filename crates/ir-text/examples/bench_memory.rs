//! Streaming memory profile; abstract fixed tables plus input-dependent cycles.
use denotate_check::*;
use denotate_check_session::{
    Retention, Session,
    profiling::{MemoryEvent, MemoryProfiler, process_memory},
};
use denotate_ir_text::*;
use serde_json::{Value, json};
use std::{io::Write, result::Result, time::Duration};

#[derive(Debug)]
struct Shape {
    items: usize,
    inputs: usize,
    width: usize,
    layers: usize,
    verifications: usize,
}
impl Default for Shape {
    fn default() -> Self {
        Self {
            items: 200,
            inputs: 200,
            width: 4,
            layers: 28,
            verifications: 1,
        }
    }
}
fn source(s: &Shape) -> String {
    let mut t = String::from(
        "sort Item; sort Signal; sort Lane; const a,b,c:Lane; relation item(x:Item); relation lane(l:Lane); lane(a);lane(b);lane(c); relation same(x:Item,y:Item); relation link(x:Item,y:Signal); input bit(y:Signal);\n",
    );
    for i in 0..s.inputs {
        t.push_str(&format!("const s{i}:Signal;\n"));
    }
    for i in 0..s.items {
        t.push_str(&format!("const k{i}:Item; item(k{i}); same(k{i},k{i});\n"));
        for w in 0..s.width {
            t.push_str(&format!("link(k{i},s{});\n", (i + w) % s.inputs));
        }
    }
    for i in 0..s.layers {
        t.push_str(&format!("relation f{i}(x:Item,l:Lane);\n"));
    }
    t.push_str("f0(X,L):-item(X),same(X,Y),item(Y),lane(L);\n");
    for i in 1..s.layers {
        // Roughly half the possible fixed tuples are false; retain multiple
        // producers per head, as in the measured inventory. Joins stay bounded
        // by the authored same relation rather than an uncontrolled product.
        let negative = if i > 2 && i % 2 == 1 { ",!f0(X,L)" } else { "" };
        t.push_str(&format!(
            "f{i}(X,L):-f0(X,L),item(X),same(X,Y),item(Y){negative};\nf{i}(X,L):-f0(X,L),item(X),lane(L),same(X,X){negative};\n"
        ));
    }
    t.push_str("f1(X,L):-f2(X,L); relation off(x:Item,l:Lane); off(X,L):-f2(X,L),!f0(X,L);\n");
    t.push_str("relation gate(x:Item); gate(X):-link(X,Y),bit(Y); relation left(x:Item); relation right(x:Item); left(X):-gate(X),!right(X); right(X):-item(X),!gate(X),!left(X);\n");
    t.push_str("relation pass(x:Item); relation again(x:Item); pass(X):-gate(X); pass(X):-again(X); again(X):-pass(X);\n");
    for i in 0..5 {
        t.push_str(&format!(
            "relation r{i}(x:Item); r{i}(X):-{}(X),item(X);\n",
            if i == 0 {
                "pass".into()
            } else {
                format!("r{}", i - 1)
            }
        ));
    }
    t.push_str("relation error(x:Item); error(X):-left(X),right(X); error(X):-off(X,L),r4(X); obligation clean:empty(error);\n");
    for i in 0..s.verifications {
        t.push_str(&format!(
            "verification v{i}{{assumptions:[];obligations:[clean];}}\n"
        ));
    }
    t
}
fn emit(v: Value) {
    let mut out = std::io::stdout().lock();
    let _ = writeln!(out, "{v}");
    let _ = out.flush();
}
fn event(e: MemoryEvent) {
    emit(e.data());
}
fn main() {
    let mut shape = Shape::default();
    let mut warm = false;
    let mut folded = true;
    let mut retained = true;
    let mut timeout_ms = 120_000;
    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        let target = match flag.as_str() {
            "--items" => &mut shape.items,
            "--inputs" => &mut shape.inputs,
            "--width" => &mut shape.width,
            "--layers" => &mut shape.layers,
            "--verifications" => &mut shape.verifications,
            "--timeout-ms" => &mut timeout_ms,
            "--warm" => {
                warm = true;
                continue;
            }
            "--unfolded" => {
                folded = false;
                continue;
            }
            "--no-retention" => {
                retained = false;
                continue;
            }
            "--help" => {
                println!(
                    "bench_memory [--items 200] [--inputs 200] [--width 4] [--layers 28] [--verifications 1] [--timeout-ms 120000] [--warm] [--unfolded] [--no-retention]\nJSON lines stream to stdout. Logical limits are checker defaults x100. Memory is sampled every 20ms; unavailable metrics are null."
                );
                return;
            }
            _ => panic!("unknown argument {flag}"),
        };
        *target = args
            .next()
            .expect("missing value")
            .parse()
            .expect("expected unsigned integer");
    }
    assert!(
        shape.items > 0
            && shape.inputs > 0
            && shape.inputs < 65534
            && shape.width > 0
            && shape.width <= shape.inputs
            && shape.layers >= 3
            && shape.verifications > 0
    );
    let monitor = MemoryProfiler::new(event);
    let d = Limits::default();
    let limits = Limits {
        profile: monitor.profile.clone(),
        timeout: Duration::from_millis(timeout_ms as u64),
        max_atoms: d.max_atoms * 100,
        max_rules: d.max_rules * 100,
        max_dependencies: d.max_dependencies * 100,
        max_work: d.max_work * 100,
        max_bdd_variables: d.max_bdd_variables * 100,
        max_bdd_nodes: d.max_bdd_nodes * 100,
        max_bdd_tasks: d.max_bdd_tasks * 100,
        max_condition_nodes: d.max_condition_nodes * 100,
        ..d
    };
    emit(
        json!({"type":"configuration","items":shape.items,"inputs":shape.inputs,"width":shape.width,"fixedLayers":shape.layers,
        "verifications":shape.verifications,"folded":folded,"retention":retained,"warm":warm,"timeoutMs":timeout_ms,
        "limits":{"atoms":limits.max_atoms,"rules":limits.max_rules,"dependencies":limits.max_dependencies,"work":limits.max_work,
        "bddVariables":limits.max_bdd_variables,"bddNodes":limits.max_bdd_nodes,"bddTasks":limits.max_bdd_tasks,"conditionNodes":limits.max_condition_nodes}}),
    );
    let text = source(&shape);
    let mut session = if retained {
        Session::default()
    } else {
        Session::new(Retention {
            max_entries: 0,
            ..Default::default()
        })
    };
    let mut controls = Vec::new();
    for run in 0..if warm { 2 } else { 1 } {
        emit(json!({"type":"run","run":run,"memory":process_memory()}));
        match run_check(&text, &limits, &mut session, folded) {
            Ok(outcomes) => {
                if run == 0 {
                    controls = outcomes.clone();
                } else {
                    assert_eq!(controls, outcomes);
                }
                emit(
                    json!({"type":"result","run":run,"outcomes":outcomes,"memory":process_memory(),
                    "fixedCache":{"executed":session.fixed_stats().executed,"reused":session.fixed_stats().reused,"retainedBytes":session.fixed_stats().retained_bytes}}),
                );
                if outcomes.iter().any(|s| s["state"] != "proved") {
                    std::process::exit(2);
                }
            }
            Err(e) => {
                emit(
                    json!({"type":"stopped","run":run,"error":format!("{e}"),"memory":process_memory()}),
                );
                std::process::exit(2);
            }
        }
    }
}
fn run_check(
    text: &str,
    limits: &Limits,
    session: &mut Session,
    folded: bool,
) -> Result<Vec<Value>, CheckError> {
    let p = {
        let _span = limits.profile.span("loading", None);
        let file = SourceFile::new("file:///memory.den", 1, text);
        load(
            &ProgramMembership::single("memory", [file.uri.clone()]),
            &[file],
        )
        .expect("generated source loads")
    };
    let validated = {
        let _span = limits.profile.span("assumption-validation", None);
        validate_assumption_cones_for_run(&p.corpus, &p.domains, &p.keys, limits)?
    };
    let fixed = if folded {
        Some(session.prepare_fixed_with_validation(&validated, limits)?)
    } else {
        None
    };
    let mut outcomes = Vec::new();
    for (_, request) in p.verification_requests(limits)? {
        let ops = limits.into();
        let prepared = if let Some(fixed) = &fixed {
            session.prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, fixed)?
        } else {
            session.prepare(&request, &p.corpus, &p.keys, &ops)?
        };
        let RequestPreparation::Complete(prepared) = prepared else {
            let RequestPreparation::Inconclusive { reason, .. } = prepared else {
                unreachable!()
            };
            return Err(reason.into());
        };
        let (atoms, rules, components) = prepared.program().residual_size();
        let (fixed_atoms, present, fixed_rules, fixed_components, dependencies) =
            prepared.program().fixed_size();
        emit(
            json!({"type":"size","residual":{"atoms":atoms,"rules":rules,"components":components},
            "fixed":{"atoms":fixed_atoms,"present":present,"rules":fixed_rules,"components":fixed_components,"dependencies":dependencies},
            "retainedBytes":session.fixed_stats().retained_bytes,"memory":process_memory()}),
        );
        let prepared = {
            let _span = limits.profile.span("admission", None);
            prepared.admit(&ops)?
        };
        let _span = limits.profile.span("checking", None);
        match session.verify(&prepared, &ops)? {
            LocalCheckOutcome::Complete(report) => {
                let summary = denotate_presentation::summary(&report.checked.results.value);
                outcomes.push(summary);
            }
            LocalCheckOutcome::Inconclusive { reason, .. } => return Err(reason.into()),
        }
    }
    Ok(outcomes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};
    #[test]
    fn profiled_cold_warm_and_unfolded_outcomes_agree() {
        let text = source(&Shape {
            items: 4,
            inputs: 4,
            width: 2,
            layers: 3,
            verifications: 2,
        });
        let quiet = run_check(&text, &Limits::default(), &mut Session::default(), true).unwrap();
        assert!(quiet.iter().all(|s| s["state"] == "proved"));
        let events = Arc::new(Mutex::new(Vec::new()));
        let out = events.clone();
        let limits = Limits {
            profile: Profile::new(move |e| out.lock().unwrap().push(e)),
            ..Default::default()
        };
        let mut session = Session::default();
        for folded in [true, true, false] {
            assert_eq!(
                quiet,
                run_check(&text, &limits, &mut session, folded).unwrap()
            );
        }
        let events = events.lock().unwrap();
        for stage in [
            "fixed-evaluation",
            "fixed-export",
            "fixed-binding",
            "residual-preparation",
            "semantic-keys",
            "admission-symbolic",
            "admission-summaries",
            "admission-key-refresh",
        ] {
            assert!(
                events.iter().any(|e| e.stage == stage && e.finished),
                "{stage}"
            );
        }
        assert!(events.iter().any(|e| e.bdd_result_nodes > 0));
        assert!(
            events
                .iter()
                .any(|e| e.retained.is_some_and(|s| s.references > s.distinct_arrays))
        );
    }
    #[test]
    fn exhausted_profile_closes_spans_without_claiming_a_result() {
        let text = source(&Shape {
            items: 2,
            inputs: 2,
            width: 1,
            layers: 3,
            verifications: 1,
        });
        let events = Arc::new(Mutex::new(Vec::new()));
        let out = events.clone();
        let limits = Limits {
            max_atoms: 0,
            profile: Profile::new(move |e| out.lock().unwrap().push(e)),
            ..Default::default()
        };
        assert!(matches!(
            run_check(&text, &limits, &mut Session::default(), true),
            Err(CheckError::LimitExceeded { .. })
        ));
        let events = events.lock().unwrap();
        for start in events.iter().filter(|e| !e.finished) {
            assert!(events.iter().any(|e| e.id == start.id && e.finished));
        }
    }
}
