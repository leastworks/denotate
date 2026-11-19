//! Explicit CLI engine selection. No BDD admission or W construction on this path.
use super::*;
use denotate_check::stable_query::{CheckOptions, Engine, QueryLimits};

pub(super) fn run(
    p: &LoadedProgram,
    limits: &Limits,
    requests: &[(denotate_ir::VerificationKey, denotate_check::CheckRequest)],
    query: QueryLimits,
    mut check: CheckOptions,
    partial: bool,
    unchecked: bool,
    validate_all: bool,
    json: bool,
    verbose: bool,
    output: &mut String,
    trace: &trace::Trace,
    flush: &mut dyn FnMut(&mut String) -> Result<(), Failure>,
) -> Result<u8, Failure> {
    let mut incomplete = partial || unchecked;
    let mut failure = false;
    if validate_all {
        let validation =
            denotate_check::validate_assumption_cones(&p.corpus, &p.domains, &p.keys, limits)
                .map_err(checker_failure)?;
        let presented = presentation::present_assumption_validation(p, &validation)
            .map_err(|e| (2, e.to_string()))?;
        incomplete |= validation.has_failures();
        if json {
            writeln!(output, "Assumption validation: {:#}", presented.status).unwrap();
        } else {
            print_diagnostics(p, &presented, output, verbose)?;
        }
    }
    if requests.is_empty() {
        writeln!(output, "No verification configured").unwrap();
        return Ok(2);
    }
    let mut limits = limits.clone();
    let names = p
        .corpus
        .obligations()
        .map(|o| (o.id, o.name.clone()))
        .collect::<std::collections::BTreeMap<_, _>>();
    let observer = trace.clone();
    limits.progress = denotate_check::CheckingProgress::new(move |e| {
        if let Some(denotate_check::CheckingTarget::SatExistence(ref stats)) = e.target {
            observer.message(format!(
                "SAT existence {}: {}",
                e.state,
                denotate_presentation::stable_existence_stats(stats)
            ));
        }
        let target = match &e.target {
            Some(denotate_check::CheckingTarget::Obligation(id)) => {
                names.get(id).map(String::as_str).unwrap_or("obligation")
            }
            _ => "",
        };
        if !matches!(
            e.target,
            Some(denotate_check::CheckingTarget::SatExistence(_))
        ) {
            observer.message(format!("{} {}: {}", e.stage, target, e.state));
        }
        if let Some(error) = e.failure {
            observer.message(checker_failure(error).1);
        }
    });
    check.attribution.cancellation = limits.cancellation.clone();
    trace.message(format!("SAT limits: worlds={}, tuples={}, solves={}, refinements={}, polls={}, conflicts={}, propagations={}",check.max_worlds,check.max_tuples,query.max_solves,query.max_refinements,query.max_solver_polls,query.max_conflicts,query.max_propagations));
    for (i, (key, _)) in requests.iter().enumerate() {
        let v = p
            .corpus
            .verifications()
            .find(|v| p.keys.verification(v.id).is_ok_and(|k| k == key))
            .unwrap();
        let label = name(p.corpus.namespace(v.id).unwrap(), &v.name);
        writeln!(output, "Verification {label}").unwrap();
        writeln!(
            output,
            "Selected assumptions: {}",
            v.assumptions
                .iter()
                .map(|id| name(
                    p.corpus.namespace(*id).unwrap(),
                    &p.corpus.assumption(*id).unwrap().name
                ))
                .collect::<Vec<_>>()
                .join(", ")
        )
        .unwrap();
        trace.message(format!(
            "Verification {}/{}: {label}; SAT preparation",
            i + 1,
            requests.len()
        ));
        flush(output)?;
        let prepared =
            Engine::prepare(&p.corpus, &p.domains, &p.keys, v.id, &limits, query.clone());
        let mut engine = match prepared {
            Ok(e) => e,
            Err(e) => {
                let (_, text) = checker_failure(e);
                incomplete = true;
                if json {
                    writeln!(
                        output,
                        "Results: {}",
                        json!({"backend":{"backend":"sat"},"state":"incomplete","reason":text})
                    )
                    .unwrap();
                } else {
                    writeln!(output, "{text}").unwrap();
                }
                trace.message(text);
                flush(output)?;
                continue;
            }
        };
        trace.message(format!(
            "SAT checking: fixed obligations, empty, at_most_one; meaning mode {}",
            check.meaning.label()
        ));
        let report = engine.check(&p.keys, &check).map_err(checker_failure)?;
        let presented = presentation::present_stable(p, &report).map_err(|e| (2, e.to_string()))?;
        let s = &presented.status;
        incomplete |= s["incomplete"].as_bool().unwrap();
        failure |= s["hasFailures"].as_bool().unwrap();
        if json {
            writeln!(output, "Results: {s:#}").unwrap();
        } else {
            writeln!(
                output,
                "Context: {}",
                s["context"]["state"].as_str().unwrap()
            )
            .unwrap();
            if let Some(reason) = s["context"].get("reason") {
                writeln!(output, "  reason: {reason}").unwrap();
            }
            for phase in ["existence", "uniqueness"] {
                if let Some(m) = s["meaning"].get(phase) {
                    writeln!(
                        output,
                        "Meaning {phase} (whole program): {}",
                        m["state"].as_str().unwrap()
                    )
                    .unwrap();
                    if let Some(reason) = m.get("reason") {
                        writeln!(output, "  reason: {reason}").unwrap();
                    }
                }
            }
            if let Some(stats) = s["meaning"].get("existenceStats").filter(|v| !v.is_null()) {
                writeln!(output, "Existence search: {stats}").unwrap();
            }
            print_diagnostics(p, &presented, output, verbose)?;
            for o in s["obligations"].as_array().unwrap() {
                writeln!(
                    output,
                    "Obligation {} ({}): {}{}",
                    o["name"].as_str().unwrap(),
                    o["kind"].as_str().unwrap(),
                    o["state"].as_str().unwrap(),
                    if o["fixed"] == true { " [fixed]" } else { "" }
                )
                .unwrap();
                for reason in o["reasons"].as_array().unwrap() {
                    writeln!(output, "  reason: {reason}").unwrap();
                }
            }
            for n in s["notices"].as_array().unwrap() {
                writeln!(
                    output,
                    "Notice {}: not analysed by the SAT engine",
                    n["name"].as_str().unwrap()
                )
                .unwrap();
            }
            writeln!(output, "Result: {}", s["state"].as_str().unwrap()).unwrap();
        }
        trace.message(format!(
            "SAT result for {label}: {}; {} findings",
            s["state"].as_str().unwrap(),
            presented.diagnostics.len()
        ));
        flush(output)?;
    }
    Ok(if incomplete {
        2
    } else if failure {
        1
    } else {
        0
    })
}
