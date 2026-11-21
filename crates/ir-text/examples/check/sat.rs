//! Explicit CLI engine selection. No BDD admission or W construction on this path.
use super::*;
use denotate_check::stable_query::{
    CheckOptions, Engine, MeaningMode, PreparationScope, QueryLimits,
};

pub(super) fn run(
    p: &LoadedProgram,
    limits: &Limits,
    requests: &[(denotate_ir::VerificationKey, denotate_check::CheckRequest)],
    query: QueryLimits,
    mut check: CheckOptions,
    circular_support: bool,
    dump: &mut Option<component_dump::Dump>,
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
    if validate_all
        || requests
            .iter()
            .any(|(_, r)| r.semantics == denotate_ir::Semantics::Completion)
    {
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
        if let Some(denotate_check::CheckingTarget::SatUniqueness(ref stats)) = e.target {
            observer.message(format!(
                "SAT uniqueness {}: {}",
                e.state,
                denotate_presentation::stable_uniqueness_stats(stats)
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
            Some(
                denotate_check::CheckingTarget::SatExistence(_)
                    | denotate_check::CheckingTarget::SatUniqueness(_)
            )
        ) {
            observer.message(format!("{} {}: {}", e.stage, target, e.state));
        }
        if let Some(error) = e.failure {
            observer.message(checker_failure(error).1);
        }
    });
    check.attribution.cancellation = limits.cancellation.clone();
    trace.message(format!("SAT limits: worlds={}, tuples={}, solves={}, refinements={}, polls={}, conflicts={}, propagations={}",check.max_worlds,check.max_tuples,query.max_solves,query.max_refinements,query.max_solver_polls,query.max_conflicts,query.max_propagations));
    for (i, (key, request)) in requests.iter().enumerate() {
        let v = p
            .corpus
            .verifications()
            .find(|v| p.keys.verification(v.id).is_ok_and(|k| k == key))
            .unwrap();
        let label = name(p.corpus.namespace(v.id).unwrap(), &v.name);
        writeln!(output, "Verification {label}").unwrap();
        if v.options.semantics == denotate_ir::Semantics::Completion {
            let (inc, failed) = completion(
                p,
                v,
                &limits,
                &query,
                &check,
                circular_support,
                json,
                verbose,
                output,
            )?;
            incomplete |= inc;
            failure |= failed;
            flush(output)?;
            continue;
        }
        if let Some(reason) = request.unsupported_semantics() {
            let shown = presentation::unsupported_semantics(p, v.id, reason)
                .map_err(|e| (2, e.to_string()))?;
            if json {
                writeln!(output, "Results: {}", shown.status).unwrap();
            } else {
                print_diagnostics(p, &shown, output, verbose)?;
            }
            incomplete = true;
            flush(output)?;
            continue;
        }
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
        let prepared = Engine::prepare_scoped(
            &p.corpus,
            &p.domains,
            &p.keys,
            v.id,
            &limits,
            query.clone(),
            if check.meaning == MeaningMode::Cone {
                PreparationScope::ObligationCones
            } else {
                PreparationScope::WholeProgram
            },
        );
        let mut engine = match prepared {
            Ok(e) => e,
            Err(e) => {
                let (_, text) = checker_failure(e);
                incomplete = true;
                if json {
                    writeln!(
                        output,
                        "Results: {}",
                        json!({"backend":{"backend":"sat"},"state":"incomplete","reason":text,"meaning":{"state":"not-analysed","scope":if check.meaning == MeaningMode::Cone {"obligation-cones"} else {"whole-program"}}})
                    )
                    .unwrap();
                } else {
                    writeln!(output, "{text}").unwrap();
                    if check.meaning == MeaningMode::Cone {
                        writeln!(
                            output,
                            "Obligation cones: preparation incomplete; outside not analysed"
                        )
                        .unwrap();
                    }
                }
                trace.message(text);
                flush(output)?;
                continue;
            }
        };
        let inventory = inventory(&engine, p, &limits)?;
        if json {
            writeln!(output, "Negative components: {inventory:#}").unwrap();
        } else {
            print_inventory(&inventory, output);
        }
        if let Some(dump) = dump {
            dump.capture_sat(p, v, &engine);
        }
        flush(output)?;
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
            writeln!(
                output,
                "Input pins: {} proved, {} attempted, {} unknown{}",
                report.pins.proved,
                report.pins.attempted,
                report.pins.unknown,
                if report.pins.truncated {
                    " (candidate limit)"
                } else {
                    ""
                }
            )
            .unwrap();
            if let Some(split) = s["meaning"].get("split").filter(|s| !s.is_null()) {
                writeln!(output, "Meaning split: {}", split).unwrap();
            }
            for phase in ["existence", "uniqueness"] {
                if let Some(m) = s["meaning"].get(phase) {
                    writeln!(
                        output,
                        "Meaning {phase} ({}): {}",
                        s["meaning"]["scope"]
                            .as_str()
                            .unwrap_or("not analysed")
                            .replace('-', " "),
                        m["state"].as_str().unwrap()
                    )
                    .unwrap();
                    if let Some(reason) = m.get("reason") {
                        writeln!(output, "  reason: {reason}").unwrap();
                    }
                }
            }
            if let Some(size) = s["meaning"].get("coneSize").filter(|v| !v.is_null()) {
                writeln!(
                    output,
                    "Obligation cones: {} atoms, {} rule instances; outside not analysed",
                    size["atoms"], size["ruleInstances"]
                )
                .unwrap();
            }
            if let Some(stats) = s["meaning"].get("existenceStats").filter(|v| !v.is_null()) {
                writeln!(output, "Existence search: {stats}").unwrap();
            }
            if let Some(stats) = s
                .get("meaning")
                .and_then(|m| m.get("uniquenessStats"))
                .filter(|s| !s.is_null())
            {
                writeln!(output, "Uniqueness search: {stats}").unwrap();
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

fn completion(
    p: &LoadedProgram,
    v: &denotate_ir::VerificationDeclaration,
    limits: &Limits,
    query: &QueryLimits,
    check: &CheckOptions,
    circular_support: bool,
    json: bool,
    verbose: bool,
    output: &mut String,
) -> Result<(bool, bool), Failure> {
    use denotate_check::completion_query as cq;
    writeln!(output, "Semantics: completion").unwrap();
    if let Some(h) = v.options.hypothesis {
        writeln!(
            output,
            "Hypothesis: {}",
            presentation::diagnostic_names(&p.corpus)(h.into())
        )
        .unwrap();
    }
    let refusal = if check.meaning != MeaningMode::Full {
        Some("completion supports full meaning analysis only")
    } else if check.splits.relation.is_some() {
        Some("completion does not support SAT split hints")
    } else {
        None
    };
    let mut problem = refusal.map(str::to_owned);
    let mut prepared = None;
    let mut compatibility = None;
    let mut exhausted = None;
    if problem.is_none() {
        match cq::Engine::prepare(
            &p.corpus,
            &p.domains,
            &p.keys,
            v.id,
            limits,
            cq::QueryLimits {
                max_solves: query.max_solves,
                max_solver_polls: query.max_solver_polls,
                max_conflicts: query.max_conflicts,
                max_propagations: query.max_propagations,
            },
        ) {
            Ok(cq::Preparation::Ready(e)) => prepared = Some(e),
            Ok(cq::Preparation::Unsupported(issue)) => {
                let relation = p
                    .corpus
                    .relations()
                    .find(|r| p.keys.relation(r.id).is_ok_and(|k| k == &issue.relation))
                    .unwrap();
                problem = Some(format!(
                    "Completion compatibility: {} has a recursive assumption or input-domain cone; this increment requires an acyclic cone.",
                    relation.name
                ));
                compatibility = Some(issue);
            }
            Ok(cq::Preparation::Inconclusive(c)) => {
                exhausted = Some(c);
                problem = Some(denotate_presentation::exhaustion_text(
                    c.phase, c.resource, c.details,
                ))
            }
            Err(
                e @ (denotate_check::CheckError::Internal(_)
                | denotate_check::CheckError::Cancelled),
            ) => return Err((3, e.to_string())),
            Err(e) => problem = Some(checker_failure(e).1),
        }
    }
    if let Some(problem) = problem {
        let shown = presentation::completion_preparation_failure(
            p,
            v.id,
            compatibility.as_ref(),
            exhausted,
            &problem,
        )
        .map_err(|e| (2, e.to_string()))?;
        if json {
            writeln!(output, "Results: {}", shown.status).unwrap();
        } else {
            print_diagnostics(p, &shown, output, verbose)?;
        }
        return Ok((true, false));
    }
    let options = cq::CheckOptions {
        meaning: check.meaning,
        max_worlds: check.max_worlds,
        max_tuples: check.max_tuples,
        max_examples: match check.examples {
            denotate_check::EmptinessExamples::Limited(n) => n.get(),
            denotate_check::EmptinessExamples::All => usize::MAX,
        },
        circular_support,
        advisory_limits: check.attribution.clone(),
    };
    let report = prepared
        .unwrap()
        .check(&p.keys, &options)
        .map_err(|e| match e {
            e @ (CheckError::Internal(_) | CheckError::Cancelled) => (3, e.to_string()),
            e => checker_failure(e),
        })?;
    let shown = presentation::present_completion(p, &report).map_err(|e| (2, e.to_string()))?;
    let s = &shown.status;
    if json {
        writeln!(output, "Results: {s:#}").unwrap();
    } else {
        writeln!(
            output,
            "Context: {}",
            s["context"]["state"].as_str().unwrap()
        )
        .unwrap();
        if report.classification.is_some() {
            let state = |s: &serde_json::Value| s["state"].as_str().unwrap().to_owned();
            if report.all_rejected() {
                writeln!(output, "Classification: all-rejected").unwrap();
            } else {
                writeln!(
                    output,
                    "Classification: accepted {}; rejected {}; ambiguous {}",
                    state(&s["classification"]["accepted"]),
                    state(&s["classification"]["rejected"]),
                    state(&s["classification"]["ambiguous"])
                )
                .unwrap();
            }
        }
        if !report.meaning.applicable {
            writeln!(output, "Processing meaning: not-applicable").unwrap();
        } else {
            for phase in ["existence", "uniqueness"] {
                writeln!(
                    output,
                    "Meaning {phase} ({}): {}",
                    s["meaning"]["scope"].as_str().unwrap(),
                    s["meaning"][phase]["state"].as_str().unwrap()
                )
                .unwrap();
            }
        }
        print_diagnostics(p, &shown, output, verbose)?;
        for o in s["obligations"].as_array().unwrap() {
            writeln!(
                output,
                "Obligation {} ({}): {} [{}]",
                o["name"].as_str().unwrap(),
                o["kind"].as_str().unwrap(),
                o["state"].as_str().unwrap(),
                o["scope"].as_str().unwrap()
            )
            .unwrap();
            for reason in o["reasons"].as_array().unwrap() {
                writeln!(output, "  reason: {}", reason["message"]).unwrap();
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
        if circular_support {
            writeln!(
                output,
                "Circular-support advisory: {}",
                s["advisories"]["circularSupport"]["state"]
                    .as_str()
                    .unwrap()
            )
            .unwrap();
        }
        writeln!(output, "Result: {}", s["state"].as_str().unwrap()).unwrap();
    }
    Ok((report.is_incomplete(), report.has_failures()))
}

fn inventory(
    engine: &Engine,
    p: &LoadedProgram,
    limits: &Limits,
) -> Result<serde_json::Value, Failure> {
    let allowance = Limits {
        max_work: 1_000_000,
        timeout: std::time::Duration::from_secs(2),
        cancellation: limits.cancellation.clone(),
        ..Limits::default()
    };
    let inventory = engine
        .negative_components(&p.keys, &allowance)
        .map_err(checker_failure)?;
    let qualified = |id: denotate_ir::OccurrenceId, raw: &str, kind| {
        let text = denotate_ir_text::spelling(raw, kind);
        let ns = p.corpus.namespace(id).unwrap();
        let prefix = ns
            .segments()
            .iter()
            .map(|s| denotate_ir_text::spelling(s, denotate_ir_text::NameKind::Identifier))
            .collect::<Vec<_>>()
            .join("::");
        if prefix.is_empty() {
            text
        } else {
            format!("{prefix}::{text}")
        }
    };
    let atom = |a: &denotate_check::GroundAtom| {
        let r = p.corpus.relation(a.relation).unwrap();
        let relation = index::Name {
            namespace: Some(p.corpus.namespace(r.id).unwrap().clone()),
            text: r.name.clone(),
            generated: p.corpus.is_generated_relation(r.id),
        }
        .spelling();
        let values = a
            .arguments
            .iter()
            .map(|c| {
                let c = p.corpus.constant(*c).unwrap();
                qualified(c.id.into(), &c.name, denotate_ir_text::NameKind::Constant)
            })
            .collect::<Vec<_>>();
        format!("{relation}({})", values.join(", "))
    };
    let mut index = origins::SourceIndex::new(&p.sources);
    let mut components = Vec::new();
    for c in inventory.components {
        let mut cycle = Vec::new();
        for e in c.cycle {
            let r = engine.original_instance(e.rule).unwrap();
            let source = p.provenance.origins(r.source).first().and_then(|o| {
                let source = p.sources.snapshot(o.span.snapshot()).ok()?;
                let coordinate = index
                    .coordinate(o.span.snapshot(), o.span.byte_range().start)
                    .ok()??;
                Some(json!({"uri":source.uri,"line":coordinate.line,"column":coordinate.column}))
            });
            cycle.push(json!({"consumer":atom(&e.consumer),"provider":atom(&e.provider),
                "polarity":if e.polarity == denotate_check::Polarity::Negative {"negative"} else {"positive"},
                "source":source}));
        }
        let relations = c.relations.iter().map(|(id, count)| {
            let r = p.corpus.relation(*id).unwrap();
            json!({"name":index::Name {namespace:Some(p.corpus.namespace(*id).unwrap().clone()), text:r.name.clone(),generated:p.corpus.is_generated_relation(*id)}.spelling(),"atoms":count})
        }).collect::<Vec<_>>();
        components.push(json!({"atoms":c.atoms,"relations":relations,"cycle":cycle,"omittedEdges":c.omitted_edges,"cycleSearchComplete":c.cycle_search_complete}));
    }
    Ok(
        json!({"total":inventory.total,"components":components,"complete":inventory.incomplete.is_none(),
        "reason":inventory.incomplete.map(|c| denotate_presentation::exhaustion_text(c.phase,c.resource,c.details))}),
    )
}
fn print_inventory(inventory: &serde_json::Value, output: &mut String) {
    writeln!(output, "Negative components: {}", inventory["total"]).unwrap();
    for (i, c) in inventory["components"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
    {
        writeln!(output, "  Component {}: {} atoms", i + 1, c["atoms"]).unwrap();
        for r in c["relations"].as_array().unwrap() {
            writeln!(
                output,
                "    {}: {} atoms",
                r["name"].as_str().unwrap(),
                r["atoms"]
            )
            .unwrap();
        }
        for e in c["cycle"].as_array().unwrap() {
            let source = &e["source"];
            let location = if source.is_null() {
                "source unavailable".into()
            } else {
                format!(
                    "{}:{}:{}",
                    source["uri"].as_str().unwrap(),
                    source["line"],
                    source["column"]
                )
            };
            writeln!(
                output,
                "    {} -[{}, {}]-> {}",
                e["consumer"].as_str().unwrap(),
                location,
                if e["polarity"] == "negative" {
                    "-"
                } else {
                    "+"
                },
                e["provider"].as_str().unwrap()
            )
            .unwrap();
        }
        if c["cycleSearchComplete"] == false {
            writeln!(
                output,
                "    Cycle sample unavailable: reporting allowance exhausted"
            )
            .unwrap();
        }
        if c["omittedEdges"].as_u64().unwrap() > 0 {
            writeln!(output, "    +{} cycle edges omitted", c["omittedEdges"]).unwrap();
        }
    }
    if inventory["complete"] == false {
        writeln!(
            output,
            "  Inventory truncated: {}",
            inventory["reason"].as_str().unwrap()
        )
        .unwrap();
    }
}
