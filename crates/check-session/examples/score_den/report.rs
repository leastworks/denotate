use denotate_check::*;
use denotate_check_session::{Retention, Session};
use serde_json::{Value, json};
use std::{collections::BTreeMap, fmt::Write};

pub fn limits(l: &Limits) -> Value {
    json!({"max_atoms":l.max_atoms,"max_rules":l.max_rules,"max_dependencies":l.max_dependencies,
        "max_work":l.max_work,"max_bdd_variables":l.max_bdd_variables,"max_bdd_nodes":l.max_bdd_nodes,
        "max_bdd_tasks":l.max_bdd_tasks,"max_condition_nodes":l.max_condition_nodes,"timeout_ms":l.timeout.as_millis()})
}
pub fn variant(mode: &str, unconstrained: bool) -> Value {
    let retention = if mode == "global-bdd" {
        Value::Null
    } else {
        let r = if mode == "fresh-local-bdd" {
            Retention {
                max_entries: 0,
                max_bytes: 0,
                max_condition_nodes: 0,
            }
        } else if unconstrained {
            Retention {
                max_entries: usize::MAX,
                max_bytes: usize::MAX,
                max_condition_nodes: usize::MAX,
            }
        } else {
            Retention::default()
        };
        json!({"max_entries":r.max_entries,"max_bytes":r.max_bytes,"max_condition_nodes":r.max_condition_nodes})
    };
    json!({"mode":mode,"session_retention":retention,
        "planning":if mode=="global-bdd"||mode=="bdd-no-plans" {"fresh"}else{"cached-small-rule-bypass"},
        "grounding":match mode {"grounding-bdd"=>"cached-relation-scc","fresh-grounding-bdd"=>"fresh-relation-scc","folded-bdd"=>"fixed-facts-and-residual",_=>"fresh"}})
}
pub fn size(p: &PreparedCheck<'_>) -> Value {
    let g = p.program();
    let mut rules = BTreeMap::new();
    for r in g.rules() {
        if let Ok(c) = g.component_for(&r.head.atom) {
            *rules.entry(c.id).or_insert(0usize) += 1;
        }
    }
    let mut components = g
        .components()
        .map(|c| json!({"atoms":c.atoms.len(),"rules":rules.get(&c.id).copied().unwrap_or(0)}))
        .collect::<Vec<_>>();
    components.sort_by_key(|v| {
        std::cmp::Reverse((v["atoms"].as_u64().unwrap(), v["rules"].as_u64().unwrap()))
    });
    let count = components.len();
    components.truncate(5);
    let (atoms, present, fixed_rules, fixed_components, dependencies) = g.fixed_size();
    let (residual_atoms, residual_rules, residual_components) = g.residual_size();
    json!({"inputs":g.input_atoms().count(),"ground_atoms":g.atoms().count(),"rule_instances":g.rules().count(),
        "components":count,"largest_components":components,
        "fold":{"present_facts":present,"absent_facts":atoms-present,
            "retained_evidence":{"atoms":atoms,"rule_instances":fixed_rules,"components":fixed_components,"dependencies":dependencies},
            "residual":{"atoms":residual_atoms,"rule_instances":residual_rules,"components":residual_components}}})
}
pub fn preparation_stats(s: &Session, mode: &str) -> Value {
    let p = s.plan_stats();
    let g = s.grounding_stats();
    json!({"plans":if mode=="bdd-no-plans" {Value::Null}else{json!({
        "queries":p.queries,"executed":p.executed,"reused":p.reused,"fallback":p.fallback,
        "small_rules":p.small_rules,"evicted":p.evicted,"bypassed":p.bypassed,"reused_work":p.reused_work,
        "retained_entries":p.retained_entries,"retained_bytes":p.retained_bytes,
        "query_ns":p.query_ns,"execution_ns":p.execution_ns,"projection_ns":p.projection_ns})},
        "grounding":if !matches!(mode,"grounding-bdd"|"fresh-grounding-bdd") {Value::Null}else{json!({
        "units":g.units,"executed":g.executed,"reused":g.reused,"bypassed_graphs":g.bypassed_graphs,
        "evicted":g.evicted,"allocated_slots":g.allocated_slots,"retained_units":g.retained_units,
        "retained_bytes":g.retained_bytes,"reused_work":g.reused_work,
        "install_ns":g.install_ns,"equality_ns":g.equality_ns,"query_ns":g.query_ns,"receipts_ns":g.receipts_ns,
        "retention_ns":g.retention_ns,"reconstruction_ns":g.reconstruction_ns,"closure_ns":g.closure_ns,"export_ns":g.export_ns})}})
}
pub fn cache(s: &Session) -> Value {
    let s = s.stats();
    json!({"lookup_ns":s.lookup_ns,"publication_ns":s.publication_ns,"reused_query_work":s.reused_query_work,
        "evaluation_hits":s.evaluation_hits,"evaluation_misses":s.evaluation_misses,
        "verdict_hits":s.verdict_hits,"verdict_misses":s.verdict_misses,
        "completion_hits":s.completion_hits,"completion_misses":s.completion_misses,
        "invalidated":s.invalidated,"evicted":s.evicted,"bypassed":s.bypassed,"resets":s.resets,
        "retained_entries":s.retained_entries,"retained_bytes":s.retained_bytes,
        "retained_condition_nodes":s.retained_condition_nodes})
}
pub fn work(receipts: &WorkReceipts) -> Value {
    let mut peaks = BTreeMap::<(&str, &str), usize>::new();
    for (_, receipt) in receipts.entries() {
        for (k, n) in &receipt.own.resource_peaks {
            peaks
                .entry((&k.phase, &k.resource))
                .and_modify(|p| *p = (*p).max(*n))
                .or_insert(*n);
        }
    }
    let max = |resource| {
        peaks
            .iter()
            .filter(|((_, r), _)| *r == resource)
            .map(|(_, n)| *n)
            .max()
    };
    json!({"logical_work":receipts.total().ok().map(|t|t.work),
        "max_per_query_bdd_nodes":max("BDD nodes"),
        "max_per_query_retained_condition_nodes":max("condition nodes"),
        "per_query_resource_high_water":peaks.into_iter().map(|((phase,resource),peak)|json!({"phase":phase,"resource":resource,"max":peak})).collect::<Vec<_>>()})
}
pub fn human(report: &Value) -> String {
    let mut out = format!(
        ".den scorecard: {}\n{} sample(s) after one warm-up; checker phases in milliseconds (median).\n",
        report["root"].as_str().unwrap(),
        report["samples"]
    );
    for (label, config) in report["configuration"].as_object().unwrap() {
        writeln!(
            out,
            "{label}: {}; {} unchecked obligation(s)",
            config["state"].as_str().unwrap(),
            config["unchecked_obligations"].as_array().unwrap().len()
        )
        .unwrap();
    }
    for v in report["verifications"].as_array().unwrap() {
        writeln!(
            out,
            "\nVerification {} ({})",
            v["name"].as_str().unwrap(),
            v["change"].as_str().unwrap()
        )
        .unwrap();
        writeln!(
            out,
            "  mode / snapshot                    prepare    admit    check  notices  outcome; BDD maxima (query / retained-query / cache)"
        )
        .unwrap();
        let samples = v["samples"].as_array().unwrap();
        for mode in super::driver::MODES {
            for phase in ["cold", "warm", "edit"] {
                let rows = samples
                    .iter()
                    .filter_map(|s| s[mode].get(phase))
                    .collect::<Vec<_>>();
                if rows.is_empty() {
                    continue;
                }
                let timing = |key| {
                    let mut values = rows
                        .iter()
                        .filter_map(|r| r["timings_ns"][key].as_u64())
                        .collect::<Vec<_>>();
                    values.sort();
                    if values.is_empty() {
                        "—".into()
                    } else {
                        format!("{:.3}", values[values.len() / 2] as f64 / 1_000_000.0)
                    }
                };
                let r = rows[0];
                let states = rows
                    .iter()
                    .map(|r| r["outcomes"]["state"].as_str().unwrap_or("error"))
                    .collect::<std::collections::BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>()
                    .join("/");
                writeln!(
                    out,
                    "  {:<34} {:>8} {:>8} {:>8} {:>8}  {}{}; {} / {} / {}",
                    format!("{mode}/{phase}"),
                    timing("preparation"),
                    timing("admission"),
                    timing("checking"),
                    timing("notices"),
                    states,
                    if r["effective_path"] == "global-bdd-general-assumptions" {
                        " [global fallback]"
                    } else {
                        ""
                    },
                    max_observation(&rows, "bdd", "max_per_query_bdd_nodes"),
                    max_observation(&rows, "bdd", "max_per_query_retained_condition_nodes"),
                    max_observation(&rows, "cache", "retained_condition_nodes")
                )
                .unwrap();
            }
        }
        for phase in ["cold", "edit"] {
            if let Some(r) = samples.first().and_then(|s| s["folded-bdd"].get(phase)) {
                writeln!(
                    out,
                    "  {phase} folded size (evidence and residual): {}",
                    r["size"]["fold"]
                )
                .unwrap();
            }
            if let Some(r) = samples.first().and_then(|s| s["global-bdd"].get(phase)) {
                writeln!(out, "  {phase} size (after preparation): {}", r["size"]).unwrap();
                writeln!(
                    out,
                    "  {phase} obligations: {}; notices: {}; regions: {}; consistency: {}",
                    r["outcomes"]["obligations_by_kind"],
                    r["outcomes"]["notices_by_state"],
                    r["outcomes"]["regions"],
                    r["outcomes"]["consistency"]
                )
                .unwrap();
            }
        }
    }
    writeln!(out,"\nBDD figures are logical observations, including reused work; not heap peaks.\nFull cache measurements, keyed outcome comparisons and individual samples: use --json FILE.\nIncomplete/unsupported runs are not speed wins; — means unavailable. No diagnostics or witnesses are included.").unwrap();
    for failure in report["failures"].as_array().unwrap() {
        writeln!(out, "FAIL: {}", failure.as_str().unwrap()).unwrap();
    }
    out
}

fn max_observation(rows: &[&Value], object: &str, key: &str) -> String {
    rows.iter()
        .filter_map(|r| r[object][key].as_u64())
        .max()
        .map(|n| n.to_string())
        .unwrap_or_else(|| "—".into())
}
