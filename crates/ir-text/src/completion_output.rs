//! Snapshot-only source adapter for completion's structural cycle diagnostics.
use crate::LoadedProgram;
use denotate_check::{CompletionOddExplanation, CompletionSizeSnapshot};
use denotate_presentation::Result;
use serde_json::{Value, json};
use std::collections::BTreeMap;

pub fn explanations(
    p: &LoadedProgram,
) -> impl Fn(&CompletionOddExplanation) -> Result<Value> + Send + Sync + use<> {
    let names = crate::presentation::diagnostic_names(&p.corpus);
    // A cycle edge cannot come from a fact. Keep only compact spans for
    // non-fact source rules; do not allocate JSON locations for a large lowering.
    let spans: BTreeMap<_, _> = p
        .corpus
        .rules()
        .filter(|r| !r.body.is_empty())
        .filter_map(|r| p.provenance.origins(r.id).first().map(|o| (r.id, o.span)))
        .collect();
    let snapshots: BTreeMap<_, _> = p
        .sources
        .snapshots()
        .map(|s| (s.id, (s.uri.clone(), s.text.clone())))
        .collect();
    move |o| {
        let lines = std::cell::RefCell::new(BTreeMap::new());
        let locations = std::cell::RefCell::new(BTreeMap::new());
        denotate_presentation::completion_odd_explanation(
            o,
            |a| Ok(json!(crate::progress::atom_text(a, &names))),
            |r| {
                Ok(locations
                    .borrow_mut()
                    .entry(r)
                    .or_insert_with(|| {
                        let location = spans.get(&r).and_then(|span| {
                            let (uri, text) = snapshots.get(&span.snapshot())?;
                            let at = lines
                                .borrow_mut()
                                .entry(span.snapshot())
                                .or_insert_with(|| crate::origins::LineIndex::new(text))
                                .coordinate(span.byte_range().start)?;
                            Some(json!({"uri":uri,"line":at.line,"column":at.column}))
                        });
                        json!({"location":location})
                    })
                    .clone())
            },
            |r| Ok(json!(names(r.into()))),
            |g| {
                Ok(json!({"relation":names(g.relation.into()),
            "values":g.values.iter().map(|v|names((*v).into())).collect::<Vec<_>>(),
            "assumption":g.assumption.map(|a|names(a.into())),"declared":g.declared}))
            },
        )
    }
}
pub fn sizes(p: &LoadedProgram, s: &CompletionSizeSnapshot) -> Result<Value> {
    denotate_presentation::completion_sizes_with_explanations(&p.keys, s, explanations(p))
}

/// A bounded explanation already formatted with .den names and source locations.
pub fn odd_lines(o: &Value) -> Vec<String> {
    if o.is_null() {
        return vec![];
    }
    let text = |v: &Value| {
        v.as_str()
            .map(str::to_owned)
            .unwrap_or_else(|| v.to_string())
    };
    let mut lines = vec![format!(
        "odd cycles: at least {} distinct found (search cap {}); {} long cycles omitted",
        o["distinctCyclesFound"], o["cycleLimit"], o["omittedLongCycles"]
    )];
    lines.push(format!(
        "  signed SCCs with a found cycle: {} / {}",
        o["componentsWithCyclesFound"], o["oddComponents"]
    ));
    lines.push("Guards: falsify a conjunct to disable that producer; ALL alternative producers must be disabled to cut an edge. These are structural candidates, not proven cuts.".into());
    for (i, c) in o["cycles"].as_array().into_iter().flatten().enumerate() {
        lines.push(format!("  odd cycle {}:", i + 1));
        for e in c.as_array().into_iter().flatten() {
            lines.push(format!(
                "    {} --{}--> {} ({} producers)",
                text(&e["from"]),
                if e["negative"] == true {
                    "negative"
                } else {
                    "positive"
                },
                text(&e["to"]),
                e["producerCount"]
            ));
            for p in e["producers"].as_array().into_iter().flatten() {
                let l = &p["source"]["location"];
                let at = if l.is_null() {
                    "source unavailable".into()
                } else {
                    format!("{}:{}:{}", text(&l["uri"]), l["line"], l["column"])
                };
                let guards = p["guards"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|g| {
                        format!(
                            "{}{}",
                            if g["negative"] == true { "!" } else { "" },
                            text(&g["atom"])
                        )
                    })
                    .collect::<Vec<_>>();
                lines.push(format!(
                    "      {at}; other conjuncts: {}{}",
                    if guards.is_empty() {
                        "(none)".into()
                    } else {
                        guards.join(", ")
                    },
                    if p["omittedGuards"].as_u64().unwrap_or(0) > 0 {
                        format!(" (+{} omitted)", p["omittedGuards"])
                    } else {
                        String::new()
                    }
                ));
            }
            if e["omittedProducers"].as_u64().unwrap_or(0) > 0 {
                lines.push(format!("      +{} other producers", e["omittedProducers"]));
            }
        }
    }
    let complete = o["histogramsComplete"] == true;
    lines.push(format!(
        "  negative rule-instance occurrences by consumer -> provider ({}):",
        if complete {
            "complete scan"
        } else {
            "partial counts"
        }
    ));
    for r in o["negativeRelations"].as_array().into_iter().flatten() {
        lines.push(format!(
            "    {} -> {}: {}",
            text(&r["consumer"]),
            text(&r["provider"]),
            r["occurrences"]
        ));
    }
    lines.push(format!(
        "  input groups structurally reaching other conjuncts of negative edges ({}):",
        if complete {
            "complete scan"
        } else {
            "partial counts"
        }
    ));
    for r in o["inputGroups"].as_array().into_iter().flatten() {
        let g = &r["group"];
        lines.push(format!(
            "    {} {} ({}): {} edges",
            text(&g["relation"]),
            g["values"],
            if g["declared"] == true {
                "declared cardinality".into()
            } else if !g["assumption"].is_null() {
                format!("assumption {}", text(&g["assumption"]))
            } else {
                "singleton tuple".into()
            },
            r["edges"]
        ));
    }
    if o["omittedNegativeRelations"].as_u64().unwrap_or(0) > 0
        || o["omittedInputGroups"].as_u64().unwrap_or(0) > 0
    {
        lines.push(format!(
            "  +{} relation rows, +{} input-group rows omitted",
            o["omittedNegativeRelations"], o["omittedInputGroups"]
        ));
    }
    if !o["searchIncomplete"].is_null() {
        lines.push(format!(
            "  explanation incomplete: {}",
            text(&o["searchIncomplete"])
        ));
    }
    lines
}

pub fn pruning_formatter(
    p: &LoadedProgram,
) -> impl Fn(&denotate_check::completion_query::PruningComponent) -> String + Send + Sync + use<> {
    let names = crate::presentation::diagnostic_names(&p.corpus);
    move |c| {
        let mut text = format!(
            "Pruning {} {} component {} ({}; {} atoms): {} candidates considered, {} proved; {} instances removed, {} implied body literals removed; last head {}",
            c.scope,
            match c.context {
                denotate_check::completion_query::PruningContext::World => "W",
                _ => "W+H",
            },
            crate::progress::atom_text(&c.representative, &names),
            c.kind,
            c.atoms,
            c.considered,
            c.proved,
            c.removed,
            c.removed_literals,
            c.last_head
                .as_ref()
                .map(|a| crate::progress::atom_text(a, &names))
                .unwrap_or_else(|| "(none)".into())
        );
        text.push_str(&format!(
            "; {} candidate heads / {} producers{}",
            c.candidate_heads,
            c.candidate_producers,
            if c.discovery_complete {
                ""
            } else {
                " (discovery incomplete; lower bounds)"
            }
        ));
        if let Some(c) = c.cutoff {
            text.push_str(&format!(
                "; optional cutoff: {}",
                denotate_presentation::exhaustion_text(c.phase, c.resource, c.details)
            ));
        }
        text
    }
}

fn forcing_text(records: &[denotate_check::completion_query::ForcingRecord]) -> String {
    let mut text = String::new();
    for r in records {
        text.push_str(&format!("; forcing [{}]: {} constants ({} witness atoms), {}/{} candidates; shadow cache {} model / {} core claims, {} checked, {} mismatches{}",
            r.context,r.forced,r.forced_witnesses,r.attempted,r.candidates,r.cache.model_hits,r.cache.core_hits,r.cache.checked_hits,r.cache.mismatches,
            if r.no_model { "; context has no model; no constants installed" } else { "" }));
        if let Some(c) = r.cutoff {
            text.push_str(&format!(
                "; {}",
                denotate_presentation::exhaustion_text(c.phase, c.resource, c.details)
            ));
        }
    }
    text
}

pub fn branch_line(c: &denotate_check::completion_query::BranchRecord) -> String {
    let mut line = format!(
        "{} branch depth {}: {}, {} children, {} work, {:.3}s",
        c.phase,
        c.depth,
        c.state,
        c.children,
        c.work,
        c.elapsed.as_secs_f64()
    );
    if let Some(c) = c.cutoff {
        line.push_str(&format!(
            "; {}",
            denotate_presentation::exhaustion_text(c.phase, c.resource, c.details)
        ));
    }
    line.push_str(&forcing_text(&c.forcing));
    line
}

pub fn branch_formatter(
    p: &LoadedProgram,
) -> impl Fn(&denotate_check::completion_query::BranchRecord) -> String + Send + Sync + use<> {
    let names = crate::presentation::diagnostic_names(&p.corpus);
    move |c| {
        let mut line = branch_line(c);
        line.push_str(&format!(
            "; preparation work {}, search work {}; unit {}{}",
            c.preparation_work,
            c.search_work,
            c.id,
            if c.rest { " (rest)" } else { "" }
        ));
        if let Some(a) = c.assumption {
            line.push_str(&format!("; assumption {}", names(a.into())));
        }
        if c.children > 0 {
            line.push_str(&format!(
                "; {} partition, rest {}, {} children proved",
                c.split_kind, c.has_rest, c.closed_children
            ));
        }

        if let Some(group) = &c.split {
            line.push_str(&format!(
                "; split group {}, {} guarded edges",
                crate::progress::atom_text(group, &names),
                c.guarded_edges
            ));
        }
        if let Some(r) = &c.runner_up {
            line.push_str(&format!(
                "; runner-up {}: {} edges / {} extra children",
                crate::progress::atom_text(&r.split, &names),
                r.guarded_edges,
                r.children - 1
            ));
        }
        for r in &c.candidates {
            line.push_str(&format!("; candidate {} [{}; {}]: {} guard edges, {}/{} children tried, {} disabled edges (min {}), {} cycles cut in every child{}{}",
                crate::progress::atom_text(&r.split, &names),r.context,r.state,r.guarded_edges,
                r.checked_children,r.children,r.disabled_edges,r.minimum_disabled,r.cycles_cut_every_child,
                if r.selected { " selected" } else { "" },
                if r.cutoff.is_some() { " trial incomplete" } else { "" }));
        }
        for r in &c.candidates {
            if r.pruning_attempts > 0 {
                line.push_str(&format!(
                    "; candidate {}: {} conditional pruning attempts, {} proved",
                    crate::progress::atom_text(&r.split, &names),
                    r.pruning_attempts,
                    r.pruning_proved
                ));
            }
            for child in &r.child_trials {
                line.push_str(&format!("; candidate {} child {}{} [{}]: {} pruning attempts, {} proved, {} producers / {} literals removed, {}/{} target atoms settled, {} edges disabled, {} witness cycles cut{}; guards: +{} omitted{}",
                    crate::progress::atom_text(&r.split, &names), child.child, if r.formula { if child.rest { " (false)" } else { " (true)" } } else { "" },
                    child.context,child.pruning_attempts,child.pruning_proved,child.removed_producers,child.removed_literals,
                    child.settled_target_atoms,child.target_atoms,child.disabled_edges,child.cycles_cut,
                    if !child.complete || child.cutoff.is_some() { " (trial incomplete)" } else { "" },
                    child.omitted_derived_guards,if child.derived_guards_complete { "" } else { " (inventory incomplete/not sampled)" }));
                line.push_str(&forcing_text(&child.forcing));
                for producer in &child.removed_producer_examples {
                    let body = producer
                        .original_body
                        .iter()
                        .map(|(a, positive)| {
                            format!(
                                "{}{}",
                                if *positive { "" } else { "!" },
                                crate::progress::atom_text(a, &names)
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    line.push_str(&format!(
                        "; removed producer [{}] {} :- {}{}",
                        producer.context,
                        crate::progress::atom_text(&producer.head, &names),
                        body,
                        if producer.omitted_body_literals > 0 {
                            format!(", +{} body literals", producer.omitted_body_literals)
                        } else {
                            String::new()
                        }
                    ));
                }
                if child.omitted_producer_examples > 0 {
                    line.push_str(&format!(
                        "; +{} omitted producer examples",
                        child.omitted_producer_examples
                    ));
                }
                for head in &child.pruned_heads {
                    line.push_str(&format!(
                        "; pruned head {}",
                        crate::progress::atom_text(head, &names)
                    ));
                }
            }
            for g in &r.derived_guards {
                line.push_str(&format!(
                    "; child {} [{}] derived guard {}: upstream {}",
                    g.child,
                    r.child_trials.get(g.child).map_or(r.context, |c| c.context),
                    crate::progress::atom_text(&g.atom, &names),
                    if g.acyclic_upstream {
                        "acyclic"
                    } else {
                        "cyclic"
                    }
                ));
            }
            if r.selected && !r.derived_guards_complete && r.pruning_attempts > 0 {
                line.push_str("; derived guard inventory incomplete");
            }
            if r.omitted_derived_guards > 0 {
                line.push_str(&format!(
                    "; +{} omitted derived guards",
                    r.omitted_derived_guards
                ));
            }
        }
        if c.omitted_candidates > 0 {
            line.push_str(&format!("; +{} omitted candidates", c.omitted_candidates));
        }
        if !c.values.is_empty() {
            line.push_str(&format!(
                "; own values [{}]{}",
                c.values
                    .iter()
                    .map(|a| crate::progress::atom_text(a, &names))
                    .collect::<Vec<_>>()
                    .join(", "),
                if c.omitted_values > 0 {
                    format!(" (+{})", c.omitted_values)
                } else {
                    String::new()
                }
            ));
        }
        if !c.pins.is_empty() {
            line.push_str("; inputs ");
            line.push_str(
                &c.pins
                    .iter()
                    .map(|(a, v)| format!("{}={v}", crate::progress::atom_text(a, &names)))
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            if c.omitted_pins > 0 {
                line.push_str(&format!(" (+{} pins)", c.omitted_pins));
            }
        }
        line
    }
}
