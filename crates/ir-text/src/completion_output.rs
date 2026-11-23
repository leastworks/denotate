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
            "Pruning {} {} component {} ({}; {} atoms): {} candidates considered, {} proved; {} instances removed; last head {}",
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
