//! Whole-program SAT status and the shared property findings. No CLI or IO.
use crate::*;
use denotate_check::{stable_query::*, *};
use denotate_ir::{Corpus, SemanticKeys};
use serde_json::{Value, json};

pub fn stable_findings<'a>(
    corpus: &Corpus,
    r: &'a Report,
    names: &dyn Fn(denotate_ir::OccurrenceId) -> String,
) -> Result<Vec<Finding<'a>>> {
    let mut findings = Vec::new();
    for g in &r.groups {
        if let Some(f) = uniqueness_finding(corpus, g, names, None)? {
            findings.push(f);
        }
    }
    for (id, e) in &r.emptiness {
        if let Some(f) = emptiness_finding(corpus, *id, e, names)? {
            findings.push(f);
        }
    }
    for (id, c) in &r.coverage {
        if let Some(f) = coverage_finding(corpus, *id, c, names, None)? {
            findings.push(f);
        }
    }
    Ok(findings)
}

pub fn stable_summary(corpus: &Corpus, keys: &SemanticKeys, r: &Report) -> Result<Value> {
    let reason = |c: &Inconclusive| exhaustion_data(c.phase, c.resource, c.details);
    let atoms = |atoms: &std::collections::BTreeSet<GroundAtom>| -> Result<Value> {
        Ok(Value::Array(
            atoms
                .iter()
                .map(|a| Ok(atom_data(&AtomKey::from_atom(keys, a)?)))
                .collect::<Result<_>>()?,
        ))
    };
    let world = |w: &Observation| -> Result<Value> {
        Ok(json!({"present":atoms(&w.present)?,"absent":atoms(&w.absent)?}))
    };
    let context = match &r.context {
        Context::Permitted => json!({"state":"consistent"}),
        Context::EmptyUniverse => json!({"state":"empty-input-universe"}),
        Context::InconsistentAssumptions => json!({"state":"inconsistent-assumptions"}),
        Context::Inconclusive(c) => json!({"state":"inconclusive","reason":reason(c)}),
    };
    let mut failure = r.has_failures()
        || matches!(
            r.context,
            Context::EmptyUniverse | Context::InconsistentAssumptions
        );
    let mut incomplete = r.meaning_mode != MeaningMode::Full
        || matches!(r.context, Context::Inconclusive(_))
        || (matches!(r.context, Context::Permitted)
            && (!r.not_analysed.is_empty()
                || !r.incomplete.is_empty()
                || r.emptiness.values().any(|e| !e.complete())
                || r.coverage.values().any(|c| !c.complete())
                || r.groups.iter().any(|g| {
                    matches!(
                        g.outcome,
                        VerifiedOutcome::Inconclusive(_) | VerifiedOutcome::Unsupported
                    )
                })));
    let meaning = if let Some(m) = &r.meaning {
        let existence = match &m.existence {
            Existence::NotAnalysed => {
                incomplete = true;
                json!({"state":"not-analysed", "reason":"disabled-by-option"})
            }
            Existence::EveryWorld => json!({"state":"every-world"}),
            Existence::NoMeaning(w) => {
                failure = true;
                json!({"state":"no-meaning","world":world(w)?})
            }
            Existence::Inconclusive(c) => {
                incomplete = true;
                json!({"state":"inconclusive","reason":reason(c)})
            }
        };
        let uniqueness = match &m.uniqueness {
            Uniqueness::NotAnalysed => {
                incomplete = true;
                json!({"state":"not-analysed", "reason":"disabled-by-option"})
            }
            Uniqueness::AtMostOne => json!({"state":"at-most-one"}),
            Uniqueness::Inconclusive(c) => {
                incomplete = true;
                json!({"state":"inconclusive","reason":reason(c)})
            }
            Uniqueness::Multiple {
                observation,
                first,
                second,
            } => {
                failure = true;
                let mut differences = Vec::new();
                for (a, x, y) in first
                    .differences(second)
                    .ok_or(Error::InvalidFinding("foreign SAT interpretations"))?
                {
                    differences.push(json!({"atom":atom_data(&AtomKey::from_atom(keys,a)?),"first":x,"second":y}));
                }
                json!({"state":"multiple-meanings","world":world(observation)?,"differences":differences})
            }
        };
        json!({"scope":"whole-program","mode":m.mode.label(),"existence":existence,"uniqueness":uniqueness, "existenceStats":m.existence_stats.as_ref().map(stable_existence_stats)})
    } else {
        json!({"state":"not-analysed"})
    };
    let v = corpus
        .verification(r.verification)
        .ok_or(Error::InvalidFinding("foreign verification"))?;
    let mut obligations = Vec::new();
    for id in &v.obligations {
        let o = corpus.obligation(*id).unwrap();
        let groups = r
            .groups
            .iter()
            .filter(|g| g.group.obligation == *id)
            .collect::<Vec<_>>();
        let failed = r.emptiness.get(id).is_some_and(|e| e.present > 0)
            || r.coverage.get(id).is_some_and(|c| c.missing > 0)
            || groups
                .iter()
                .any(|g| matches!(g.outcome, VerifiedOutcome::Counterexample(_)));
        let mut reasons = Vec::new();
        if let Some(c) = r.incomplete.get(id) {
            reasons.push(reason(c));
        }
        if let Some(c) = r.emptiness.get(id).and_then(|e| e.inconclusive) {
            reasons.push(reason(&c));
        }
        if let Some(c) = r.coverage.get(id).and_then(|e| e.inconclusive) {
            reasons.push(reason(&c));
        }
        for g in &groups {
            if let VerifiedOutcome::Inconclusive(c) = g.outcome {
                reasons.push(reason(&c));
            }
        }
        obligations.push(json!({"name":o.name,"identity":json!([keys.obligation(*id)?.0.namespace.as_ref(),keys.obligation(*id)?.0.name.as_ref()]),
            "kind":match o.requirement.kind(){denotate_ir::Cardinality::Empty=>"empty",denotate_ir::Cardinality::AtMostOne=>"at-most-one",denotate_ir::Cardinality::AtLeastOne=>"at-least-one",denotate_ir::Cardinality::ExactlyOne=>"exactly-one"},
            "state":if r.not_analysed.contains(id){"not-analysed"}else if failed{"counterexample"}else if !reasons.is_empty(){"inconclusive"}else{"proved"},
            "fixed":r.fixed_obligations.contains(id),"reasons":reasons,
            "present":r.emptiness.get(id).map(|e|e.present),"missing":r.coverage.get(id).map(|e|e.missing),
            "complete":!r.not_analysed.contains(id) && reasons.is_empty()}));
    }
    Ok(
        json!({"backend":{"backend":"sat","configuration":"original-stable-v1"},"state":if incomplete{"incomplete"}else if failure{"findings"}else{"proved"},
        "verification":[keys.verification(v.id)?.0.namespace.as_ref(),keys.verification(v.id)?.0.name.as_ref()],
        "activeAssumptions":v.assumptions.iter().map(|id|corpus.assumption(*id).unwrap().name.clone()).collect::<Vec<_>>(),
        "hasFailures":failure,"incomplete":incomplete,"context":context,"meaning":meaning,"obligations":obligations,
        "notices":r.notices_not_analysed.iter().map(|id|json!({"name":corpus.notice(*id).unwrap().name,"state":"not-analysed"})).collect::<Vec<_>>()}),
    )
}

/// Shared numeric layout for final status and progress observers.
pub fn stable_existence_stats(s: &ExistenceStats) -> Value {
    json!({"cubes":s.cubes,"inputsPerCube":{"min":s.min_inputs,"mean":s.mean_inputs(),"max":s.max_inputs},
        "supportSize":s.support_size,"distinctInputs":s.distinct_inputs,"distinctCubeLiterals":s.distinct_cube_literals,
        "emittedExclusionLiterals":s.emitted_exclusion_literals,"emittedSelectorLiterals":s.emitted_selector_literals})
}
