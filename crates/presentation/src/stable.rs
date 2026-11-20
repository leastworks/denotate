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
        json!({"scope":"whole-program","mode":m.mode.label(),"existence":existence,"uniqueness":uniqueness, "existenceStats":m.existence_stats.as_ref().map(stable_existence_stats), "uniquenessStats":m.uniqueness_stats.as_ref().map(stable_uniqueness_stats)})
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
        "hasFailures":failure,"incomplete":incomplete,"context":context,"subsumptionIncomplete":r.subsumption_incomplete.as_ref().map(reason),"meaning":meaning,"obligations":obligations,
        "notices":r.notices_not_analysed.iter().map(|id|json!({"name":corpus.notice(*id).unwrap().name,"state":"not-analysed"})).collect::<Vec<_>>()}),
    )
}

/// Shared numeric layout for final status and progress observers.
pub fn stable_existence_stats(s: &ExistenceStats) -> Value {
    let mut value = stable_cube_stats(&s.total);
    value["componentsTotal"] = json!(s.components_total);
    value["fallbackReason"] = json!(s.fallback);
    value["scopes"] =
        json!(s.scopes.iter().map(|scope| {
        json!({"component":scope.component,"position":scope.position,"state":scope.state,
            "statistics":stable_cube_stats(&scope.counters)})
    }).collect::<Vec<_>>());
    value
}
fn stable_cube_stats(s: &denotate_check::stable_query::CubeStats) -> Value {
    json!({"cubes":s.cubes,"inputsPerCube":{"min":s.min_inputs,"mean":s.mean_inputs(),"max":s.max_inputs},
        "supportSize":s.support_size,"distinctInputs":s.distinct_inputs,"distinctCubeLiterals":s.distinct_cube_literals,
        "emittedExclusionLiterals":s.emitted_exclusion_literals,"emittedSelectorLiterals":s.emitted_selector_literals})
}

/// Scope measurements for the global uniqueness check, separate from existence.
pub fn stable_uniqueness_stats(s: &denotate_check::stable_query::UniquenessStats) -> Value {
    json!({"scope":s.scope,"components":s.components,"atoms":s.atoms,"inputs":s.inputs,
        "pairQueries":s.pair_queries,"extensionQueries":s.extension_queries,"fallbackReason":s.fallback_reason})
}

/// Advisory preparation findings use the same placement path as named notices.
/// No rewrite is installed and no removal edit is offered.
pub fn stable_producer_notices(
    r: &Report,
    corpus: &Corpus,
    names: &dyn Fn(denotate_ir::OccurrenceId) -> String,
) -> Result<Vec<ContextFinding>> {
    let mut result = Vec::new();
    for notice in &r.subsumed_producers {
        let mut instances = Vec::new();
        let mut contributions = vec![Contribution {
            occurrence: notice.rule.into(),
            role: Role::Producer,
        }];
        for (id, producer) in &notice.instances {
            let rule = r
                .program()
                .original_rule(*id)
                .ok_or(Error::InvalidFinding("missing subsumed instance"))?;
            let producer = r
                .program()
                .original_rule(*producer)
                .ok_or(Error::InvalidFinding("missing settling producer"))?;
            instances.push(crate::evidence::atom_name(corpus, names, &rule.head.atom)?);
            contributions.push(Contribution {
                occurrence: producer.source.into(),
                role: Role::DirectRewriteProof,
            });
        }
        instances.sort();
        instances.dedup();
        contributions.sort_by_key(|c| (c.role, c.occurrence));
        contributions.dedup_by_key(|c| (c.role, c.occurrence));
        let omitted = instances.len().saturating_sub(8);
        let mut note = format!(
            "Subsumed instances: {}.",
            instances
                .iter()
                .take(8)
                .cloned()
                .collect::<Vec<_>>()
                .join(", ")
        );
        if omitted > 0 {
            note.push_str(&format!(" {omitted} more tuples omitted."));
        }
        let related_omitted = contributions.len().saturating_sub(17);
        contributions.truncate(17);
        if related_omitted > 0 {
            note.push_str(&format!(
                " {related_omitted} more supporting locations omitted."
            ));
        }
        result.push(ContextFinding {identity:Identity::SubsumedProducer(notice.rule),kind:Kind::SubsumedProducer,
            message:if notice.instances.len()==notice.total_instances {"This rule is subsumed by independently settled producers of the same tuples."} else {"Some instances of this rule are subsumed by independently settled producers of the same tuples."}.into(),
            notes:vec![note], contributions});
    }
    Ok(result)
}
