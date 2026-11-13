//! Interpret program-level assumption validation; never reconstruct dependencies.
use crate::*;
use denotate_check::{AssumptionValidation, AssumptionValidity};
use denotate_ir::{Corpus, OccurrenceId, OccurrenceKey, SemanticKeys};
use serde_json::{Value, json};

pub fn assumption_validity_data(state: &AssumptionValidity) -> Value {
    match state {
        AssumptionValidity::Valid => json!({"kind":"assumption-validation","state":"valid"}),
        AssumptionValidity::NotSelected => {
            json!({"kind":"assumption-validation","state":"not-selected"})
        }
        AssumptionValidity::Invalid { cycles } => json!({
            "kind":"assumption-validation", "state":"invalid",
            "cycles":cycles.iter().map(|c| c.0.iter().map(|e|
                crate::cycles::cycle_edge_data(&e.consumer, &e.provider, e.negative)
            ).collect::<Vec<_>>()).collect::<Vec<_>>()
        }),
        AssumptionValidity::Inconclusive(reason) => with_limit_details(
            json!({
                "kind":"assumption-validation","state":"inconclusive",
                "phase":reason.phase,"resource":reason.resource
            }),
            reason.details,
        ),
    }
}

pub fn assumption_validation_summary(validation: &AssumptionValidation) -> Value {
    json!({
        "state":if validation.assumptions.values().any(|s| matches!(s, AssumptionValidity::Invalid {..})) {"invalid"}
            else if validation.has_failures() {"inconclusive"}
            else if !validation.is_valid() {"not-selected"} else {"valid"},
        "assumptions":validation.assumptions.iter().map(|(key, state)| json!({
            "assumption":[key.0.namespace.as_ref(),key.0.name.as_ref()],
            "validation":assumption_validity_data(state)
        })).collect::<Vec<_>>()
    })
}

pub fn assumption_validation_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    validation: &AssumptionValidation,
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<(ContextFinding, Value)>> {
    let mut findings = Vec::new();
    for assumption in corpus.assumptions() {
        let state = validation
            .assumptions
            .get(keys.assumption(assumption.id)?)
            .ok_or(Error::InvalidFinding(
                "assumption validation does not cover program",
            ))?;
        let mut contributions = vec![Contribution {
            occurrence: assumption.id.into(),
            role: Role::Declaration,
        }];
        let mut notes = Vec::new();
        let (kind, message) = match state {
            AssumptionValidity::Valid => continue,
            AssumptionValidity::NotSelected => (
                Kind::UnvalidatedAssumption,
                format!(
                    "Assumption {} is not selected by this run; its ground cone is validated when a verification selects it.",
                    assumption.name
                ),
            ),
            AssumptionValidity::Invalid { cycles } => {
                for cycle in cycles {
                    notes.push(crate::cycles::assumption_cycle_note(keys, names, cycle)?);
                    for edge in &cycle.0 {
                        for occurrence in [&edge.premise, &OccurrenceKey::Rule(edge.rule.clone())] {
                            contributions.push(Contribution {
                                occurrence: keys.bindings().resolve(occurrence)?,
                                role: Role::BlockingCycle,
                            });
                        }
                    }
                }
                (
                    Kind::InvalidAssumption,
                    format!(
                        "Assumption {} has a dependency cycle through negation in its ground cone; its meaning cannot be established independently of assumptions.",
                        assumption.name
                    ),
                )
            }
            AssumptionValidity::Inconclusive(reason) => (
                Kind::UnvalidatedAssumption,
                format!(
                    "Assumption {} could not be validated ({}).",
                    assumption.name,
                    exhaustion_text(&reason.phase, &reason.resource, reason.details)
                ),
            ),
        };
        findings.push((
            ContextFinding {
                identity: Identity::Assumption(assumption.id),
                kind,
                message,
                notes,
                contributions,
            },
            assumption_validity_data(state),
        ));
    }
    Ok(findings)
}
