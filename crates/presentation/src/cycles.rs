//! Render the checker's retained path. No traversal, cycle search or proof work.
use crate::{Error, Result, atom_data, evidence::atom_name};
use denotate_check::{AssumptionCycle, AtomKey, Cycle, Polarity};
use denotate_ir::{Corpus, OccurrenceId, OccurrenceKey, SemanticKeys};
use serde_json::{Value, json};

fn path_note(edges: impl IntoIterator<Item = Result<(String, String, bool)>>) -> Result<String> {
    let mut edges = edges.into_iter();
    let first = edges
        .next()
        .ok_or(Error::InvalidFinding("empty retained cycle"))??;
    let mut note = format!(
        "Ground dependency cycle (structural; arrows mean \"depends on\"): {}",
        first.0
    );
    for edge in std::iter::once(Ok(first)).chain(edges) {
        let (_, provider, negative) = edge?;
        note.push_str(if negative { " -not-> " } else { " -> " });
        note.push_str(&provider);
    }
    note.push('.');
    Ok(note)
}

pub(crate) fn ground_cycle_note(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    cycle: &Cycle,
) -> Result<String> {
    path_note(cycle.edges.iter().map(|edge| {
        Ok((
            atom_name(corpus, names, &edge.consumer)?,
            atom_name(corpus, names, &edge.provider)?,
            edge.polarity == Polarity::Negative,
        ))
    }))
}

pub(crate) fn assumption_cycle_note(
    keys: &SemanticKeys,
    names: &dyn Fn(OccurrenceId) -> String,
    cycle: &AssumptionCycle,
) -> Result<String> {
    // Rebind keys to the current declarations before asking the frontend to spell
    // them. Keys themselves are identities, not source-language display names.
    let atom = |key: &AtomKey| -> Result<String> {
        let relation = names(
            keys.bindings()
                .resolve(&OccurrenceKey::Relation(key.relation.clone()))?,
        );
        let arguments = key
            .arguments
            .iter()
            .map(|key| {
                Ok(names(
                    keys.bindings()
                        .resolve(&OccurrenceKey::Constant(key.clone()))?,
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(format!("{relation}({})", arguments.join(", ")))
    };
    path_note(
        cycle
            .0
            .iter()
            .map(|edge| Ok((atom(&edge.consumer)?, atom(&edge.provider)?, edge.negative))),
    )
}

pub(crate) fn cycle_edge_data(consumer: &AtomKey, provider: &AtomKey, negative: bool) -> Value {
    json!({
        "consumer":atom_data(consumer), "provider":atom_data(provider),
        "polarity":if negative {"negative"} else {"positive"}
    })
}
