use super::*;
use std::collections::{BTreeMap, BTreeSet};
fn context(c: PruningContext) -> &'static str {
    match c {
        PruningContext::World => "W",
        PruningContext::Hypothesis => "W+H",
    }
}
fn record(p: &PruningRecord, r: &Report, keys: &SemanticKeys) -> Result<Value> {
    Ok(
        json!({"head":atom(&p.head,keys)?,"context":context(p.context),
        "kind":match p.kind {PruningKind::Subsumption=>"subsumption",PruningKind::Coverage=>"coverage"},
        "removedInstances":p.removed,"scopeHeads":p.scope_heads,"scope":p.scope,
        "sources":p.rules.iter().map(|id|Ok(crate::identity::rule(keys.rule(r.program().original_rule(*id).unwrap().source)?))).collect::<Result<Vec<_>>>()?,
        "omittedSources":p.removed.saturating_sub(p.rules.len())}),
    )
}
pub(super) fn summary(r: &Report, keys: &SemanticKeys) -> Result<Value> {
    Ok(json!({"elapsedMs":r.pruning.elapsed.as_secs_f64()*1000.0,
        "components":r.pruning.components.iter().map(|c|completion_pruning_component(c,|a|atom(a,keys))).collect::<Result<Vec<_>>>()?,
        "omittedComponents":r.pruning.omitted_components,"attempts":r.pruning.attempts,"removedInstances":r.pruning.removed,
        "coveredHeads":r.pruning.covered,"records":r.pruning.records.iter().map(|p|record(p,r,keys)).collect::<Result<Vec<_>>>()?,
        "omittedRecords":r.pruning.omitted,"cutoffs":r.pruning.incomplete.iter().map(|c|reason(*c)).collect::<Vec<_>>() }))
}
pub(super) fn findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    r: &Report,
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<CompletionFinding>> {
    let mut groups: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for p in &r.pruning.records {
        groups.entry((&p.head, p.context)).or_default().push(p);
    }
    groups.into_iter().map(|((head, c), records)| {
        let label = context(c);
        let sources: BTreeSet<_> = records.iter()
            .flat_map(|p| p.rules.iter())
            .map(|id| r.program().original_rule(*id).unwrap().source)
            .collect();
        let mut contributions: Vec<_> = sources.iter().take(32)
            .map(|id| Contribution { occurrence: (*id).into(), role: Role::Producer })
            .collect();
        if contributions.is_empty() {
            contributions.push(Contribution { occurrence: r.verification.into(), role: Role::Declaration });
        }
        let scopes = records.iter().map(|p|p.scope).collect::<BTreeSet<_>>()
            .into_iter().collect::<Vec<_>>().join(", ");
        let mut notes = vec![
            format!("Question scopes: {scopes}."),
            "These are solver-instance simplifications within the recorded question scopes; they are not edits to the authored rules.".into(),
        ];
        let omitted = sources.len().saturating_sub(32) + records.iter()
            .map(|p| p.removed.saturating_sub(p.rules.len())).sum::<usize>();
        if omitted > 0 {
            notes.push(format!("{omitted} additional source references omitted."));
        }
        let removed: usize = records.iter().map(|p| p.removed).sum();
        let coverage = records.iter().any(|p| p.kind == PruningKind::Coverage);
        let explanation = if coverage { "; coverage proves the head true" } else { " by subsumption" };
        let message = format!(
            "Completion simplification for {} under {label}: {removed} producer instance(s) removed{explanation}.",
            crate::evidence::atom_name(corpus, names, head)?,
        );
        let evidence = json!({
            "kind": "completion-pruning", "context": label, "head": atom(head, keys)?,
            "records": records.iter().map(|p| record(p,r,keys)).collect::<Result<Vec<_>>>()?,
        });
        Ok(CompletionFinding {
            finding: ContextFinding {
                identity: Identity::CompletionPruning(head.clone(), label),
                kind: Kind::CompletionPruning,
                message,
                notes,
                contributions,
            },
            evidence,
        })
    }).collect()
}
