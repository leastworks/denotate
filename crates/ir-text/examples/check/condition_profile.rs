//! Serialize opt-in generic checker observations using this invocation's names.
use denotate_check::{ConditionObservation as O, GroundAtom, Profile};
use denotate_ir_text::{LoadedProgram, presentation::diagnostic_names};
use serde_json::json;

pub fn install(p: &LoadedProgram, profile: &Profile, file: Option<super::profile_writer::Shared>) {
    let spelling = diagnostic_names(&p.corpus);
    let relations: std::collections::BTreeMap<_, _> = p
        .corpus
        .relations()
        .map(|r| {
            (
                p.keys.relation(r.id).unwrap().clone(),
                spelling(r.id.into()),
            )
        })
        .collect();
    let constants: std::collections::BTreeMap<_, _> = p
        .corpus
        .constants()
        .map(|c| {
            (
                p.keys.constant(c.id).unwrap().clone(),
                spelling(c.id.into()),
            )
        })
        .collect();
    let names = std::sync::Mutex::new(
        p.corpus
            .relations()
            .map(|r| (r.id.into(), spelling(r.id.into())))
            .chain(
                p.corpus
                    .constants()
                    .map(|c| (c.id.into(), spelling(c.id.into()))),
            )
            .collect::<std::collections::BTreeMap<denotate_ir::OccurrenceId, String>>(),
    );
    let started = std::time::Instant::now();
    profile.observe_conditions(move |event| {
        let mut labels = names.lock().unwrap();
        match &event.observation {
            O::BindDeclarations { relations: rs, constants: cs } => {
                for (id,key) in rs { if let Some(name) = relations.get(key) { labels.insert((*id).into(),name.clone()); } }
                for (id,key) in cs { if let Some(name) = constants.get(key) { labels.insert((*id).into(),name.clone()); } }
                return;
            }
            O::UnbindDeclarations { ids } => { for id in ids { labels.remove(id); } return; }
            _ => {}
        }
        let names = |id| labels.get(&id).cloned().unwrap_or_else(|| format!("unresolved-profile-id:{id:?}"));
        let atom = |a: &GroundAtom| json!({"relation": names(a.relation.into()), "arguments": a.arguments.iter().map(|c| names((*c).into())).collect::<Vec<_>>()});
        let mut detail = match event.observation {
            O::BindDeclarations { .. } | O::UnbindDeclarations { .. } => unreachable!(),
            O::RecursiveShape(s) => json!({"kind":"recursive-component-shape", "component":s.component,"atoms":s.atoms,"rules":s.rules,
                "relations":s.relations.iter().map(|(r,n)| json!({"relation":names((*r).into()),"atoms":n})).collect::<Vec<_>>(),
                "omittedRelations":s.omitted_relations,"cycles":s.cycles.iter().map(|c| c.iter().map(atom).collect::<Vec<_>>()).collect::<Vec<_>>(),"cycleSearchTruncated":s.cycle_search_truncated}),
            O::RecursiveSnapshot(s) => json!({"kind":"recursive-component", "component":s.component,"state":s.state,"error":s.error.map(|e|e.to_string()),
                "completedRounds":s.completed_rounds,"ruleVisits":s.rule_visits,"ruleEvaluations":s.rule_evaluations,"changedHeads":s.changed_heads,"previousRoundChangedHeads":s.previous_round_changed_heads,"restarts":s.restarts,"schedulerEntries":s.scheduler_entries,"schedule":if s.scheduler_entries==0 {"scan"}else{"worklist"},
                "accountedNodes":s.accounted_nodes,"componentNodes":s.component_nodes,
                "retainedArrays":s.storage.distinct_arrays,"retainedArrayNodes":s.storage.nodes,"retainedNodeBytes":s.storage.node_bytes,"conditionReferences":s.storage.references,
                "resultArrays":s.result_arrays,"resultNodes":s.result_nodes,
                "largest":s.largest.iter().map(|(a,n)|json!({"atom":atom(a),"nodes":n})).collect::<Vec<_>>(),
                "relations":s.relations.iter().map(|r|json!({"relation":names(r.relation.into()),"atoms":r.atoms,"conditions":r.conditions,"nodes":r.nodes})).collect::<Vec<_>>(),"omittedRelations":s.omitted_relations}),
            O::InputOrder {atoms, report} => json!({"kind":"input-order", "atoms":atoms.iter().map(atom).collect::<Vec<_>>(), "requested":report.requested.label(), "effective":report.effective.label(), "fallback":report.fallback,"declaredBlocks":report.declared_blocks,"placementBlocks":report.placement_blocks,"scatteredDeclaredGroups":report.scattered_declared_groups}),
            O::Retained {atom:a, nodes} => json!({"kind":"retained-condition", "atom":atom(&a), "nodes":nodes, "minimumNodes":64}),
            O::AssumptionStep {kind, group, atom:a, seen_nodes, permitted_nodes} => json!({"kind":"assumption-step", "restriction":kind,"group":group,"atom":a.as_ref().map(atom),"seenNodes":seen_nodes,"permittedNodes":permitted_nodes}),
            O::FailedOperation {operation, left_nodes, right_nodes, error} => json!({"kind":"failed-operation", "operation":if right_nodes.is_none() { "not" } else { match operation { [Some(false),Some(false),Some(false),Some(true)] => "and", [Some(false),Some(true),Some(true),Some(true)] => "or", [Some(false),Some(false),Some(true),Some(false)] => "and-not", _ => "binary" } }, "truthTable":operation,"leftNodes":left_nodes,"rightNodes":right_nodes,"error":error.to_string()}),
        };
        detail["type"] = json!("condition-profile");
        detail["elapsedMs"] = json!(started.elapsed().as_secs_f64() * 1000.);
        detail["stages"] = json!(event.stages);
        detail["target"] = json!(event.target.as_ref().map(atom));
        super::profile_record(&file, detail);
    });
}
