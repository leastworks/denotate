use super::*;
use denotate_check::completion_query as q;
use denotate_plan::completion::{Accepted, AcceptedNext, Build, Next, Planner, Problem, Region};

pub(super) fn export(
    p: &LoadedProgram,
    args: &Args,
    v: denotate_ir::VerificationId,
    outputs: &[denotate_plan::Output],
) -> Result<(u8, Value), String> {
    let planner = Planner::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &args.limits,
        q::QueryLimits {
            max_solves: args.queries.max_solves,
            max_solver_polls: args.queries.max_solver_polls,
            max_conflicts: args.queries.max_conflicts,
            max_propagations: args.queries.max_propagations,
        },
    )
    .map_err(|e| e.to_string())?;
    let (code, mut json) = match planner
        .build(outputs, &args.options)
        .map_err(|e| e.to_string())?
    {
        Build::Ready(plan) => {
            let mut j = plan.to_json();
            let mut sources = denotate_ir_text::origins::SourceIndex::new(&p.sources);
            region_origins(p, &mut sources, plan.root(), &mut j["plan"])?;
            (0, j)
        }
        Build::NoPermittedWorlds => (2, json!({"state":"no-permitted-worlds"})),
        Build::Inconclusive(e) => (2, json!({"state":"inconclusive","reason":e.to_string()})),
        Build::OracleInconclusive(e) => (
            2,
            json!({"state":"inconclusive","phase":e.phase,"resource":e.resource}),
        ),
        Build::Problem(problem) => (2, problem_json(p, *problem)?),
    };
    json["semantics"] = json!("completion");
    qualify_constants(p, &mut json);
    Ok((code, json))
}
fn problem_json(p: &LoadedProgram, problem: Problem) -> Result<Value, String> {
    let atom = |a: &denotate_check::GroundAtom| {
        denotate_check::AtomKey::from_atom(&p.keys, a)
            .map(|a| denotate_plan::atom_json(&a))
            .map_err(|e| e.to_string())
    };
    let observation = |o: &denotate_check::Observation| -> Result<Value, String> {
        Ok(
            json!({"present":o.present.iter().map(&atom).collect::<Result<Vec<_>,_>>()?,"absent":o.absent.iter().map(&atom).collect::<Result<Vec<_>,_>>()?}),
        )
    };
    let model = |m: &q::Model| -> Result<Value, String> {
        Ok(
            json!({"observation":observation(&m.observation())?,"values":m.interpretation().map(|(a,v)|Ok(json!({"atom":atom(a)?,"value":v}))).collect::<Result<Vec<_>,String>>()?}),
        )
    };
    Ok(match problem {
        Problem::InputDomains(issues) => {
            let mut unknown = false;
            let mut rows = Vec::new();
            for issue in issues {
                let relation = |r| -> Result<Value, String> {
                    Ok(denotate_plan::atom_json(&denotate_check::AtomKey {
                        relation: p.keys.relation(r).map_err(|e| e.to_string())?.clone(),
                        arguments: vec![],
                    })["relation"]
                        .clone())
                };
                let mut row =
                    json!({"input":relation(issue.input)?,"provider":relation(issue.provider)?});
                match issue.failure {
                    q::InputDomainFailure::Ambiguous(pair) => {
                        row["reason"] = json!("multiple-meanings");
                        row["first"] = model(&pair.first)?;
                        row["second"] = model(&pair.second)?;
                    }
                    q::InputDomainFailure::NoMeaning => row["reason"] = json!("no-meaning"),
                    q::InputDomainFailure::NotNeeded => row["reason"] = json!("not-needed"),
                    q::InputDomainFailure::Inconclusive(c) => {
                        unknown = true;
                        row["reason"] = json!("inconclusive");
                        row["phase"] = json!(c.phase);
                        row["resource"] = json!(c.resource);
                    }
                }
                rows.push(row);
            }
            json!({"state":if unknown {"inconclusive"}else{"unresolved"},"code":"plan-meaning-failure","reason":"input-domains","issues":rows})
        }
        Problem::Context(c) => {
            let mut j = json!({"state":if c.outcome==q::PathOutcome::Inconclusive {"inconclusive"}else{"unresolved"},"code":"plan-meaning-failure","phase":"classification","outcome":format!("{:?}",c.outcome)});
            let mut cutoffs = Vec::new();
            if let Some(cause) = &c.inconclusive {
                cutoffs.push(json!({"phase":cause.phase,"resource":cause.resource}));
            }
            let mut assumptions = Vec::new();
            for a in &c.assumptions {
                let key = p.keys.assumption(a.assumption).map_err(|e| e.to_string())?;
                let mut item = json!({"assumption":{"namespace":key.0.namespace.as_ref(),"name":key.0.name.as_ref()},"certified":a.certified()});
                if let q::Search::Exists(w) = &a.no_meaning {
                    item["reason"] = json!("no-meaning");
                    item["world"] = observation(w)?;
                }
                if let q::Search::Exists(pair) = &a.ambiguous {
                    item["reason"] = json!("multiple-truths");
                    item["first"] = model(&pair.models.first)?;
                    item["second"] = model(&pair.models.second)?;
                }
                for cause in [cause(&a.no_meaning), cause(&a.ambiguous)]
                    .into_iter()
                    .flatten()
                {
                    cutoffs.push(cause);
                }
                assumptions.push(item);
            }
            j["assumptions"] = json!(assumptions);
            if let Some(c) = c.classification {
                for cause in [
                    cause(&c.accepted),
                    cause(&c.rejected),
                    cause(&c.no_meaning),
                    cause(&c.ambiguous),
                ]
                .into_iter()
                .flatten()
                {
                    cutoffs.push(cause);
                }

                if let q::Search::Exists(w) = c.no_meaning {
                    j["reason"] = json!("no-meaning");
                    j["world"] = observation(&w)?;
                }
                if let q::Search::Exists(pair) = c.ambiguous {
                    j["reason"] = json!("multiple-meanings");
                    j["first"] = model(&pair.first)?;
                    j["second"] = model(&pair.second)?;
                }
            }
            j["inconclusive"] = json!(cutoffs);
            j
        }
        Problem::MeaningFailure { path } => {
            json!({"state":"unresolved","code":"plan-meaning-failure","phase":"outputs","reason":"no-meaning","path":path_json(&path)})
        }
        Problem::PathInconclusive { path, cause } => {
            json!({"state":"inconclusive","phase":cause.phase,"resource":cause.resource,"path":path_json(&path)})
        }
        Problem::Unresolved {
            phase,
            path,
            atoms,
            dependencies,
        } => {
            json!({"state":"unresolved","code":"plan-value-unresolved","phase":phase,"reason":"path-driver-unresolved","path":path_json(&path),"atoms":atoms.iter().map(denotate_plan::atom_json).collect::<Vec<_>>(),"dependencies":dependencies.iter().map(|(a,b,p)|json!({"consumer":denotate_plan::atom_json(a),"provider":denotate_plan::atom_json(b),"positive":p})).collect::<Vec<_>>()})
        }
    })
}

fn cause<T>(search: &q::Search<T>) -> Option<Value> {
    match search {
        q::Search::Inconclusive(c) => Some(json!({"phase":c.phase,"resource":c.resource})),
        _ => None,
    }
}

fn path_json(path: &[(denotate_check::AtomKey, bool)]) -> Value {
    json!(
        path.iter()
            .map(|(a, v)| json!({"atom": denotate_plan::atom_json(a), "value": v}))
            .collect::<Vec<_>>()
    )
}
fn region_origins(
    p: &LoadedProgram,
    sources: &mut denotate_ir_text::origins::SourceIndex<'_>,
    r: &Region,
    j: &mut Value,
) -> Result<(), String> {
    attach_origins(p, sources, &r.nodes, &mut j["nodes"])?;
    match &r.next {
        Next::Split {
            then, otherwise, ..
        } => {
            region_origins(p, sources, then, &mut j["next"]["then"])?;
            region_origins(p, sources, otherwise, &mut j["next"]["else"])
        }
        Next::Leaf {
            accepted: Some(a), ..
        } => accepted_origins(p, sources, a, &mut j["next"]["accepted"]),
        Next::Leaf { .. } => Ok(()),
    }
}
fn accepted_origins(
    p: &LoadedProgram,
    sources: &mut denotate_ir_text::origins::SourceIndex<'_>,
    a: &Accepted,
    j: &mut Value,
) -> Result<(), String> {
    attach_origins(p, sources, &a.nodes, &mut j["nodes"])?;
    if let AcceptedNext::Split {
        then, otherwise, ..
    } = &a.next
    {
        accepted_origins(p, sources, then, &mut j["next"]["then"])?;
        accepted_origins(p, sources, otherwise, &mut j["next"]["else"])?;
    }
    Ok(())
}
