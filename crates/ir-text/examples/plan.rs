//! Experimental plan export. Source IO and origin rendering remain in the frontend.
use denotate_check::{Limits, stable_query::QueryLimits};
use denotate_ir_text::{LoadedProgram, filesystem, index, load};
use denotate_plan::{Build, Options, Planner, Problem};
use serde_json::{Value, json};
use std::{path::PathBuf, process::ExitCode};

const USAGE: &str = "just plan-den ROOT --verification NAME --output RELATION [--output RELATION ...]\n\
  --max-atoms N --max-rules N --max-work N --timeout-ms N\n\
  --max-nodes N --max-oracle-calls N --max-available N\n\
  --max-split-depth N --max-splits N --max-split-candidates N --max-support-trials N\n\
Exports a conditional plan for permitted inputs, not executable code or input validation.";
struct Args {
    root: PathBuf,
    verification: String,
    outputs: Vec<String>,
    limits: Limits,
    options: Options,
}
fn parse(args: impl IntoIterator<Item = String>) -> Result<Args, String> {
    let mut args = args.into_iter();
    let root = args.next().ok_or(USAGE)?.into();
    let mut result = Args {
        root,
        verification: String::new(),
        outputs: vec![],
        limits: Limits::default(),
        options: Options::default(),
    };
    while let Some(arg) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("Missing value for {arg}\n{USAGE}"))?;
        match arg.as_str() {
            "--verification" => {
                if !result.verification.is_empty() {
                    return Err("Select one verification".into());
                }
                result.verification = value;
            }
            "--output" => result.outputs.push(value),
            "--max-atoms" => result.limits.max_atoms = number(&value)?,
            "--max-rules" => result.limits.max_rules = number(&value)?,
            "--max-work" => result.limits.max_work = number(&value)?,
            "--timeout-ms" => {
                result.limits.timeout =
                    std::time::Duration::from_millis(value.parse().map_err(|_| "Invalid timeout")?)
            }
            "--max-nodes" => result.options.max_nodes = number(&value)?,
            "--max-oracle-calls" => result.options.max_oracle_calls = number(&value)?,
            "--max-split-depth" => result.options.max_split_depth = number(&value)?,
            "--max-splits" => result.options.max_splits = number(&value)?,
            "--max-split-candidates" => result.options.max_split_candidates = number(&value)?,
            "--max-support-trials" => result.options.max_support_trials = number(&value)?,
            "--max-available" => result.options.oracle.max_available = number(&value)?,
            _ => return Err(format!("Unknown option {arg}\n{USAGE}")),
        }
    }
    if result.verification.is_empty() || result.outputs.is_empty() {
        return Err(USAGE.into());
    }
    Ok(result)
}
fn number(raw: &str) -> Result<usize, String> {
    raw.parse()
        .map_err(|_| format!("Expected non-negative integer: {raw}"))
}
fn matches(
    p: &LoadedProgram,
    id: impl Into<denotate_ir::OccurrenceId>,
    name: &str,
    wanted: &index::Name,
) -> bool {
    !wanted.generated
        && wanted.text == name
        && wanted
            .namespace
            .as_ref()
            .is_none_or(|ns| p.corpus.namespace(id) == Some(ns))
}
fn export(p: &LoadedProgram, args: &Args) -> Result<(u8, Value), String> {
    let wanted = index::parse_name(&args.verification)?;
    let vs: Vec<_> = p
        .corpus
        .verifications()
        .filter(|v| matches(p, v.id, &v.name, &wanted))
        .collect();
    let [v] = vs.as_slice() else {
        return Err("Unknown or ambiguous verification; use its qualified name".into());
    };
    let mut planner = Planner::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v.id,
        &args.limits,
        QueryLimits::default(),
    )
    .map_err(|e| e.to_string())?;
    let mut outputs = Vec::new();
    for raw in &args.outputs {
        let wanted = index::parse_name(raw)?;
        let rs: Vec<_> = p
            .corpus
            .relations()
            .filter(|r| matches(p, r.id, &r.name, &wanted))
            .collect();
        let [r] = rs.as_slice() else {
            return Err(format!(
                "Unknown or ambiguous output {raw}; use its qualified name"
            ));
        };
        outputs.extend(
            planner
                .relation_outputs(r.id, 0)
                .map_err(|e| e.to_string())?,
        );
        if outputs.len() > args.limits.max_atoms {
            return Err("Output expansion exceeds max-atoms".into());
        }
    }
    let built = planner
        .build(&outputs, &args.options)
        .map_err(|e| e.to_string())?;
    let result: Result<(u8, Value), String> = match built {
        Build::Ready(plan) => {
            let mut output = plan.to_json();
            // Source metadata is separate from plan identity. Keep embedded loc
            // descriptors even when upstream documents cannot be opened here.
            let mut source_index = denotate_ir_text::origins::SourceIndex::new(&p.sources);
            attach_origins(p, &mut source_index, plan.nodes(), &mut output["nodes"])?;
            qualify_constants(p, &mut output);
            Ok((0, output))
        }
        Build::NoPermittedWorlds => Ok((2, json!({"state":"no-permitted-worlds"}))),
        Build::Inconclusive(e) => Ok((2, json!({"state":"inconclusive","reason":e.to_string()}))),
        Build::OracleInconclusive(e) => Ok((
            2,
            json!({"state":"inconclusive","phase":e.phase,"resource":e.resource}),
        )),
        Build::Problem(problem) => Ok((2, problem_json(p, problem))),
    };
    let (code, mut result) = result?;
    result["meaningScope"] = denotate_plan::scope_json(planner.scope());
    Ok((code, result))
}
fn attach_origins(
    p: &LoadedProgram,
    source_index: &mut denotate_ir_text::origins::SourceIndex<'_>,
    nodes: &std::collections::BTreeMap<denotate_check::AtomKey, denotate_plan::Node>,
    json_nodes: &mut Value,
) -> Result<(), String> {
    let mut metadata = Vec::new();
    for node in nodes.values() {
        let mut origins = std::collections::BTreeSet::new();
        for key in &node.sources {
            let id = p
                .keys
                .bindings()
                .resolve(&denotate_ir::OccurrenceKey::Rule(key.clone()))
                .map_err(|e| e.to_string())?;
            for origin in p.provenance.origins(id) {
                origins.insert(source_index.descriptor(origin).map_err(|e| e.to_string())?);
            }
            if let Some(upstream) = p
                .embedded
                .associations
                .get(&denotate_ir_text::origins::OriginTarget::Occurrence(id))
            {
                origins.extend(upstream.iter().cloned());
            }
        }
        metadata.push(json!(
            origins
                .into_iter()
                .map(|o| json!({
                    "uri": o.source.uri, "view": o.source.view, "hash": o.source.hash,
                    "start": {"line": o.start.line, "column": o.start.column},
                    "end": {"line": o.end.line, "column": o.end.column}
                }))
                .collect::<Vec<_>>()
        ));
    }
    for (node, origins) in json_nodes.as_array_mut().unwrap().iter_mut().zip(metadata) {
        node["origins"] = origins;
    }

    for (n, j) in nodes.values().zip(json_nodes.as_array_mut().unwrap()) {
        if let denotate_plan::Operation::Split {
            when_true,
            when_false,
            ..
        } = &n.operation
        {
            for (arm, name) in [(when_true, "then"), (when_false, "else")] {
                if let Some(r) = arm {
                    attach_origins(p, source_index, &r.nodes, &mut j["operation"][name])?;
                }
            }
        }
    }
    Ok(())
}
// The .den loader owns this encoding. Generic API callers' opaque constant keys
// must not be guessed/decoded by denotate-plan.
fn qualify_constants(p: &LoadedProgram, value: &mut Value) {
    let names = p
        .corpus
        .constants()
        .map(|c| {
            let key = p.keys.constant(c.id).unwrap();
            let (namespace, name): (String, String) =
                serde_json::from_str(&key.name).expect(".den constant key");
            (
                key.name.to_string(),
                json!({"namespace":namespace,"name":name}),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    fn visit(v: &mut Value, names: &std::collections::BTreeMap<String, Value>) {
        match v {
            Value::Object(o) => {
                if o.contains_key("sort") {
                    if let Some(name) = o
                        .get("name")
                        .and_then(Value::as_str)
                        .and_then(|s| names.get(s))
                        .cloned()
                    {
                        o.insert("name".into(), name);
                    }
                }
                for v in o.values_mut() {
                    visit(v, names);
                }
            }
            Value::Array(xs) => {
                for x in xs {
                    visit(x, names);
                }
            }
            _ => {}
        }
    }
    visit(value, &names);
}
fn problem_json(p: &LoadedProgram, problem: Problem) -> Value {
    use denotate_check::stable_query::{Existence, Uniqueness};
    let mut result = json!({"state":"unresolved"});
    match problem {
        Problem::Meaning(m) => {
            let world = match m.existence {
                Existence::NoMeaning(w) => {
                    result["reason"] = json!("no-meaning");
                    Some(w)
                }
                _ => match m.uniqueness {
                    Uniqueness::Multiple { observation, .. } => {
                        result["reason"] = json!("multiple-meanings");
                        Some(observation)
                    }
                    _ => None,
                },
            };
            if let Some(w) = world {
                let tuple = |a: &denotate_check::GroundAtom| {
                    denotate_plan::atom_json(
                        &denotate_check::AtomKey::from_atom(&p.keys, a).unwrap(),
                    )
                };
                result["world"] = json!({
                    "present": w.present.iter().map(tuple).collect::<Vec<_>>(),
                    "absent": w.absent.iter().map(tuple).collect::<Vec<_>>()
                });
            }
        }
        Problem::Unresolved {
            atoms,
            path,
            dependencies,
            world,
            ..
        } => {
            result["path"] = json!(
                path.iter()
                    .map(|(a, v)| json!({"atom":denotate_plan::atom_json(a),"value":v}))
                    .collect::<Vec<_>>()
            );
            result["dependencies"]=json!(dependencies.iter().map(|(a,b,p)|json!({"consumer":denotate_plan::atom_json(a),"provider":denotate_plan::atom_json(b),"positive":p})).collect::<Vec<_>>());
            if let Some(w) = world {
                result["world"] = json!({"present":w.true_inputs().map(|a|denotate_plan::atom_json(&denotate_check::AtomKey::from_atom(&p.keys,a).unwrap())).collect::<Vec<_>>(),"otherInputs":"absent"});
            }
            result["reason"] = json!("bounded-strategies-unresolved");
            result["atoms"] = json!(
                atoms
                    .iter()
                    .map(denotate_plan::atom_json)
                    .collect::<Vec<_>>()
            );
        }
    }
    qualify_constants(p, &mut result);
    result
}
fn main() -> ExitCode {
    if std::env::args().any(|a| a == "--help") {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let result = (|| {
        let args = parse(std::env::args().skip(1))?;
        let (membership, sources) =
            filesystem::discover(&args.root).map_err(|e| format!("{e:?}"))?;
        let program = load(&membership, &sources).map_err(|e| format!("{e:?}"))?;
        export(&program, &args)
    })();
    match result {
        Ok((code, output)) => {
            println!("{}", serde_json::to_string_pretty(&output).unwrap());
            ExitCode::from(code)
        }
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use denotate_ir_text::{ProgramMembership, SourceFile};
    fn program(text: &str) -> LoadedProgram {
        let s = SourceFile::new("file:///plan.den", 1, text);
        load(&ProgramMembership::single("plan", [s.uri.clone()]), &[s]).unwrap()
    }
    fn args() -> Args {
        parse(["root", "--verification", "checks", "--output", "out"].map(str::to_owned)).unwrap()
    }
    #[test]
    fn export_contains_dependency_plan_and_source_origins() {
        let p = program(
            "input i(); relation out(); out() :- !i(); verification checks { assumptions: []; obligations: []; }",
        );
        let (code, json) = export(&p, &args()).unwrap();
        assert_eq!(code, 0);
        assert_eq!(json["size"]["nodes"], 1);
        assert_eq!(json["inputs"].as_array().unwrap().len(), 1);
        assert_eq!(json["nodes"][0]["origins"][0]["uri"], "file:///plan.den");
    }
    #[test]
    fn missing_meaning_and_limits_have_no_plan_and_nonzero_exit() {
        let p = program(
            "relation out(); out() :- !out(); verification checks { assumptions: []; obligations: []; }",
        );
        let (code, j) = export(&p, &args()).unwrap();
        assert_eq!(code, 2);
        assert_eq!(j["reason"], "no-meaning");
        assert!(j.get("nodes").is_none());
        let p = program(
            "relation out(); out(); verification checks { assumptions: []; obligations: []; }",
        );
        let mut a = args();
        a.options.max_nodes = 0;
        let (code, j) = export(&p, &a).unwrap();
        assert_eq!(code, 2);
        assert_eq!(j["state"], "inconclusive");
    }
    #[test]
    fn explicit_selection_and_resolved_domain_output_expansion() {
        assert!(parse(["root".into()]).is_err());
        let p = program(
            "sort S; const a,b:S; domain S=[b]; relation out(x:S); out(b); verification checks { assumptions: []; obligations: []; }",
        );
        let (_, j) = export(&p, &args()).unwrap();
        assert_eq!(j["outputs"].as_array().unwrap().len(), 1);
        let b = p.corpus.constants().find(|c| c.name == "b").unwrap();
        assert_eq!(
            j["outputs"][0]["atom"]["arguments"][0]["name"],
            json!({"namespace":"","name":b.name})
        );
    }

    #[test]
    fn runnable_example_plan_matches_independent_models_in_every_world() {
        use denotate_check::{
            AtomKey, GroundProgram,
            test_support::rewrites::{stable_models, subsets},
        };
        use std::collections::{BTreeMap, BTreeSet};
        let p = program(include_str!("../../../fixtures/execution-plan/program.den"));
        let v = p.corpus.verifications().next().unwrap();
        let r = p.corpus.relations().find(|r| r.name == "result").unwrap();
        let mut planner = Planner::prepare(
            &p.corpus,
            &p.domains,
            &p.keys,
            v.id,
            &Limits::default(),
            QueryLimits::default(),
        )
        .unwrap();
        let outputs = planner.relation_outputs(r.id, 0).unwrap();
        let Build::Ready(plan) = planner.build(&outputs, &Options::default()).unwrap() else {
            panic!("expected complete plan")
        };
        let graph = GroundProgram::prepare(&p.corpus, &p.domains, &Limits::default()).unwrap();
        let atoms = graph.atoms().cloned().collect::<Vec<_>>();
        let inputs = graph.input_atoms().cloned().collect::<BTreeSet<_>>();
        let rules = graph.rules().cloned().collect::<Vec<_>>();
        for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
            let models = stable_models(&atoms, &inputs, &rules, &world);
            assert_eq!(models.len(), 1);
            let values = inputs
                .iter()
                .map(|a| (AtomKey::from_atom(&p.keys, a).unwrap(), world.contains(a)))
                .collect::<BTreeMap<_, _>>();
            let actual = plan
                .execute_permitted(&values, denotate_plan::Order::Semantic, 100_000)
                .unwrap();
            for output in &outputs {
                assert_eq!(
                    actual.outputs[&AtomKey::from_atom(&p.keys, &output.atom).unwrap()],
                    models.first().unwrap().contains(&output.atom)
                );
            }
        }
    }
    #[test]
    fn branch_export_has_join_bindings_nested_origins_and_new_limit_flags() {
        let p = program(include_str!(
            "../../../fixtures/execution-plan-branches/program.den"
        ));
        let mut a = args();
        a.outputs = vec!["result".into()];
        let (code, j) = export(&p, &a).unwrap();
        assert_eq!(code, 0);
        assert_eq!(j["version"], 4);
        assert_eq!(j["size"]["branches"], 1);
        assert_eq!(j["size"]["joins"], 1);
        let split = j["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .find(|n| n["operation"]["kind"] == "split")
            .unwrap();
        for arm in ["then", "else"] {
            for node in split["operation"][arm].as_array().unwrap() {
                assert!(!node["origins"].as_array().unwrap().is_empty());
            }
        }
        assert_eq!(
            split["operation"]["join"]["outputs"]
                .as_array()
                .unwrap()
                .len(),
            2
        );
        let a = parse(
            [
                "root",
                "--verification",
                "checks",
                "--output",
                "result",
                "--max-split-depth",
                "0",
                "--max-splits",
                "2",
                "--max-split-candidates",
                "10",
                "--max-support-trials",
                "0",
            ]
            .map(str::to_owned),
        )
        .unwrap();
        let (code, j) = export(&p, &a).unwrap();
        assert_eq!(code, 2);
        assert_eq!(j["state"], "inconclusive");
        assert!(j.get("nodes").is_none());
    }
    #[test]
    fn reviewer_example_exports_a_direct_read_without_unrelated_support() {
        let p = program(include_str!("../../../fixtures/execution-plan/program.den"));
        let mut a = args();
        a.outputs = vec!["result".into()];
        let (_, j) = export(&p, &a).unwrap();
        let left = j["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .find(|n| n["id"]["relation"]["named"]["name"] == "left")
            .unwrap();
        assert_eq!(left["inputs"].as_array().unwrap().len(), 1);
        assert_eq!(
            left["operation"]["expression"]["nodes"]
                .as_array()
                .unwrap()
                .len(),
            1
        );
        assert_eq!(
            left["operation"]["expression"]["nodes"][0]["read"]["relation"]["named"]["name"],
            "selected"
        );
    }
    #[test]
    fn qualified_constant_names_are_structured_and_preserve_quoted_names() {
        let p = program(
            "sort S; namespace vals {const 'odd value': S;} relation out(x:S); out(vals::'odd value'); verification checks {assumptions: []; obligations: [];}",
        );
        let (_, j) = export(&p, &args()).unwrap();
        assert_eq!(
            j["outputs"][0]["atom"]["arguments"][0]["name"],
            json!({"namespace":"vals","name":"odd value"})
        );
    }
    #[test]
    fn ambiguous_output_cone_is_not_hidden_by_downstream_filters() {
        let p = program(
            "input p(); relation a(); relation b(); relation reject(); a() :- !b(); b() :- !a(); reject() :- a(), !p(), !reject(); reject() :- b(), p(), !reject(); verification checks {assumptions: []; obligations: [];}",
        );
        let mut a = args();
        a.outputs = vec!["a".into()];
        let (code, j) = export(&p, &a).unwrap();
        assert_eq!(code, 2);
        assert_eq!(j["state"], "unresolved");
        assert_eq!(j["reason"], "multiple-meanings");
        assert_eq!(j["meaningScope"]["kind"], "output-cones");
        assert_eq!(j["meaningScope"]["outsideAnalysed"], false);
        assert!(j["world"].is_object());
        assert!(j.get("nodes").is_none());
    }
    #[test]
    fn output_scope_exports_boundary_for_success_and_cutoffs() {
        let p = program(
            "input x(); relation out(); out():-x(); relation bad(); bad():-out(),!bad(); verification checks{assumptions:[];obligations:[];}",
        );
        let (code, j) = export(&p, &args()).unwrap();
        assert_eq!(code, 0, "{j}");
        assert_eq!(
            j["meaningScope"]["coneSize"],
            json!({"atoms":2,"ruleInstances":1})
        );
        assert_eq!(j["meaningScope"]["outsideAnalysed"], false);
        assert!(
            j["contract"]
                .as_str()
                .unwrap()
                .contains("outside not analysed")
        );
        let mut a = args();
        a.limits.max_work = 0;
        let (code, j) = export(&p, &a).unwrap();
        assert_eq!(code, 2);
        assert_eq!(j["state"], "inconclusive");
        assert!(j["meaningScope"]["coneSize"].is_null());
        assert_eq!(j["meaningScope"]["outsideAnalysed"], false);
    }
    #[test]
    fn outside_assumptions_still_restrict_the_plans_input_contract() {
        let p = program(
            "input x();relation guard();guard():-x();relation out();out():-!x();assumption yes:at_least_one(guard,group_by:());verification checks{assumptions:[yes];obligations:[];}",
        );
        let (code, j) = export(&p, &args()).unwrap();
        assert_eq!(code, 0, "{j}");
        assert_eq!(
            j["nodes"][0]["operation"]["expression"]["nodes"][0],
            json!({"constant":false})
        );
        let p = program(
            "input x();relation guard();guard():-x();relation out();out():-x();assumption yes:at_least_one(guard,group_by:());assumption no:empty(guard);verification checks{assumptions:[yes,no];obligations:[];}",
        );
        let (code, j) = export(&p, &args()).unwrap();
        assert_eq!(code, 2);
        assert_eq!(j["state"], "no-permitted-worlds");
        assert_eq!(j["meaningScope"]["outsideAnalysed"], false);
    }
    #[test]
    fn explicit_atom_roots_exclude_sibling_tuples_and_include_legal_absences() {
        use denotate_check::{AtomKey, GroundAtom};
        let p = program(
            "sort S;const a,b,c:S;relation out(s:S);out(a);out(b):-!out(b);verification checks{assumptions:[];obligations:[];}",
        );
        let r = p.corpus.relations().find(|r| r.name == "out").unwrap().id;
        let v = p.corpus.verifications().next().unwrap().id;
        let mut planner = Planner::prepare(
            &p.corpus,
            &p.domains,
            &p.keys,
            v,
            &Limits::default(),
            QueryLimits::default(),
        )
        .unwrap();
        for (name, expected) in [
            ("a", Some(true)),
            ("b", None),
            ("c", Some(false)),
            ("a", Some(true)),
        ] {
            let c = p.corpus.constants().find(|c| c.name == name).unwrap().id;
            let a = GroundAtom::new(r, [c]);
            let result = planner
                .build(
                    &[denotate_plan::Output {
                        atom: a.clone(),
                        priority: 0,
                    }],
                    &Options::default(),
                )
                .unwrap();
            if let Some(expected) = expected {
                let Build::Ready(plan) = result else {
                    panic!("{result:?}")
                };
                let run = plan
                    .execute_permitted(&Default::default(), denotate_plan::Order::Semantic, 1000)
                    .unwrap();
                assert_eq!(
                    run.outputs[&AtomKey::from_atom(&p.keys, &a).unwrap()],
                    expected
                );
            } else {
                assert!(matches!(result, Build::Problem(Problem::Meaning(_))));
            }
        }
        // Relation expansion intentionally selects all three tuples, including b.
        let (code, j) = export(&p, &args()).unwrap();
        assert_eq!(code, 2);
        assert_eq!(j["reason"], "no-meaning");
    }
    #[test]
    fn scheduling_branch_queries_do_not_see_an_outside_paradox() {
        let p = program(&format!(
            "{} relation outside(); outside():-!outside();",
            include_str!("../../../fixtures/execution-plan-branches/program.den")
        ));
        let mut a = args();
        a.outputs = vec!["result".into()];
        let (code, j) = export(&p, &a).unwrap();
        assert_eq!(code, 0, "{j}");
        assert_eq!(j["size"]["branches"], 1);
        let split = j["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .find(|n| n["operation"]["kind"] == "split")
            .unwrap();
        assert!(split["operation"]["then"].is_array());
        assert!(split["operation"]["else"].is_array());
        assert_eq!(j["meaningScope"]["outsideAnalysed"], false);
    }
}
