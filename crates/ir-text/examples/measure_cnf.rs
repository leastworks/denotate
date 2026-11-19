//! Size-only experiment: the input universe U, without selected assumptions.
use denotate_check::{
    Limits,
    cnf_measurement::{Measurement, RelationSize, Report, SimplificationLimits, Size},
};
use denotate_ir_text::{LoadedProgram, filesystem, load};
use serde_json::{Value, json};
use std::time::{Duration, Instant};
fn size(s: &Size) -> Value {
    json!({"variables":s.variables,"clauses":s.clauses,"literal_occurrences":s.literals,"cnf_vector_bytes":s.storage_bytes})
}
fn relation_json(
    p: &LoadedProgram,
    sizes: &std::collections::BTreeMap<denotate_ir::RelationId, RelationSize>,
) -> Result<Vec<Value>, String> {
    let mut relations: Vec<_> = sizes.iter().map(|(r, s)| {
        let key = p.keys.relation(*r).map_err(|e| format!("{e:?}"))?;
        Ok(json!({"relation":format!("{key:?}"),"atom_variables":s.atom_variables,"auxiliary_variables":s.auxiliary_variables,"clauses":s.clauses,"literal_occurrences":s.literals,"payload_bytes":s.payload_bytes}))
    }).collect::<Result<_, String>>()?;
    relations.sort_by_key(|r| r["relation"].as_str().unwrap().to_owned());
    Ok(relations)
}
fn report_json(p: &LoadedProgram, report: &Report) -> Result<Value, String> {
    let relations = relation_json(p, &report.relations)?;
    let after_relations = relation_json(p, &report.after_relations)?;
    Ok(
        json!({"before":size(&report.before),"after":size(&report.after),
        "eliminated_variables":report.eliminated,"reconstruction_vector_bytes":report.reconstruction_bytes,
        "fixed_atoms":report.fixed_atoms,"residual_atoms":report.residual_atoms,"residual_rules":report.residual_rules,
        "before_by_relation":relations,"after_by_relation":after_relations}),
    )
}
fn measure(args: impl IntoIterator<Item = String>) -> Result<Value, String> {
    let mut args = args.into_iter();
    let root = args.next().ok_or("usage: just measure-den-cnf ROOT [--eliminate] [--simplify] [--compare-local-limits CONE,NODES,WORK] [--local-cone-atoms N] [--local-bdd-nodes N] [--local-work N] [--max-atoms N] [--max-rules N] [--max-dependencies N] [--max-work N] [--timeout-ms N]")?;
    let mut limits = Limits::default();
    let mut local = SimplificationLimits::default();
    let mut comparison = None;
    let mut eliminate = false;
    let mut simplify = false;
    while let Some(arg) = args.next() {
        if arg == "--eliminate" {
            eliminate = true;
            continue;
        }
        if arg == "--simplify" {
            simplify = true;
            continue;
        }
        if arg == "--compare-local-limits" {
            let values = args.next().ok_or("missing CONE,NODES,WORK")?;
            let values = values
                .split(',')
                .map(str::parse::<usize>)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|_| "invalid CONE,NODES,WORK")?;
            if values.len() != 3 {
                return Err("expected CONE,NODES,WORK".into());
            }
            comparison = Some(SimplificationLimits {
                max_cone_atoms: values[0],
                max_bdd_nodes: values[1],
                max_proof_work: values[2],
            });
            continue;
        }
        let value: usize = args
            .next()
            .ok_or("missing limit value")?
            .parse()
            .map_err(|_| "invalid nonnegative limit")?;
        match arg.as_str() {
            "--max-atoms" => limits.max_atoms = value,
            "--max-rules" => limits.max_rules = value,
            "--max-dependencies" => limits.max_dependencies = value,
            "--max-work" => limits.max_work = value,
            "--timeout-ms" => limits.timeout = Duration::from_millis(value as u64),
            "--local-cone-atoms" => local.max_cone_atoms = value,
            "--local-bdd-nodes" => local.max_bdd_nodes = value,
            "--local-work" => local.max_proof_work = value,
            _ => return Err(format!("unknown option {arg}")),
        }
    }
    let start = Instant::now();
    let (membership, files) =
        filesystem::discover(std::path::Path::new(&root)).map_err(|e| format!("{e:?}"))?;
    let p = load(&membership, &files).map_err(|e| format!("{e:?}"))?;
    let loading = start.elapsed();
    let start = Instant::now();
    let prepared =
        Measurement::prepare(&p.corpus, &p.domains, &limits).map_err(|e| e.to_string())?;
    let preparation = start.elapsed();
    let start = Instant::now();
    let mut output = if simplify {
        // Comparison always includes both elimination controls; --eliminate is
        // redundant when --simplify is present.
        let mut variants = Vec::new();
        for v in prepared
            .simplify_comparison(&local, &limits)
            .map_err(|e| e.to_string())?
        {
            let mut row = report_json(&p, &v.report)?;
            row["variant"] = json!(v.name);
            row["elapsed_ms"] = json!(v.elapsed.as_secs_f64() * 1000.);
            row["rewrite_record_vector_bytes"] = json!(v.proof_bytes);
            row["alias_mapping_vector_bytes"] = json!(v.mapping_bytes);
            row["model_vector_bytes_including_mapping"] = json!(v.model_bytes);
            row["passes"]=json!(v.passes.iter().map(|s|json!({"pass":s.pass.label(),"candidates":s.candidates,"proved":s.proved,"unchanged":s.unchanged,"unsupported_recursive_heads":s.unsupported,"cut_off":s.cut_off,"elapsed_ms":s.elapsed.as_secs_f64()*1000.})).collect::<Vec<_>>());
            variants.push(row);
        }
        json!({"variants":variants,"local_limits":{"cone_atoms":local.max_cone_atoms,"bdd_nodes_created":local.max_bdd_nodes,"work_per_proof":local.max_proof_work}})
    } else {
        report_json(
            &p,
            &prepared
                .measure(eliminate, &limits)
                .map_err(|e| e.to_string())?,
        )?
    };
    let encoding = start.elapsed();
    if let Some(other) = &comparison {
        let started = Instant::now();
        let difference = prepared
            .first_local_difference(&local, other, &limits)
            .map_err(|e| e.to_string())?;
        let observation = |v: &denotate_check::cnf_measurement::ProofObservation| json!({"answer":v.answer,"cutoff":v.cutoff.as_ref().map(ToString::to_string),"work":v.work,"cone_atoms":v.shape.cone_atoms,"expanded_definitions":v.shape.definitions,"free_cut_points":v.shape.cut_points,"groups":v.shape.groups,"omitted_groups":v.shape.omitted_groups,"bdd_nodes_created":v.shape.bdd_nodes_created});
        let atom = |a: &denotate_check::GroundAtom| -> Result<Value, String> {
            Ok(
                json!({"relation":format!("{:?}",p.keys.relation(a.relation).map_err(|e|format!("{e:?}"))?),"arguments":a.arguments.iter().map(|c|p.keys.constant(*c).map(|k|format!("{k:?}")).map_err(|e|format!("{e:?}"))).collect::<Result<Vec<_>,_>>()?}),
            )
        };
        let literal = |(a, v): &(denotate_check::GroundAtom, bool)| -> Result<Value, String> {
            Ok(json!({"atom":atom(a)?,"positive":v}))
        };
        let first = match difference {
            None => Value::Null,
            Some(d) => {
                json!({"question":d.question,"head":atom(&d.head)?,"body":d.body.iter().map(literal).collect::<Result<Vec<_>,_>>()?,"premise":d.premise.as_ref().map(literal).transpose()?,"base":observation(&d.base),"comparison":observation(&d.comparison)})
            }
        };
        output["local_proof_comparison"] = json!({"scope":"same original acyclic snapshot; no sequential rewriting","base_limits":{"cone_atoms":local.max_cone_atoms,"bdd_nodes_created":local.max_bdd_nodes,"work_per_proof":local.max_proof_work},"comparison_limits":{"cone_atoms":other.max_cone_atoms,"bdd_nodes_created":other.max_bdd_nodes,"work_per_proof":other.max_proof_work},"first_lost_proof":first});
        output["local_comparison_ms"] = json!(started.elapsed().as_secs_f64() * 1000.);
    }
    let component_start = Instant::now();
    let recursive = prepared
        .recursive_components(&limits)
        .map_err(|e| e.to_string())?;
    let sizes = |s: &denotate_check::cnf_measurement::RecursiveSizes| json!({"components":s.components,"atoms":s.atoms,"rule_instances":s.rules,"largest_atoms":s.largest_atoms,"largest_rule_instances":s.largest_rules,"above_100_atoms":s.above_100_atoms,"atom_size_histogram":s.histogram});
    let components=recursive.components.iter().map(|c| {
        let relations=c.relations.iter().map(|(r,n)|Ok(json!({"relation":format!("{:?}",p.keys.relation(*r).map_err(|e|format!("{e:?}"))?),"atoms":n}))).collect::<Result<Vec<_>,String>>()?;
        Ok(json!({"index":c.index,"kind":if c.negative {"negative"} else {"positive"},"atoms":c.atoms,"rule_instances":c.rules,"relations":relations}))
    }).collect::<Result<Vec<_>,String>>()?;
    output["recursive_components"] = json!({"scope":"original residual graph after fixed preparation, before simplification","positive":sizes(&recursive.positive),"negative":sizes(&recursive.negative),"components":components});
    output["component_report_ms"] = json!(component_start.elapsed().as_secs_f64() * 1000.);
    output["scope"] =
        json!("whole-program completion plus declared input cardinality; no selected assumptions");
    output["verdict"] = json!("not-checked");
    output["loading_ms"] = json!(loading.as_secs_f64() * 1000.);
    output["preparation_ms"] = json!(preparation.as_secs_f64() * 1000.);
    output["encoding_and_elimination_ms"] = json!(encoding.as_secs_f64() * 1000.);
    output["limits"] = json!({"max_atoms":limits.max_atoms,"max_rules":limits.max_rules,"max_dependencies":limits.max_dependencies,"max_work":limits.max_work,"timeout_ms":limits.timeout.as_millis()});
    Ok(output)
}
fn main() -> std::process::ExitCode {
    match measure(std::env::args().skip(1)) {
        Ok(output) => {
            println!("{}", serde_json::to_string_pretty(&output).unwrap());
            std::process::ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("measure-den-cnf: {e}");
            std::process::ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Fixture(std::path::PathBuf);
    impl Fixture {
        fn new() -> Self {
            static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let path = std::env::temp_dir().join(format!(
                "denotate-cnf-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).unwrap();
            std::fs::write(path.join("den.root"), "{}").unwrap();
            std::fs::write(
                path.join("program.den"),
                "input x(); relation a(); relation b(); a() :- x(); b() :- x();",
            )
            .unwrap();
            Self(path)
        }
        fn args(&self, flags: &[&str]) -> Vec<String> {
            std::iter::once(self.0.to_str().unwrap())
                .chain(flags.iter().copied())
                .map(str::to_owned)
                .collect()
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
    #[test]
    fn command_reports_original_components_and_paired_proof_scope() {
        let root = Fixture::new();
        std::fs::write(root.0.join("program.den"),"input x();relation a();relation b();relation p();a():-x(),!b();b():-!a();p():-x(),p();p():-x();").unwrap();
        let report = measure(root.args(&["--compare-local-limits", "256,65536,100000"])).unwrap();
        assert_eq!(report["recursive_components"]["negative"]["atoms"], 2);
        assert_eq!(report["recursive_components"]["positive"]["atoms"], 1);
        assert_eq!(
            report["recursive_components"]["negative"]["atom_size_histogram"]["2"],
            1
        );
        assert!(report["local_proof_comparison"]["first_lost_proof"].is_null());
        assert!(measure(root.args(&["--compare-local-limits", "256,65536"])).is_err());
    }
    #[test]
    fn command_reports_independent_passes_and_both_elimination_controls() {
        let root = Fixture::new();
        let plain = measure(root.args(&[])).unwrap();
        let compared = measure(root.args(&["--simplify", "--eliminate"])).unwrap();
        assert_eq!(compared["verdict"], "not-checked");
        let variants = compared["variants"].as_array().unwrap();
        assert_eq!(variants.len(), 8);
        for row in variants {
            let vars: u64 = row["after_by_relation"]
                .as_array()
                .unwrap()
                .iter()
                .map(|r| {
                    r["atom_variables"].as_u64().unwrap()
                        + r["auxiliary_variables"].as_u64().unwrap()
                })
                .sum();
            let clauses: u64 = row["after_by_relation"]
                .as_array()
                .unwrap()
                .iter()
                .map(|r| r["clauses"].as_u64().unwrap())
                .sum();
            assert_eq!(vars, row["after"]["variables"].as_u64().unwrap());
            assert_eq!(clauses, row["after"]["clauses"].as_u64().unwrap());
        }
        assert_eq!(variants[0]["before"], plain["before"]);
        let hashing = variants
            .iter()
            .find(|v| v["variant"] == "structural-hashing")
            .unwrap();
        assert!(
            hashing["after"]["variables"].as_u64().unwrap()
                < plain["after"]["variables"].as_u64().unwrap()
        );
        assert!(hashing["rewrite_record_vector_bytes"].as_u64().unwrap() > 0);
        assert!(hashing["before_by_relation"].as_array().unwrap().len() > 0);
    }
    #[test]
    fn local_limits_skip_proofs_global_limits_do_not_return_successful_reports() {
        let root = Fixture::new();
        let cut = measure(root.args(&["--simplify", "--local-work", "0"])).unwrap();
        assert!(
            cut["variants"]
                .as_array()
                .unwrap()
                .iter()
                .flat_map(|v| v["passes"].as_array().unwrap())
                .any(|p| p["cut_off"].as_u64().unwrap() > 0)
        );
        assert!(measure(root.args(&["--simplify", "--max-work", "0"])).is_err());
    }
}
