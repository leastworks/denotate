//! Size-only experiment: the input universe U, without selected assumptions.
use denotate_check::{
    Limits,
    cnf_measurement::{Measurement, Size},
};
use denotate_ir_text::{filesystem, load};
use serde_json::{Value, json};
use std::time::{Duration, Instant};
fn size(s: &Size) -> Value {
    json!({"variables":s.variables,"clauses":s.clauses,"literal_occurrences":s.literals,"cnf_vector_bytes":s.storage_bytes})
}
fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let root = args.next().ok_or("usage: just measure-den-cnf ROOT [--eliminate] [--max-atoms N] [--max-rules N] [--max-dependencies N] [--max-work N] [--timeout-ms N]")?;
    let mut limits = Limits::default();
    let mut eliminate = false;
    while let Some(arg) = args.next() {
        if arg == "--eliminate" {
            eliminate = true;
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
    let report = prepared
        .measure(eliminate, &limits)
        .map_err(|e| e.to_string())?;
    let encoding = start.elapsed();
    let mut relations: Vec<_> = report.relations.iter().map(|(r, s)| {
        let key = p.keys.relation(*r).map_err(|e| format!("{e:?}"))?;
        Ok(json!({"relation":format!("{key:?}"),"atom_variables":s.atom_variables,"auxiliary_variables":s.auxiliary_variables,"clauses":s.clauses,"literal_occurrences":s.literals,"payload_bytes":s.payload_bytes}))
    }).collect::<Result<_, String>>()?;
    relations.sort_by_key(|r| r["relation"].as_str().unwrap().to_owned());
    println!("{}", serde_json::to_string_pretty(&json!({
        "scope":"whole-program completion plus declared input cardinality; no selected assumptions",
        "verdict":"not-checked", "before":size(&report.before),"after":size(&report.after),
        "eliminated_variables":report.eliminated,"reconstruction_vector_bytes":report.reconstruction_bytes,
        "fixed_atoms":report.fixed_atoms,"residual_atoms":report.residual_atoms,"residual_rules":report.residual_rules,
        "loading_ms":loading.as_secs_f64()*1000.,"preparation_ms":preparation.as_secs_f64()*1000.,"encoding_and_elimination_ms":encoding.as_secs_f64()*1000.,
        "before_by_relation":relations,
        "limits":{"max_atoms":limits.max_atoms,"max_rules":limits.max_rules,"max_dependencies":limits.max_dependencies,"max_work":limits.max_work,"timeout_ms":limits.timeout.as_millis()}
    })).unwrap());
    Ok(())
}
fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("measure-den-cnf: {e}");
            std::process::ExitCode::from(2)
        }
    }
}
