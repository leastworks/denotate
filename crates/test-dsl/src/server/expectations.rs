//! Expected behavior of every corpus program: diagnostics, obligation groups and the
//! facts of every small input world, through cached and uncached lowering. Regenerate
//! deliberately with `just update-test-dsl-expectations` and review every changed
//! expectation as a behavior change.
//!
//! Expectations exclude implementation choices: generated helper relations are
//! projected out of world facts, and diagnostics backed by a checker-selected witness
//! become one summary per finding (code, severity and evidence kind). The world facts already pin
//! whether such a finding exists; replay validates witnesses in the checker, and
//! witness wording is tested in `tests/checking.rs`, `completion.rs` and `values.rs`.
use denotate_check::*;
use denotate_editor::Document;
use denotate_test_dsl::analysis;
use denotate_test_dsl::{lowering::incremental::Session, syntax};
use lsp_types::Url;
use serde_json::{Value, json};
use std::{collections::BTreeMap, sync::Arc};

#[path = "../../tests/support/corpus.rs"]
mod corpus;

const EXPECTED: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures/expected");

fn capture(uncached: bool) -> Vec<Value> {
    let mut cases = Vec::new();
    for text in corpus::programs() {
        let document = Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            text.into(),
            1,
            true,
        ));
        let prepared = analysis::prepare(
            &Url::parse("file:///corpus.testdsl").unwrap(),
            1,
            document,
            &mut Session::default(),
        )
        .unwrap();
        let Some(mut program) = prepared.program else {
            cases.push(json!({"text": text, "diagnostics": prepared.fast}));
            continue;
        };
        if uncached {
            let syntax::ParseOutcome::Parsed(ast) =
                syntax::project(&program.document, &program.sources, program.snapshot).unwrap()
            else {
                panic!("corpus syntax")
            };
            let denotate_test_dsl::lowering::LoweringOutcome::Lowered(lowered) =
                denotate_test_dsl::lowering::lower(&ast, &program.sources).unwrap()
            else {
                panic!("corpus names")
            };
            program.lowered = lowered;
        }
        let p = &program.lowered;
        let limits = Limits::default();
        let ground = p.prepare(&limits).unwrap().admit(&limits).unwrap();
        let atom = |a: &GroundAtom| {
            format!(
                "{}({})",
                p.corpus.relation(a.relation).unwrap().name,
                a.arguments
                    .iter()
                    .map(|c| p.corpus.constant(*c).unwrap().name.clone())
                    .collect::<Vec<_>>()
                    .join(",")
            )
        };
        let meaningful = |a: &&GroundAtom| !p.corpus.is_generated_relation(a.relation);
        let component = |id| {
            ground
                .component(id)
                .unwrap()
                .atoms
                .iter()
                .filter(meaningful)
                .map(&atom)
                .collect::<Vec<_>>()
        };
        let groups: Vec<_> = ground
            .at_most_one_groups()
            .map(|g| {
                json!([
                    g.key
                        .iter()
                        .map(|c| p.corpus.constant(*c).unwrap().name.clone())
                        .collect::<Vec<_>>(),
                    g.tuples.iter().map(&atom).collect::<Vec<_>>()
                ])
            })
            .collect();
        let inputs: Vec<_> = ground.input_atoms().cloned().collect();
        assert!(
            inputs.len() <= 6,
            "corpus programs stay small enough to enumerate"
        );
        let mut worlds = Vec::new();
        for bits in 0..(1 << inputs.len()) {
            let present: Vec<_> = inputs
                .iter()
                .enumerate()
                .filter(|(i, _)| bits & (1 << i) != 0)
                .map(|(_, a)| a.clone())
                .collect();
            // Every candidate is an input atom, so an invalid observation is one the
            // input assumptions exclude. Record it; any other error fails the test.
            let replay = match ground.evaluate(present.clone(), &limits) {
                Ok(replay) => replay,
                Err(CheckError::InvalidObservation(_)) => {
                    worlds.push(json!({
                        "inputs": present.iter().map(&atom).collect::<Vec<_>>(),
                        "permitted": false,
                    }));
                    continue;
                }
                Err(error) => panic!("{text}: {error:?}"),
            };
            let facts: BTreeMap<_, _> = ground
                .atoms()
                .filter(meaningful)
                .map(|a| {
                    (
                        atom(a),
                        match replay.fact(a).unwrap() {
                            FactState::Settled(v) => json!(v),
                            FactState::Blocked(ids) => json!(
                                ids.into_iter()
                                    .map(&component)
                                    .filter(|atoms| !atoms.is_empty())
                                    .collect::<Vec<_>>()
                            ),
                        },
                    )
                })
                .collect();
            worlds.push(json!({
                "inputs": replay.present_inputs().map(&atom).collect::<Vec<_>>(),
                "facts": facts,
                "complete": replay.is_complete(),
            }));
        }
        let output = program.check(&limits, || {}).unwrap();
        let (diagnostics, witness_findings) = diagnostics(output.diagnostics);
        cases.push(json!({
            "text": text,
            "groups": groups,
            "worlds": worlds,
            "diagnostics": diagnostics,
            "witness_findings": witness_findings,
            "creator_warnings": output.creator_warnings,
        }));
    }
    cases
}

/// Evidence kinds whose diagnostic content depends on a checker-selected input world.
const WITNESS_EVIDENCE: [&str; 3] = [
    "replayed-counterexample",
    "replayed-coverage-counterexamples",
    "no-meaning-observation",
];

/// Visible diagnostics in emitted order, except those built from a selected witness.
/// Their message, ranges, related locations and number of highlights depend on the
/// witness, so each distinct finding (grouped by `data.finding`) contributes one
/// summary of witness-independent fields, sorted. The identity groups but is not
/// recorded: region identities can name generated helpers.
fn diagnostics(all: Vec<lsp_types::Diagnostic>) -> (Vec<Value>, Vec<Value>) {
    let mut visible = Vec::new();
    let mut findings = BTreeMap::new();
    for mut d in all {
        let data = d.data.take().unwrap_or(Value::Null);
        match data["evidence"]["kind"].as_str() {
            Some(evidence) if WITNESS_EVIDENCE.contains(&evidence) => {
                let summary = json!({"code": d.code, "severity": d.severity, "evidence": evidence});
                let previous = findings.insert(data["finding"].to_string(), summary.clone());
                assert!(
                    previous.is_none_or(|p| p == summary),
                    "one finding with different summaries"
                );
            }
            _ => visible.push(serde_json::to_value(d).unwrap()),
        }
    }
    let mut summaries: Vec<_> = findings.into_values().collect();
    summaries.sort_by_key(Value::to_string);
    (visible, summaries)
}

fn path(i: usize) -> String {
    format!("{EXPECTED}/corpus-{i:02}.json")
}

#[test]
fn corpus_programs_match_their_expectations() {
    let cases = capture(false);
    assert_eq!(cases, capture(true), "cached and uncached lowering differ");
    if std::env::var_os("UPDATE_EXPECTATIONS").is_some() {
        if std::path::Path::new(EXPECTED).exists() {
            std::fs::remove_dir_all(EXPECTED).unwrap();
        }
        std::fs::create_dir_all(EXPECTED).unwrap();
        for (i, case) in cases.iter().enumerate() {
            let text = serde_json::to_string_pretty(case).unwrap() + "\n";
            std::fs::write(path(i), text).unwrap();
        }
    }
    assert_eq!(
        std::fs::read_dir(EXPECTED).unwrap().count(),
        cases.len(),
        "one expectation file per corpus program"
    );
    for (i, case) in cases.iter().enumerate() {
        let expected: Value =
            serde_json::from_str(&std::fs::read_to_string(path(i)).unwrap()).unwrap();
        assert_eq!(
            case, &expected,
            "corpus/{i:02} differs from fixtures/expected/corpus-{i:02}.json; if the change \
             is intended, run `just update-test-dsl-expectations` and review the diff"
        );
    }
}
