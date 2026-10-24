//! 5.1 capture before normalization extraction. Never refresh to accept drift.
use denotate_check::*;
use denotate_editor::Document;
use denotate_test_dsl::analysis;
use denotate_test_dsl::{lowering::incremental::Session, syntax};
use lsp_types::Url;
use serde_json::{Value, json};
use std::{collections::BTreeMap, sync::Arc};

#[path = "../../tests/support/mod.rs"]
mod support;

#[path = "../../tests/support/normalization_fingerprint.rs"]
mod fingerprint;

#[path = "../../tests/support/value_compatibility.rs"]
mod value_compatibility;

fn capture(uncached: bool) -> Value {
    let mut cases = Vec::new();
    let texts = include_str!("../../fixtures/pre-normalize.txt").split("\n---\n");
    for text in texts {
        let document = Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            text.into(),
            1,
            true,
        ));
        let prepared = analysis::prepare(
            &Url::parse("file:///baseline.inputmapping").unwrap(),
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
                panic!("captured syntax")
            };
            let denotate_test_dsl::lowering::LoweringOutcome::Lowered(lowered) =
                denotate_test_dsl::lowering::lower(&ast, &program.sources).unwrap()
            else {
                panic!("captured names")
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
        let source: BTreeMap<_, _> = p
            .corpus
            .rules()
            .enumerate()
            .map(|(i, r)| (r.id, i))
            .collect();
        let rules: BTreeMap<_, _> = ground
            .rules()
            .map(|r| {
                (
                    r.id,
                    format!("{}:{}", source[&r.source], atom(&r.head.atom)),
                )
            })
            .collect();
        let component = |id| {
            ground
                .component(id)
                .unwrap()
                .atoms
                .iter()
                .map(&atom)
                .collect::<Vec<_>>()
        };
        let ground_rules: Vec<_> = ground
            .rules()
            .map(|r| {
                json!([
                    rules[&r.id],
                    r.body
                        .iter()
                        .map(|l| format!("{:?}:{}", l.polarity, atom(&l.term.atom)))
                        .collect::<Vec<_>>()
                ])
            })
            .collect();
        let dependencies: Vec<_> = ground
            .dependencies()
            .map(|d| {
                json!([
                    atom(&d.consumer),
                    atom(&d.provider),
                    rules[&d.rule],
                    format!("{:?}", d.polarity)
                ])
            })
            .collect();
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
        assert!(inputs.len() <= 6);
        let mut worlds = Vec::new();
        for bits in 0..(1 << inputs.len()) {
            let replay = ground
                .evaluate(
                    inputs
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| bits & (1 << i) != 0)
                        .map(|(_, a)| a.clone()),
                    &limits,
                )
                .unwrap();
            let facts: BTreeMap<_, _> = ground
                .atoms()
                .map(|a| {
                    (
                        atom(a),
                        match replay.fact(a).unwrap() {
                            FactState::Settled(v) => json!(v),
                            FactState::Blocked(ids) => {
                                json!(ids.into_iter().map(&component).collect::<Vec<_>>())
                            }
                        },
                    )
                })
                .collect();
            let evidence: BTreeMap<_, _> = replay
                .established_facts()
                .map(|a| {
                    let value = match &replay.derivation(a).unwrap().evidence {
                        Evidence::Input => json!("input"),
                        Evidence::Derived { rule, premises } => {
                            json!([
                                rules[rule],
                                premises
                                    .iter()
                                    .map(|e| match e {
                                        PremiseEvidence::Positive { fact, .. } =>
                                            json!(["positive", atom(fact)]),
                                        PremiseEvidence::Absent { fact, provider, .. } => json!([
                                            "absent",
                                            atom(fact),
                                            match provider {
                                                CompletedProvider::NoPossibleProducer =>
                                                    json!("no producer"),
                                                CompletedProvider::InputSnapshot => json!("input"),
                                                CompletedProvider::Component(id) =>
                                                    json!(component(*id)),
                                            }
                                        ]),
                                        PremiseEvidence::Discharged {
                                            literal_occurrence, ..
                                        } => {
                                            let r = p
                                                .corpus
                                                .rule(ground.rule(*rule).unwrap().source)
                                                .unwrap();
                                            json!([
                                                "discharged",
                                                r.body
                                                    .iter()
                                                    .position(
                                                        |l| l.atom().id() == *literal_occurrence
                                                    )
                                                    .unwrap()
                                            ])
                                        }
                                    })
                                    .collect::<Vec<_>>()
                            ])
                        }
                    };
                    (atom(a), value)
                })
                .collect();
            worlds.push(json!({"inputs": replay.present_inputs().map(&atom).collect::<Vec<_>>(), "facts": facts, "evidence": evidence, "complete": replay.is_complete()}));
        }
        let mut output = program.check(&limits, || {}).unwrap();
        // This frozen capture predates structured finding identities. Keep every
        // visible diagnostic field exact; stage-3 parity tests exercise data.
        for diagnostic in &mut output.diagnostics {
            diagnostic.data = None;
        }
        cases.push(json!({"text": text, "structure": fingerprint::fingerprint(p, &program.sources), "rules": ground_rules, "dependencies": dependencies, "groups": groups, "worlds": worlds, "diagnostics": output.diagnostics, "creator_warnings": output.creator_warnings}));
    }
    json!({"revision": "c84005847bb62dad7b8fd6fa2a69dffe9a3486be", "cases": cases})
}

#[test]
fn completed_masking_matches_pre_normalization_capture() {
    let expected: Value =
        serde_json::from_str(include_str!("../../fixtures/pre-normalize.json")).unwrap();
    assert_eq!(value_compatibility::capture(capture(false)), expected);
    assert_eq!(value_compatibility::capture(capture(true)), expected);
}
