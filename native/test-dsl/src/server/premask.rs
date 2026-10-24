//! Recorded before changing the library, independently of the live old lowerer.
use denotate_check::*;
use denotate_editor::Document;
use denotate_test_dsl::analysis;
use denotate_test_dsl::{lowering::incremental::Session, syntax};
use lsp_types::Url;
use serde_json::{Value, json};
use std::{collections::BTreeMap, sync::Arc};

#[path = "../../tests/support/mod.rs"]
mod support;

#[path = "../../tests/support/value_compatibility.rs"]
mod value_compatibility;

fn capture() -> Value {
    let mut cases = Vec::new();
    let mut texts: Vec<String> = [
        support::Fixture::overlap(),
        support::Fixture::exclusive(),
        support::Fixture::ambiguous(),
        support::Fixture::redundant(),
        support::Fixture::mixed(false, false),
        support::Fixture::mixed(true, false),
        support::Fixture::mixed(false, true),
    ]
    .into_iter()
    .map(|f| f.text)
    .collect();
    let examples = include_str!("../../fixtures/lowering.txt");
    let lines: Vec<_> = examples.lines().filter(|s| !s.is_empty()).collect();
    for mapping in &lines[2..] {
        texts.push(format!("{}\n{}\n{mapping}\n", lines[0], lines[1]));
    }
    for text in texts {
        let document = Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            text.clone(),
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
        let Some(program) = prepared.program else {
            cases.push(json!({"text": text, "diagnostics": prepared.fast}));
            continue;
        };
        let p = &program.lowered;
        // Optional lookup keeps this capture harness runnable on the pinned
        // pre-mask revision too (which has no MappingLibrary::masked field).
        let masked = p
            .corpus
            .relations()
            .find(|r| r.name == "masked")
            .map(|r| r.id);
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
        // Only the added structural absence is normalized away. It must be a
        // negative, impossible masked(Slot) in the library's supplies rule.
        let mask_absence = |r: &GroundRule, l: &GroundLiteral| {
            if Some(l.term.atom.relation) != masked {
                return false;
            }
            assert_eq!(source[&r.source], 0);
            assert_eq!(r.head.atom.relation, p.library.supplies);
            assert_eq!(l.polarity, Polarity::Negative);
            assert_eq!(l.term.atom.arguments, vec![r.head.atom.arguments[1]]);
            assert!(!ground.is_possible(&l.term.atom).unwrap());
            true
        };
        let ground_rules: Vec<_> = ground
            .rules()
            .map(|r| {
                assert_eq!(
                    r.body.iter().filter(|l| mask_absence(r, l)).count(),
                    usize::from(masked.is_some() && r.head.atom.relation == p.library.supplies)
                );
                json!([
                    rules[&r.id],
                    r.body
                        .iter()
                        .filter(|l| !mask_absence(r, l))
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
                            let structural_absence = |e: &&PremiseEvidence| match e {
                                PremiseEvidence::Absent { fact, provider, .. }
                                    if Some(fact.relation) == masked =>
                                {
                                    assert_eq!(provider, &CompletedProvider::NoPossibleProducer);
                                    assert_eq!(a.relation, p.library.supplies);
                                    assert_eq!(fact.arguments, vec![a.arguments[1]]);
                                    true
                                }
                                _ => false,
                            };
                            assert_eq!(
                                premises.iter().filter(structural_absence).count(),
                                usize::from(masked.is_some() && a.relation == p.library.supplies)
                            );
                            json!([
                                rules[rule],
                                premises
                                    .iter()
                                    .filter(|e| !structural_absence(e))
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
        cases.push(json!({"text": text, "rules": ground_rules, "dependencies": dependencies, "groups": groups, "worlds": worlds, "diagnostics": output.diagnostics, "creator_warnings": output.creator_warnings}));
    }
    json!({"revision": "85fac25ae5c2bff8479e2b942c3b71d526fb9e9d", "cases": cases})
}

#[test]
fn unmasked_programs_match_recorded_pre_mask_meaning_and_lsp_diagnostics() {
    let expected: Value =
        serde_json::from_str(include_str!("../../fixtures/pre-mask.json")).unwrap();
    assert_eq!(value_compatibility::capture(capture()), expected);
}
