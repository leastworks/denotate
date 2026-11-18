use super::generate::{knowledge::Knowledge, *};
use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;
use std::collections::BTreeSet;
fn shape() -> Shape {
    Shape {
        encoding: Encoding::Knowledge,
        knowledge: Knowledge {
            trees: 0,
            ..Default::default()
        },
        ..Default::default()
    }
}
fn load_shape(s: &Shape) -> LoadedProgram {
    load(
        &ProgramMembership::single("root", ["file:///knowledge.den".into()]),
        &[SourceFile::new(
            "file:///knowledge.den",
            0,
            source(s).unwrap(),
        )],
    )
    .unwrap()
}
fn atom(p: &LoadedProgram, rel: &str, args: &[&str]) -> GroundAtom {
    let (ns, name) = rel.rsplit_once("::").unwrap();
    let r = p
        .corpus
        .relations()
        .find(|r| {
            r.name == name
                && p.corpus.namespace(r.id)
                    == Some(&denotate_ir::Namespace::new(ns.split("::")).unwrap())
        })
        .unwrap();
    GroundAtom::new(
        r.id,
        args.iter()
            .map(|a| p.corpus.constants().find(|c| c.name == *a).unwrap().id),
    )
}
fn truth(p: &LoadedProgram, replay: &Replay<'_>, name: &str) -> Option<bool> {
    let t = replay
        .fact(&atom(p, "schema::known_true", &[name]))
        .unwrap();
    let f = replay
        .fact(&atom(p, "schema::known_false", &[name]))
        .unwrap();
    match (t, f) {
        (FactState::Settled(true), FactState::Settled(false)) => Some(true),
        (FactState::Settled(false), FactState::Settled(true)) => Some(false),
        (FactState::Settled(false), FactState::Settled(false)) => None,
        x => panic!("{name}: {x:?}"),
    }
}
fn and(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}
// Per-message slot evaluation. It knows source flows/results, not generated gates.
fn ring_reference(
    k: usize,
    w: usize,
    flows: &[bool],
    results: &[bool],
) -> (Vec<Option<bool>>, Vec<Option<bool>>) {
    let mut terms = vec![None; k];
    loop {
        let writers = (0..k * w)
            .map(|i| and(Some(flows[i]), terms[(i / w + 1) % k]))
            .collect::<Vec<_>>();
        let next = (0..k)
            .map(|t| {
                let range = t * w..(t + 1) * w;
                range.clone().all(|i| writers[i].is_some()).then(|| {
                    range
                        .clone()
                        .any(|i| writers[i] == Some(true) && results[i])
                })
            })
            .collect::<Vec<_>>();
        if terms == next {
            return (terms, writers);
        }
        assert!(terms.iter().zip(&next).all(|(a, b)| a.is_none() || a == b));
        terms = next;
    }
}
fn prepare<'a>(p: &'a LoadedProgram) -> PreparedCheck<'a> {
    let limits = Limits::default();
    let req = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(p) =
        req.prepare(&p.corpus, &p.keys, &(&limits).into()).unwrap()
    else {
        panic!("preparation exhausted")
    };
    let p = p.admit(&(&limits).into()).unwrap();
    assert!(p.program().is_admitted());
    assert_eq!(p.program().rewrite_proofs().count(), 0);
    p
}
#[test]
fn knowledge_rings_match_all_tiny_input_worlds_including_single_term_and_overlap() {
    for (k, w, nv) in [(1, 1, 1), (1, 2, 2), (2, 1, 2)] {
        for overlaps in [false, true] {
            let s = Shape {
                overlaps,
                knowledge: Knowledge {
                    trees: 0,
                    ring_terms: k,
                    ring_writers: w,
                    result_values: nv,
                    ..Default::default()
                },
                ..shape()
            };
            let p = load_shape(&s);
            let prep = prepare(&p);
            let limits = Limits::default();
            let inputs = prep.program().input_atoms().cloned().collect::<Vec<_>>();
            assert!(inputs.len() <= 11);
            let mut permitted = 0;
            let mut unknown = 0;
            for bits in 0..1usize << inputs.len() {
                let world = inputs
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits & (1 << i) != 0)
                    .map(|(_, a)| a.clone())
                    .collect::<BTreeSet<_>>();
                let selected = (0..k * w)
                    .map(|i| {
                        world.contains(&atom(
                            &p,
                            "workload::selector",
                            &[&format!("f{}_{}", i / w, i % w)],
                        ))
                    })
                    .collect::<Vec<_>>();
                let results = (0..k * w)
                    .map(|i| {
                        (0..nv)
                            .filter(|v| {
                                world.contains(&atom(
                                    &p,
                                    "workload::result",
                                    &[&format!("u{}_{}", i / w, i % w), &format!("v{v}")],
                                ))
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                if (!overlaps && selected.iter().filter(|x| **x).count() > 1)
                    || results.iter().any(|r| r.len() != 1)
                {
                    continue;
                }
                permitted += 1;
                let flows = (0..k * w)
                    .map(|i| {
                        selected[i]
                            && world.contains(&atom(
                                &p,
                                "workload::fa",
                                &[&format!("l{}_{}_0", i / w, i % w)],
                            ))
                            && !world.contains(&atom(
                                &p,
                                "workload::fb",
                                &[&format!("l{}_{}_0", i / w, i % w)],
                            ))
                    })
                    .collect::<Vec<_>>();
                let result_ok = results.iter().map(|v| v[0] == 0).collect::<Vec<_>>();
                let (terms, writers) = ring_reference(k, w, &flows, &result_ok);
                unknown += usize::from(terms.contains(&None));
                let replay = prep.program().evaluate(world, &limits).unwrap();
                assert!(replay.is_complete());
                for t in 0..k {
                    assert_eq!(truth(&p, &replay, &format!("term{t}")), terms[t]);
                    for u in 0..w {
                        assert_eq!(
                            truth(&p, &replay, &format!("writer{t}_{u}")),
                            writers[t * w + u]
                        );
                    }
                }
            }
            assert!(permitted > 0);
            assert_eq!(unknown > 0, k == 1 || overlaps);
        }
    }
}
#[test]
fn knowledge_forest_exhaustive_reference_separates_classification_and_validation() {
    // One level, one extra field per leaf: optional tree selector, branch selector,
    // and two payloads. Enumerate all scalar worlds independently of the emitter.
    let s = Shape {
        knowledge: Knowledge {
            trees: 1,
            unlocked_fields: 0,
            ..Default::default()
        },
        ..shape()
    };
    let p = load_shape(&s);
    let prep = prepare(&p);
    let limits = Limits::default();
    for tree in [false, true] {
        for branch in [None, Some(0), Some(1)] {
            for payload in 0..4 {
                let mut world = vec![];
                if tree {
                    world.push(atom(
                        &p,
                        "schema::raw_value",
                        &["tree_selector", "tree_value0"],
                    ));
                }
                if let Some(b) = branch {
                    world.push(atom(
                        &p,
                        "schema::raw_value",
                        &["select0_0", &format!("branch{b}")],
                    ));
                }
                for i in 0..2 {
                    if payload & (1 << i) != 0 {
                        world.push(atom(
                            &p,
                            "schema::raw_value",
                            &[&format!("field0_{}_0", i + 1), "payload"],
                        ));
                    }
                }
                let replay = prep.program().evaluate(world, &limits).unwrap();
                let matched = tree && branch.is_some();
                let invalid = matched
                    && match branch.unwrap() {
                        0 => payload & 1 == 0,
                        _ => payload & 2 != 0,
                    };
                assert_eq!(truth(&p, &replay, "path_matches"), Some(matched));
                assert_eq!(truth(&p, &replay, "invalid_message"), Some(invalid));
                assert_eq!(truth(&p, &replay, "recognized"), Some(matched && !invalid));
                for i in 0..2 {
                    let accepted = !matched || branch == Some(i);
                    assert_eq!(
                        truth(&p, &replay, &format!("accept_field0_{}_0", i + 1)),
                        Some(accepted)
                    );
                    assert_eq!(
                        truth(&p, &replay, &format!("present_field0_{}_0", i + 1)),
                        Some(accepted && payload & (1 << i) != 0)
                    );
                }
            }
        }
    }
}
fn summary(p: &LoadedProgram, session: &mut Session) -> serde_json::Value {
    let limits = Limits::default();
    let req = p.verification_requests(&limits).unwrap().remove(0).1;
    let ops = (&limits).into();
    let RequestPreparation::Complete(prep) =
        session.prepare(&req, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prep = prep.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&prep, &ops).unwrap() else {
        panic!()
    };
    let shown = presentation::present(p, &report.checked).unwrap();
    serde_json::json!({"state":shown.status["state"],"findings":shown.status["findings"].as_array().unwrap().iter().map(|f|serde_json::json!({"kind":f["kind"],"identity":f["identity"]})).collect::<Vec<_>>()})
}
#[test]
fn combined_shapes_and_chain_repairs_agree_cold_warm() {
    let mut session = Session::with_grounding();
    for broken in [false, true, false] {
        let s = Shape {
            depth: 2,
            knowledge: Knowledge {
                trees: 2,
                chain_length: 3,
                self_dependent: broken,
                writers_per_field: 2,
                ring_terms: 2,
                ring_writers: 1,
                ..Default::default()
            },
            ..shape()
        };
        let p = load_shape(&s);
        let warm = summary(&p, &mut session);
        assert_eq!(warm, summary(&p, &mut Session::default()));
        assert_eq!(warm["state"], if broken { "findings" } else { "proved" });
        let prep = prepare(&p);
        for start in [false, true] {
            let mut world = vec![];
            // Supply each computation's mandatory result; all flows are inactive.
            for t in 0..2 {
                world.push(atom(&p, "workload::result", &[&format!("u{t}_0"), "v0"]));
            }
            if start {
                world.push(atom(&p, "workload::chain_start", &[]));
            }
            let replay = prep.program().evaluate(world, &Limits::default()).unwrap();
            for i in 0..3 {
                assert_eq!(
                    truth(&p, &replay, &format!("chain{i}")),
                    if broken && start { None } else { Some(start) }
                );
            }
        }
    }
}
#[test]
fn generated_source_is_bounded_deterministic_and_options_are_explicit() {
    let s = Shape {
        knowledge: Knowledge {
            trees: 1,
            ..Default::default()
        },
        ..shape()
    };
    assert_eq!(source(&s).unwrap(), source(&s).unwrap());
    let bad = Shape {
        knowledge: Knowledge {
            trees: usize::MAX,
            ..Default::default()
        },
        ..shape()
    };
    assert!(source(&bad).is_err());
    for args in [
        vec!["--encoding", "knowledge", "--fields", "100"],
        vec!["--ring-terms", "2"],
        vec!["--encoding", "plain-term-ring"],
        vec!["--encoding", "knowledge", "--self-dependent"],
    ] {
        assert!(super::runner::run(args.into_iter().map(str::to_owned).collect()).is_err());
    }
}

#[test]
fn plain_and_knowledge_rings_have_identical_inputs_and_explicit_exhaustion() {
    let s = Shape {
        knowledge: Knowledge {
            trees: 0,
            ring_terms: 2,
            ring_writers: 1,
            ..Default::default()
        },
        ..shape()
    };
    let knowledge = load_shape(&s);
    let plain = load_shape(&Shape {
        encoding: Encoding::PlainTermRing,
        ..s
    });
    let inventory = |p: &LoadedProgram| {
        let limits = Limits::default();
        let r = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(prep) =
            r.prepare(&p.corpus, &p.keys, &(&limits).into()).unwrap()
        else {
            panic!()
        };
        prep.program()
            .input_atoms()
            .map(|a| {
                (
                    p.corpus
                        .relations()
                        .find(|r| r.id == a.relation)
                        .unwrap()
                        .name
                        .clone(),
                    a.arguments
                        .iter()
                        .map(|id| {
                            p.corpus
                                .constants()
                                .find(|c| c.id == *id)
                                .unwrap()
                                .name
                                .clone()
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(inventory(&knowledge), inventory(&plain));
    let limits = Limits {
        max_atoms: 0,
        ..Limits::default()
    };
    let request = knowledge
        .verification_requests(&limits)
        .unwrap()
        .remove(0)
        .1;
    assert!(matches!(
        request
            .prepare(&knowledge.corpus, &knowledge.keys, &(&limits).into())
            .unwrap(),
        RequestPreparation::Inconclusive { .. }
    ));
}

#[test]
fn inherited_validation_waits_for_a_complete_matching_path() {
    let p = load_shape(&Shape {
        knowledge: Knowledge::default(),
        ..shape()
    });
    let prep = prepare(&p);
    let mut world = vec![
        atom(&p, "schema::raw_value", &["tree_selector", "tree_value0"]),
        atom(&p, "schema::raw_value", &["unlocked0_0_0", "payload"]),
    ];
    for matched in [false, true] {
        if matched {
            world.extend([
                atom(&p, "schema::raw_value", &["select0_0", "branch0"]),
                atom(&p, "schema::raw_value", &["field0_1_0", "payload"]),
            ]);
        }
        let replay = prep
            .program()
            .evaluate(world.clone(), &Limits::default())
            .unwrap();
        assert_eq!(truth(&p, &replay, "path_matches"), Some(matched));
        assert_eq!(truth(&p, &replay, "invalid_message"), Some(matched));
        assert_eq!(truth(&p, &replay, "recognized"), Some(false));
    }
}
