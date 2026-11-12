use super::generate::*;
use denotate_check::*;
use denotate_ir_text::*;

fn load_shape(s: &Shape) -> LoadedProgram {
    let doc = SourceFile::new("file:///schema.den", 0, source(s).unwrap());
    load(
        &ProgramMembership::single("root", [doc.uri.clone()]),
        &[doc],
    )
    .unwrap()
}
fn tiny(encoding: Encoding) -> Shape {
    Shape {
        fields: 3,
        reads: 2,
        depth: 1,
        width: 2,
        encoding,
        shadowed: 1,
        computed: 0,
        catalog: 2,
        catalog_layers: 1,
        ..Default::default()
    }
}
#[test]
fn reference_presets_have_the_intended_verdicts() {
    for encoding in [
        Encoding::Ambiguous,
        Encoding::Coverage,
        Encoding::Negated,
        Encoding::Assumed,
    ] {
        let p = load_shape(&tiny(encoding));
        let limits = Limits::default();
        let ops = (&limits).into();
        let r = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(prepared) = r.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!("{encoding:?}")
        };
        let admitted = prepared.admit(&ops).unwrap();
        assert_eq!(
            admitted.program().is_admitted(),
            encoding != Encoding::Ambiguous,
            "{encoding:?}"
        );
        assert!(
            admitted.program().admission_limit().is_none(),
            "{encoding:?}"
        );
        let CheckOutcome::Complete(report) = admitted.verify(&ops).unwrap() else {
            panic!("{encoding:?}")
        };
        let shown = presentation::present(&p, &report).unwrap();
        assert_eq!(shown.status["consistency"], "consistent");
        if encoding != Encoding::Ambiguous {
            assert_eq!(shown.status["emptiness"][0]["outcome"], "proved");
        } else {
            assert!(!shown.status["regions"].as_array().unwrap().is_empty());
        }
    }
}

// The reference reads raw selectors first, allocates that leaf's payload, then
// checks required presence and declared absence. It neither solves equations nor calls the generator.
fn reference(s: &Shape, raw: &[bool], selector_choices: &[Option<usize>]) -> Option<usize> {
    let mut leaf = 0;
    for choice in selector_choices {
        leaf = leaf * s.width + (*choice)?;
    }
    let leaves = s.width.pow(s.depth as u32);
    let mut accepted = 0;
    for (i, present) in raw.iter().enumerate() {
        if (i % (leaves / s.width)) * s.width == leaf {
            if *present != (i % 3 != 2) {
                return None;
            }
            accepted |= 1 << i;
        }
    }
    Some(accepted)
}
#[test]
fn assumed_acceptance_matches_the_independent_layout_for_every_tiny_raw_message() {
    for depth in [1, 2] {
        let s = Shape {
            depth,
            fields: depth + 3,
            reads: 3,
            wide_heads: 2,
            producers: 3,
            ..tiny(Encoding::Assumed)
        };
        let p = load_shape(&s);
        let l = Limits::default();
        let ops = (&l).into();
        let r = p.verification_requests(&l).unwrap().remove(0).1;
        let RequestPreparation::Complete(check) = r.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let check = check.admit(&ops).unwrap();
        let g = check.program();
        assert!(g.is_admitted());
        let context = g.condition_context(&l).unwrap();
        let constant = |name: &str| p.corpus.constants().find(|c| c.name == name).unwrap().id;
        let relation = |name: &str| p.corpus.relations().find(|r| r.name == name).unwrap().id;
        let raw_id = relation("raw_value");
        let guess_id = relation("assumed_accepted");
        let expected_id = relation("expected");
        for selectors in 0..(s.width + 1).pow(depth as u32) {
            let mut n = selectors;
            let mut choices = Vec::new();
            let mut selected = Vec::new();
            for d in 0..depth {
                let choice = n % (s.width + 1);
                n /= s.width + 1;
                choices.push((choice < s.width).then_some(choice));
                if choice < s.width {
                    selected.push(GroundAtom::new(
                        raw_id,
                        [
                            constant(&format!("f{d}")),
                            constant(&format!("choice{choice}")),
                        ],
                    ));
                }
            }
            for raw_mask in 0..1usize << s.reads {
                let raw: Vec<_> = (0..s.reads).map(|i| raw_mask & (1 << i) != 0).collect();
                let intended = reference(&s, &raw, &choices);
                let mut assignments = Vec::new();
                for guesses in 0..1usize << s.reads {
                    let mut world = selected.clone();
                    for (i, present) in raw.iter().enumerate() {
                        let f = constant(&format!("f{}", depth + i));
                        if *present {
                            world.push(GroundAtom::new(raw_id, [f, constant("present")]));
                        }
                        if guesses & (1 << i) != 0 {
                            world.push(GroundAtom::new(guess_id, [f]));
                        }
                    }
                    match context.evaluate(&context.true_condition(), world.clone(), &l) {
                        Ok(true) => {
                            assignments.push(guesses);
                            let replay = g.evaluate(world, &l).unwrap();
                            for i in 0..s.reads {
                                let a = GroundAtom::new(
                                    expected_id,
                                    [constant(&format!("f{}", depth + i))],
                                );
                                assert_eq!(
                                    replay.fact(&a).unwrap(),
                                    FactState::Settled(guesses & (1 << i) != 0)
                                );
                            }
                        }
                        Err(CheckError::InvalidInputGroup(
                            "observation violates selected assumptions",
                        )) => {}
                        other => panic!("unexpected world result: {other:?}"),
                    }
                }
                assert_eq!(
                    assignments,
                    intended.into_iter().collect::<Vec<_>>(),
                    "depth={depth} selectors={choices:?} raw={raw:?}"
                );
            }
        }
    }
}
#[test]
fn injected_overlap_remains_an_obligation_failure() {
    for encoding in [Encoding::Assumed] {
        let p = load_shape(&Shape {
            overlaps: true,
            ..tiny(encoding)
        });
        let l = Limits::default();
        let ops = (&l).into();
        let r = p.verification_requests(&l).unwrap().remove(0).1;
        let RequestPreparation::Complete(check) = r.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let check = check.admit(&ops).unwrap();
        let CheckOutcome::Complete(report) = check.verify(&ops).unwrap() else {
            panic!()
        };
        let shown = presentation::present(&p, &report).unwrap();
        assert!(
            shown
                .diagnostics
                .iter()
                .any(|d| d.kind.code() == "counterexample"),
            "{:?}",
            shown.status
        );
    }
}
#[test]
fn source_is_deterministic_and_shape_controls_are_exercised() {
    for topology in [Topology::Independent, Topology::Coupled, Topology::Mixed] {
        let shape = Shape {
            depth: 2,
            topology,
            wide_heads: 2,
            producers: 5,
            ..Shape::default()
        };
        assert_eq!(source(&shape).unwrap(), source(&shape).unwrap());
        let p = load_shape(&shape);
        assert!(p.corpus.relations().any(|r| r.name == "wide1"));
        assert!(p.corpus.relations().any(|r| r.name == "computed_value"));
        assert!(p.corpus.rules().count() > shape.producers * shape.wide_heads);
    }
    assert!(
        source(&Shape {
            depth: usize::MAX,
            ..Default::default()
        })
        .is_err()
    );
}
#[test]
fn partial_and_completed_reports_preserve_logs_and_distinguish_completion() {
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    let dir = std::env::temp_dir().join(format!(
        "den-schema-report-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir(&dir).unwrap();
    fs::write(
        dir.join("run.json"),
        r#"{"state":"running","limits":{"--max-work":0}}"#,
    )
    .unwrap();
    let partial =
        "{\"type\":\"profile\",\"event\":\"start\",\"stage\":\"grounding\",\"span\":1}\n{\"type\":";
    fs::write(dir.join("memory.jsonl"), partial).unwrap();
    super::runner::summarize(&dir).unwrap();
    let read = || {
        serde_json::from_slice::<serde_json::Value>(&fs::read(dir.join("report.json")).unwrap())
            .unwrap()
    };
    assert_eq!(read()["checkerFinished"], false);
    assert_eq!(read()["unfinishedSpans"][0]["stage"], "grounding");
    assert_eq!(read()["malformedProfileLines"], 1);
    assert_eq!(
        fs::read_to_string(dir.join("memory.jsonl")).unwrap(),
        partial
    );
    fs::write(
        dir.join("memory.jsonl"),
        concat!(
            r#"{"type":"progress","detail":{"phase":"checking","admitted":false,"ground":{"ruleInstances":8},"fold":{"retainedEvidence":{"ruleInstances":3},"residual":{"ruleInstances":9}}}}"#,
            "\n",
            "{\"type\":\"run-end\",\"exitCode\":2,\"error\":\"exhausted\"}\n"
        ),
    )
    .unwrap();
    fs::write(
        dir.join("stdout.txt"),
        "Verification: checks\nResults: {\"state\":\"inconclusive\"}\n",
    )
    .unwrap();
    super::runner::summarize(&dir).unwrap();
    assert_eq!(read()["checkerFinished"], true);
    assert_eq!(read()["checkerExitCode"], 2);
    // The executable count excludes retained fixed evidence; stored slots keep
    // their original inventory after removals. These are mock stream records.
    assert_eq!(read()["afterAdmission"]["activeResidualRuleInstances"], 5);
    assert_eq!(
        read()["afterAdmission"]["fold"]["residual"]["ruleInstances"],
        9
    );
    assert_eq!(read()["outcomes"][0]["state"], "inconclusive");
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn coupled_conditions_connect_otherwise_separate_ambiguous_components() {
    let largest = |topology| {
        let p = load_shape(&Shape {
            fields: 6,
            reads: 4,
            depth: 2,
            width: 2,
            encoding: Encoding::Ambiguous,
            topology,
            shadowed: 0,
            computed: 0,
            catalog: 0,
            ..Default::default()
        });
        let l = Limits::default();
        let ops = (&l).into();
        let r = p.verification_requests(&l).unwrap().remove(0).1;
        let RequestPreparation::Complete(check) = r.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        check
            .program()
            .components()
            .map(|c| c.atoms.len())
            .max()
            .unwrap()
    };
    assert!(largest(Topology::Coupled) > largest(Topology::Independent));
}
