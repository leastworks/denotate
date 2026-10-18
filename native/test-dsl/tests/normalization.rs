#[path = "support/normalization_cases.rs"]
mod cases;
#[path = "support/normalization_fingerprint.rs"]
mod fingerprint;
#[path = "support/before_normalization.rs"]
mod reference;
mod support;
#[path = "support/value_compatibility.rs"]
mod value_compatibility;
use denotate_editor::Document;
use denotate_ir::installation::{self, BoundAtom};
use denotate_ir::*;
use denotate_normalize as n;
use denotate_test_dsl::{
    ast::Program,
    library,
    lowering::{self, assembly, projection, recipe, semantic::*},
    syntax,
};
use std::{collections::BTreeMap, sync::Arc};

fn parse(text: &str, revision: u64) -> (Program, Sources) {
    let mut sources = Sources::new();
    let snapshot = sources
        .add("file:///generic.inputmapping", revision, "test-dsl", text)
        .unwrap();
    let doc = Document::new(
        &mut syntax::parser().unwrap(),
        text.into(),
        revision as i32,
        true,
    );
    let syntax::ParseOutcome::Parsed(ast) = syntax::project(&doc, &sources, snapshot).unwrap()
    else {
        panic!("syntax: {text}")
    };
    (ast, sources)
}
fn lowered(outcome: lowering::LoweringOutcome) -> lowering::LoweredProgram {
    let lowering::LoweringOutcome::Lowered(p) = outcome else {
        panic!("names")
    };
    p
}
fn compare_recipes(form: Arc<SemanticStatement>) {
    let old = reference::Recipe::lower(form.clone());
    let new = recipe::Recipe::lower(form).unwrap();
    let Some(recipe) = new.normalized else { return };
    let local = |id: n::Local| reference::LocalOccurrence(id.0);
    let constant = |a: &recipe::Value| {
        let recipe::Value::Name(a) = a else {
            panic!("not a legacy leaf");
        };
        reference::ConstantRef {
            kind: a.kind,
            name: a.name.clone(),
        }
    };
    let instructions: Vec<_> = recipe
        .instructions()
        .iter()
        .map(|i| match i {
            n::Instruction::Helper { id } => reference::Instruction::Helper { id: local(*id) },
            n::Instruction::Atom {
                id,
                target,
                arguments,
            } => {
                let (relation, values) = match target {
                    n::Target::Helper(id) => (reference::RelationRef::Helper(local(*id)), vec![]),
                    n::Target::Head(p) | n::Target::Leaf(p) => (
                        match p.relation {
                            recipe::Relation::MappedTo => reference::RelationRef::MappedTo,
                            recipe::Relation::Masked => reference::RelationRef::Masked,
                            recipe::Relation::Present => reference::RelationRef::Present,
                            recipe::Relation::Available => reference::RelationRef::Available,
                            _ => panic!("not a legacy leaf"),
                        },
                        p.arguments.iter().map(constant).collect(),
                    ),
                };
                assert_eq!(arguments.len(), values.len());
                reference::Instruction::Atom {
                    id: local(*id),
                    relation,
                    arguments: arguments
                        .iter()
                        .zip(values)
                        .map(|(a, value)| reference::Argument {
                            id: local(a.id),
                            value,
                        })
                        .collect(),
                }
            }
            n::Instruction::Rule { id, head, body } => reference::Instruction::Rule {
                id: local(*id),
                head: local(*head),
                body: body
                    .iter()
                    .map(|l| reference::Literal {
                        atom: local(l.atom),
                        negative: l.polarity == n::Polarity::Negative,
                    })
                    .collect(),
            },
        })
        .collect();
    assert_eq!(old.instructions(), instructions);
    let convert = |map: BTreeMap<n::Local, AstPath>| {
        map.into_iter()
            .map(|(id, path)| (local(id), path))
            .collect::<BTreeMap<_, _>>()
    };
    assert_eq!(*old.origins(), convert(new.assignments.origins));
    assert_eq!(old.guards, convert(new.assignments.guards));
    assert_eq!(old.removals, convert(new.assignments.removals));
}
#[test]
fn frozen_recipes_agree_for_mapping_mask_and_nested_conditions() {
    let capture: serde_json::Value =
        serde_json::from_str(include_str!("../fixtures/pre-normalize.json")).unwrap();
    // Syntax-error captures are exercised through the server, before lowering.
    let mut texts: Vec<_> = capture["cases"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|c| c.get("structure").is_some())
        .map(|c| c["text"].as_str().unwrap().to_owned())
        .collect();
    texts.extend(cases::nested());
    for text in texts {
        let (ast, sources) = parse(&text, 1);
        let projected = projection::project(&ast, &sources).unwrap();
        for s in projected.keys() {
            compare_recipes(s.form);
        }
        // Installed compatibility is pinned independently in the server capture
        // and additional_installed_cases_match_frozen_legacy_output below.
    }
}
#[test]
fn unchanged_recipes_rebind_moved_sources_and_duplicate_statements_independently() {
    let text = cases::DUPLICATES;
    let (ast, sources) = parse(text, 1);
    let original = projection::project(&ast, &sources).unwrap();
    let recipes: Vec<_> = original
        .keys()
        .iter()
        .map(|s| recipe::Recipe::lower(s.form.clone()).unwrap())
        .collect();
    assert_eq!(recipes[2], recipes[3]);
    for (revision, text) in cases::moved() {
        let (ast, sources) = parse(&text, revision);
        let projected = projection::project(&ast, &sources).unwrap();
        let reused = assembly::assemble(&projected, &recipes, &sources).unwrap();
        let fresh = lowered(lowering::lower(&ast, &sources).unwrap());
        assert_eq!(
            fingerprint::fingerprint(&reused, &sources),
            fingerprint::fingerprint(&fresh, &sources)
        );
        assert_eq!(
            value_compatibility::structure(fingerprint::fingerprint(&reused, &sources)),
            frozen_installed(&text, revision)
        );
        let helpers: Vec<_> = reused
            .corpus
            .relations()
            .filter(|r| reused.corpus.is_generated_relation(r.id))
            .collect();
        assert_eq!(helpers.len(), 2);
        assert_ne!(helpers[0].id, helpers[1].id);
    }
    // A changed semantic form must not accept an old recipe.
    let (ast, sources) = parse(&text.replace("present(j)", "present(i)"), 4);
    assert!(
        assembly::assemble(
            &projection::project(&ast, &sources).unwrap(),
            &recipes,
            &sources
        )
        .is_err()
    );
}
#[test]
fn name_errors_gate_cached_and_uncached_pipelines_and_repair_agrees() {
    let mut session = lowering::incremental::Session::new(true);
    for text in [
        "input i; slot a; a <- missing when present(i);",
        "input i; slot a; mask a when present(a);",
        "input i, i; slot a; a <- i;",
        "input i; slot a; a <- i when not not available(a);",
    ] {
        let (ast, sources) = parse(text, 1);
        match (
            lowering::lower(&ast, &sources).unwrap(),
            session.lower(&ast, &sources).unwrap(),
        ) {
            (
                lowering::LoweringOutcome::UserErrors(a),
                lowering::LoweringOutcome::UserErrors(b),
            ) => assert_eq!(a, b),
            (lowering::LoweringOutcome::Lowered(a), lowering::LoweringOutcome::Lowered(b)) => {
                assert_eq!(
                    fingerprint::fingerprint(&a, &sources),
                    fingerprint::fingerprint(&b, &sources)
                )
            }
            _ => panic!("gating differs"),
        }
    }
}
#[test]
fn variable_library_definition_equals_hand_written_conjunctive_rule() {
    let mut corpus = Corpus::new();
    let library = library::build(&mut corpus).unwrap();
    let original = corpus.rules().next().unwrap().id;
    // Opaque symbolic payloads carry variable names, never SortId/RelationId.
    let leaf = |key: usize, name: &'static str, args: Vec<&'static str>| n::Expression {
        key,
        kind: n::ExpressionKind::Leaf {
            payload: (name, args.clone()),
            arguments: args
                .iter()
                .enumerate()
                .map(|(i, _)| n::Argument {
                    key: key + 100 + i,
                    variable: true,
                })
                .collect(),
        },
    };
    let body = n::Expression {
        key: 1,
        kind: n::ExpressionKind::And(
            Box::new(leaf(2, "mapped_to", vec!["I", "D"])),
            Box::new(n::Expression {
                key: 3,
                kind: n::ExpressionKind::And(
                    Box::new(leaf(4, "present", vec!["I"])),
                    Box::new(n::Expression {
                        key: 5,
                        kind: n::ExpressionKind::Not(Box::new(leaf(6, "masked", vec!["D"]))),
                    }),
                ),
            }),
        ),
    };
    let recipe = n::normalize(&n::Definition {
        head: n::Atom {
            key: 0,
            payload: ("supplies", vec!["I", "D"]),
            arguments: vec![
                n::Argument {
                    key: 100,
                    variable: true,
                },
                n::Argument {
                    key: 101,
                    variable: true,
                },
            ],
        },
        body: Some(body),
    })
    .unwrap();
    let binding = |(name, args): &(&str, Vec<&str>)| {
        Ok(BoundAtom {
            relation: match *name {
                "supplies" => library.supplies,
                "mapped_to" => library.mapped_to,
                "present" => library.present,
                "masked" => library.masked,
                _ => unreachable!(),
            },
            arguments: args
                .iter()
                .map(|name| {
                    Term::variable(
                        *name,
                        if *name == "I" {
                            library.input
                        } else {
                            library.slot
                        },
                    )
                })
                .collect(),
        })
    };
    let installed = installation::install(&mut corpus, &recipe, binding, binding).unwrap();
    assert_eq!(installed.rules().len(), 1);
    assert_eq!(
        corpus
            .relations()
            .filter(|r| corpus.is_generated_relation(r.id))
            .count(),
        0
    );
    let old = corpus.rule(original).unwrap();
    let new = corpus
        .rule(*installed.rules().values().next().unwrap())
        .unwrap();
    let shape = |r: &Rule| {
        let atom = |a: &Atom| {
            (
                a.relation(),
                a.arguments()
                    .iter()
                    .map(|t| t.value().clone())
                    .collect::<Vec<_>>(),
            )
        };
        (
            atom(&r.head),
            r.body
                .iter()
                .map(|l| (matches!(l, Literal::Negative(_)), atom(l.atom())))
                .collect::<Vec<_>>(),
        )
    };
    assert_eq!(shape(old), shape(new));
    assert_ne!(old.head.id(), new.head.id());
    assert_eq!(installed.occurrences().len(), recipe.records().len());
    for (a, b) in old.head.arguments().iter().zip(new.head.arguments()) {
        assert_ne!(a.id(), b.id());
    }
}

#[test]
#[ignore = "manual integrated release phase measurement; not a speedup claim"]
fn measure_shared_normalization_phases() {
    use denotate_check::{GroundProgram, Limits};
    use std::time::Instant;
    assert!(!cfg!(debug_assertions), "run this probe with --release");
    let mut rows = vec![];
    for size in [10, 100, 1000] {
        let slots = (0..size)
            .map(|i| format!("s{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let mappings = (0..size)
            .map(|i| format!("s{i} <- i when (present(i) or present(j)) and present(i);\n"))
            .collect::<String>();
        let text = format!("input i, j;\nslot {slots};\n{mappings}");
        let mut session = lowering::incremental::Session::new(true);
        let (ast, sources) = parse(&text, 1);
        session.lower(&ast, &sources).unwrap();
        let before = session.stats().queries;
        let mut samples = vec![];
        for sample in 0..5 {
            let (ast, sources) = parse(&format!("// sample {sample}\n{text}"), sample + 2);
            let start = Instant::now();
            let projection = projection::project(&ast, &sources).unwrap();
            let projection_ns = start.elapsed().as_nanos();
            let keys = projection.keys();
            assert!(validate(&keys).unwrap().is_empty());
            let start = Instant::now();
            let recipes = keys
                .iter()
                .map(|s| recipe::Recipe::lower(s.form.clone()).unwrap())
                .collect::<Vec<_>>();
            let normalization_assignment_ns = start.elapsed().as_nanos();
            let start = Instant::now();
            let program = assembly::assemble(&projection, &recipes, &sources).unwrap();
            let assembly_attribution_ns = start.elapsed().as_nanos();
            let start = Instant::now();
            let limits = Limits::default();
            let ground =
                GroundProgram::prepare(&program.corpus, &support::domains(&program), &limits)
                    .unwrap()
                    .admit(&limits)
                    .unwrap();
            let report = ground
                .symbolic(&limits)
                .unwrap()
                .verify_at_most_one(&limits)
                .unwrap();
            assert!(report.whole_program_admitted());
            let checking_ns = start.elapsed().as_nanos();
            session.lower(&ast, &sources).unwrap();
            assert_eq!(before, session.stats().queries);
            samples.push(serde_json::json!({"projection_ns":projection_ns,"normalization_assignment_ns":normalization_assignment_ns,"assembly_attribution_ns":assembly_attribution_ns,"checking_ns":checking_ns,"cached_query_access_ns":session.stats().last.queries_ns,"cached_projection_ns":session.stats().last.projection_ns,"cached_assembly_attribution_ns":session.stats().last.assembly_attribution_ns}));
        }
        rows.push(serde_json::json!({"mappings":size,"helpers":size,"inputs":2,"source":text,"queries_before":before,"queries_after":session.stats().queries,"samples":samples}));
    }
    println!(
        "NORMALIZATION_PHASES={}",
        serde_json::json!({"rows":rows,"note":"Shared normalization plus frontend assignment is uncached. Query access is measured separately on the integrated Salsa path with unchanged-form reuse asserted; no speedup claim. Parsing, name validation, diagnostics and serialization are outside the timed phases."})
    );
}

fn frozen_installed(text: &str, revision: u64) -> serde_json::Value {
    let capture: serde_json::Value = serde_json::from_str(include_str!(
        "../fixtures/pre-integration-fingerprints.json"
    ))
    .unwrap();
    capture["cases"].as_array().unwrap().iter().find(|case|case["text"]==text && case["revision"]==revision)
        .unwrap_or_else(||panic!("missing frozen case at revision {revision}: {text}"))["fingerprint"].clone()
}
#[test]
fn additional_installed_cases_match_frozen_legacy_output() {
    let capture: serde_json::Value = serde_json::from_str(include_str!(
        "../fixtures/pre-integration-fingerprints.json"
    ))
    .unwrap();
    let expected_cases = cases::capture_cases();
    assert_eq!(
        capture["cases"].as_array().unwrap().len(),
        expected_cases.len()
    );
    let mut session = lowering::incremental::Session::new(true);
    for (revision, text) in expected_cases {
        let (ast, sources) = parse(&text, revision);
        let expected = frozen_installed(&text, revision);
        let uncached = lowered(lowering::lower(&ast, &sources).unwrap());
        let cached = lowered(session.lower(&ast, &sources).unwrap());
        assert_eq!(
            value_compatibility::structure(fingerprint::fingerprint(&uncached, &sources)),
            expected
        );
        assert_eq!(
            value_compatibility::structure(fingerprint::fingerprint(&cached, &sources)),
            expected
        );
    }
}

#[test]
fn keyed_frontend_preparation_preserves_limits_and_routes_binding_failures_to_creator() {
    use denotate_check::{CheckError, Limits};
    let frozen: serde_json::Value =
        serde_json::from_str(include_str!("../../check/fixtures/SLICE-6.0-BASELINE.json")).unwrap();
    for observation in frozen["budgets"].as_array().unwrap() {
        let (ast, sources) = parse(observation["source"].as_str().unwrap(), 1);
        let p = lowered(lowering::lower(&ast, &sources).unwrap());
        let limits = Limits {
            max_work: observation["max_work"].as_u64().unwrap() as usize,
            ..Limits::default()
        };
        match (p.prepare(&limits), p.prepare_keyed(&limits)) {
            (Ok(old), Ok(new)) => {
                assert_eq!(
                    old.atoms().collect::<Vec<_>>(),
                    new.program.atoms().collect::<Vec<_>>()
                );
                assert_eq!(old.rules().count(), new.keys.instances.len());
                assert_eq!(old.components().count(), new.keys.components.len());
            }
            (Err(old), Err(new)) => assert_eq!(old, new),
            _ => panic!("key computation changed preparation exhaustion"),
        }
    }
    let (ast, sources) = parse("input i; slot a; a <- i;", 1);
    let mut p = lowered(lowering::lower(&ast, &sources).unwrap());
    p.keys = SemanticKeys::default();
    let Err(error @ CheckError::Keys(_)) = p.prepare_keyed(&Limits::default()) else {
        panic!("missing bindings accepted")
    };
    assert!(matches!(
        denotate_test_dsl::analysis::Failure::from(error),
        denotate_test_dsl::analysis::Failure::Creator(_)
    ));
    let limits = Limits::default();
    limits.cancellation.cancel();
    assert!(matches!(
        p.prepare_keyed(&limits),
        Err(CheckError::Cancelled)
    ));
}
