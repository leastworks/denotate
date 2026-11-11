#[path = "support/normalization_cases.rs"]
mod cases;
#[path = "support/corpus.rs"]
mod corpus;
#[path = "support/normalization_fingerprint.rs"]
mod fingerprint;
mod support;
use denotate_editor::Document;
use denotate_ir::installation::{self, BoundAtom};
use denotate_ir::*;
use denotate_normalize as n;
use denotate_test_dsl::{
    ast::Program,
    library,
    lowering::{self, assembly, projection, recipe},
    syntax,
};

fn parse(text: &str, revision: u64) -> (Program, Sources) {
    let mut sources = Sources::new();
    let snapshot = sources
        .add("file:///generic.testdsl", revision, "test-dsl", text)
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
fn generated_cases_install_identically_cached_and_uncached() {
    let mut session = lowering::incremental::Session::new(true);
    for (revision, text) in cases::capture_cases() {
        let (ast, sources) = parse(&text, revision);
        let uncached = lowered(lowering::lower(&ast, &sources).unwrap());
        let cached = lowered(session.lower(&ast, &sources).unwrap());
        assert_eq!(
            fingerprint::fingerprint(&cached, &sources),
            fingerprint::fingerprint(&uncached, &sources),
            "{text}"
        );
    }
}

#[test]
fn keyed_frontend_preparation_preserves_limits_and_routes_binding_failures_to_creator() {
    use denotate_check::{CheckError, Limits};
    let corpus: serde_json::Value = serde_json::from_str(include_str!(
        "../../check-session/fixtures/regression/outcomes.json"
    ))
    .unwrap();
    for row in corpus["cases"].as_array().unwrap() {
        for work in [0, 100, 500, 2000, 20000, Limits::default().max_work] {
            let (ast, sources) = parse(row["source"].as_str().unwrap(), 1);
            let p = lowered(lowering::lower(&ast, &sources).unwrap());
            let limits = Limits {
                max_work: work,
                ..Limits::default()
            };
            match (p.prepare(&limits), p.prepare_keyed(&limits)) {
                (Ok(old), Ok(new)) => {
                    assert_eq!(
                        old.atoms().collect::<Vec<_>>(),
                        new.program.atoms().collect::<Vec<_>>()
                    );
                    assert_eq!(
                        old.rules().count(),
                        new.keys
                            .view(&p.corpus, &p.keys, &new.program)
                            .original_content()
                            .unwrap()
                            .len()
                    );
                    assert_eq!(old.components().count(), new.program.components().count());
                }
                (Err(old), Err(new)) => assert_eq!(old, new),
                _ => panic!("key computation changed preparation exhaustion"),
            }
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
