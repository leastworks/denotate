#[path = "support/before_recipes.rs"]
mod before_recipes;
#[path = "support/cached.rs"]
mod cached;
mod support;

use denotate_check::*;
use denotate_editor::Document;
use denotate_ir::*;
use denotate_test_dsl::{
    ast::Program,
    attribution::SourceView,
    lowering::{
        self, LoweredProgram, LoweringOutcome, assembly, projection,
        recipe::Recipe,
        semantic::{self, AstPath},
    },
    syntax::{self, ParseOutcome},
};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use support::{Fixture, domains};

fn parse(text: &str) -> (Sources, Program) {
    let mut sources = Sources::new();
    let snapshot = sources
        .add(
            "file:///recipe.inputmapping",
            1,
            SourceView::TestDsl.as_str(),
            text,
        )
        .unwrap();
    let document = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
    let ParseOutcome::Parsed(ast) = syntax::project(&document, &sources, snapshot).unwrap() else {
        panic!("{text}")
    };
    (sources, ast)
}
fn lowered(ast: &Program, sources: &Sources) -> LoweredProgram {
    let LoweringOutcome::Lowered(p) = lowering::lower(ast, sources).unwrap() else {
        panic!("name errors")
    };
    p
}
fn recipes(projection: &projection::Projection) -> Vec<Recipe> {
    projection
        .keys()
        .into_iter()
        .map(|s| Recipe::lower(s.form))
        .collect()
}
fn constant(p: &LoweredProgram, id: ConstantId) -> String {
    let c = p.corpus.constant(id).unwrap();
    format!("{}:{}", c.name, p.corpus.sort(c.sort).unwrap().name)
}
fn atom_text(p: &LoweredProgram, atom: &Atom) -> String {
    let args: Vec<_> = atom
        .arguments()
        .iter()
        .map(|a| match a.value() {
            Term::Constant(id) => constant(p, *id),
            Term::Variable { name, sort } => {
                format!("{name}:{}", p.corpus.sort(*sort).unwrap().name)
            }
        })
        .collect();
    format!(
        "{}({})",
        p.corpus.relation(atom.relation()).unwrap().name,
        args.join(", ")
    )
}
fn ground_text(p: &LoweredProgram, atom: &GroundAtom) -> String {
    format!(
        "{}({})",
        p.corpus.relation(atom.relation).unwrap().name,
        atom.arguments
            .iter()
            .map(|c| constant(p, *c))
            .collect::<Vec<_>>()
            .join(", ")
    )
}
fn span(sources: &Sources, s: SourceSpan) -> Value {
    let source = sources.snapshot(s.snapshot()).unwrap();
    json!([
        source.uri,
        source.view,
        s.byte_range().start,
        s.byte_range().end,
        sources.text(s).unwrap()
    ])
}

/// Structural occurrence addresses compare everything without comparing arenas.
fn fingerprint(p: &LoweredProgram, sources: &Sources) -> Value {
    let mut ids = BTreeMap::<OccurrenceId, String>::new();
    for (i, s) in p.corpus.sorts().enumerate() {
        ids.insert(s.id.into(), format!("sort/{i}"));
    }
    for (i, c) in p.corpus.constants().enumerate() {
        ids.insert(c.id.into(), format!("constant/{i}"));
    }
    for (i, r) in p.corpus.relations().enumerate() {
        ids.insert(r.id.into(), format!("relation/{i}"));
    }
    for (i, o) in p.corpus.obligations().enumerate() {
        ids.insert(o.id.into(), format!("obligation/{i}"));
    }
    let mut rules = Vec::new();
    for (i, rule) in p.corpus.rules().enumerate() {
        ids.insert(rule.id.into(), format!("rule/{i}"));
        for (label, atom) in std::iter::once(("head".into(), &rule.head)).chain(
            rule.body
                .iter()
                .enumerate()
                .map(|(j, l)| (format!("body/{j}"), l.atom())),
        ) {
            ids.insert(atom.id(), format!("rule/{i}/{label}"));
            for (j, term) in atom.arguments().iter().enumerate() {
                ids.insert(term.id(), format!("rule/{i}/{label}/arg/{j}"));
            }
        }
        rules.push(format!(
            "{} :- {};",
            atom_text(p, &rule.head),
            rule.body
                .iter()
                .map(|l| format!(
                    "{}{}",
                    if matches!(l, Literal::Negative(_)) {
                        "!"
                    } else {
                        ""
                    },
                    atom_text(p, l.atom())
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    let origins: BTreeMap<_, _> = p
        .attribution
        .provenance
        .entries()
        .map(|(id, origins)| {
            (
                ids[&id].clone(),
                origins
                    .iter()
                    .map(|o| span(sources, o.span))
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    let guards: BTreeMap<_, _> = p
        .attribution
        .guards
        .iter()
        .map(|((id, view), s)| {
            (
                format!("{}:{view:?}", ids[&(*id).into()]),
                span(sources, *s),
            )
        })
        .collect();
    let edits: BTreeMap<_, _> = p
        .attribution
        .rewrites
        .removals
        .iter()
        .map(|(id, edit)| {
            (
                ids[id].clone(),
                json!([span(sources, edit.span), edit.replacement]),
            )
        })
        .collect();
    let owners: BTreeMap<_, _> = p
        .attribution
        .rewrites
        .owners
        .iter()
        .map(|(id, owner)| (ids[&(*id).into()].clone(), format!("{owner:?}")))
        .collect();
    let masks: BTreeMap<_, _> = p
        .attribution
        .masks
        .iter()
        .map(|(id, mask)| {
            (
                ids[&(*id).into()].clone(),
                json!([
                    constant(p, mask.target),
                    span(sources, mask.statement),
                    mask.condition.map(|s| span(sources, s))
                ]),
            )
        })
        .collect();
    json!({
        "constants": p.corpus.constants().map(|c| constant(p, c.id)).collect::<Vec<_>>(),
        "relations": p.corpus.relations().map(|r| json!([r.name, format!("{:?}",r.role), r.parameters.iter().map(|a| json!([a.name, p.corpus.sort(a.sort).unwrap().name])).collect::<Vec<_>>()])).collect::<Vec<_>>(),
        "rules": rules, "origins": origins, "guards": guards, "edits": edits, "owners": owners, "masks": masks
    })
}

fn check(p: &LoweredProgram) -> Value {
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&p.corpus, &domains(p), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let inputs: Vec<_> = ground.input_atoms().cloned().collect();
    assert!(inputs.len() <= 6, "tiny exhaustive oracle only");
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
                    ground_text(p, a),
                    match replay.fact(a).unwrap() {
                        FactState::Settled(true) => "true",
                        FactState::Settled(false) => "false",
                        FactState::Blocked(_) => "blocked",
                    },
                )
            })
            .collect();
        worlds.push(facts);
    }
    let meaning = ground.symbolic(&limits).unwrap();
    let report = meaning.verify_at_most_one(&limits).unwrap();
    let groups: BTreeMap<_, _> = report
        .groups
        .iter()
        .map(|g| {
            (
                g.group
                    .key
                    .iter()
                    .map(|c| constant(p, *c))
                    .collect::<Vec<_>>()
                    .join(","),
                match &g.outcome {
                    VerifiedOutcome::Proved => "proved",
                    VerifiedOutcome::Unsupported => "unsupported",
                    VerifiedOutcome::Inconclusive(_) => {
                        panic!("tiny fixture unexpectedly inconclusive")
                    }
                    VerifiedOutcome::Counterexample(example) => {
                        let replay = ground
                            .evaluate(example.observation.present.iter().cloned(), &limits)
                            .unwrap();
                        for tuple in &example.tuples {
                            assert_eq!(replay.fact(tuple).unwrap(), FactState::Settled(true));
                        }
                        "counterexample"
                    }
                },
            )
        })
        .collect();
    let completion: Vec<_> = report
        .unresolved
        .iter()
        .map(|r| match r.completion {
            CompletionOutcome::NoMeaning(_) => "no meaning",
            CompletionOutcome::NoContradiction => "unsupported",
            CompletionOutcome::Deferred { .. } => "deferred",
            CompletionOutcome::Inconclusive(_) => panic!("completion limit"),
        })
        .collect();
    json!({"admitted": report.whole_program_admitted(), "worlds": worlds, "groups": groups, "completion": completion})
}

fn compare(ast: &Program, sources: &Sources) {
    match (
        before_recipes::lower(ast, sources).unwrap(),
        lowering::lower(ast, sources).unwrap(),
    ) {
        (LoweringOutcome::Lowered(old), LoweringOutcome::Lowered(new)) => {
            assert_eq!(fingerprint(&old, sources), fingerprint(&new, sources));
            assert_eq!(check(&old), check(&new));
        }
        (LoweringOutcome::UserErrors(old), LoweringOutcome::UserErrors(new)) => {
            assert_eq!(old, new)
        }
        _ => panic!("outcomes differ"),
    }
}

#[test]
fn every_existing_fixture_agrees_with_the_pre_recipe_lowerer() {
    for fixture in [
        Fixture::overlap(),
        Fixture::exclusive(),
        Fixture::ambiguous(),
        Fixture::redundant(),
        Fixture::mixed(false, false),
        Fixture::mixed(true, false),
        Fixture::mixed(false, true),
    ] {
        compare(&fixture.ast, &fixture.sources);
    }
    let text = include_str!("../fixtures/lowering.txt");
    let declarations = text.lines().take(2).collect::<Vec<_>>().join("\n");
    for mapping in text.lines().skip(2).filter(|s| !s.is_empty()) {
        let (sources, ast) = parse(&format!("{declarations}\n{mapping}\n"));
        compare(&ast, &sources);
    }
    for text in [
        "input i, i; slot s; s <- i;",
        "input i; slot s; missing <- i; s <- missing;",
        "input same; slot same; same <- same;",
        "input i; slot s; s <- i; s <- i;",
    ] {
        let (sources, ast) = parse(text);
        compare(&ast, &sources);
    }
}

#[test]
fn nested_and_generated_boolean_shapes_preserve_all_occurrence_paths() {
    let mut expressions = vec![
        "not ((available(a) and available(c)) or present(x))".to_owned(),
        "not (not available(a) or available(c))".into(),
        "not not (available(a) and available(c))".into(),
        "not not (available(a) or available(c))".into(),
        "not (available(a) and (present(x) or available(c)))".into(),
    ];
    for a in ["available(a)", "not available(a)", "not not available(a)"] {
        for op in ["and", "or"] {
            for prefix in ["", "not ", "not not "] {
                expressions.push(format!("{prefix}({a} {op} present(x))"));
            }
        }
    }
    for expr in expressions {
        let (sources, ast) = parse(&format!(
            "input i, x; slot a, b, c; a <- x; b <- i when {expr};"
        ));
        compare(&ast, &sources);
    }
}

#[test]
fn recipes_reassemble_against_current_spans_and_current_edit_eligibility() {
    let text =
        "input i, x; slot a; a <- i when present(x) and not present(x) and not available(a);";
    let (old_sources, old_ast) = parse(text);
    let old_projection = projection::project(&old_ast, &old_sources).unwrap();
    let old_recipes = recipes(&old_projection);
    assert!(
        !lowered(&old_ast, &old_sources)
            .attribution
            .rewrites
            .removals
            .is_empty()
    );
    for text in [
        format!("// shifted 😀\n{text}"),
        text.replace(
            "and not available",
            "and // keep this comment\n not available",
        ),
    ] {
        let (sources, ast) = parse(&text);
        let current = projection::project(&ast, &sources).unwrap();
        assert_eq!(old_projection.keys(), current.keys());
        let assembled = assembly::assemble(&current, &old_recipes, &sources).unwrap();
        assert_eq!(
            fingerprint(&assembled, &sources),
            fingerprint(&lowered(&ast, &sources), &sources)
        );
        assert_eq!(old_recipes, recipes(&current));
        for edit in assembled.attribution.rewrites.removals.values() {
            let mut edited = text.clone();
            edited.replace_range(edit.span.byte_range(), &edit.replacement);
            let (edited_sources, edited_ast) = parse(&edited);
            lowered(&edited_ast, &edited_sources);
        }
        if text.contains("keep this comment") {
            assert!(
                assembled.attribution.rewrites.removals.len()
                    < lowered(&old_ast, &old_sources)
                        .attribution
                        .rewrites
                        .removals
                        .len()
            );
        }
    }
}

#[test]
fn path_diagnostics_move_primary_and_related_locations_without_revalidation() {
    for text in [
        "input i; slot s; s <- missing;",
        "input i; slot s; s <- i when available(i);",
        "input i; slot s; slot s; s <- i;",
    ] {
        let (old_sources, old_ast) = parse(text);
        let old = projection::project(&old_ast, &old_sources).unwrap();
        let diagnostics = semantic::validate(&old.keys()).unwrap();
        assert!(!diagnostics.is_empty());
        let shifted = format!("// new snapshot 😀\n{text}");
        let (sources, ast) = parse(&shifted);
        let current = projection::project(&ast, &sources).unwrap();
        assert_eq!(old.keys(), current.keys());
        assert_eq!(diagnostics, semantic::validate(&current.keys()).unwrap());
        let relocated = current.diagnostics(&diagnostics).unwrap();
        let LoweringOutcome::UserErrors(fresh) = lowering::lower(&ast, &sources).unwrap() else {
            panic!()
        };
        assert_eq!(relocated, fresh);
        for (old, new) in old
            .diagnostics(&diagnostics)
            .unwrap()
            .iter()
            .zip(&relocated)
        {
            assert_eq!(
                old_sources.text(old.span).unwrap(),
                sources.text(new.span).unwrap()
            );
            assert_eq!(
                old.span.byte_range().start + shifted.len() - text.len(),
                new.span.byte_range().start
            );
            for (old, new) in old.related.iter().zip(&new.related) {
                assert_eq!(
                    old.byte_range().start + shifted.len() - text.len(),
                    new.byte_range().start
                );
            }
        }
    }
}

#[test]
fn local_helpers_and_duplicate_occurrences_survive_new_assembly_order() {
    let declaration = "input i; slot a, b, c;";
    let first = "b <- i when not (available(a) and available(c));";
    let second = "c <- i when (available(a) or available(b)) and present(i);";
    let (sources, ast) = parse(&format!("{declaration} {first} {second} {first}"));
    let original = projection::project(&ast, &sources).unwrap();
    let old_recipes: BTreeMap<_, _> = original
        .keys()
        .into_iter()
        .zip(recipes(&original))
        .collect();
    assert_eq!(original.statements[2].key.duplicate, 0);
    assert_eq!(original.statements[4].key.duplicate, 1);
    for text in [
        format!("{declaration} {second} {first} {first}"),
        format!(
            "{declaration} a <- i when not (available(b) and available(c)); {second} {first} {first}"
        ),
    ] {
        let (sources, ast) = parse(&text);
        let projection = projection::project(&ast, &sources).unwrap();
        let reused: Vec<_> = projection
            .keys()
            .iter()
            .map(|k| {
                old_recipes
                    .get(k)
                    .cloned()
                    .unwrap_or_else(|| Recipe::lower(k.form.clone()))
            })
            .collect();
        let assembled = assembly::assemble(&projection, &reused, &sources).unwrap();
        assert_eq!(
            fingerprint(&assembled, &sources),
            fingerprint(&lowered(&ast, &sources), &sources)
        );
        let LoweringOutcome::Lowered(baseline) = before_recipes::lower(&ast, &sources).unwrap()
        else {
            panic!()
        };
        assert_eq!(
            fingerprint(&assembled, &sources),
            fingerprint(&baseline, &sources)
        );
    }
}

#[test]
fn incompatible_recipe_or_path_fails_instead_of_guessing_an_origin() {
    let (sources, ast) = parse("input i; slot s; s <- i;");
    let original = projection::project(&ast, &sources).unwrap();
    let (other_sources, other_ast) = parse("input i; slot s; s <- i when present(i);");
    let other = projection::project(&other_ast, &other_sources).unwrap();
    assert!(assembly::assemble(&other, &recipes(&original), &other_sources).is_err());
    assert!(other.statements[2].span(&AstPath::DeclaredName(0)).is_err());
    let (neg_sources, neg_ast) = parse("input i; slot s; s <- i when not not present(i);");
    let neg = projection::project(&neg_ast, &neg_sources).unwrap();
    assert_ne!(
        other.keys(),
        neg.keys(),
        "equal meaning does not erase authored structure"
    );
}
