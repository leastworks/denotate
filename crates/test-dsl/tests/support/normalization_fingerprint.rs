//! Structural snapshot addresses; captured independently before 5.3a implementation.
#![allow(dead_code)]
use denotate_check::GroundAtom;
use denotate_ir::*;
use denotate_test_dsl::lowering::LoweredProgram;
use serde_json::{Value, json};
use std::collections::BTreeMap;
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
pub fn fingerprint(p: &LoweredProgram, sources: &Sources) -> Value {
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
