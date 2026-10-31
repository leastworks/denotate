#![allow(dead_code)]
//! Independent structural correspondence: no printer symbol allocation or rule-position helpers.
use denotate_ir::*;
use denotate_ir_text::*;
use std::collections::{BTreeMap, BTreeSet};
pub struct Correspondence {
    pub ids: BTreeMap<OccurrenceId, OccurrenceId>,
}
fn bind(ids: &mut BTreeMap<OccurrenceId, OccurrenceId>, a: OccurrenceId, b: OccurrenceId) {
    if let Some(previous) = ids.get(&a) {
        assert_eq!(*previous, b, "one identity must keep all references");
    } else {
        assert!(
            !ids.values().any(|id| *id == b),
            "bijection must preserve multiplicity"
        );
        ids.insert(a, b);
    }
}
fn origins(
    s: &Sources,
    p: &Provenance,
    id: OccurrenceId,
) -> BTreeSet<(String, String, String, usize, usize)> {
    p.origins(id)
        .iter()
        .map(|o| {
            let source = s.snapshot(o.span.snapshot()).unwrap();
            let range = o.span.byte_range();
            (
                source.uri.clone(),
                source.view.clone(),
                origins::content_hash(&source.text),
                range.start,
                range.end,
            )
        })
        .collect()
}
fn atom(
    a: &Atom,
    b: &Atom,
    original: &Corpus,
    loaded: &Corpus,
    ids: &mut BTreeMap<OccurrenceId, OccurrenceId>,
) {
    let ar = a.relation();
    let br = b.relation();
    assert_eq!(original.namespace(ar), loaded.namespace(br));
    assert_eq!(
        original.is_generated_relation(ar),
        loaded.is_generated_relation(br)
    );
    bind(ids, ar.into(), br.into());
    bind(ids, a.id(), b.id());
    assert_eq!(a.arguments().len(), b.arguments().len());
    for (a, b) in a.arguments().iter().zip(b.arguments()) {
        match (a.value(), b.value()) {
            (Term::Constant(a), Term::Constant(b)) => assert_eq!(ids[&(*a).into()], (*b).into()),
            (Term::Variable { name: a, sort: sa }, Term::Variable { name: b, sort: sb }) => {
                assert_eq!(a, b);
                assert_eq!(ids[&(*sa).into()], (*sb).into());
            }
            _ => panic!("term kind changed"),
        }
        bind(ids, a.id(), b.id());
    }
}
pub fn compare(
    p: &ExportProgram<'_>,
    q: &LoadedProgram,
    base: &str,
    traced: bool,
) -> Correspondence {
    let a = p.corpus;
    let b = &q.corpus;
    let mut ids = BTreeMap::new();
    assert_eq!(a.sorts().count(), b.sorts().count());
    assert_eq!(a.constants().count(), b.constants().count());
    assert_eq!(a.relations().count(), b.relations().count());
    assert_eq!(a.rules().count(), b.rules().count());
    assert_eq!(a.obligations().count(), b.obligations().count());
    for x in a.sorts() {
        let y = b
            .sorts()
            .find(|y| y.name == x.name && a.namespace(x.id) == b.namespace(y.id))
            .unwrap();
        bind(&mut ids, x.id.into(), y.id.into());
    }
    for x in a.constants() {
        let y = b
            .constants()
            .find(|y| {
                y.name == x.name
                    && a.namespace(x.id) == b.namespace(y.id)
                    && ids[&x.sort.into()] == y.sort.into()
            })
            .unwrap();
        bind(&mut ids, x.id.into(), y.id.into());
    }
    for x in a.relations().filter(|r| !a.is_generated_relation(r.id)) {
        let y = b
            .relations()
            .find(|y| {
                !b.is_generated_relation(y.id)
                    && y.name == x.name
                    && a.namespace(x.id) == b.namespace(y.id)
            })
            .unwrap();
        bind(&mut ids, x.id.into(), y.id.into());
    }
    for (file_index, file) in p.layout.files.iter().enumerate() {
        let uri = format!("{base}/{}", file.path);
        let left = a
            .rules()
            .filter(|r| p.layout.placements[&r.id.into()] == file_index)
            .collect::<Vec<_>>();
        let right = b
            .rules()
            .filter(|r| q.owners[&r.id.into()] == uri)
            .collect::<Vec<_>>();
        assert_eq!(left.len(), right.len());
        for (x, y) in left.into_iter().zip(right) {
            assert_eq!(a.namespace(x.id), b.namespace(y.id));
            bind(&mut ids, x.id.into(), y.id.into());
            atom(&x.head, &y.head, a, b, &mut ids);
            assert_eq!(x.body.len(), y.body.len());
            for (x, y) in x.body.iter().zip(&y.body) {
                assert_eq!(
                    matches!(x, Literal::Negative(_)),
                    matches!(y, Literal::Negative(_))
                );
                atom(x.atom(), y.atom(), a, b, &mut ids);
            }
        }
    }
    // Unused/symmetric helpers have no structural uses; choose a remaining match
    // with the same namespace, placement and origin set instead of merging them.
    for x in a.relations().filter(|r| a.is_generated_relation(r.id)) {
        if ids.contains_key(&x.id.into()) {
            continue;
        }
        let uri = format!(
            "{base}/{}",
            p.layout.files[p.layout.placements[&x.id.into()]].path
        );
        let y = b
            .relations()
            .find(|y| {
                b.is_generated_relation(y.id)
                    && !ids.values().any(|id| *id == y.id.into())
                    && a.namespace(x.id) == b.namespace(y.id)
                    && q.owners[&y.id.into()] == uri
                    && (!traced
                        || origins(p.sources, p.provenance, x.id.into())
                            == origins(&q.sources, &q.embedded.provenance, y.id.into()))
            })
            .unwrap();
        bind(&mut ids, x.id.into(), y.id.into());
    }
    for x in a.relations() {
        let y = b
            .relations()
            .find(|r| OccurrenceId::from(r.id) == ids[&x.id.into()])
            .unwrap();
        assert_eq!(x.role, y.role);
        assert_eq!(
            x.input_domain.map(|id| ids[&id.into()]),
            y.input_domain.map(Into::into)
        );
        assert_eq!(x.parameters.len(), y.parameters.len());
        for (x, y) in x.parameters.iter().zip(&y.parameters) {
            assert_eq!(x.name, y.name);
            assert_eq!(ids[&x.sort.into()], y.sort.into());
        }
    }
    for x in a.obligations() {
        let y = b
            .obligations()
            .find(|y| y.name == x.name && a.namespace(x.id) == b.namespace(y.id))
            .unwrap();
        assert_eq!(x.message_template, y.message_template);
        assert_eq!(
            std::mem::discriminant(&x.requirement),
            std::mem::discriminant(&y.requirement)
        );
        assert_eq!(
            ids[&x.requirement.relation().into()],
            y.requirement.relation().into()
        );
        assert_eq!(x.requirement.group_by(), y.requirement.group_by());
        bind(&mut ids, x.id.into(), y.id.into());
    }
    for x in a.assumptions() {
        let y = b
            .assumptions()
            .find(|y| y.name == x.name && a.namespace(x.id) == b.namespace(y.id))
            .unwrap();
        assert_eq!(x.restriction.kind(), y.restriction.kind());
        assert_eq!(
            ids[&x.restriction.relation().into()],
            y.restriction.relation().into()
        );
        assert_eq!(x.restriction.group_by(), y.restriction.group_by());
        bind(&mut ids, x.id.into(), y.id.into());
    }
    assert_eq!(a.notices().count(), b.notices().count());
    for x in a.notices() {
        let y = b
            .notices()
            .find(|y| y.name == x.name && a.namespace(x.id) == b.namespace(y.id))
            .unwrap();
        assert_eq!(x.message, y.message);
        assert_eq!(ids[&x.condition.into()], y.condition.into());
        assert_eq!(x.within.map(|id| ids[&id.into()]), y.within.map(Into::into));
        bind(&mut ids, x.id.into(), y.id.into());
    }
    assert_eq!(a.verifications().count(), b.verifications().count());
    for x in a.verifications() {
        let y = b
            .verifications()
            .find(|y| y.name == x.name && a.namespace(x.id) == b.namespace(y.id))
            .unwrap();
        assert_eq!(
            x.assumptions
                .iter()
                .map(|id| ids[&(*id).into()])
                .collect::<Vec<_>>(),
            y.assumptions
                .iter()
                .map(|id| (*id).into())
                .collect::<Vec<OccurrenceId>>()
        );
        assert_eq!(
            x.obligations
                .iter()
                .map(|id| ids[&(*id).into()])
                .collect::<Vec<_>>(),
            y.obligations
                .iter()
                .map(|id| (*id).into())
                .collect::<Vec<OccurrenceId>>()
        );
        assert_eq!(
            x.notices
                .iter()
                .map(|id| ids[&(*id).into()])
                .collect::<Vec<_>>(),
            y.notices
                .iter()
                .map(|id| (*id).into())
                .collect::<Vec<OccurrenceId>>()
        );
        bind(&mut ids, x.id.into(), y.id.into());
    }
    for (sort, domain) in p.domains {
        let mapped = domain
            .iter()
            .map(|id| ids[&(*id).into()])
            .collect::<BTreeSet<_>>();
        let sort = b
            .sorts()
            .find(|s| OccurrenceId::from(s.id) == ids[&(*sort).into()])
            .unwrap();
        assert_eq!(
            mapped,
            q.domains[&sort.id].iter().map(|id| (*id).into()).collect()
        );
    }
    assert_eq!(a.assumptions().count(), b.assumptions().count());
    for (x, y) in &ids {
        if traced {
            assert_eq!(
                origins(p.sources, p.provenance, *x),
                origins(&q.sources, &q.embedded.provenance, *y),
                "origin association changed"
            );
        }
        assert_eq!(q.provenance.origins(*y).len(), 1);
        let span = q.provenance.origins(*y)[0].span;
        let source = q.sources.snapshot(span.snapshot()).unwrap();
        assert_eq!(source.view, "denotate");
        let tree = parser().parse(source.text.as_ref(), None).unwrap();
        let range = span.byte_range();
        let node = tree
            .root_node()
            .descendant_for_byte_range(range.start, range.end)
            .unwrap();
        assert_eq!(
            node.byte_range(),
            range,
            "current .den origin must be an exact syntax node"
        );
        if let Some(file) = p.layout.placements.get(x) {
            let uri = format!("{base}/{}", p.layout.files[*file].path);
            assert_eq!(q.owners[y], uri);
            let doc = q.documents.iter().find(|d| d.uri == uri).unwrap();
            assert_eq!(
                doc.ownership,
                if p.layout.files[*file].ownership == Ownership::Library {
                    "library"
                } else {
                    "user"
                }
            );
        }
    }
    check_current_rule_spans(q);
    assert_eq!(
        ids.len(),
        q.owners.len(),
        "every current occurrence must have a correspondence"
    );
    Correspondence { ids }
}

fn check_current_rule_spans(p: &LoadedProgram) {
    fn statements<'a>(node: tree_sitter::Node<'a>, out: &mut Vec<tree_sitter::Node<'a>>) {
        if node.kind() == "statement" {
            out.push(node);
            return;
        }
        for child in node.named_children(&mut node.walk()) {
            statements(child, out);
        }
    }
    let span = |id| p.provenance.origins(id)[0].span.byte_range();
    for document in &p.documents {
        let source = p.sources.snapshot(document.snapshot).unwrap();
        let tree = parser().parse(source.text.as_ref(), None).unwrap();
        let mut nodes = Vec::new();
        statements(tree.root_node(), &mut nodes);
        let rules = p
            .corpus
            .rules()
            .filter(|r| p.owners[&r.id.into()] == document.uri)
            .collect::<Vec<_>>();
        assert_eq!(rules.len(), nodes.len());
        for (rule, node) in rules.into_iter().zip(nodes) {
            assert_eq!(span(rule.id.into()), node.byte_range());
            let head = node.child_by_field_name("head").unwrap();
            let body = node
                .named_children(&mut node.walk())
                .filter(|n| matches!(n.kind(), "positive_atom" | "negative_atom"))
                .collect::<Vec<_>>();
            assert_eq!(body.len(), rule.body.len());
            for (atom, node) in std::iter::once((&rule.head, head))
                .chain(rule.body.iter().map(Literal::atom).zip(body))
            {
                assert_eq!(span(atom.id()), node.byte_range());
                let node = if node.kind() == "negative_atom" {
                    node.named_children(&mut node.walk())
                        .find(|n| n.kind() == "atom")
                        .unwrap()
                } else {
                    node
                };
                let name = node.child_by_field_name("name").unwrap();
                let terms = node
                    .named_children(&mut node.walk())
                    .filter(|n| n.id() != name.id() && n.kind() != "comment")
                    .collect::<Vec<_>>();
                assert_eq!(terms.len(), atom.arguments().len());
                for (term, node) in atom.arguments().iter().zip(terms) {
                    assert_eq!(span(term.id()), node.byte_range());
                }
            }
        }
    }
}
