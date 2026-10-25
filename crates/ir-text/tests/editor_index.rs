use denotate_ir::Namespace;
use denotate_ir_text::{
    ProgramMembership, SourceFile,
    index::{Expected, Index, Kind, Lookup, Name, Scope},
    load, parser,
};
use std::sync::Arc;

fn update(index: &mut Index, uri: &str, text: &str) {
    let tree = parser().parse(text, None).unwrap();
    index.update(SourceFile::new(uri, 1, text), tree);
}
fn targets(index: &Index, root: &str, uri: &str, needle: &str) -> Vec<String> {
    let file = &index.files[uri];
    let byte = file.source.text.find(needle).unwrap();
    let r = file.reference_at(byte).unwrap();
    index
        .candidates(root, uri, &r.scope, &r.lookup, Some(&r.name))
        .into_iter()
        .map(|s| {
            let d = index.declaration(&s).unwrap();
            format!(
                "{}:{:?}:{:?}:{}",
                s.uri, d.scope.namespace, d.kind, d.name.text
            )
        })
        .collect()
}
#[test]
fn complete_grammar_shares_strict_loader_resolution_and_origins_are_not_symbols() {
    let a = "namespace a { sort S; const '007', 7: S; relation $helper(); relation r(x:S); input p(x:S); }";
    let b = r#"use a;
namespace b;
relation q(x: a::S);
q(X) :- a::r(X), a::p(X);
a::$helper();
a::r('007');
a::r(007);
domain a::S = [a::'007', a::7];
obligation one: at_most_one(q, group_by: x);
assumption known: at_most_one(a::p, group_by: (x));
#src = source("file:///source.dsl", view: "dsl", hash: "sha256:0000000000000000000000000000000000000000000000000000000000000000");
#origin = loc(#src 1:1 to 1:2);
q('007') loc(#src {self: 1:1 to 1:2, head.0: 1:1 to 1:2});
q(7) loc(#origin);
"#;
    let membership = ProgramMembership::single("root", ["a".into(), "b".into()]);
    let mut index = Index::default();
    update(&mut index, "a", a);
    update(&mut index, "b", b);
    index.set_membership(&membership).unwrap();
    assert!(index.diagnostics("root", "a").is_empty());
    assert!(
        index.diagnostics("root", "b").is_empty(),
        "{:?}",
        index.diagnostics("root", "b")
    );
    let loaded = load(
        &membership,
        &[SourceFile::new("a", 1, a), SourceFile::new("b", 1, b)],
    );
    assert!(loaded.is_ok(), "{loaded:?}");
    for (uri, file) in &index.files {
        for r in &file.references {
            if !matches!(r.lookup, Lookup::Variable { .. } | Lookup::Anonymous(_)) {
                assert_eq!(
                    index
                        .candidates("root", uri, &r.scope, &r.lookup, Some(&r.name))
                        .len(),
                    1,
                    "{uri}: {r:?}"
                );
            }
        }
    }
    let projection = &index.files["b"];
    for ignored in ["file:///source.dsl", "head.0", "self", "sha256:"] {
        let byte = b.find(ignored).unwrap();
        assert!(projection.reference_at(byte).is_none(), "{ignored}");
    }
    assert_eq!(
        targets(&index, "root", "b", "a::'007'")[0]
            .split(':')
            .last(),
        Some("007")
    );
    assert_eq!(
        targets(&index, "root", "b", "a::7")[0].split(':').last(),
        Some("7")
    );
}
#[test]
fn root_specific_resolution_does_not_union_namespaces_or_follow_use() {
    let mut index = Index::default();
    update(&mut index, "a", "namespace a; sort S; relation r(x:S);");
    update(&mut index, "b", "namespace b; sort S; relation r(x:S);");
    update(
        &mut index,
        "user",
        "use a; use b; relation q(); q() :- r(_);",
    );
    for (root, members) in [
        ("left", vec!["a", "user"]),
        ("right", vec!["b", "user"]),
        ("both", vec!["a", "b", "user"]),
        ("single", vec!["user"]),
    ] {
        index
            .set_membership(&ProgramMembership::single(
                root,
                members.into_iter().map(String::from),
            ))
            .unwrap();
    }
    assert!(targets(&index, "left", "user", "r(_)")[0].starts_with("a:"));
    assert!(targets(&index, "right", "user", "r(_)")[0].starts_with("b:"));
    assert_eq!(targets(&index, "both", "user", "r(_)").len(), 2);
    assert!(targets(&index, "single", "user", "r(_)").is_empty());
}
#[test]
fn namespace_blocks_qualification_generated_names_and_enclosing_ambiguity() {
    let text = "sort S; namespace a { sort S; namespace b { relation r(x:S); relation exact(x:::S); relation $h(); relation '$h'(); $h(); '$h'(); } } namespace a { relation more(x:a::S); }";
    let mut index = Index::default();
    update(&mut index, "doc", text);
    index
        .set_membership(&ProgramMembership::single("root", ["doc".into()]))
        .unwrap();
    let issues = index.diagnostics("root", "doc");
    assert_eq!(issues.len(), 1, "{issues:?}");
    assert!(issues[0].message.contains("Ambiguous"));
    assert_eq!(
        targets(&index, "root", "doc", "S); relation exact").len(),
        2
    );
    assert_eq!(targets(&index, "root", "doc", "::S").len(), 1);
    let helper = index.files["doc"]
        .references
        .iter()
        .filter(|r| r.lookup == Lookup::Name(Kind::Relation))
        .collect::<Vec<_>>();
    let symbols = helper
        .iter()
        .map(|r| {
            index.candidates("root", "doc", &r.scope, &r.lookup, Some(&r.name))[0]
                .id
                .clone()
        })
        .collect::<Vec<_>>();
    assert_ne!(symbols[0], symbols[1]);
}
#[test]
fn recovery_keeps_declarations_but_suppresses_guessed_arity_and_dependent_constants() {
    for broken in [
        "relation r(x:S, y: );",
        "relation r(x:S,);",
        "relation r(x:S,y);",
    ] {
        let text = format!(
            "namespace a; sort S; {broken} r(missing); relation good(x:S); good(X) :- good(X);"
        );
        let mut index = Index::default();
        update(&mut index, "doc", &text);
        index
            .set_membership(&ProgramMembership::single("root", ["doc".into()]))
            .unwrap();
        let declarations = &index.files["doc"].declarations;
        assert!(
            declarations
                .values()
                .find(|d| d.name.text == "r" && d.kind == Kind::Relation)
                .unwrap()
                .parameters
                .is_none()
        );
        assert!(
            declarations
                .values()
                .find(|d| d.name.text == "good" && d.kind == Kind::Relation)
                .unwrap()
                .parameters
                .is_some()
        );
        let diagnostics = index.diagnostics("root", "doc");
        assert!(
            diagnostics
                .iter()
                .all(|d| d.code != "arity" && !d.message.contains("missing")),
            "{broken}: {diagnostics:?}"
        );
    }
}
#[test]
fn incremental_edits_refresh_anchors_and_reuse_unrelated_files_and_queries() {
    let mut index = Index::default();
    let a = "namespace a; sort S; const a:S; relation r(x:S); r(X) :- r(X);";
    let b = "namespace b; sort T; const b:T; relation q(x:T); q(X) :- q(X);";
    update(&mut index, "a", a);
    update(&mut index, "b", b);
    index
        .set_membership(&ProgramMembership::single("root", ["a".into(), "b".into()]))
        .unwrap();
    index
        .set_membership(&ProgramMembership::single("other", ["b".into()]))
        .unwrap();
    index.diagnostics("root", "a");
    index.diagnostics("other", "b");
    let before = index.query_counts();
    let other = index.files["b"].clone();
    let old = index.files["a"].clone();
    // Exercise a real edited tree, exactly the update B supplies.
    let prefix = "// 🦀 trivia\n";
    let changed = format!("{prefix}{a}");
    let mut tree = old.tree.clone();
    tree.edit(&tree_sitter::InputEdit {
        start_byte: 0,
        old_end_byte: 0,
        new_end_byte: prefix.len(),
        start_position: tree_sitter::Point::new(0, 0),
        old_end_position: tree_sitter::Point::new(0, 0),
        new_end_position: tree_sitter::Point::new(1, 0),
    });
    let tree = parser().parse(&changed, Some(&tree)).unwrap();
    index.update(SourceFile::new("a", 2, changed.as_str()), tree);
    assert!(Arc::ptr_eq(&other, &index.files["b"]));
    assert_eq!(old.declarations, index.files["a"].declarations);
    assert_ne!(old.anchors, index.files["a"].anchors);
    index.diagnostics("root", "a");
    index.diagnostics("other", "b");
    assert_eq!(before, index.query_counts());
    for text in [
        changed.replace("r(X) :- r(X)", "r(X) :- r(Y)"),
        changed.replace("relation r(x:S)", "relation r(x:S,y:S)"),
        changed.replace("sort S", "sort T"),
    ] {
        update(&mut index, "a", &text);
        let before = index.query_counts();
        index.diagnostics("other", "b");
        assert_eq!(
            before,
            index.query_counts(),
            "unrelated selected root should reuse queries"
        );
        let mut cold = Index::default();
        update(&mut cold, "a", &text);
        update(&mut cold, "b", b);
        cold.set_membership(&ProgramMembership::single("root", ["a".into(), "b".into()]))
            .unwrap();
        assert_eq!(
            index.diagnostics("root", "a"),
            cold.diagnostics("root", "a")
        );
        assert_eq!(
            targets(&index, "root", "a", "r(X)"),
            targets(&cold, "root", "a", "r(X)")
        );
    }
    index
        .set_membership(&ProgramMembership::single("root", ["b".into()]))
        .unwrap();
    let scope = Scope {
        namespace: Namespace::new(["a"]).unwrap(),
        imports: vec![],
    };
    assert!(
        index
            .candidates(
                "root",
                "a",
                &scope,
                &Lookup::Name(Kind::Relation),
                Some(&Name::bare("r"))
            )
            .is_empty()
    );
    assert!(
        index
            .expected_sort(
                "other",
                &Scope {
                    namespace: Namespace::new(["b"]).unwrap(),
                    imports: vec![]
                },
                &Expected::Argument(Name::bare("q"), 0)
            )
            .is_some()
    );
}

#[test]
fn declaration_ids_survive_spelling_edits_and_unrelated_queries_are_backdated() {
    let mut index = Index::default();
    let text = "namespace a { sort S; relation r(x:S); r(X) :- r(X); } namespace b { sort T; relation q(x:T); q(X) :- q(X); }";
    update(&mut index, "doc", text);
    index
        .set_membership(&ProgramMembership::single("root", ["doc".into()]))
        .unwrap();
    // Opening the same text with a fresh parse must retain a coherent node-ID
    // map for the following edit, and must still refresh the snapshot revision.
    update(&mut index, "doc", text);
    let old = index.files["doc"].clone();
    let r = old
        .declarations
        .values()
        .find(|d| d.kind == Kind::Relation && d.name.text == "r")
        .unwrap()
        .id
        .clone();
    let b_rule = old
        .rules
        .iter()
        .find(|(_, r)| r.scope.namespace.segments() == ["b"])
        .unwrap()
        .0
        .clone();
    index.rule_analysis("root", "doc", &b_rule);
    let before = index.query_counts();
    let changed = text.replace("relation r(x:S)", "relation renamed(x:S)");
    update(&mut index, "doc", &changed);
    assert_eq!(index.files["doc"].declarations[&r].name.text, "renamed");
    index.rule_analysis("root", "doc", &b_rule);
    assert_eq!(
        before,
        index.query_counts(),
        "renaming a declaration must reuse unrelated root-local queries"
    );
    update(&mut index, "doc", &format!("// moved\n{changed}"));
    index.rule_analysis("root", "doc", &b_rule);
    assert_eq!(
        before,
        index.query_counts(),
        "namespace-block anchors must not enter semantic dependencies"
    );
}

#[test]
fn aliases_are_file_local_and_invalid_names_do_not_become_guessed_references() {
    let mut index = Index::default();
    update(
        &mut index,
        "a",
        "relation r(); r() loc(#origin); #origin = loc(#missing 1:1 to 1:2);",
    );
    update(
        &mut index,
        "b",
        "#origin = loc(#missing 1:1 to 1:2); relation r();",
    );
    index
        .set_membership(&ProgramMembership::single("root", ["a".into(), "b".into()]))
        .unwrap();
    assert_eq!(targets(&index, "root", "a", "#origin").len(), 1);
    assert!(targets(&index, "root", "a", "#origin")[0].starts_with("a:"));
    update(
        &mut index,
        "a",
        "sort S; const 999999999999999999999: S; relation 'bad\\q'(); relation good(); good();",
    );
    let issues = index.diagnostics("root", "a");
    assert!(issues.iter().any(|d| d.message.contains("64-bit")));
    assert!(issues.iter().any(|d| d.message.contains("escape")));
    assert_eq!(targets(&index, "root", "a", "good();").len(), 1);
}

#[test]
fn diagnostic_namespace_labels_use_den_spelling_and_name_spelling_preserves_kind() {
    let mut index = Index::default();
    let uri = "file:///labels.den";
    update(
        &mut index,
        uri,
        "sort S; const g:S; relation q(x:S); namespace a { sort S; const a:a::S; relation q(x:a::S); } namespace b { use a; q(g); a::q(g); }",
    );
    index
        .set_membership(&ProgramMembership::single("root", [uri.into()]))
        .unwrap();
    let messages = index
        .diagnostics("root", uri)
        .iter()
        .map(|i| i.message.clone())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(messages.contains("(::, a)"), "{messages}");
    assert!(messages.contains("a::S"), "{messages}");
    assert!(!messages.contains("a.S"));
    use denotate_ir_text::{NameKind, spelling};
    assert_eq!(spelling("I", NameKind::Constant), "'I'");
    assert_eq!(spelling("I", NameKind::Variable), "I");
    assert_eq!(spelling("i", NameKind::Variable), "?'i'");
}
