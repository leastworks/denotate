mod support;
use denotate_check::InputAtMostOne;
use denotate_ir::*;
use denotate_ir_text::{origins::*, *};
use std::collections::BTreeMap;

fn fixture() -> (
    Corpus,
    Sources,
    Provenance,
    denotate_check::Domains,
    ExportLayout,
    Vec<ExportAssumption>,
) {
    let mut c = Corpus::new();
    let ns = Namespace::new(["a::quoted", "b"]).unwrap();
    let s = c.declare_sort("S").unwrap();
    let empty = c.declare_sort("Empty").unwrap();
    let a = c.declare_constant("01", s).unwrap();
    let _unused = c.declare_constant("unused", s).unwrap();
    let p = c
        .declare_relation("input", RelationRole::Input, [Parameter::new("x", s)])
        .unwrap();
    let r = c
        .declare_relation_in(
            &ns,
            "$condition_1",
            RelationRole::Derived,
            [Parameter::new("x", s)],
        )
        .unwrap();
    let helper = c
        .declare_generated_relation_named_in(&ns, "arbitrary helper")
        .unwrap();
    let duplicate_helper = c
        .declare_generated_relation_named_in(&ns, "arbitrary helper")
        .unwrap();
    let mut user_rules = vec![];
    for h in [helper, duplicate_helper] {
        let head = c.atom(h, []).unwrap();
        let body = c.atom(p, [Term::Constant(a)]).unwrap();
        user_rules.push(c.add_rule_in(&ns, head, [Literal::Positive(body)]).unwrap());
    }
    let head = c.atom(r, [Term::Constant(a)]).unwrap();
    let body = c.atom(helper, []).unwrap();
    user_rules.push(c.add_rule_in(&ns, head, [Literal::Negative(body)]).unwrap());
    let obligation = c
        .at_most_one("unique", r, [], "quoted \"message\"\n")
        .unwrap();
    let mut sources = Sources::new();
    let snapshot = sources
        .add(
            "file:///origin.den",
            7,
            "denotate",
            "\u{feff}é😀e\u{301}\r\nend\n",
        )
        .unwrap();
    let mut provenance = Provenance::new();
    for id in top_level(&c) {
        provenance
            .attach(
                &c,
                &sources,
                id,
                [Origin::new(
                    sources
                        .span(snapshot, 0..sources.snapshot(snapshot).unwrap().text.len())
                        .unwrap(),
                )],
            )
            .unwrap();
    }
    for rule in c.rules() {
        for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
            for id in std::iter::once(atom.id()).chain(atom.arguments().iter().map(|t| t.id())) {
                provenance
                    .attach(
                        &c,
                        &sources,
                        id,
                        [Origin::new(sources.span(snapshot, 3..5).unwrap())],
                    )
                    .unwrap();
            }
        }
    }
    let mut layout = ExportLayout {
        files: vec![
            ExportFile {
                path: "library/base.den".into(),
                ownership: Ownership::Library,
            },
            ExportFile {
                path: "sources/a.den".into(),
                ownership: Ownership::User,
            },
            ExportFile {
                path: "sources/b.den".into(),
                ownership: Ownership::User,
            },
        ],
        placements: top_level(&c).into_iter().map(|id| (id, 0)).collect(),
        assumptions: vec![0, 0],
    };
    for (i, id) in user_rules.iter().enumerate() {
        layout
            .placements
            .insert((*id).into(), if i == 1 { 2 } else { 1 });
    }
    layout.placements.insert(r.into(), 1);
    layout.placements.insert(helper.into(), 1);
    layout.placements.insert(duplicate_helper.into(), 2);
    layout.placements.insert(obligation.into(), 1);
    let assumptions = (0..2)
        .map(|_| ExportAssumption {
            namespace: Namespace::default(),
            name: None,
            constraint: InputAtMostOne {
                relation: p,
                group_by: vec![],
            },
            origins: vec![Origin::new(sources.span(snapshot, 3..5).unwrap())],
        })
        .collect();
    (
        c,
        sources,
        provenance,
        BTreeMap::from([(s, vec![a]), (empty, vec![])]),
        layout,
        assumptions,
    )
}
#[test]
fn export_preserves_origins_domains_helpers_ownership_and_file_rule_sequences() {
    let (c, sources, provenance, domains, layout, assumptions) = fixture();
    let p = ExportProgram {
        corpus: &c,
        sources: &sources,
        provenance: &provenance,
        domains: &domains,
        layout: &layout,
        assumptions: &assumptions,
    };
    for embedded_origins in [false, true] {
        let bundle = print(&p, PrintOptions { embedded_origins }).unwrap();
        assert_eq!(
            bundle,
            print(&p, PrintOptions { embedded_origins }).unwrap()
        );
        let (membership, documents) = bundle.documents("file:///export");
        let loaded = load_with_resolver(&membership, &documents, Some(&mut &sources))
            .unwrap_or_else(|e| panic!("{e:?}\n{:#?}", bundle.files));
        assert!(loaded.embedded.notices.is_empty());
        support::compare(&p, &loaded, "file:///export", embedded_origins);
        assert_eq!(loaded.corpus.rules().count(), 3);
        assert_eq!(loaded.corpus.constants().count(), 2);
        assert_eq!(loaded.assumptions.len(), 2);
        assert_eq!(
            loaded
                .corpus
                .relations()
                .filter(|r| loaded.corpus.is_generated_relation(r.id))
                .count(),
            2
        );
        assert_eq!(loaded.domains.values().map(Vec::len).sum::<usize>(), 1);
        assert_eq!(
            loaded
                .corpus
                .constants()
                .find(|k| k.name == "01")
                .unwrap()
                .name,
            "01"
        );
        assert_eq!(
            loaded
                .corpus
                .rules()
                .filter(|r| loaded.owners[&r.id.into()].ends_with("/a.den"))
                .count(),
            2
        );
        assert!(loaded.documents.iter().any(|d| d.ownership == "library"));
        for id in top_level(&loaded.corpus) {
            assert_eq!(loaded.provenance.origins(id).len(), 1);
            assert_eq!(
                loaded.embedded.provenance.origins(id).len(),
                usize::from(embedded_origins)
            );
        }
        if embedded_origins {
            assert!(bundle.files.values().any(|s| s.contains("= loc(#src0 {")));
            assert_eq!(loaded.embedded.assumptions.len(), 2);
        }
    }
}
#[test]
fn invalid_layout_domains_and_assumptions_fail_before_export() {
    let (c, sources, provenance, domains, layout, assumptions) = fixture();
    let mut invalid = layout.clone();
    invalid
        .placements
        .remove(&c.sorts().next().unwrap().id.into());
    let p = |layout, domains, assumptions| {
        print(
            &ExportProgram {
                corpus: &c,
                sources: &sources,
                provenance: &provenance,
                domains,
                layout,
                assumptions,
            },
            PrintOptions::default(),
        )
    };
    assert!(p(&invalid, &domains, &assumptions).is_err());
    let mut invalid = layout.clone();
    invalid.files[1].path = invalid.files[0].path.clone();
    assert!(p(&invalid, &domains, &assumptions).is_err());
    let mut invalid = layout.clone();
    invalid.files[1].path = "../escape.den".into();
    assert!(p(&invalid, &domains, &assumptions).is_err());
    let mut invalid = domains.clone();
    invalid.clear();
    assert!(p(&layout, &invalid, &assumptions).is_err());
    let mut invalid = assumptions.clone();
    invalid[0].constraint.group_by = vec![99];
    assert!(p(&layout, &domains, &invalid).is_err());
}
#[test]
fn hash_vectors_and_every_character_boundary_round_trip() {
    assert_eq!(
        content_hash(""),
        "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    assert_eq!(
        content_hash("abc"),
        "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    for text in ["", "\u{feff}é😀e\u{301}\r\nend\n", "a\rb", "\n"] {
        for byte in (0..=text.len()).filter(|b| text.is_char_boundary(*b)) {
            assert_eq!(
                byte_offset(text, coordinate(text, byte).unwrap()),
                Some(byte)
            );
        }
    }
    assert_ne!(content_hash("é"), content_hash("e\u{301}"));
    assert_ne!(content_hash("a\r\n"), content_hash("a\n"));
}
fn located(
    suffix: &str,
    table: &str,
    resolver: Option<&mut dyn OriginResolver>,
) -> Result<LoadedProgram> {
    let doc = SourceFile::new(
        "file:///program.den",
        4,
        format!("relation p(); p() {suffix}; {table}"),
    );
    load_with_resolver(
        &ProgramMembership::single("root", [doc.uri.clone()]),
        &[doc],
        resolver,
    )
}
fn source_table() -> String {
    format!(
        "#s = source(\"file:///dsl\", view: \"dsl\", hash: \"{}\");",
        content_hash("abc")
    )
}
#[test]
fn aliases_compact_maps_fused_origins_and_availability() {
    let table = format!(
        "{} #map = loc(#s {{ self: 1:1 to 1:4, head: 1:2 to 1:3 }});",
        source_table()
    );
    let mut resolver = |_: &SourceIdentity| Ok(std::sync::Arc::<str>::from("abc"));
    let compact = located("loc(#map)", &table, Some(&mut resolver)).unwrap();
    let expanded=located("loc(#map)",&format!("{} #map = {{self: loc(#s 1:1 to 1:4), head: loc(fused[#s 1:2 to 1:3, #s 1:2 to 1:3])}};",source_table()),Some(&mut resolver)).unwrap();
    assert_eq!(
        compact.embedded.associations.values().collect::<Vec<_>>(),
        expanded.embedded.associations.values().collect::<Vec<_>>()
    );
    let unavailable = located("loc(#map)", &table, None).unwrap();
    assert_eq!(unavailable.embedded.notices.len(), 1);
    assert_eq!(unavailable.embedded.associations.len(), 2);
    assert_eq!(unavailable.embedded.provenance.entries().count(), 0);
    let mut wrong = |_: &SourceIdentity| Ok(std::sync::Arc::<str>::from("changed"));
    assert_eq!(
        located("loc(#map)", &table, Some(&mut wrong))
            .unwrap()
            .embedded
            .notices[0]
            .reason,
        Unavailable::HashMismatch
    );
}
#[test]
fn invalid_location_graphs_fail_even_when_unused_or_sources_unavailable() {
    for (suffix, extra) in [
        ("loc(#missing)", ""),
        ("", "#a = loc(#b); #b = loc(#a);"),
        ("", "#a = loc(#s);"),
        ("loc(#map)", "#map = {head.0: loc(#s 1:1 to 1:2)};"),
        (
            "",
            "#map = {self: loc(#s 1:1 to 1:2), self: loc(#s 1:1 to 1:2)};",
        ),
        (
            "",
            "#map = loc(#s {self: 1:1 to 1:2}); #bad = loc(fused[#map]);",
        ),
        (
            "",
            "#map = {self: loc(#other)}; #other = loc(#s {self: 1:1 to 1:2});",
        ),
        ("", "#bad = loc(#s 0:1 to 1:1);"),
        ("", "#bad = loc(#s 2:1 to 1:1);"),
    ] {
        assert!(
            located(suffix, &format!("{} {extra}", source_table()), None).is_err(),
            "{suffix} {extra}"
        );
    }
    let mut resolver = |_: &SourceIdentity| Ok(std::sync::Arc::<str>::from("abc"));
    assert!(
        located(
            "",
            &format!("{} #unused = loc(#s 1:1 to 1:99);", source_table()),
            Some(&mut resolver)
        )
        .is_err()
    );
    assert!(located("loc(#s 1:1 to 1:99)", &source_table(), None).is_ok());
    assert!(
        located(
            "",
            "#s = source(\"file:///x\", view: \"dsl\", hash: \"sha256:ABC\");",
            None
        )
        .is_err()
    );
}

#[test]
fn fused_views_and_revisions_share_a_uri_without_merging_with_current_text() {
    let (c, mut sources, mut provenance, domains, layout, assumptions) = fixture();
    // This URI is also the destination. All three historical identities must
    // survive independently of the current .den snapshot and of local revisions.
    let mut origins = Vec::new();
    for (revision, view, text) in [
        (0, "denotate", "old"),
        (1, "dsl", "old"),
        (2, "denotate", "new😀"),
    ] {
        let id = sources
            .add("file:///export/sources/a.den", revision, view, text)
            .unwrap();
        origins.push(Origin::new(
            sources.span(id, text.len()..text.len()).unwrap(),
        ));
    }
    let rule = c.rules().next().unwrap();
    provenance
        .attach(&c, &sources, rule.id, origins.clone())
        .unwrap();
    provenance
        .attach(&c, &sources, rule.head.id(), origins)
        .unwrap();
    let p = ExportProgram {
        corpus: &c,
        sources: &sources,
        provenance: &provenance,
        domains: &domains,
        layout: &layout,
        assumptions: &assumptions,
    };
    let bundle = print(&p, PrintOptions::default()).unwrap();
    assert!(bundle.files["sources/a.den"].contains("loc(fused["));
    assert!(bundle.files["sources/a.den"].contains(" = { "));
    let (membership, documents) = bundle.documents("file:///export");
    let q = load_with_resolver(&membership, &documents, Some(&mut &sources)).unwrap();
    assert!(q.embedded.notices.is_empty());
    support::compare(&p, &q, "file:///export", true);
    assert_eq!(
        q.sources
            .snapshots()
            .filter(|s| s.uri == "file:///export/sources/a.den")
            .count(),
        4
    );
}

#[test]
fn grouped_constants_union_self_and_indexed_origins_and_resolve_once() {
    let text = format!(
        "sort S; const a, b: S loc(#map); {} #map = {{ self: loc(#s 1:1 to 1:2), decl.1: loc(#s 1:2 to 1:4) }};",
        source_table()
    );
    let doc = SourceFile::new("file:///group.den", 1, text);
    let membership = ProgramMembership::single("root", [doc.uri.clone()]);
    let mut calls = 0;
    let mut resolver = |_: &SourceIdentity| {
        calls += 1;
        Ok(std::sync::Arc::<str>::from("abc"))
    };
    let p = load_with_resolver(&membership, &[doc], Some(&mut resolver)).unwrap();
    assert_eq!(calls, 1);
    for c in p.corpus.constants() {
        let spans = p
            .embedded
            .provenance
            .origins(c.id)
            .iter()
            .map(|o| o.span.byte_range())
            .collect::<Vec<_>>();
        assert_eq!(
            spans,
            if c.name == "a" {
                vec![0..1]
            } else {
                vec![0..1, 1..3]
            }
        );
    }
    for table in [
        "#bad = loc(#missing {});",
        "#scalar = loc(#s 1:1 to 1:2); #bad = loc(#scalar {});",
    ] {
        assert!(located("", &format!("{} {table}", source_table()), None).is_err());
    }
    let mut missing = |_: &SourceIdentity| Err(Unavailable::Missing);
    let p = located(
        "loc(#s 1:1 to 1:2)",
        &format!("{} #unused = loc(#s 1:1 to 1:3);", source_table()),
        Some(&mut missing),
    )
    .unwrap();
    assert_eq!(p.embedded.notices.len(), 1);
    assert_eq!(p.embedded.notices[0].reason, Unavailable::Missing);
}

#[test]
fn fresh_arenas_and_source_registration_history_do_not_change_bytes() {
    let export = |noise: bool| {
        let (c, sources, provenance, domains, layout, assumptions) = fixture();
        let mut reordered = Sources::new();
        if noise {
            reordered
                .add("file:///unused", 99, "unused", "irrelevant")
                .unwrap();
        }
        let mut snapshots = BTreeMap::new();
        for s in sources.snapshots() {
            snapshots.insert(
                s.id,
                reordered
                    .add(&s.uri, s.revision + 10, &s.view, s.text.clone())
                    .unwrap(),
            );
        }
        let map_origin = |o: &Origin| {
            Origin::new(
                reordered
                    .span(snapshots[&o.span.snapshot()], o.span.byte_range())
                    .unwrap(),
            )
        };
        let mut remapped = Provenance::new();
        for (id, origins) in provenance.entries() {
            remapped
                .attach(&c, &reordered, id, origins.iter().map(&map_origin))
                .unwrap();
        }
        let assumptions = assumptions
            .into_iter()
            .map(|mut a| {
                a.origins = a.origins.iter().map(&map_origin).collect();
                a
            })
            .collect::<Vec<_>>();
        print(
            &ExportProgram {
                corpus: &c,
                sources: &reordered,
                provenance: &remapped,
                domains: &domains,
                layout: &layout,
                assumptions: &assumptions,
            },
            PrintOptions::default(),
        )
        .unwrap()
    };
    assert_eq!(export(false), export(true));
}

fn readable_export(text: &str) -> String {
    let doc = SourceFile::new("file:///authored.den", 1, text);
    let p = load(
        &ProgramMembership::single("root", [doc.uri.clone()]),
        &[doc],
    )
    .unwrap();
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&p.corpus).into_iter().map(|id| (id, 0)).collect(),
        assumptions: vec![0; p.assumptions.len()],
    };
    let assumptions = p
        .assumptions
        .iter()
        .map(|a| ExportAssumption {
            namespace: a.namespace.clone(),
            name: Some(a.name.name.to_string()),
            constraint: a.constraint.clone(),
            origins: vec![Origin::new(a.location)],
        })
        .collect::<Vec<_>>();
    let export = ExportProgram {
        corpus: &p.corpus,
        domains: &p.domains,
        sources: &p.sources,
        provenance: &p.provenance,
        assumptions: &assumptions,
        layout: &layout,
    };
    let mut plain = String::new();
    for embedded_origins in [false, true] {
        let bundle = print(&export, PrintOptions { embedded_origins }).unwrap();
        let (membership, docs) = bundle.documents("file:///export");
        let q = load_with_resolver(&membership, &docs, Some(&mut &p.sources))
            .unwrap_or_else(|e| panic!("{e:?}\n{}", bundle.files["program.den"]));
        support::compare(&export, &q, "file:///export", embedded_origins);
        if !embedded_origins {
            plain = bundle.files["program.den"].clone();
        }
    }
    plain
}

#[test]
fn readable_names_keep_syntactic_kinds_and_exact_spelling() {
    let text = readable_export(
        r#"
        sort S;
        const i, a, '007', 'module', 'I', 'é', 'a-b', 'quote\'x', 0, -1, '-0': S;
        input present(input: S);
        relation mapped_to(input: S, slot: S);
        relation supplies(input: S, slot: S);
        relation masked(slot: S);
        relation '$condition_1'();
        relation $condition_1();
        mapped_to(i, a);
        supplies(I, D) :- mapped_to(I, D), present(I), !masked(D);
        mapped_to(?'lower', ?'variable name') :- mapped_to(?'lower', ?'variable name');
        masked('I'); masked('007'); masked('module');
        '$condition_1'() :- $condition_1();
        assumption unique: at_most_one(present, group_by: (input));
    "#,
    );
    for expected in [
        "sort S;",
        "const 0: S;",
        "const -1: S;",
        "const '-0': S;",
        "const '007': S;",
        "const 'module': S;",
        "const 'I': S;",
        "input present(input: S);",
        "mapped_to(i, a);",
        "supplies(I, D) :- mapped_to(I, D), present(I), !masked(D);",
        "mapped_to(?'lower', ?'variable name') :- mapped_to(?'lower', ?'variable name');",
        "masked('I');",
        "'$condition_1'() :- $condition_1();",
        "assumption unique: at_most_one(present, group_by: (input));",
    ] {
        assert!(text.contains(expected), "missing {expected}\n{text}");
    }
    assert!(!text.contains("::"), "{text}");
}

#[test]
fn qualification_uses_enclosing_scopes_expected_sorts_and_emitted_helper_names() {
    let text = readable_export(
        r#"
        sort S; const item: S; relation p(x: S); relation $condition_8();
        namespace a {
            sort S;
            const item: ::S;
            const item: a::S;
            relation p(x: ::S);
            relation typed(x: a::S);
            relation inherited(x: ::S);
            relation $condition_9();
        }
        namespace a::inner {
            ::p(::item);
            a::p(a::item);
            a::typed(item);
            inherited(::item);
            a::$condition_9() :- ::$condition_8();
        }
        namespace sibling { a::p(item); }
        namespace 'module'::'a::b' { relation r(); r(); }
    "#,
    );
    for expected in [
        "const item: ::S;",
        "const item: a::S;",
        "relation p(x: ::S);",
        "relation typed(x: a::S);",
        "::p(::item);",
        "a::p(a::item);",
        "typed(item);",
        "inherited(::item);",
        "$condition_9() :- $condition_8();",
        "a::p(item);",
        "namespace 'module'::'a::b' {\n  relation r();\n}",
        "namespace 'module'::'a::b' {\n  r();\n}",
    ] {
        assert!(text.contains(expected), "missing {expected}\n{text}");
    }
}

#[test]
fn consecutive_namespace_lines_share_blocks_without_reordering_rules() {
    let text = readable_export(
        r#"
        namespace a { relation p(); relation q(); }
        namespace b { relation r(); relation s(); }
        relation global();
        namespace a { p(); q(); }
        namespace b { r(); s(); }
        global();
        namespace a { p(); q(); }
    "#,
    );
    assert_eq!(
        text,
        "namespace a {\n  relation p();\n  relation q();\n}\nnamespace b {\n  relation r();\n  relation s();\n}\nrelation global();\nnamespace a {\n  p();\n  q();\n}\nnamespace b {\n  r();\n  s();\n}\nglobal();\nnamespace a {\n  p();\n  q();\n}\n"
    );
    let scoped = readable_export("namespace a::b; relation p(); relation q(); p(); q();");
    assert_eq!(
        scoped,
        "namespace a::b;\n\nrelation p();\nrelation q();\np();\nq();\n"
    );
}

#[test]
fn helper_labels_survive_except_collisions_and_unspellable_names() {
    let mut c = Corpus::new();
    c.declare_relation("$condition_3", RelationRole::Derived, [])
        .unwrap();
    let labels = [
        "not legal",
        "$keep",
        "$keep",
        "$condition_1",
        "$condition_2",
        "$2bad",
        "$under_score",
        "$",
        "$é",
    ];
    let helpers = labels.map(|name| c.declare_generated_relation_named(name).unwrap());
    c.declare_relation("$keep", RelationRole::Derived, [])
        .unwrap();
    for (index, helper) in helpers.iter().enumerate() {
        let head = c.atom(*helper, []).unwrap();
        let body = c.atom(helpers[(index + 1) % helpers.len()], []).unwrap();
        c.add_rule(head, [Literal::Positive(body)]).unwrap();
    }
    let b = Namespace::new(["b"]).unwrap();
    let other = c.declare_generated_relation_named_in(&b, "$keep").unwrap();
    let head = c.atom(other, []).unwrap();
    let body = c.atom(helpers[1], []).unwrap();
    c.add_rule_in(&b, head, [Literal::Positive(body)]).unwrap();
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&c).into_iter().map(|id| (id, 0)).collect(),
        assumptions: vec![],
    };
    let sources = Sources::new();
    let provenance = Provenance::new();
    let domains = BTreeMap::new();
    let program = ExportProgram {
        corpus: &c,
        domains: &domains,
        sources: &sources,
        provenance: &provenance,
        assumptions: &[],
        layout: &layout,
    };
    let bundle = print(&program, PrintOptions::default()).unwrap();
    let text = &bundle.files["program.den"];
    let actual = text
        .lines()
        .filter(|line| line.starts_with("relation $"))
        .collect::<Vec<_>>();
    assert_eq!(
        actual,
        [
            "relation $condition_3();",
            "relation $keep();",
            "relation $condition_4();",
            "relation $condition_1();",
            "relation $condition_2();",
            "relation $condition_5();",
            "relation $under_score();",
            "relation $condition_6();",
            "relation $condition_7();"
        ]
    );
    assert!(text.contains("relation '$condition_3'();"));
    assert!(text.contains("relation '$keep'();"));
    assert!(text.contains("b::$keep() :- ::$keep();"));
    let (membership, documents) = bundle.documents("file:///export");
    let loaded = load(&membership, &documents).unwrap();
    support::compare(&program, &loaded, "file:///export", true);
}

#[test]
fn compact_and_expanded_maps_follow_occurrence_order_with_numeric_indices() {
    let parameters = (0..12)
        .map(|i| format!("x{i}: S"))
        .collect::<Vec<_>>()
        .join(", ");
    let terms = (0..12)
        .map(|i| format!("X{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let body = vec![format!("p({terms})"); 12].join(", ");
    let doc = SourceFile::new(
        "file:///original.den",
        1,
        format!("sort S; relation p({parameters}); p({terms}) :- {body};"),
    );
    let mut p = load(
        &ProgramMembership::single("root", [doc.uri.clone()]),
        &[doc],
    )
    .unwrap();
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&p.corpus).into_iter().map(|id| (id, 0)).collect(),
        assumptions: vec![],
    };
    let expected = std::iter::once("self".to_owned())
        .chain(std::iter::once("head".to_owned()))
        .chain((0..12).map(|i| format!("head.{i}")))
        .chain((0..12).flat_map(|i| {
            std::iter::once(format!("body.{i}"))
                .chain((0..12).map(move |j| format!("body.{i}.{j}")))
        }))
        .collect::<Vec<_>>();
    for expanded in [false, true] {
        if expanded {
            let snapshot = p.sources.add("file:///other.dsl", 1, "dsl", "x").unwrap();
            let origin = Origin::new(p.sources.span(snapshot, 0..1).unwrap());
            p.provenance
                .attach(
                    &p.corpus,
                    &p.sources,
                    p.corpus.rules().next().unwrap().id,
                    [origin],
                )
                .unwrap();
        }
        let program = ExportProgram {
            corpus: &p.corpus,
            domains: &p.domains,
            sources: &p.sources,
            provenance: &p.provenance,
            assumptions: &[],
            layout: &layout,
        };
        let bundle = print(&program, PrintOptions::default()).unwrap();
        let text = &bundle.files["program.den"];
        let map = text
            .lines()
            .find(|line| line.starts_with("#origin0 ="))
            .unwrap();
        assert_eq!(map.starts_with("#origin0 = {"), expanded);
        let tree = parser().parse(text, None).unwrap();
        fn positions(node: tree_sitter::Node<'_>, text: &str, result: &mut Vec<String>) {
            if node.kind() == "occurrence_position" {
                result.push(text[node.byte_range()].into());
            }
            for child in node.named_children(&mut node.walk()) {
                positions(child, text, result);
            }
        }
        let mut actual = Vec::new();
        positions(tree.root_node(), text, &mut actual);
        assert_eq!(actual, expected);
        let (membership, documents) = bundle.documents("file:///export");
        let loaded = load_with_resolver(&membership, &documents, Some(&mut &p.sources)).unwrap();
        support::compare(&program, &loaded, "file:///export", true);
    }
}

#[test]
fn ir_assumptions_are_refused_rather_than_dropped() {
    assert_ir_contract_export_refused(|c, value| {
        c.assume_at_most_one_in(Namespace::default(), "one_value", value, [])
            .unwrap();
    });
}

#[test]
fn ir_verifications_are_refused_rather_than_dropped() {
    assert_ir_contract_export_refused(|c, _| {
        c.verification_in(Namespace::default(), "normal", [], [])
            .unwrap();
    });
}

fn assert_ir_contract_export_refused(add_contract: impl FnOnce(&mut Corpus, RelationId)) {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let value = c
        .declare_relation("value", RelationRole::Input, [Parameter::new("v", s)])
        .unwrap();
    add_contract(&mut c, value);
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&c).into_iter().map(|id| (id, 0)).collect(),
        assumptions: vec![],
    };
    let (sources, provenance, domains) = (
        Sources::new(),
        Provenance::new(),
        BTreeMap::from([(s, vec![])]),
    );
    let program = ExportProgram {
        corpus: &c,
        domains: &domains,
        sources: &sources,
        provenance: &provenance,
        assumptions: &[],
        layout: &layout,
    };
    let error = print(&program, PrintOptions::default()).unwrap_err();
    assert!(error.0.contains("not supported yet"), "{error}");
}
