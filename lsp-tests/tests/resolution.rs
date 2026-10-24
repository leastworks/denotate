mod support;
use serde_json::{json, Value};
use support::Client;

fn position(source: &str, needle: &str, offset: usize) -> Value {
    let prefix = &source[..source.find(needle).expect(needle) + offset];
    json!({"line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()})
}

fn definition(client: &mut Client, uri: &str, source: &str, needle: &str, offset: usize) -> Value {
    client.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri}, "position": position(source, needle, offset)
        }),
    )
}

fn assert_target(result: &Value, file: &str, expected: Value) {
    let links = result.as_array().expect("definition links");
    assert_eq!(links.len(), 1, "{result}");
    assert!(
        links[0]["targetUri"].as_str().unwrap().ends_with(file),
        "{result}"
    );
    assert_eq!(links[0]["targetSelectionRange"]["start"], expected);
}

fn assert_unresolved(result: &Value) {
    assert!(
        result.is_null() || result.as_array().is_some_and(|a| a.is_empty()),
        "{result}"
    );
}

fn references(client: &mut Client, uri: &str, source: &str, needle: &str, offset: usize) -> Value {
    client.request(
        "textDocument/references",
        json!({
            "textDocument": {"uri": uri}, "position": position(source, needle, offset),
            "context": {"includeDeclaration": true}
        }),
    )
}

#[test]
fn imports_sorts_and_relations_navigate_and_reference_across_files() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let library = std::fs::read_to_string(client.workspace.path().join("computation.den")).unwrap();
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert_target(
        &definition(&mut client, &uri, &source, "use computation", 4),
        "computation.den",
        position(&library, "module computation", 7),
    );
    assert_target(
        &definition(&mut client, &uri, &source, ": Slot", 2),
        "computation.den",
        position(&library, "sort Slot", 5),
    );
    assert_target(
        &definition(&mut client, &uri, &source, "mapped_to(input_a", 0),
        "computation.den",
        position(&library, "relation mapped_to", 9),
    );
    let refs = references(&mut client, &uri, &source, "mapped_to(input_a", 0);
    assert_eq!(
        refs.as_array().unwrap().len(),
        4,
        "declaration, library body, two program heads: {refs}"
    );
    let (lib_uri, lib_source) = client.open("computation.den");
    let from_declaration = references(&mut client, &lib_uri, &lib_source, "relation mapped_to", 9);
    let locations = |value: &Value| -> std::collections::BTreeSet<String> {
        value
            .as_array()
            .unwrap()
            .iter()
            .map(Value::to_string)
            .collect()
    };
    assert_eq!(
        from_declaration.as_array().unwrap().len(),
        refs.as_array().unwrap().len()
    );
    assert_eq!(
        locations(&from_declaration),
        locations(&refs),
        "declaration and use must return the same locations"
    );
    assert_target(
        &definition(&mut client, &lib_uri, &lib_source, "supplies(S, D) :-", 9),
        "computation.den",
        position(&lib_source, "supplies(S, D) :-", 9),
    );
    client.shutdown();
}

#[test]
fn same_spelling_constants_are_resolved_and_referenced_by_sort_identity() {
    let mut client = Client::start("base/10-typed-constants");
    let (uri, source) = client.open("example.den");
    assert_eq!(client.diagnostics(&uri), json!([]));
    for (offset, declaration) in [(10, "const shared: Source"), (18, "const shared: Slot")] {
        assert_target(
            &definition(
                &mut client,
                &uri,
                &source,
                "mapped_to(shared, shared)",
                offset,
            ),
            "example.den",
            position(&source, declaration, 6),
        );
        let refs = references(
            &mut client,
            &uri,
            &source,
            "mapped_to(shared, shared)",
            offset,
        );
        assert_eq!(refs.as_array().unwrap().len(), 2, "{refs}");
        assert!(refs
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r["range"]["start"] == position(&source, declaration, 6)));
    }
    client.shutdown();
}

#[test]
fn ambiguous_imports_never_choose_by_import_order_or_local_shadowing() {
    let mut client = Client::start("base/07-ambiguous-import");
    let (uri, source) = client.open("example.den");
    for (version, text) in [
        source.clone(),
        source.replace("use left;\nuse right;", "use right;\nuse left;"),
        format!("{source}\nrelation masked(slot: Slot);\n"),
    ]
    .iter()
    .enumerate()
    {
        if version > 0 {
            client.change(&uri, (version + 1) as i64, text);
        }
        assert!(client
            .diagnostics(&uri)
            .to_string()
            .contains("Ambiguous name 'masked'"));
        let messages = client.diagnostics(&uri).to_string();
        assert!(
            messages.contains("left") && messages.contains("right"),
            "{messages}"
        );
        assert_unresolved(&definition(&mut client, &uri, text, "masked(a)", 0));
    }
    let repeated = source.replace("use right;", "use left;");
    client.change(&uri, 4, &repeated);
    assert_eq!(client.diagnostics(&uri), json!([]));
    let result = definition(&mut client, &uri, &repeated, "masked(a)", 0);
    assert_eq!(result.as_array().unwrap().len(), 1);
    assert!(result[0]["targetUri"]
        .as_str()
        .unwrap()
        .ends_with("left.den"));
    client.shutdown();
}

#[test]
fn imports_are_direct_and_signatures_keep_their_declaring_sort_identity() {
    let mut client = Client::start("base/12-direct-imports");
    let (uri, source) = client.open("example.den");
    assert_unresolved(&definition(&mut client, &uri, &source, ": Slot", 2));
    assert_unresolved(&definition(&mut client, &uri, &source, "known(a)", 6));
    let result = definition(&mut client, &uri, &source, "known(a)", 0);
    assert!(result[0]["targetUri"]
        .as_str()
        .unwrap()
        .ends_with("library.den"));
    let different_sort = "module example;\nuse library;\nsort Slot;\nconst a: Slot;\nknown(a);\n";
    client.change(&uri, 2, different_sort);
    assert!(client.diagnostics(&uri).to_string().contains(
        if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("tree-sitter") {
            "No constant 'a' of sort types::Slot (found: example::Slot)."
        } else {
            "No constant 'a' of sort types.Slot (found: example.Slot)."
        }
    ));
    assert_unresolved(&definition(
        &mut client,
        &uri,
        different_sort,
        "known(a)",
        6,
    ));
    let repaired = "module example;\nuse library;\nuse types;\nknown(a);\n";
    client.change(&uri, 3, repaired);
    assert_eq!(client.diagnostics(&uri), json!([]));
    let result = definition(&mut client, &uri, repaired, "known(a)", 6);
    assert!(result[0]["targetUri"]
        .as_str()
        .unwrap()
        .ends_with("types.den"));
    client.shutdown();
}

#[test]
fn unknown_imports_module_mismatches_and_duplicate_declarations_are_diagnosed() {
    let mut client = Client::start("base/05-broken-import");
    let (uri, _) = client.open("example.den");
    assert!(!client.diagnostics(&uri).as_array().unwrap().is_empty());
    client.change(&uri, 2, "module wrong;\nsort Slot;\nsort Slot;\n");
    let diagnostics = client.diagnostics(&uri).to_string();
    // B now resolves namespaces independently of filenames; A retains its
    // original module/file contract.
    assert_eq!(
        diagnostics.contains("must match filename"),
        std::env::var("DENOTATE_BACKEND").as_deref() != Ok("tree-sitter"),
        "{diagnostics}"
    );
    assert!(
        diagnostics.contains("Duplicate declaration 'Slot'"),
        "{diagnostics}"
    );
    client.change(&uri, 3, "module example;\nsort Slot;\nconst a: Slot;\nconst a: Slot;\nrelation p(s: Slot);\np(a);\n");
    let diagnostics = client.diagnostics(&uri).to_string();
    assert!(
        diagnostics.contains("Duplicate declaration 'a'"),
        "{diagnostics}"
    );
    assert!(diagnostics.contains("Ambiguous name 'a'"), "{diagnostics}");
    client.shutdown();
}

#[test]
fn intact_library_declarations_still_resolve_with_a_broken_signature() {
    let mut client = Client::start("base/06-broken-library-declaration");
    let (uri, source) = client.open("example.den");
    assert_eq!(
        client.diagnostics(&uri),
        json!([]),
        "broken parameter must not cascade into importer errors"
    );
    let library = std::fs::read_to_string(client.workspace.path().join("computation.den")).unwrap();
    assert_target(
        &definition(&mut client, &uri, &source, "mapped_to(input_a", 0),
        "computation.den",
        position(&library, "relation mapped_to", 9),
    );
    let result = definition(&mut client, &uri, &source, "available(a)", 0);
    assert!(
        result[0]["targetUri"]
            .as_str()
            .unwrap()
            .ends_with("computation.den"),
        "{result}"
    );
    client.shutdown();
}

#[test]
fn cold_broken_library_and_edit_to_same_text_have_identical_editor_results() {
    let broken = std::fs::read_to_string(
        support::root().join("fixtures/base/06-broken-library-declaration/computation.den"),
    )
    .unwrap();
    let mut snapshots = vec![];
    for workspace in ["base/06-broken-library-declaration", "base/00-valid"] {
        let mut client = Client::start(workspace);
        let (lib_uri, library) = client.open("computation.den");
        let (uri, source) = client.open("example.den");
        if workspace == "base/00-valid" {
            client.change(&lib_uri, 2, &broken);
            client.change(&uri, 2, &source);
        }
        let snapshot = json!({
            "libraryDiagnostics":client.diagnostics(&lib_uri),
            "importerDiagnostics":client.diagnostics(&uri),
            "mapped":definition(&mut client, &uri, &source, "mapped_to(input_a", 0),
            "available":definition(&mut client, &uri, &source, "available(a)", 0),
            "hover":hover(&mut client, &uri, &source, "mapped_to(input_a", 0),
            "signature":signature(&mut client, &uri, &source, "mapped_to(input_a, a)", 18)
        });
        let normalized = snapshot
            .to_string()
            .replace(&support::file_uri(client.workspace.path()), "WORKSPACE");
        snapshots.push(normalized);
        if workspace == "base/00-valid" {
            client.change(&lib_uri, 3, &library);
            client.change(&uri, 3, &source);
            assert_eq!(client.diagnostics(&lib_uri), json!([]));
            assert_eq!(client.diagnostics(&uri), json!([]));
            assert!(!signature(&mut client, &uri, &source, "mapped_to(input_a, a)", 18).is_null());
        }
        client.shutdown();
    }
    assert_eq!(snapshots[0], snapshots[1], "no last-good semantic fallback");
}

#[test]
fn damaged_signatures_do_not_invent_arity_or_argument_type_errors() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    let signature = "relation mapped_to(source: Source, slot: Slot);";
    for (index, damaged) in [
        "relation mapped_to(source: Source, slot: );",
        "relation mapped_to(source: Source, : Slot);",
        "relation mapped_to(source: Source, slot);",
        "relation mapped_to(source: Source,);",
        "relation mapped_to(source: Source slot: Slot);",
    ]
    .iter()
    .enumerate()
    {
        let changed = library.replace(signature, damaged);
        client.change(&lib_uri, (index + 2) as i64, &changed);
        // Revalidate the importer explicitly; assertions must use fresh results,
        // not a cached empty set from before the library was damaged.
        client.change(&uri, (index + 2) as i64, &source);
        let lib_errors = client.diagnostics(&lib_uri);
        assert!(
            !lib_errors.as_array().unwrap().is_empty(),
            "{damaged}: missing syntax error"
        );
        assert!(
            !lib_errors.to_string().contains("expects"),
            "{damaged}: {lib_errors}"
        );
        let importer_errors = client.diagnostics(&uri);
        assert!(
            !importer_errors.to_string().contains("expects"),
            "{damaged}: {importer_errors}"
        );
        if index < 4 {
            assert_eq!(importer_errors, json!([]), "{damaged}");
            assert_target(
                &definition(&mut client, &uri, &source, "mapped_to(input_a", 0),
                "computation.den",
                position(&changed, "relation mapped_to", 9),
            );
        }
    }
    // A damaged declaration must not disable checks for an intact neighbour.
    client.change(
        &lib_uri,
        7,
        &library.replace(signature, "relation mapped_to(source: Source,);"),
    );
    client.change(&uri, 7, &format!("{source}\navailable(a, b);\n"));
    assert!(client
        .diagnostics(&uri)
        .to_string()
        .contains("Relation 'available' expects 1 argument, got 2."));
    // Repair restores checking of mapped_to itself.
    client.change(&lib_uri, 8, &library);
    client.change(&uri, 8, &format!("{source}\nmapped_to(input_a);\n"));
    assert!(client
        .diagnostics(&uri)
        .to_string()
        .contains("Relation 'mapped_to' expects 2 arguments, got 1."));
    client.shutdown();
}

#[test]
fn wrong_sort_constant_diagnostics_explain_expected_and_visible_sorts() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    client.change(&uri, 2, &format!("{source}\nmapped_to(a, input_a);\n"));
    let diagnostics = client.diagnostics(&uri);
    for message in [
        "No constant 'a' of sort Source (found: Slot).",
        "No constant 'input_a' of sort Slot (found: Source).",
    ] {
        assert!(
            diagnostics
                .as_array()
                .unwrap()
                .iter()
                .any(|d| d["message"] == message),
            "{diagnostics}"
        );
    }
    client.change(&uri, 3, &format!("{source}\nmapped_to(nonexistent, a);\n"));
    assert!(client
        .diagnostics(&uri)
        .to_string()
        .contains("No constant 'nonexistent' of sort Source (no visible declaration)."));
    client.change(&uri, 4, &source);
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.shutdown();
}

#[test]
fn native_completion_offers_visible_relations_and_typed_constants() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let constants = client.request(
        "textDocument/completion",
        json!({
            "textDocument": {"uri": uri}, "position": position(&source, "mapped_to(input_a, a)", 18)
        }),
    );
    let labels: Vec<_> = constants["items"]
        .as_array()
        .unwrap()
        .iter()
        .map(|i| i["label"].clone())
        .collect();
    assert!(labels.contains(&json!("a")), "{constants}");
    assert!(!labels.contains(&json!("input_a")), "{constants}");
    let extended = format!("{source}\nmapp");
    client.change(&uri, 2, &extended);
    let relations = client.request(
        "textDocument/completion",
        json!({
            "textDocument": {"uri": uri}, "position": position(&extended, "\nmapp", 5)
        }),
    );
    assert!(
        relations["items"]
            .as_array()
            .unwrap()
            .iter()
            .any(|i| i["label"] == "mapped_to"),
        "{relations}"
    );
    for (version, suffix) in [
        (3, "mapped_to(input_b,"),
        (4, "mapped_to(input_b, // comma , in comment\n"),
    ] {
        let text = format!("{source}\n{suffix}");
        client.change(&uri, version, &text);
        let completion = client.request(
            "textDocument/completion",
            json!({
                "textDocument": {"uri": uri}, "position": position(&text, suffix, suffix.len())
            }),
        );
        let labels: Vec<_> = completion["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|i| i["label"].clone())
            .collect();
        for slot in ["a", "b", "result"] {
            assert!(labels.contains(&json!(slot)), "{suffix}: {completion}");
        }
        for other in ["input_a", "input_b", "calculate"] {
            assert!(!labels.contains(&json!(other)), "{suffix}: {completion}");
        }
    }
    client.shutdown();
}

#[test]
fn changing_an_imported_declaration_invalidates_navigation_then_repairs_it() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    client.change(
        &lib_uri,
        2,
        &library.replace("mapped_to", "renamed_mapping"),
    );
    assert_unresolved(&definition(
        &mut client,
        &uri,
        &source,
        "mapped_to(input_a",
        0,
    ));
    client.change(&lib_uri, 3, &library);
    assert_target(
        &definition(&mut client, &uri, &source, "mapped_to(input_a", 0),
        "computation.den",
        position(&library, "relation mapped_to", 9),
    );
    client.shutdown();
}

#[test]
fn wrong_arity_is_reported_in_heads_and_bodies_without_hiding_extra_constants() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    for (index, atom) in [
        "mapped_to(input_a, a, nonexistent)",
        "mapped_to(input_a)",
        "mapped_to(input_a, a, a)",
    ]
    .iter()
    .enumerate()
    {
        let text = format!("{source}\n{atom};\navailable(a) :- {atom}, !{atom};\n");
        client.change(&uri, (index + 2) as i64, &text);
        let diagnostics = client.diagnostics(&uri);
        let expected = format!(
            "expects 2 arguments, got {}",
            if index == 1 { 1 } else { 3 }
        );
        assert_eq!(
            diagnostics
                .as_array()
                .unwrap()
                .iter()
                .filter(|d| d["message"].as_str().unwrap().contains(&expected))
                .count(),
            3,
            "{diagnostics}"
        );
        assert!(
            !diagnostics
                .to_string()
                .contains("Could not resolve reference"),
            "{diagnostics}"
        );
        if index == 2 {
            assert!(diagnostics.to_string().contains("Extra argument 'a' to relation 'mapped_to': no parameter 3 supplies an expected sort for constant lookup."));
        }
        if index == 0 {
            assert_eq!(
                diagnostics
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter(|d| d["message"].as_str().unwrap().contains("nonexistent"))
                    .count(),
                3,
                "{diagnostics}"
            );
        }
    }
    client.change(&uri, 5, &source);
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.shutdown();
}

#[test]
fn watched_unopened_library_create_change_delete_updates_importer() {
    let mut client = Client::start("base/00-valid");
    let registration = client.file_watcher_registration();
    assert!(
        registration["registerOptions"]["watchers"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["globPattern"] == "**/*" || w["globPattern"] == "**/*.den"),
        "{registration}"
    );
    let (uri, _) = client.open("example.den");
    let source = "module example;\nuse computation;\nuse left;\nconst a: Slot;\nextra(a);\n";
    client.change(&uri, 2, source);
    assert!(!client.diagnostics(&uri).as_array().unwrap().is_empty());
    let path = client.workspace.path().join("left.den");
    let library = "module left;\nuse computation;\nrelation extra(slot: Slot);\n";
    // Only disk writes and watched-file notifications; never didOpen(left.den).
    std::fs::write(&path, library).unwrap();
    client.watched_change("left.den", 1, &uri, 2);
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert_target(
        &definition(&mut client, &uri, source, "extra(a)", 0),
        "left.den",
        position(library, "relation extra", 9),
    );
    std::fs::write(&path, library.replace("extra", "other")).unwrap();
    client.watched_change("left.den", 2, &uri, 2);
    assert!(client.diagnostics(&uri).to_string().contains("extra"));
    assert_unresolved(&definition(&mut client, &uri, source, "extra(a)", 0));
    std::fs::remove_file(&path).unwrap();
    client.watched_change("left.den", 3, &uri, 2);
    assert!(client.diagnostics(&uri).to_string().contains("left"));
    assert_unresolved(&definition(&mut client, &uri, source, "use left", 4));
    std::fs::write(&path, library).unwrap();
    client.watched_change("left.den", 1, &uri, 2);
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.shutdown();
}

#[test]
fn watched_creation_introduces_ambiguity_module_edits_break_imports_and_deletion_clears_errors() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let source = "module example;\nuse computation;\nuse left;\nuse right;\nconst a: Slot;\nmasked_extra(a);\n";
    client.change(&uri, 2, source);
    let left = "module left;\nuse computation;\nrelation masked_extra(slot: Slot);\n";
    std::fs::write(client.workspace.path().join("left.den"), left).unwrap();
    client.watched_change("left.den", 1, &uri, 2);
    assert_target(
        &definition(&mut client, &uri, source, "masked_extra(a)", 0),
        "left.den",
        position(left, "relation masked_extra", 9),
    );
    let right_path = client.workspace.path().join("right.den");
    let right_uri = support::file_uri(&right_path);
    let right = left.replace("module left;", "module right;");
    std::fs::write(&right_path, &right).unwrap();
    client.watched_change("right.den", 1, &uri, 2);
    let diagnostics = client.diagnostics(&uri).to_string();
    assert!(
        diagnostics.contains("Ambiguous name 'masked_extra'")
            && diagnostics.contains("(left, right)"),
        "{diagnostics}"
    );
    assert_unresolved(&definition(&mut client, &uri, source, "masked_extra(a)", 0));

    // Filename stays right.den, but its module declaration stops matching.
    std::fs::write(&right_path, right.replace("module right;", "module wrong;")).unwrap();
    client.watched_change("right.den", 2, &uri, 2);
    assert_unresolved(&definition(&mut client, &uri, source, "use right", 4));
    assert!(client.diagnostics(&uri).to_string().contains("right"));
    assert_eq!(
        client
            .diagnostics(&right_uri)
            .to_string()
            .contains("must match filename"),
        std::env::var("DENOTATE_BACKEND").as_deref() != Ok("tree-sitter")
    );
    assert_target(
        &definition(&mut client, &uri, source, "masked_extra(a)", 0),
        "left.den",
        position(left, "relation masked_extra", 9),
    );

    // A real error was published for the unopened file; deletion must clear it.
    std::fs::remove_file(&right_path).unwrap();
    client.watched_change("right.den", 3, &uri, 2);
    assert_eq!(client.diagnostics(&right_uri), json!([]));
    assert_unresolved(&definition(&mut client, &uri, source, "use right", 4));
    assert!(client.diagnostics(&uri).to_string().contains("right"));
    client.shutdown();
}

fn hover(client: &mut Client, uri: &str, source: &str, needle: &str, offset: usize) -> Value {
    client.request(
        "textDocument/hover",
        json!({
            "textDocument": {"uri": uri}, "position": position(source, needle, offset)
        }),
    )
}

fn signature(client: &mut Client, uri: &str, source: &str, needle: &str, offset: usize) -> Value {
    client.request(
        "textDocument/signatureHelp",
        json!({
            "textDocument": {"uri": uri}, "position": position(source, needle, offset)
        }),
    )
}

#[test]
fn variable_identity_is_rule_local_and_uses_first_occurrence_as_navigation_target() {
    let mut client = Client::start("base/16-variable-binding");
    let (uri, source) = client.open("example.den");
    for (rule, first_offset, body_offset) in [
        (
            "given(D) :- supplies(S, D);",
            "given(".len(),
            "given(D) :- supplies(S, ".len(),
        ),
        (
            "available(D) :- given(D);",
            "available(".len(),
            "available(D) :- given(".len(),
        ),
    ] {
        assert_target(
            &definition(&mut client, &uri, &source, rule, body_offset),
            "example.den",
            position(&source, rule, first_offset),
        );
        let from_first = references(&mut client, &uri, &source, rule, first_offset);
        let from_body = references(&mut client, &uri, &source, rule, body_offset);
        assert_eq!(from_first, from_body);
        assert_eq!(from_first.as_array().unwrap().len(), 2, "{from_first}");
        for occurrence in from_first.as_array().unwrap() {
            assert_eq!(
                occurrence["range"]["start"]["line"],
                position(&source, rule, first_offset)["line"]
            );
        }
        let without_first = client.request(
            "textDocument/references",
            json!({
                "textDocument": {"uri": uri}, "position": position(&source, rule, body_offset),
                "context": {"includeDeclaration": false}
            }),
        );
        assert_eq!(without_first.as_array().unwrap().len(), 1);
        assert_eq!(
            without_first[0]["range"]["start"],
            position(&source, rule, body_offset)
        );
        assert_eq!(
            hover(&mut client, &uri, &source, rule, body_offset)["contents"]["value"],
            "variable D: Slot"
        );
    }
    // Renaming a variable spelling through an edit cannot retain an old identity.
    let changed = source.replace("given(D) :- supplies(S, D);", "given(D) :- supplies(S, E);");
    client.change(&uri, 2, &changed);
    let rule = "given(D) :- supplies(S, E);";
    let at_e = "given(D) :- supplies(S, ".len();
    assert_target(
        &definition(&mut client, &uri, &changed, rule, at_e),
        "example.den",
        position(&changed, rule, at_e),
    );
    assert_eq!(
        references(&mut client, &uri, &changed, rule, at_e)
            .as_array()
            .unwrap()
            .len(),
        1
    );
    let conflicting = "module example;\nuse computation;\ngiven(D) :- supplies(D, D);\n";
    client.change(&uri, 3, conflicting);
    let conflict = hover(&mut client, &uri, conflicting, "given(D)", 6);
    assert!(
        conflict["contents"]["value"]
            .as_str()
            .unwrap()
            .contains("Conflicting expected sorts: computation.Slot, computation.Source"),
        "{conflict}"
    );
    client.shutdown();
}

#[test]
fn anonymous_hover_reports_argument_sort_without_navigation_or_shared_references() {
    let mut client = Client::start("base/16-variable-binding");
    let (uri, source) = client.open("example.den");
    for (needle, offset, sort) in [
        ("supplies(_, D)", "supplies(".len(), "Source"),
        ("mapped_to(_, _)", "mapped_to(".len(), "Source"),
        ("mapped_to(_, _)", "mapped_to(_, ".len(), "Slot"),
    ] {
        let result = hover(&mut client, &uri, &source, needle, offset);
        assert!(
            result["contents"]["value"]
                .as_str()
                .unwrap()
                .starts_with(&format!("_: {sort}")),
            "{result}"
        );
        assert_eq!(result["range"]["start"], position(&source, needle, offset));
        assert_unresolved(&definition(&mut client, &uri, &source, needle, offset));
        assert_eq!(
            references(&mut client, &uri, &source, needle, offset),
            json!([])
        );
    }
    client.shutdown();
}

#[test]
fn declaration_and_typed_constant_hovers_show_the_resolved_signature_or_sort() {
    let mut client = Client::start("base/10-typed-constants");
    let (uri, source) = client.open("example.den");
    for (needle, offset, expected) in [
        (
            "mapped_to(shared, shared)",
            0,
            "relation mapped_to(source: Source, slot: Slot)",
        ),
        ("mapped_to(shared, shared)", 10, "const shared: Source"),
        ("mapped_to(shared, shared)", 18, "const shared: Slot"),
        (
            "use computation",
            4,
            if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("tree-sitter") {
                "namespace computation"
            } else {
                "module computation"
            },
        ),
        (": Slot", 2, "sort Slot"),
    ] {
        assert_eq!(
            hover(&mut client, &uri, &source, needle, offset)["contents"]["value"],
            expected
        );
    }
    let (lib_uri, library) = client.open("computation.den");
    assert_eq!(
        hover(&mut client, &lib_uri, &library, "relation mapped_to", 9)["contents"]["value"],
        "relation mapped_to(source: Source, slot: Slot)"
    );
    client.shutdown();
}

#[test]
fn constant_hover_qualifies_same_named_sorts_in_the_callers_scope() {
    let mut client = Client::start("base/07-ambiguous-import");
    let (left_uri, _) = client.open("left.den");
    let (right_uri, _) = client.open("right.den");
    client.change(
        &left_uri,
        2,
        "module left; sort Slot; const shared: Slot; relation from_left(value: Slot);",
    );
    client.change(
        &right_uri,
        2,
        "module right; sort Slot; const shared: Slot; relation from_right(value: Slot);",
    );
    let (uri, _) = client.open("example.den");
    let source = "module example; use left; use right; from_left(shared); from_right(shared);";
    client.change(&uri, 2, source);
    assert_eq!(client.diagnostics(&uri), json!([]));
    for (needle, offset, expected) in [
        ("from_left(shared)", 10, "const shared: left.Slot"),
        ("from_right(shared)", 11, "const shared: right.Slot"),
    ] {
        assert_eq!(
            hover(&mut client, &uri, source, needle, offset)["contents"]["value"],
            expected
        );
    }
    client.shutdown();
}

#[test]
fn signature_help_tracks_arguments_in_complete_and_unfinished_calls() {
    let mut client = Client::start("base/00-valid");
    assert_eq!(
        client.capabilities["signatureHelpProvider"]["triggerCharacters"],
        json!(["(", ","])
    );
    let (uri, source) = client.open("example.den");
    let complete = signature(&mut client, &uri, &source, "mapped_to(input_a, a)", 18);
    assert_eq!(complete["activeParameter"], 1);
    for (index, (suffix, parameter)) in [
        ("mapped_to(", json!(0)),
        ("mapped_to(input_b,", json!(1)),
        ("mapped_to(input_b, // ignored comma ,\n", json!(1)),
        ("mapped_to(input_b, b, ", Value::Null),
    ]
    .iter()
    .enumerate()
    {
        let text = format!("{source}\n{suffix}");
        client.change(&uri, (index + 2) as i64, &text);
        let result = signature(&mut client, &uri, &text, suffix, suffix.len());
        assert_eq!(
            result["signatures"][0]["label"], "mapped_to(source: Source, slot: Slot)",
            "{suffix}: {result}"
        );
        assert_eq!(
            result.get("activeParameter"),
            Some(parameter),
            "{suffix}: {result}"
        );
        assert_eq!(
            result["signatures"][0]["parameters"],
            json!([{"label":"source: Source"}, {"label":"slot: Slot"}])
        );
    }
    client.change(&uri, 6, &source);
    assert!(signature(
        &mut client,
        &uri,
        &source,
        "mapped_to(input_a, a)",
        "mapped_to(input_a, a)".len()
    )
    .is_null());
    let missing = format!("{source}\nmissing(");
    client.change(&uri, 7, &missing);
    assert!(signature(&mut client, &uri, &missing, "missing(", 8).is_null());
    client.shutdown();
}

#[test]
fn damaged_signatures_and_ambiguous_relations_do_not_invent_hover_types_or_signature_help() {
    let mut client = Client::start("base/06-broken-library-declaration");
    let (uri, source) = client.open("example.den");
    assert!(
        hover(&mut client, &uri, &source, "mapped_to(input_a", 0)["contents"]["value"]
            .as_str()
            .unwrap()
            .contains("damaged")
    );
    assert!(signature(&mut client, &uri, &source, "mapped_to(input_a, a)", 18).is_null());
    let (lib_uri, library) = client.open("computation.den");
    let partial = library.replace(
        "relation supplies(source: Source, slot: Slot);",
        "relation supplies(source: Source,);",
    );
    client.change(&lib_uri, 2, &partial);
    assert!(
        hover(&mut client, &lib_uri, &partial, "supplies(_, D)", 9)["contents"]["value"]
            .as_str()
            .unwrap()
            .contains("unknown sort")
    );
    client.shutdown();

    let mut client = Client::start("base/07-ambiguous-import");
    let (uri, source) = client.open("example.den");
    assert!(hover(&mut client, &uri, &source, "masked(a)", 0).is_null());
    assert!(signature(&mut client, &uri, &source, "masked(a)", 7).is_null());
    client.shutdown();
}
