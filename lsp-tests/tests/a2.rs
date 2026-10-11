mod support;
use serde_json::{json, Value};
use support::Client;

fn stats(client: &mut Client) -> Value {
    client.request("denotate/test/analysis", json!({}))
}

fn definition(client: &mut Client, uri: &str, source: &str) -> Value {
    let prefix = &source[..source.find("mapped_to(input_a").unwrap()];
    client.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri}, "position": {
                "line": prefix.bytes().filter(|b| *b == b'\n').count(),
                "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()
            }
        }),
    )
}

#[test]
fn native_relation_queries_reuse_semantics_and_refresh_source_ranges() {
    // A1 still runs the frozen suite, but has no native-counter contract.
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    let target = definition(&mut client, &uri, &source);
    assert_eq!(target.as_array().unwrap().len(), 1);
    let before = stats(&mut client);
    assert_eq!(before["backend"], "rust");
    assert!(before["relationQueryExecutions"].as_u64().unwrap() > 0);
    assert_eq!(definition(&mut client, &uri, &source), target);
    assert_eq!(
        stats(&mut client)["relationQueryExecutions"],
        before["relationQueryExecutions"]
    );

    client.change(&lib_uri, 2, &format!("// New comment 🦀\n{library}"));
    let moved = definition(&mut client, &uri, &source);
    assert_eq!(moved[0]["targetUri"], target[0]["targetUri"]);
    assert_eq!(
        moved[0]["targetSelectionRange"]["start"]["line"]
            .as_u64()
            .unwrap(),
        target[0]["targetSelectionRange"]["start"]["line"]
            .as_u64()
            .unwrap()
            + 1
    );
    let after = stats(&mut client);
    assert!(after["projections"].as_u64().unwrap() > before["projections"].as_u64().unwrap());
    assert_eq!(
        after["relationQueryExecutions"], before["relationQueryExecutions"],
        "trivia changes spans, not Salsa semantic inputs"
    );

    // A rule-body edit also leaves relation declarations/imports unchanged.
    client.change(
        &lib_uri,
        3,
        &library.replace("supplies(_, D)", "supplies(S, D)"),
    );
    definition(&mut client, &uri, &source);
    assert_eq!(
        stats(&mut client)["relationQueryExecutions"],
        before["relationQueryExecutions"]
    );

    // Semantic change must invalidate, not preserve a last-good target.
    client.change(&lib_uri, 4, &library.replace("mapped_to", "mapping"));
    let absent = definition(&mut client, &uri, &source);
    assert!(absent.is_null() || absent.as_array().is_some_and(|items| items.is_empty()));
    assert!(
        stats(&mut client)["relationQueryExecutions"]
            .as_u64()
            .unwrap()
            > before["relationQueryExecutions"].as_u64().unwrap()
    );
    client.change(&lib_uri, 5, &library);
    assert_eq!(definition(&mut client, &uri, &source), target);
    client.shutdown();
}

#[test]
fn signature_edits_refresh_editor_help_without_invalidating_relation_visibility() {
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    let before = stats(&mut client);
    let prefix = &source[..source.find("mapped_to(input_a").unwrap()];
    let position = json!({
        "line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count() + 18
    });
    for (index, (text, expected)) in [
        (
            library.replace("relation mapped_to", "input mapped_to"),
            Some("mapped_to(source: Source, slot: Slot)"),
        ),
        (
            library.replace("source: Source, slot: Slot", "source: Source, slot: Source"),
            Some("mapped_to(source: Source, slot: Source)"),
        ),
        (
            library.replace("source: Source, slot: Slot", "source: Source, slot: "),
            None,
        ),
        (
            library.clone(),
            Some("mapped_to(source: Source, slot: Slot)"),
        ),
    ]
    .iter()
    .enumerate()
    {
        assert!(
            *text != library || index == 3,
            "edit must change the declaration"
        );
        client.change(&lib_uri, (index + 2) as i64, text);
        assert_eq!(
            definition(&mut client, &uri, &source)
                .as_array()
                .unwrap()
                .len(),
            1
        );
        let help = client.request(
            "textDocument/signatureHelp",
            json!({
                "textDocument": {"uri": uri}, "position": position
            }),
        );
        match expected {
            Some(label) => assert_eq!(help["signatures"][0]["label"], *label),
            None => assert!(
                help.is_null()
                    || help["signatures"]
                        .as_array()
                        .is_some_and(|items| items.is_empty())
            ),
        }
        assert_eq!(
            stats(&mut client)["relationQueryExecutions"],
            before["relationQueryExecutions"],
            "signature and kind are not inputs to relation visibility"
        );
    }
    assert!(
        stats(&mut client)["projections"].as_u64().unwrap()
            > before["projections"].as_u64().unwrap()
    );
    client.shutdown();
}

fn position(source: &str, needle: &str, offset: usize) -> Value {
    let prefix = &source[..source.find(needle).unwrap() + offset];
    json!({"line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()})
}

fn typed_definition(client: &mut Client, uri: &str, source: &str) -> Value {
    client.request(
        "textDocument/definition",
        json!({"textDocument": {"uri": uri},
        "position": position(source, "mapped_to(shared, shared)", 10)}),
    )
}

fn typed_completions(client: &mut Client, uri: &str, source: &str) -> Vec<String> {
    let result = client.request(
        "textDocument/completion",
        json!({"textDocument": {"uri": uri},
        "position": position(source, "mapped_to(shared, shared)", 10)}),
    );
    result
        .as_array()
        .or_else(|| result["items"].as_array())
        .unwrap()
        .iter()
        .map(|item| item["label"].as_str().unwrap().to_owned())
        .collect()
}

#[test]
fn parameter_sort_changes_constant_targets_and_completion_but_not_visibility() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let source = "module example;\nuse computation;\nconst shared, source_only: Source;\nconst shared, slot_only: Slot;\nmapped_to(shared, shared);\n";
    client.change(&uri, 2, source);
    let (lib_uri, library) = client.open("computation.den");
    let target = typed_definition(&mut client, &uri, source);
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(source, "const shared, source_only", 6)
    );
    let offered = typed_completions(&mut client, &uri, source);
    assert!(offered.contains(&"source_only".into()) && !offered.contains(&"slot_only".into()));
    let before = stats(&mut client);
    let native = before["backend"] == "rust";
    if native {
        for key in [
            "sortQueryExecutions",
            "expectedSortQueryExecutions",
            "constantQueryExecutions",
        ] {
            assert!(
                before[key].as_u64().unwrap() > 0,
                "{key} must be Rust-owned"
            );
        }
    }

    let moved_source = format!("// Comment 🦀\n{source}");
    client.change(&uri, 3, &moved_source);
    let moved = typed_definition(&mut client, &uri, &moved_source);
    assert_eq!(
        moved[0]["targetSelectionRange"]["start"],
        position(&moved_source, "const shared, source_only", 6)
    );
    typed_completions(&mut client, &uri, &moved_source);
    if native {
        let after = stats(&mut client);
        for key in [
            "relationQueryExecutions",
            "sortQueryExecutions",
            "expectedSortQueryExecutions",
            "constantQueryExecutions",
        ] {
            assert_eq!(after[key], before[key], "comment must reuse {key}");
        }
    }

    let changed = library.replace(
        "mapped_to(source: Source, slot: Slot)",
        "mapped_to(source: Slot, slot: Slot)",
    );
    assert_ne!(changed, library);
    client.change(&lib_uri, 2, &changed);
    let changed_target = typed_definition(&mut client, &uri, &moved_source);
    assert_eq!(
        changed_target[0]["targetSelectionRange"]["start"],
        position(&moved_source, "const shared, slot_only", 6)
    );
    let offered = typed_completions(&mut client, &uri, &moved_source);
    assert!(offered.contains(&"slot_only".into()) && !offered.contains(&"source_only".into()));
    if native {
        let after = stats(&mut client);
        assert_eq!(
            after["relationQueryExecutions"],
            before["relationQueryExecutions"]
        );
        assert_eq!(after["sortQueryExecutions"], before["sortQueryExecutions"]);
        for key in ["expectedSortQueryExecutions", "constantQueryExecutions"] {
            assert!(
                after[key].as_u64().unwrap() > before[key].as_u64().unwrap(),
                "{key} must invalidate"
            );
        }
    }
    client.change(&lib_uri, 3, &library);
    assert_eq!(typed_definition(&mut client, &uri, &moved_source), moved);
    assert!(typed_completions(&mut client, &uri, &moved_source).contains(&"source_only".into()));
    client.shutdown();
}

#[test]
fn argument_diagnostics_and_sort_labels_are_native_cached_and_follow_signature_edits() {
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    let source = "module example;\nuse computation;\nconst a: Slot;\nmapped_to(a);\n";
    client.change(&uri, 2, source);
    let initial = client.diagnostics(&uri);
    assert_eq!(
        initial.as_array().unwrap().len(),
        2,
        "one arity and one wrong-sort error, not duplicate ownership"
    );
    assert!(initial
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d["code"] == "arity"));
    assert!(initial
        .to_string()
        .contains("No constant 'a' of sort Source (found: Slot)."));
    let hover = client.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri}, "position": position(source, "const a:", 6)}),
    );
    assert!(hover.to_string().contains("const a: Slot"));
    let before = stats(&mut client);
    for key in [
        "constantDiagnosticQueryExecutions",
        "sortLabelQueryExecutions",
    ] {
        assert!(
            before[key].as_u64().unwrap() > 0,
            "{key} must be Rust-owned"
        );
    }
    let moved = format!("// comment 🦀\n{source}");
    client.change(&uri, 3, &moved);
    client.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri}, "position": position(&moved, "const a:", 6)}),
    );
    let after = stats(&mut client);
    for key in [
        "constantDiagnosticQueryExecutions",
        "sortLabelQueryExecutions",
        "ruleQueryExecutions",
    ] {
        assert_eq!(after[key], before[key], "comment reuses {key}");
    }
    for diagnostic in client.diagnostics(&uri).as_array().unwrap() {
        let old = initial
            .as_array()
            .unwrap()
            .iter()
            .find(|d| d["message"] == diagnostic["message"])
            .unwrap();
        assert_eq!(
            diagnostic["range"]["start"]["line"].as_u64().unwrap(),
            old["range"]["start"]["line"].as_u64().unwrap() + 1
        );
    }
    client.change(
        &lib_uri,
        2,
        &library.replace(
            "mapped_to(source: Source, slot: Slot)",
            "mapped_to(source: Slot, slot: Slot)",
        ),
    );
    let diagnostics = client.diagnostics(&uri);
    assert_eq!(diagnostics.as_array().unwrap().len(), 1);
    assert_eq!(diagnostics[0]["code"], "arity");
    client.change(
        &lib_uri,
        3,
        &library.replace(
            "mapped_to(source: Source, slot: Slot)",
            "mapped_to(source: Slot)",
        ),
    );
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.change(
        &lib_uri,
        4,
        &library.replace(
            "mapped_to(source: Source, slot: Slot)",
            "mapped_to(source: Source,)",
        ),
    );
    assert_eq!(
        client.diagnostics(&uri),
        json!([]),
        "damaged declaration must not invent argument errors"
    );
    client.change(&lib_uri, 5, &library);
    assert_eq!(client.diagnostics(&uri).as_array().unwrap().len(), 2);
    assert!(
        stats(&mut client)["constantDiagnosticQueryExecutions"]
            .as_u64()
            .unwrap()
            > before["constantDiagnosticQueryExecutions"]
                .as_u64()
                .unwrap()
    );
    client.shutdown();
}
