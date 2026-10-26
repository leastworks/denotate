mod support;
use serde_json::{json, Value};
use support::{apply_edits, Client};

fn position(source: &str, needle: &str, offset: usize) -> Value {
    let prefix = &source[..source.find(needle).unwrap() + offset];
    json!({"line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()})
}

fn references(client: &mut Client, uri: &str, position: Value) -> Vec<Value> {
    let result = client.request(
        "textDocument/references",
        json!({
            "textDocument": {"uri": uri}, "position": position,
            "context": {"includeDeclaration": true}
        }),
    );
    let mut positions: Vec<_> = result
        .as_array()
        .unwrap()
        .iter()
        .map(|location| {
            assert_eq!(location["uri"], uri);
            location["range"]["start"].clone()
        })
        .collect();
    positions.sort_by_key(|p| {
        (
            p["line"].as_u64().unwrap(),
            p["character"].as_u64().unwrap(),
        )
    });
    positions
}

#[test]
fn signature_edit_rebinds_reference_membership_and_applied_rename() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let (library_uri, _) = client.open("computation.den");
    let library = "module computation;\nsort Source; sort Slot;\nrelation mapped_to(source: Source, slot: Slot);\n";
    let source = "module example;\nuse computation;\nconst shared: Source;\nconst shared: Slot;\nmapped_to(shared, shared);\n";
    client.change(&library_uri, 2, library);
    client.change(&uri, 2, source);
    let source_decl = position(source, "const shared: Source", 6);
    let slot_decl = position(source, "const shared: Slot", 6);
    let first = position(source, "mapped_to(shared, shared)", 10);
    let second = position(source, "mapped_to(shared, shared)", 18);
    let changed = library.replace("source: Source", "source: Slot");

    // Warm both identities, then switch and repair without editing the uses.
    for (version, text, slot_binding) in [
        (2, library, false),
        (3, changed.as_str(), true),
        (4, library, false),
        (5, changed.as_str(), true),
    ] {
        if version > 2 {
            client.change(&library_uri, version, text);
        }
        assert_eq!(client.diagnostics(&uri), json!([]));
        assert_eq!(client.diagnostics(&library_uri), json!([]));
        let expected_source = if slot_binding {
            vec![source_decl.clone()]
        } else {
            vec![source_decl.clone(), first.clone()]
        };
        let expected_slot = if slot_binding {
            vec![slot_decl.clone(), first.clone(), second.clone()]
        } else {
            vec![slot_decl.clone(), second.clone()]
        };
        assert_eq!(
            references(&mut client, &uri, source_decl.clone()),
            expected_source
        );
        assert_eq!(
            references(&mut client, &uri, slot_decl.clone()),
            expected_slot
        );
        assert_eq!(
            references(&mut client, &uri, first.clone()),
            if slot_binding {
                expected_slot
            } else {
                expected_source
            }
        );

        let rename = |position: Value| json!({"textDocument": {"uri": uri}, "position": position, "newName": "renamed"});
        let result = client.request("textDocument/rename", rename(first.clone()));
        assert_eq!(
            result,
            client.request(
                "textDocument/rename",
                rename(if slot_binding {
                    slot_decl.clone()
                } else {
                    source_decl.clone()
                })
            )
        );
        let changes = result["documentChanges"].as_array().unwrap();
        assert_eq!(changes.len(), 1);
        assert_eq!(
            changes[0]["textDocument"],
            json!({"uri": uri, "version": 2})
        );
        let renamed = apply_edits(source, changes[0]["edits"].as_array().unwrap());
        let expected = if slot_binding {
            source
                .replace("const shared: Slot", "const renamed: Slot")
                .replace("mapped_to(shared, shared)", "mapped_to(renamed, renamed)")
        } else {
            source
                .replace("const shared: Source", "const renamed: Source")
                .replace("mapped_to(shared, shared)", "mapped_to(renamed, shared)")
        };
        assert_eq!(
            renamed, expected,
            "rename must follow the current binding, version {version}"
        );
        if version == 5 {
            std::fs::write(client.workspace.path().join("example.den"), &renamed).unwrap();
            client.change(&uri, 3, &renamed);
            assert_eq!(client.diagnostics(&uri), json!([]));
        }
    }
    client.shutdown();
}

#[test]
fn insertion_and_reordering_keep_answers_current_and_report_query_reruns() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    // Distinct variables prevent positional identities from accidentally reusing
    // identical neighbouring rules. One warning tests current diagnostic anchors.
    let rules: Vec<_> = (0..20)
        .map(|i| {
            if i == 7 {
                format!("available(D{i}) :- given(D{i}), present(S{i});\n")
            } else {
                format!("available(D{i}) :- given(D{i});\n")
            }
        })
        .collect();
    let original = format!("module example;\nuse computation;\n{}", rules.concat());
    let inserted = original.replacen(
        "module example;\n",
        "module example;\nconst extra: Slot;\n",
        1,
    );
    let reordered = format!(
        "module example;\nconst extra: Slot;\nuse computation;\n{}",
        rules.iter().rev().cloned().collect::<Vec<_>>().concat()
    );
    let mut previous = None;
    for (version, phase, source) in [
        (2, "warm", original),
        (3, "insert", inserted),
        (4, "reverse", reordered),
    ] {
        client.change(&uri, version, &source);
        for i in 0..20 {
            let result = client.request(
                "textDocument/definition",
                json!({
                    "textDocument": {"uri": uri},
                    "position": position(&source, &format!("given(D{i})"), 6)
                }),
            );
            assert_eq!(result.as_array().unwrap().len(), 1);
            assert_eq!(result[0]["targetUri"], uri);
            assert_eq!(
                result[0]["targetSelectionRange"]["start"],
                position(&source, &format!("available(D{i})"), 10)
            );
        }
        let diagnostics = client.diagnostics(&uri);
        assert_eq!(diagnostics.as_array().unwrap().len(), 1);
        assert_eq!(diagnostics[0]["code"], "singleton-variable");
        assert_eq!(
            diagnostics[0]["range"]["start"],
            position(&source, "present(S7)", 8)
        );
        let stats = client.request("denotate/test/analysis", json!({}));
        let current = stats["ruleQueryExecutions"]
            .as_u64()
            .expect("shared-core rule counter");
        assert!(
            current >= 20,
            "warm all rules before measuring structural edits"
        );
        if let Some(before) = previous {
            let reruns = current.checked_sub(before).expect("cumulative counter");
            // This is a comparison measurement, not a zero-rerun promise.
            println!(
                "DENOTATE_IDENTITY {}",
                json!({"phase": phase, "unchanged_rules": 20,
                "rule_query_executions": reruns, "source_bytes": source.len()})
            );
        }
        previous = Some(current);
    }
    client.shutdown();
}
