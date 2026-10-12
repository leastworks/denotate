#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::{apply_edits, Client};

fn position(text: &str, byte: usize) -> Value {
    let mut line = 0;
    let mut column = 0;
    let mut chars = text[..byte].chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '\r' {
            if chars.peek() == Some(&'\n') {
                chars.next();
            }
            line += 1;
            column = 0;
        } else if ch == '\n' {
            line += 1;
            column = 0;
        } else {
            column += ch.len_utf16();
        }
    }
    json!({"line": line, "character": column})
}

fn replacement(text: &str, needle: &str, value: &str) -> Value {
    let start = text.find(needle).unwrap();
    json!({"range": {"start": position(text, start), "end": position(text, start + needle.len())}, "newText": value})
}

fn ranged(client: &mut Client, uri: &str, version: i64, text: &mut String, edits: Vec<Value>) {
    let changes: Vec<_> = edits
        .into_iter()
        .map(|edit| {
            *text = apply_edits(text, &[edit.clone()]);
            json!({"range": edit["range"], "text": edit["newText"]})
        })
        .collect();
    client.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri, "version": version}, "contentChanges": changes}),
    );
    client.validated(uri, version);
}

fn at(uri: &str, text: &str, needle: &str) -> Value {
    json!({"textDocument": {"uri": uri}, "position": position(text, text.find(needle).unwrap())})
}

#[test]
fn past_line_end_changes_clamp_and_subsequent_edits_use_the_real_text() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    client.change(&uri, 2, "module example;\nsort S;\n");
    client.notify("textDocument/didChange", json!({
        "textDocument": {"uri": uri, "version": 3}, "contentChanges": [{
            "range": {"start": {"line":0,"character":999}, "end": {"line":0,"character":999}}, "text":" // note"
        }]
    }));
    client.validated(&uri, 3);
    let mut text = "module example; // note\nsort S;\n".to_string();
    let edit = replacement(&text, "sort S", "sort Marker");
    ranged(&mut client, &uri, 4, &mut text, vec![edit]);
    assert_eq!(client.diagnostics(&uri), json!([]));
    // An edit at the new comment's end distinguishes the real buffer from B's
    // previously stale copy (which silently dropped the first insertion).
    let edit = replacement(&text, "note", "🦀 preserved");
    ranged(&mut client, &uri, 5, &mut text, vec![edit]);
    let edits = client.request(
        "textDocument/formatting",
        json!({"textDocument":{"uri":uri}, "options":{"tabSize":4,"insertSpaces":true}}),
    );
    let formatted = apply_edits(&text, edits.as_array().unwrap());
    assert!(formatted.contains("// 🦀 preserved\n"));
    let mut params = at(&uri, &text, "Marker");
    params["newName"] = json!("Renamed");
    let renamed = client.request("textDocument/rename", params);
    let edits: Vec<_> = renamed["documentChanges"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|change| change["textDocument"]["uri"] == uri)
        .flat_map(|change| change["edits"].as_array().unwrap().iter().cloned())
        .collect();
    assert!(!edits.is_empty());
    assert_eq!(
        apply_edits(&text, &edits),
        text.replace("Marker", "Renamed")
    );
    client.shutdown();
}

#[test]
fn ranged_edits_preserve_utf16_positions_semantic_reuse_and_recovery() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let mut text = "module example; // 🦀\r\nuse computation;\rconst a, b: Slot;\r\nconst input_a: Source;\r\nmapped_to(input_a, a);\r\n".to_string();
    client.change(&uri, 2, &text);
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.request("textDocument/definition", at(&uri, &text, "mapped_to"));
    let before = if std::env::var("DENOTATE_BACKEND").as_deref() != Ok("langium") {
        Some(client.request("denotate/test/analysis", json!({})))
    } else {
        None
    };
    // The second edit is in coordinates produced by the first, not the original.
    let first = replacement(&text, "🦀", "🦀🦀");
    let intermediate = apply_edits(&text, &[first.clone()]);
    let second = replacement(&intermediate, "🦀🦀", "🦀🦀 comment");
    ranged(&mut client, &uri, 3, &mut text, vec![first, second]);
    let target = client.request("textDocument/definition", at(&uri, &text, "mapped_to"));
    assert!(target[0]["targetUri"]
        .as_str()
        .unwrap()
        .ends_with("computation.den"));
    if let Some(before) = before {
        let after = client.request("denotate/test/analysis", json!({}));
        for key in [
            "ruleQueryExecutions",
            "relationQueryExecutions",
            "constantQueryExecutions",
        ] {
            assert_eq!(before[key], after[key], "trivia edit must reuse {key}");
        }
    }
    let damage = replacement(&text, "input_a, a)", "input_a,");
    ranged(&mut client, &uri, 4, &mut text, vec![damage]);
    assert!(!client.diagnostics(&uri).as_array().unwrap().is_empty());
    let completion = client.request("textDocument/completion", json!({"textDocument": {"uri": uri},
        "position": position(&text, text.find("mapped_to(input_a,").unwrap()+"mapped_to(input_a,".len())}));
    let items = completion
        .as_array()
        .or_else(|| completion["items"].as_array())
        .unwrap();
    assert!(items.iter().any(|i| i["label"] == "b"));
    assert!(!items.iter().any(|i| i["label"] == "input_a"));
    let repair = replacement(&text, "mapped_to(input_a,;", "mapped_to(input_a, b);");
    ranged(&mut client, &uri, 5, &mut text, vec![repair]);
    assert_eq!(client.diagnostics(&uri), json!([]));
    let use_b = text.find("input_a, b").unwrap() + "input_a, ".len();
    let target = client.request(
        "textDocument/definition",
        json!({"textDocument": {"uri": uri}, "position": position(&text, use_b)}),
    );
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(&text, text.find("a, b:").unwrap() + 3)
    );
    client.shutdown();
}

#[test]
fn library_edit_burst_refreshes_unchanged_importer_without_version_regression() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let source = "module example; use computation; const shared: Source; const shared: Slot; mapped_to(shared, shared);";
    client.change(&uri, 2, source);
    let (lib_uri, library) = client.open("computation.den");
    client.request("denotate/test/idle", json!({}));
    let start = client.publications().len();
    for version in 2..=9 {
        let sort = if version % 2 == 0 { "Source" } else { "Slot" };
        client.change_without_waiting(
            &lib_uri,
            version,
            &library.replace(
                "mapped_to(source: Source,",
                &format!("mapped_to(source: {sort},"),
            ),
        );
    }
    client.validated(&lib_uri, 9);
    client.request("denotate/test/idle", json!({}));
    assert_eq!(client.diagnostics(&uri), json!([]));
    let target = client.request("textDocument/definition", json!({"textDocument": {"uri": uri}, "position": position(source, source.find("mapped_to(shared").unwrap()+10)}));
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(source, source.find("const shared: Slot").unwrap() + 6)
    );
    let publications: Vec<_> = client.publications()[start..]
        .iter()
        .filter(|p| p["uri"] == lib_uri)
        .collect();
    assert!(!publications.is_empty());
    assert_eq!(publications.last().unwrap()["version"], 9);
    assert!(publications
        .windows(2)
        .all(|p| p[0]["version"].as_i64() <= p[1]["version"].as_i64()));
    assert!(client.publications()[start..]
        .iter()
        .filter(|p| p["uri"] == uri)
        .all(|p| p["version"] == 2));
    // Reopening must restore disk's Source parameter. B also restores on close;
    // A currently retains its indexed unsaved signature until reopen/reindexing.
    client.notify(
        "textDocument/didClose",
        json!({"textDocument": {"uri": lib_uri}}),
    );
    client.request("denotate/test/idle", json!({}));
    let closed_target = client.request("textDocument/definition", json!({"textDocument": {"uri": uri}, "position": position(source, source.find("mapped_to(shared").unwrap()+10)}));
    let restored_position = position(source, source.find("const shared: Source").unwrap() + 6);
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("tree-sitter") {
        assert_eq!(
            closed_target[0]["targetSelectionRange"]["start"],
            restored_position
        );
    } else {
        eprintln!(
            "A close-before-reopen restored disk target: {}",
            closed_target[0]["targetSelectionRange"]["start"] == restored_position
        );
    }
    client.open("computation.den");
    let restored = client.request("textDocument/definition", json!({"textDocument": {"uri": uri}, "position": position(source, source.find("mapped_to(shared").unwrap()+10)}));
    assert_eq!(
        restored[0]["targetSelectionRange"]["start"],
        position(source, source.find("const shared: Source").unwrap() + 6)
    );
    client.shutdown();
}

#[test]
fn cancellation_race_does_not_poison_later_requests() {
    let mut client = Client::start("base/00-valid");
    let (uri, text) = client.open("example.den");
    let params = at(&uri, &text, "mapped_to");
    let id = client.begin_request("textDocument/definition", params.clone());
    client.notify("$/cancelRequest", json!({"id": id}));
    let reply = client.await_reply(id);
    // A response already completed before cancellation is legal. Deterministic
    // checkpoint cancellation is tested in B's component suite (A uses holds).
    if reply.get("error").is_some() {
        assert_eq!(reply["error"]["code"], -32800);
    } else {
        assert_eq!(reply["result"].as_array().unwrap().len(), 1);
    }
    client.notify("$/cancelRequest", json!({"id": id}));
    assert_eq!(
        client
            .request("textDocument/definition", params)
            .as_array()
            .unwrap()
            .len(),
        1
    );
    client.shutdown();
}
