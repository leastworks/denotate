mod support;
use serde_json::json;
use support::Client;

#[test]
fn outline_is_positional_and_retains_repeated_rule_heads() {
    let mut client = Client::start("base/00-valid");
    assert_eq!(client.capabilities["documentSymbolProvider"], true);
    // Capabilities can be enabled by either true or an options object.
    // These features remain disabled until their safety/presentation work lands.
    for capability in ["renameProvider", "workspaceSymbolProvider"] {
        assert!(
            matches!(
                client.capabilities.get(capability),
                None | Some(serde_json::Value::Bool(false))
            ),
            "{capability} must be absent or false, got {:?}",
            client.capabilities.get(capability)
        );
    }
    for capability in ["definitionProvider", "referencesProvider", "hoverProvider"] {
        let value = &client.capabilities[capability];
        assert!(
            value == &json!(true) || value.is_object(),
            "{capability} must be true or an options object, got {value}"
        );
    }
    let (uri, _) = client.open("computation.den");
    let symbols = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    let symbols = symbols.as_array().expect("document symbols");
    assert!(symbols.iter().any(|s| s["name"] == "sort Slot"));
    assert!(symbols
        .iter()
        .any(|s| s["name"] == "relation mapped_to(source: Source, slot: Slot)"));
    let alternatives: Vec<_> = symbols
        .iter()
        .filter(|s| s["name"] == "available(D) :- …")
        .collect();
    assert_eq!(alternatives.len(), 2);
    assert_ne!(alternatives[0]["range"], alternatives[1]["range"]);
    assert!(symbols
        .windows(2)
        .all(|pair| pair[0]["range"]["start"]["line"].as_u64()
            <= pair[1]["range"]["start"]["line"].as_u64()));
    assert_eq!(client.diagnostics(&uri), json!([]));

    let (program_uri, _) = client.open("example.den");
    let program_symbols = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": program_uri}}),
    );
    for label in [
        "const a, b, result: Slot",
        "mapped_to(input_a, a)",
        "mapped_to(input_b, b) :- …",
        "applies(calculate) :- …",
    ] {
        assert!(
            program_symbols
                .as_array()
                .unwrap()
                .iter()
                .any(|s| s["name"] == label),
            "missing compact outline label {label}: {program_symbols}"
        );
    }
    client.shutdown();
}

#[test]
fn unopened_bom_file_uses_editor_columns() {
    let mut client = Client::start("base/18-leading-bom");
    let path = client.workspace.path().join("example.den");
    let source = std::fs::read_to_string(&path).unwrap();
    let editor_text = source.strip_prefix('\u{feff}').expect("BOM fixture");
    let uri = support::file_uri(&path);
    // No didOpen: the server must load and normalize the file from disk.
    let disk_symbols = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    assert_eq!(disk_symbols[0]["name"], "module example");
    assert_eq!(
        disk_symbols[0]["selectionRange"]["start"],
        json!({"line": 0, "character": 7})
    );
    client.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri, "languageId": "denotate", "version": 1, "text": editor_text
        }}),
    );
    client.validated(&uri, 1);
    let open_symbols = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    assert_eq!(disk_symbols, open_symbols);
    assert_eq!(
        std::fs::read_to_string(path).unwrap(),
        source,
        "disk bytes unchanged"
    );
    client.shutdown();
}

#[test]
fn keyword_completion_is_available_without_resolution() {
    let mut client = Client::start("base/00-valid");
    assert!(client.capabilities["completionProvider"].is_object());
    let (uri, _) = client.open("example.den");
    client.change(&uri, 2, "module example;\n\n");
    let completion = client.request(
        "textDocument/completion",
        json!({
            "textDocument": {"uri": uri}, "position": {"line": 2, "character": 0}
        }),
    );
    let items = completion
        .as_array()
        .or_else(|| completion["items"].as_array())
        .unwrap();
    for keyword in ["use", "sort", "const", "relation", "input"] {
        assert!(
            items.iter().any(|item| item["label"] == keyword),
            "missing {keyword}: {completion}"
        );
    }
    client.shutdown();
}

#[test]
fn syntax_error_is_published_and_clears_after_a_versioned_edit() {
    let mut client = Client::start("base/01-missing-semicolon");
    let (uri, source) = client.open("computation.den");
    assert!(!client.diagnostics(&uri).as_array().unwrap().is_empty());
    let before = client.diagnostics(&uri);
    // Same error/range, new version: this must receive a fresh publication,
    // not succeed by reusing diagnostics cached from version 1.
    client.change(&uri, 2, &format!("{source}\n// Still broken.\n"));
    assert_eq!(client.diagnostics(&uri), before);
    client.change(&uri, 3, &source.replace("sort Source ", "sort Source; "));
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.shutdown();
}

#[test]
fn incomplete_sort_reference_gets_type_token_not_variable() {
    let mut client = Client::start("base/03-truncated-argument");
    let (uri, _) = client.open("incomplete.den");
    let tokens = client.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument": {"uri": uri}}),
    );
    let legend = client.capabilities["semanticTokensProvider"]["legend"]["tokenTypes"]
        .as_array()
        .unwrap();
    let data = tokens["data"].as_array().unwrap();
    let (mut line, mut column) = (0, 0);
    let mut found = false;
    for token in data.chunks_exact(5) {
        let delta = token[0].as_u64().unwrap();
        line += delta;
        column = if delta == 0 {
            column + token[1].as_u64().unwrap()
        } else {
            token[1].as_u64().unwrap()
        };
        if line == 2 && column == 16 {
            assert_eq!(token[2], 2);
            assert_eq!(legend[token[3].as_u64().unwrap() as usize], "type");
            found = true;
        }
    }
    assert!(found, "missing token for incomplete sort Sl: {tokens}");
    client.shutdown();
}

#[test]
fn standalone_unicode_comment_shifts_outline_lines() {
    // Line shifting only; UTF-16 versus code-point columns are an A1.3 check.
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("computation.den");
    let before = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    client.change(&uri, 2, &format!("// café 🦀\r\n{source}"));
    let after = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    let before = before.as_array().unwrap();
    let after = after.as_array().unwrap();
    assert_eq!(before.len(), after.len());
    for (old, new) in before.iter().zip(after) {
        assert_eq!(old["name"], new["name"]);
        assert_eq!(
            old["selectionRange"]["start"]["line"].as_u64().unwrap() + 1,
            new["selectionRange"]["start"]["line"].as_u64().unwrap()
        );
        assert_eq!(
            old["selectionRange"]["start"]["character"],
            new["selectionRange"]["start"]["character"]
        );
    }
    client.shutdown();
}

#[test]
fn uppercase_rule_arguments_get_variable_tokens() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("computation.den");
    let tokens = client.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument": {"uri": uri}}),
    );
    let legend = client.capabilities["semanticTokensProvider"]["legend"]["tokenTypes"]
        .as_array()
        .unwrap();
    let mut decoded = Vec::new();
    let (mut line, mut column) = (0, 0);
    for token in tokens["data"].as_array().unwrap().chunks_exact(5) {
        let delta = token[0].as_u64().unwrap();
        line += delta;
        column = if delta == 0 {
            column + token[1].as_u64().unwrap()
        } else {
            token[1].as_u64().unwrap()
        };
        decoded.push((
            line,
            column,
            token[2].as_u64().unwrap(),
            legend[token[3].as_u64().unwrap() as usize]
                .as_str()
                .unwrap(),
        ));
    }
    // Head, positive body, and negative body: capitals are variables by role.
    for snippet in [
        "supplies(S, D) :-",
        "mapped_to(S, D)",
        "present(S)",
        "!masked(D)",
    ] {
        let (line, text) = source
            .lines()
            .enumerate()
            .find(|(_, text)| text.contains(snippet))
            .unwrap();
        let start = text.find(snippet).unwrap();
        for (offset, character) in snippet
            .char_indices()
            .filter(|(_, c)| c.is_ascii_uppercase())
        {
            // These fixture lines are ASCII; this is not a Unicode-position test.
            assert!(
                decoded.contains(&(line as u64, (start + offset) as u64, 1, "variable")),
                "missing variable token for {character} in {snippet}: {tokens}"
            );
        }
    }
    client.shutdown();
}

#[test]
fn damaged_library_does_not_prevent_importer_syntax_outline() {
    let mut client = Client::start("base/06-broken-library-declaration");
    let (library, _) = client.open("computation.den");
    assert!(!client.diagnostics(&library).as_array().unwrap().is_empty());
    let (uri, _) = client.open("example.den");
    let symbols = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    assert!(symbols
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s["name"] == "use computation"));
    assert_eq!(client.diagnostics(&uri), json!([]));
    // This establishes syntax recovery only; navigation/resolution is A1.2.
    client.shutdown();
}
