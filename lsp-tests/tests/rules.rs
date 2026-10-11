mod support;
use serde_json::{json, Value};
use support::Client;

fn native() -> bool {
    std::env::var("DENOTATE_BACKEND").as_deref() != Ok("langium")
}
fn count(client: &mut Client) -> u64 {
    client.request("denotate/test/analysis", json!({}))["ruleQueryExecutions"]
        .as_u64()
        .unwrap()
}
fn position(source: &str, needle: &str, offset: usize) -> Value {
    let prefix = &source[..source.find(needle).unwrap() + offset];
    json!({ "line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count() })
}
fn query(
    client: &mut Client,
    method: &str,
    uri: &str,
    source: &str,
    needle: &str,
    offset: usize,
) -> Value {
    client.request(
        method,
        json!({ "textDocument": {"uri": uri}, "position": position(source, needle, offset) }),
    )
}
fn issues(client: &Client, uri: &str, code: &str) -> Vec<Value> {
    client
        .diagnostics(uri)
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["code"] == code)
        .cloned()
        .collect()
}

#[test]
fn rule_edit_reuses_other_rules_and_comments_only_move_ranges() {
    if !native() {
        return;
    }
    let mut client = Client::start("base/08-singleton-variable");
    let (uri, source) = client.open("computation.den");
    assert_eq!(issues(&client, &uri, "singleton-variable").len(), 1);
    let before = count(&mut client);
    let hover = query(
        &mut client,
        "textDocument/hover",
        &uri,
        &source,
        "present(Ss)",
        8,
    );
    assert!(hover.to_string().contains("variable Ss: Source"));
    let target = query(
        &mut client,
        "textDocument/definition",
        &uri,
        &source,
        "present(Ss)",
        8,
    );
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(&source, "present(Ss)", 8)
    );
    let diagnostic = issues(&client, &uri, "singleton-variable")[0].clone();
    assert_eq!(
        count(&mut client),
        before,
        "editor queries reuse validation's rule analysis"
    );
    let moved = format!("// 🦀 comment\n{source}");
    client.change(&uri, 2, &moved);
    assert_eq!(
        count(&mut client),
        before,
        "trivia must not execute rule queries"
    );
    assert_eq!(
        issues(&client, &uri, "singleton-variable")[0]["range"]["start"]["line"]
            .as_u64()
            .unwrap(),
        diagnostic["range"]["start"]["line"].as_u64().unwrap() + 1
    );
    let target = query(
        &mut client,
        "textDocument/definition",
        &uri,
        &moved,
        "present(Ss)",
        8,
    );
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(&moved, "present(Ss)", 8)
    );
    let fixed = moved.replace("present(Ss),", "present(S),");
    client.change(&uri, 3, &fixed);
    assert!(issues(&client, &uri, "singleton-variable").is_empty());
    assert_eq!(
        count(&mut client),
        before + 1,
        "only the edited rule should execute"
    );
    let target = query(
        &mut client,
        "textDocument/definition",
        &uri,
        &fixed,
        "present(S),",
        8,
    );
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(&fixed, "supplies(S, D) :-", 9)
    );
    // The separate seen(Ss) rule retains its identity, unrelated to the edit.
    let target = query(
        &mut client,
        "textDocument/definition",
        &uri,
        &fixed,
        "present(Ss);",
        8,
    );
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(&fixed, "seen(Ss) :-", 5)
    );
    assert_eq!(count(&mut client), before + 1);
    client.shutdown();
}

#[test]
fn variable_sort_conflicts_follow_signature_edits_and_recovery() {
    if !native() {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let source =
        "module example;\nsort A; sort B;\nrelation r(x: A);\nrelation s(x: B);\nr(D) :- s(D);\n";
    client.change(&uri, 2, source);
    let errors = issues(&client, &uri, "variable-sort-conflict");
    assert_eq!(errors.len(), 1);
    assert!(errors[0]["message"]
        .as_str()
        .unwrap()
        .contains("example.A, example.B"));
    let hover = query(&mut client, "textDocument/hover", &uri, source, "s(D);", 2);
    assert!(hover
        .to_string()
        .contains("Conflicting expected sorts: example.A, example.B"));
    let fixed = source.replace("s(x: B)", "s(x: A)");
    client.change(&uri, 3, &fixed);
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert!(
        query(&mut client, "textDocument/hover", &uri, &fixed, "s(D);", 2)
            .to_string()
            .contains("variable D: A")
    );
    let broken = source.replace("s(x: B)", "s(x: )");
    client.change(&uri, 4, &broken);
    assert!(issues(&client, &uri, "variable-sort-conflict").is_empty());
    let hover = query(&mut client, "textDocument/hover", &uri, &broken, "s(D);", 2);
    assert!(hover
        .to_string()
        .contains("Some occurrences have unknown argument sorts."));
    client.change(&uri, 5, source);
    assert_eq!(issues(&client, &uri, "variable-sort-conflict").len(), 1);
    client.shutdown();
}

#[test]
fn incomplete_rules_suppress_lints_and_missing_binding_claims() {
    if !native() {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let prefix = "module example; use computation;\n";
    for (index, body) in [
        "given(D) :- present(S)",
        "given(D) :- present(S),",
        "given(D) :- present(",
        "given(D) :- present(S), !mapped_to(Other, D)",
    ]
    .iter()
    .enumerate()
    {
        client.change(&uri, (index + 2) as i64, &format!("{prefix}{body}"));
        for code in [
            "singleton-variable",
            "unsafe-variable",
            "variable-sort-conflict",
        ] {
            assert!(issues(&client, &uri, code).is_empty(), "{body}: {code}");
        }
    }
    client.change(&uri, 6, &format!("{prefix}given(D) :- present(S);"));
    assert_eq!(issues(&client, &uri, "unsafe-variable").len(), 1);
    assert_eq!(issues(&client, &uri, "singleton-variable").len(), 1);
    client.change(&uri, 7, prefix);
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.change(&uri, 8, &format!("{prefix}given(D) :- supplies(_, D);"));
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.shutdown();
}

#[test]
fn imported_input_kind_change_updates_head_diagnostics() {
    if !native() {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    client.change(
        &uri,
        2,
        "module example; use computation; const a: Source; present(a);",
    );
    let (lib, source) = client.open("computation.den");
    assert_eq!(issues(&client, &uri, "input-definition").len(), 1);
    client.change(
        &lib,
        2,
        &source.replace("input present", "relation present"),
    );
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.change(&lib, 3, &source);
    assert_eq!(issues(&client, &uri, "input-definition").len(), 1);
    client.shutdown();
}
