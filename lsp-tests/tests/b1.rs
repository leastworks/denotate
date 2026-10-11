mod support;
use serde_json::{json, Value};
use support::Client;

fn symbols(client: &mut Client, uri: &str) -> Vec<Value> {
    client
        .request(
            "textDocument/documentSymbol",
            json!({"textDocument": {"uri": uri}}),
        )
        .as_array()
        .unwrap()
        .clone()
}

#[test]
fn syntax_outline_retains_alternatives_and_compact_source_order() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("computation.den");
    assert_eq!(client.diagnostics(&uri), json!([]));
    let items = symbols(&mut client, &uri);
    for label in [
        "module computation",
        "sort Slot",
        "relation mapped_to(source: Source, slot: Slot)",
        "given(D) :- …",
    ] {
        assert!(
            items.iter().any(|item| item["name"] == label),
            "{label}: {items:?}"
        );
    }
    let alternatives: Vec<_> = items
        .iter()
        .filter(|item| item["name"] == "available(D) :- …")
        .collect();
    assert_eq!(alternatives.len(), 2);
    assert_ne!(alternatives[0]["range"], alternatives[1]["range"]);
    assert!(items
        .windows(2)
        .all(|pair| pair[0]["range"]["start"]["line"].as_u64()
            <= pair[1]["range"]["start"]["line"].as_u64()));
    let (uri, _) = client.open("example.den");
    let items = symbols(&mut client, &uri);
    assert!(items
        .iter()
        .any(|item| item["name"] == "const a, b, result: Slot"));
    assert!(items
        .iter()
        .any(|item| item["name"] == "mapped_to(input_b, b) :- …"));
    client.shutdown();
}

#[test]
fn syntax_error_is_versioned_then_clears_on_repair() {
    let mut client = Client::start("base/01-missing-semicolon");
    let (uri, source) = client.open("computation.den");
    assert!(!client.diagnostics(&uri).as_array().unwrap().is_empty());
    let start = client.publications().len();
    client.change(&uri, 2, &format!("{source}\n// still broken\n"));
    assert!(!client.diagnostics(&uri).as_array().unwrap().is_empty());
    client.change(&uri, 3, &source.replace("sort Source ", "sort Source; "));
    assert_eq!(client.diagnostics(&uri), json!([]));
    let versions: Vec<_> = client.publications()[start..]
        .iter()
        .filter(|p| p["uri"] == uri)
        .map(|p| p["version"].as_i64().unwrap())
        .collect();
    assert!(versions.contains(&2));
    assert_eq!(versions.last(), Some(&3));
    client.shutdown();
}

#[test]
fn broken_library_retains_intact_outline_and_does_not_invent_importer_errors() {
    let mut client = Client::start("base/06-broken-library-declaration");
    let (library, _) = client.open("computation.den");
    assert!(!client.diagnostics(&library).as_array().unwrap().is_empty());
    assert!(symbols(&mut client, &library)
        .iter()
        .any(|s| s["name"] == "relation available(slot: Slot)"));
    let (uri, _) = client.open("example.den");
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert!(symbols(&mut client, &uri)
        .iter()
        .any(|s| s["name"] == "use computation"));
    client.shutdown();
}
