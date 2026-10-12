#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::{apply_edits, Client};

fn params(uri: &str, source: &str, needle: &str, delta: usize) -> Value {
    let prefix = &source[..source.find(needle).unwrap() + delta];
    json!({"textDocument":{"uri":uri},"position":{"line":prefix.bytes().filter(|b| *b == b'\n').count(),
        "character":prefix.rsplit('\n').next().unwrap().encode_utf16().count()}})
}

#[test]
fn zero_arity_imports_navigation_rename_hover_signature_outline_and_formatting() {
    let mut c = Client::start("extensions/zero-arity/valid");
    let (uri, source) = c.open("example.den");
    let (lib, library) = c.open("signals.den");
    assert_eq!(c.diagnostics(&uri), json!([]));
    assert_eq!(c.diagnostics(&lib), json!([]));
    let at = params(&uri, &source, "running()", 0);
    let definitions = c.request("textDocument/definition", at.clone());
    assert_eq!(definitions.as_array().unwrap().len(), 1);
    assert_eq!(definitions[0]["targetUri"], lib);
    let hover = c.request("textDocument/hover", at.clone());
    assert!(hover.to_string().contains("relation running()"), "{hover}");
    let signature = c.request(
        "textDocument/signatureHelp",
        params(&uri, &source, "running()", 8),
    );
    assert_eq!(signature["signatures"][0]["label"], "running()");
    assert_eq!(signature["signatures"][0]["parameters"], json!([]));
    assert!(signature
        .as_object()
        .unwrap()
        .contains_key("activeParameter"));
    assert!(signature["activeParameter"].is_null());
    let symbols = c.request(
        "textDocument/documentSymbol",
        json!({"textDocument":{"uri":uri}}),
    );
    assert!(symbols
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s["name"] == "relation observed()"));
    let mut rename = at;
    rename["newName"] = json!("active");
    let edits = c.request("textDocument/rename", rename);
    for (file, text) in [(&uri, &source), (&lib, &library)] {
        let batches: Vec<_> = edits["documentChanges"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e["textDocument"]["uri"] == *file)
            .collect();
        assert_eq!(batches.len(), 1);
        let changed = apply_edits(text, batches[0]["edits"].as_array().unwrap());
        assert_eq!(changed, text.replace("running", "active"));
        c.change(file, 2, &changed);
    }
    assert_eq!(c.diagnostics(&uri), json!([]));
    let ugly =
        "module example;\nuse signals;\nrelation observed ( );\nobserved ( ) :- active ( );\n";
    c.change(&uri, 3, ugly);
    let options = json!({"textDocument":{"uri":uri},"options":{"tabSize":4,"insertSpaces":true}});
    let formatted = c.request("textDocument/formatting", options.clone());
    let text = apply_edits(ugly, formatted.as_array().unwrap());
    assert_eq!(
        text,
        "module example;\nuse signals;\nrelation observed();\nobserved() :-\n    active();\n"
    );
    c.change(&uri, 4, &text);
    assert_eq!(c.diagnostics(&uri), json!([]));
    assert_eq!(c.request("textDocument/formatting", options), json!([]));
    // Incomplete call still has a relation/signature but no argument to offer.
    let partial = "module example;\nuse signals;\nrelation observed();\nobserved() :- active(";
    c.change(&uri, 5, partial);
    let signature = c.request(
        "textDocument/signatureHelp",
        params(&uri, partial, "active(", 7),
    );
    assert_eq!(signature["signatures"][0]["label"], "active()");
    let completion = c.request(
        "textDocument/completion",
        params(&uri, partial, "active(", 7),
    );
    assert!(!completion["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["label"] == "observed"));
    c.shutdown();
}

#[test]
fn zero_arity_still_checks_excess_arguments_and_forbids_input_definitions() {
    let mut c = Client::start("extensions/zero-arity/wrong-arity");
    let (uri, source) = c.open("example.den");
    assert!(c
        .diagnostics(&uri)
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d["message"]
            .as_str()
            .unwrap()
            .contains("expects 0 arguments, got 1")));
    let source = source.replace("enabled(a)", "enabled()");
    c.change(&uri, 2, &source);
    assert_eq!(c.diagnostics(&uri), json!([]));
    if std::env::var("DENOTATE_BACKEND").as_deref() != Ok("langium") {
        c.change(
            &uri,
            3,
            &source.replace("relation enabled", "input enabled"),
        );
        assert!(c
            .diagnostics(&uri)
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["code"] == "input-definition"));
    }
    c.shutdown();
}
