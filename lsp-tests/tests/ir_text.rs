//! Step-3 B services for the full text format. A keeps its module/file grammar.
#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::Client;
fn position(text: &str, needle: &str, delta: usize) -> Value {
    let p = &text[..text.find(needle).unwrap() + delta];
    json!({"line":p.bytes().filter(|b|*b==b'\n').count(),"character":p.rsplit('\n').next().unwrap().encode_utf16().count()})
}
fn query(c: &mut Client, method: &str, uri: &str, text: &str, needle: &str, delta: usize) -> Value {
    c.request(method,json!({"textDocument":{"uri":uri},"position":position(text,needle,delta),"context":{"includeDeclaration":true}}))
}
/// Only B implements the full text format; A's shared runs skip these scenarios.
fn b_only() -> bool {
    std::env::var("DENOTATE_BACKEND").as_deref() == Ok("tree-sitter")
}
#[test]
fn namespaces_quoted_names_helpers_domains_contracts_and_locations_use_one_index() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("base/00-valid");
    let (uri, _) = c.open("example.den");
    let text = r#"namespace a {
 sort S; const '007', 7:S;
 relation r(x:S); input p(x:S);
 relation $gate(); $gate();
 r('007'); r(007);
}
namespace a { relation s(x:S); }
namespace a::nested { relation z(); }
namespace b {
 use a;
 relation q(x:a::S);
 q(X) :- a::r(X), a::p(X), a::$gate();
 domain a::S=[a::'007', a::7];
 obligation unique: at_most_one(q, group_by: x);
 assumption known: at_most_one(a::p, group_by: (x));
 #source = source("file:///source.inputmapping", view: "dsl", hash: "sha256:0000000000000000000000000000000000000000000000000000000000000000");
 #origin = loc(#source 1:1 to 1:2);
 q('007') loc(#source {self: 1:1 to 1:2, head.0: 1:1 to 1:2});
 q(7) loc(#origin);
}
"#;
    c.change(&uri, 2, text);
    assert_eq!(c.diagnostics(&uri), json!([]));
    for (needle, offset, target) in [
        ("a::r(X)", 0, "relation r"),
        ("a::$gate()", 0, "relation $gate"),
        ("a::'007'", 0, "const '007'"),
        ("a::7", 0, "7:S"),
        ("group_by: x", 10, "q(x:a::S)"),
        ("loc(#origin)", 4, "#origin ="),
    ] {
        let result = query(
            &mut c,
            "textDocument/definition",
            &uri,
            text,
            needle,
            offset,
        );
        assert_eq!(result.as_array().unwrap().len(), 1, "{needle}: {result}");
        let expected = match target {
            "relation r" => 9,
            "relation $gate" => 9,
            "const '007'" => 6,
            "q(x:a::S)" => 2,
            _ => 0,
        };
        assert_eq!(
            result[0]["targetSelectionRange"]["start"],
            position(text, target, expected),
            "{needle}"
        );
    }
    let namespace = query(&mut c, "textDocument/definition", &uri, text, "use a", 4);
    assert_eq!(
        namespace.as_array().unwrap().len(),
        2,
        "reopened namespace definitions"
    );
    let namespace_refs = query(&mut c, "textDocument/references", &uri, text, "use a", 4);
    assert_eq!(
        namespace_refs.as_array().unwrap().len(),
        3,
        "both declarations and the use"
    );
    let aliases = query(
        &mut c,
        "textDocument/completion",
        &uri,
        text,
        "loc(#origin)",
        6,
    );
    assert!(aliases["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["textEdit"]["newText"] == "#origin"));
    let namespaces = query(&mut c, "textDocument/completion", &uri, text, "use a", 5);
    assert!(namespaces["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["textEdit"]["newText"] == "a::nested"));
    let help = query(
        &mut c,
        "textDocument/signatureHelp",
        &uri,
        text,
        "q('007')",
        6,
    );
    assert_eq!(help["signatures"][0]["label"], "q(x: S)");
    let refs = query(
        &mut c,
        "textDocument/references",
        &uri,
        text,
        "relation r",
        9,
    );
    assert_eq!(refs.as_array().unwrap().len(), 4);
    let hover = query(&mut c, "textDocument/hover", &uri, text, "a::'007'", 0);
    assert!(hover["contents"]["value"].as_str().unwrap().contains("007"));
    let completion = query(&mut c, "textDocument/completion", &uri, text, "q('007')", 2);
    assert!(completion["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["textEdit"]["newText"] == "'007'"));
    let symbols = c.request(
        "textDocument/documentSymbol",
        json!({"textDocument":{"uri":uri}}),
    );
    assert_eq!(symbols.as_array().unwrap().len(), 4);
    assert!(!symbols[0]["children"].as_array().unwrap().is_empty());
    let guarded = c.request_reply(
        "textDocument/prepareRename",
        json!({"textDocument":{"uri":uri},"position":position(text,"relation r",9)}),
    );
    assert!(guarded["error"]["message"]
        .as_str()
        .unwrap()
        .contains("stage 6"));
    c.shutdown();
}
#[test]
fn no_manifest_means_standalone_even_when_use_names_a_workspace_file() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("ir-text/standalone");
    let (uri, text) = c.open("example.den");
    let diagnostics = c.diagnostics(&uri).to_string();
    assert!(diagnostics.contains("Unknown namespace 'library'"));
    assert!(diagnostics.contains("Unknown relation 'library::r'"));
    assert_eq!(
        query(
            &mut c,
            "textDocument/definition",
            &uri,
            &text,
            "library::r",
            0
        ),
        json!([])
    );
    let (library, _) = c.open("library.den");
    assert_eq!(c.diagnostics(&library), json!([]));
    c.shutdown();
}

#[test]
fn export_folder_without_direct_den_children_loads_sources_and_library() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("ir-text/export-layout");
    let (uri, text) = c.open("sources/example.den");
    assert_eq!(c.diagnostics(&uri), json!([]));
    let definition = query(&mut c, "textDocument/definition", &uri, &text, "r(a)", 0);
    assert_eq!(definition.as_array().unwrap().len(), 1);
    assert_eq!(
        definition[0]["targetUri"],
        support::file_uri(&c.workspace.path().join("library/library.den"))
    );
    let hover = query(&mut c, "textDocument/hover", &uri, &text, "r(a)", 0);
    assert_eq!(hover["contents"]["value"], "relation r(x: S)");
    c.shutdown();
}
