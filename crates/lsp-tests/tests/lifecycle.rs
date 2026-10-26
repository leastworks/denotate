#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::Client;

fn position(source: &str, needle: &str, offset: usize) -> Value {
    let prefix = &source[..source.find(needle).unwrap() + offset];
    json!({"line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()})
}

fn at(uri: &str, source: &str, needle: &str, offset: usize) -> Value {
    json!({"textDocument": {"uri": uri}, "position": position(source, needle, offset)})
}

fn idle(client: &mut Client) {
    client.request("denotate/test/idle", json!({}));
}

fn publications<'a>(client: &'a Client, start: usize, uri: &str) -> Vec<&'a Value> {
    client.publications()[start..]
        .iter()
        .filter(|p| p["uri"] == uri)
        .collect()
}

fn latest(client: &Client, start: usize, uri: &str, version: i64) {
    let messages = publications(client, start, uri);
    assert!(
        !messages.is_empty(),
        "must publish, not merely skip all obsolete results"
    );
    let mut previous = 0;
    for message in &messages {
        let current = message["version"]
            .as_i64()
            .expect("analysis version on diagnostics");
        assert!(
            current >= previous,
            "older diagnostics overwrote a newer publication: {messages:?}"
        );
        previous = current;
    }
    assert_eq!(previous, version);
}

fn completion_labels(client: &mut Client, params: Value) -> Vec<String> {
    let result = client.request("textDocument/completion", params);
    result
        .as_array()
        .or_else(|| result["items"].as_array())
        .unwrap()
        .iter()
        .map(|item| item["label"].as_str().unwrap().to_owned())
        .collect()
}

const SOURCE: &str = "module example;\nuse computation;\nconst shared, source_only: Source;\nconst shared, slot_only: Slot;\nmapped_to(shared, slot_only);\n";

#[test]
fn rapid_edits_converge_to_latest_diagnostics_navigation_and_completion() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    idle(&mut client);
    let start = client.publications().len();
    for version in 2..14 {
        let text = match version % 3 {
            0 => SOURCE.to_owned(),
            1 => SOURCE.replace(
                "mapped_to(shared, slot_only)",
                "mapped_to(slot_only, slot_only)",
            ),
            _ => SOURCE.replace("mapped_to(shared, slot_only);", "mapped_to("),
        };
        client.change_without_waiting(&uri, version, &text);
    }
    let final_source = format!("// newest 🦀\n{SOURCE}");
    client.change_without_waiting(&uri, 14, &final_source);
    client.validated(&uri, 14);
    idle(&mut client);
    latest(&client, start, &uri, 14);
    assert_eq!(client.diagnostics(&uri), json!([]));
    let target = client.request(
        "textDocument/definition",
        at(&uri, &final_source, "mapped_to(shared", 10),
    );
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(&final_source, "const shared, source_only", 6)
    );
    let labels = completion_labels(&mut client, at(&uri, &final_source, "mapped_to(shared", 10));
    assert!(labels.contains(&"source_only".into()) && !labels.contains(&"slot_only".into()));
    idle(&mut client);
    latest(&client, start, &uri, 14);
    assert_eq!(client.diagnostics(&uri), json!([]));
    client.shutdown();
}
