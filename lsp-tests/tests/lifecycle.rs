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

fn hold(client: &mut Client, uri: &str, version: i64, phase: &str) {
    client.request(
        "denotate/test/holdBuild",
        json!({"uri": uri, "version": version, "phase": phase}),
    );
}

fn held(client: &mut Client, uri: &str, version: i64, phase: &str) -> Value {
    let event = client.notification("denotate/test/buildHeld");
    assert_eq!(event["uri"], uri);
    assert_eq!(event["version"], version);
    assert_eq!(event["phase"], phase);
    event
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

#[test]
fn superseded_computed_diagnostics_are_cancelled_before_publication() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    idle(&mut client);
    let start = client.publications().len();
    hold(&mut client, &uri, 2, "validated");
    client.change_without_waiting(
        &uri,
        2,
        &SOURCE.replace("mapped_to(shared", "mapped_to(slot_only"),
    );
    let old = held(&mut client, &uri, 2, "validated");
    assert!(old["diagnostics"]
        .to_string()
        .contains("No constant 'slot_only' of sort Source"));
    client.change_without_waiting(&uri, 3, "module example; use computation; mapped_to(");
    client.change_without_waiting(&uri, 4, SOURCE);
    let final_source = SOURCE.replace("mapped_to(shared", "mapped_to(missing_latest");
    client.change_without_waiting(&uri, 5, &final_source);
    // didChange mutates the live TextDocument even while validation is held.
    // The publication label must retain the parsed version independently of
    // the cancellation that prevents this obsolete result from being sent.
    assert_eq!(client.request("denotate/test/parsedVersion", json!(uri)), 2);
    assert_eq!(
        client.request("denotate/test/releaseBuild", json!({}))["cancelled"],
        true
    );
    client.validated(&uri, 5);
    idle(&mut client);
    latest(&client, start, &uri, 5);
    assert_eq!(client.request("denotate/test/parsedVersion", json!(uri)), 5);
    assert!(publications(&client, start, &uri)
        .iter()
        .all(|p| p["version"] != 2));
    let diagnostics = client.diagnostics(&uri);
    assert_eq!(diagnostics.as_array().unwrap().len(), 1);
    assert!(diagnostics[0]["message"]
        .as_str()
        .unwrap()
        .contains("missing_latest"));
    assert_eq!(
        diagnostics[0]["range"]["start"],
        position(&final_source, "missing_latest", 0)
    );
    client.shutdown();
}

#[test]
fn library_burst_replaces_importer_results_even_when_importer_version_is_unchanged() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    let (library_uri, library) = client.open("computation.den");
    client.change(&uri, 2, SOURCE);
    idle(&mut client);
    let initial = client.request(
        "textDocument/definition",
        at(&uri, SOURCE, "mapped_to(shared", 10),
    );
    assert_eq!(
        initial[0]["targetSelectionRange"]["start"],
        position(SOURCE, "const shared, source_only", 6)
    );
    let start = client.publications().len();
    hold(&mut client, &uri, 2, "validated");
    client.change_without_waiting(
        &library_uri,
        2,
        &library.replace(
            "mapped_to(source: Source, slot: Slot)",
            "mapped_to(source: Source, slot: Source)",
        ),
    );
    let old = held(&mut client, &uri, 2, "validated");
    assert!(old["diagnostics"]
        .to_string()
        .contains("No constant 'slot_only' of sort Source"));
    client.change_without_waiting(
        &library_uri,
        3,
        &library.replace(
            "mapped_to(source: Source, slot: Slot)",
            "mapped_to(source: Source,)",
        ),
    );
    client.change_without_waiting(&library_uri, 4, &library);
    client.change_without_waiting(
        &library_uri,
        5,
        &library.replace(
            "mapped_to(source: Source, slot: Slot)",
            "mapped_to(source: Slot, slot: Slot)",
        ),
    );
    assert_eq!(
        client.request("denotate/test/releaseBuild", json!({}))["cancelled"],
        true
    );
    client.validated(&library_uri, 5);
    idle(&mut client);
    latest(&client, start, &library_uri, 5);
    let messages = publications(&client, start, &uri);
    assert!(!messages.is_empty());
    assert!(messages.iter().all(|p| p["version"] == 2 && p["diagnostics"] == json!([])),
        "unchanged importer version must not hide stale library-dependent diagnostics: {messages:?}");
    let target = client.request(
        "textDocument/definition",
        at(&uri, SOURCE, "mapped_to(shared", 10),
    );
    assert_eq!(
        target[0]["targetSelectionRange"]["start"],
        position(SOURCE, "const shared, slot_only", 6)
    );
    let labels = completion_labels(&mut client, at(&uri, SOURCE, "mapped_to(shared", 10));
    assert!(labels.contains(&"slot_only".into()) && !labels.contains(&"source_only".into()));
    client.shutdown();
}

#[test]
fn a_request_waiting_for_linking_can_be_cancelled_without_cancelling_the_build() {
    let mut client = Client::start("base/00-valid");
    let (uri, _) = client.open("example.den");
    idle(&mut client);
    hold(&mut client, &uri, 2, "parsed");
    client.change_without_waiting(&uri, 2, SOURCE);
    held(&mut client, &uri, 2, "parsed");
    let params = at(&uri, SOURCE, "mapped_to(shared", 0);
    let id = client.begin_request("textDocument/definition", params.clone());
    client.notify("$/cancelRequest", json!({"id": id}));
    let cancelled = client.await_reply(id);
    assert_eq!(cancelled["error"]["code"], -32800);
    assert!(cancelled.get("result").is_none());
    assert_eq!(
        client.request("denotate/test/releaseBuild", json!({}))["cancelled"],
        false
    );
    client.validated(&uri, 2);
    idle(&mut client);
    assert_eq!(client.diagnostics(&uri), json!([]));
    let completed_id = client.begin_request("textDocument/definition", params.clone());
    let result = client.await_reply(completed_id);
    assert!(result.get("error").is_none());
    assert_eq!(result["result"].as_array().unwrap().len(), 1);
    // Cancellation arriving after completion cannot undo the result or poison
    // the next request. No claim of preempting synchronous Rust work.
    client.notify("$/cancelRequest", json!({"id": completed_id}));
    assert_eq!(
        client.request("textDocument/definition", params),
        result["result"]
    );
    client.shutdown();
}
