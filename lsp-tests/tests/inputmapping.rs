#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::{file_uri, Client};

const SOURCE: &str = include_str!("../../native/test-dsl/fixtures/overlapping-mappings.txt");
fn uri(client: &Client, name: &str) -> String {
    file_uri(&client.workspace.path().join(name))
}
fn open(client: &mut Client, uri: &str, text: &str) {
    client.notify("textDocument/didOpen", json!({"textDocument": {"uri": uri, "languageId": "inputmapping", "version": 1, "text": text}}));
    ready(client, uri, 1);
}
fn ready(client: &mut Client, uri: &str, version: i64) {
    let event = client.notification("denotate/test/frontendReady");
    assert_eq!(event, json!({"uri": uri, "version": version}));
}
fn change(client: &mut Client, uri: &str, version: i64, text: &str) {
    client.change_without_waiting(uri, version, text);
    ready(client, uri, version);
    client.validated(uri, version);
}
fn idle(client: &mut Client) {
    client.request("denotate/test/idle", Value::Null);
}
fn hold(client: &mut Client, phase: &str) {
    client.request("inputmapping/test/hold", json!({"phase": phase}));
}
fn checkpoint(client: &mut Client, uri: &str, version: i64) -> Value {
    let event = client.notification("inputmapping/test/checkpoint");
    assert_eq!(event["uri"], uri);
    assert_eq!(event["version"], version);
    event
}
fn release(client: &mut Client, event: &Value) {
    client.request(
        "inputmapping/test/release",
        json!({"revision": event["revision"]}),
    );
}
fn codes(client: &Client, uri: &str, code: &str) -> Vec<Value> {
    client
        .diagnostics(uri)
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["code"] == code)
        .cloned()
        .collect()
}
fn assert_paused(client: &Client, uri: &str, error_code: &str) {
    assert_eq!(codes(client, uri, "paused").len(), 1);
    assert!(!codes(client, uri, error_code).is_empty());
    assert!(codes(client, uri, "OverlappingMappings").is_empty());
    assert!(client
        .diagnostics(uri)
        .as_array()
        .unwrap()
        .iter()
        .all(|d| d["code"] == "paused" || d["code"] == error_code));
}

#[test]
fn parsed_program_reports_both_targets_related_terms_and_clears_on_repair() {
    let mut c = Client::start("base/00-valid");
    assert_eq!(c.capabilities["textDocumentSync"]["change"], 2);
    for feature in [
        "completionProvider",
        "definitionProvider",
        "renameProvider",
        "documentFormattingProvider",
        "codeActionProvider",
    ] {
        assert!(c.capabilities[feature].is_null() || c.capabilities[feature] == false);
    }
    let u = uri(&c, "program.inputmapping");
    open(&mut c, &u, SOURCE);
    c.validated(&u, 1);
    let errors = codes(&c, &u, "OverlappingMappings");
    assert_eq!(errors.len(), 2);
    for line in [4, 5] {
        let d = errors
            .iter()
            .find(|d| d["range"]["start"]["line"] == line)
            .unwrap();
        assert_eq!(
            d["range"],
            json!({"start":{"line":line,"character":0},"end":{"line":line,"character":1}})
        );
        assert_eq!(d["severity"], 1);
        assert!(d["message"].as_str().unwrap().contains("input_b, input_bb"));
        let related = d["relatedInformation"].as_array().unwrap();
        for other in [4, 5] {
            assert!(related.iter().any(|r| r["location"]["uri"] == u
                && r["location"]["range"]["start"] == json!({"line":other,"character":5})));
        }
    }
    let fixed = SOURCE
        .replace("slot a, b;", "slot a, b, c;")
        .replace("b <- input_bb", "c <- input_bb");
    change(&mut c, &u, 2, &fixed);
    assert_eq!(c.diagnostics(&u), json!([]));
    // Current spans, not offsets saved from an earlier IR or editor version.
    let moved = format!("// 😀 comment\r\n{}", SOURCE.replace('\n', "\r\n"));
    change(&mut c, &u, 3, &moved);
    let lines: Vec<_> = codes(&c, &u, "OverlappingMappings")
        .iter()
        .map(|d| d["range"]["start"]["line"].as_i64().unwrap())
        .collect();
    assert_eq!(lines, [5, 6]);
    c.shutdown();
}

#[test]
fn invalid_source_pauses_the_whole_program_and_repairs_resume_checking() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "invalid.inputmapping");
    open(&mut c, &u, SOURCE);
    c.validated(&u, 1);
    for (version, text, kind) in [
        (2, SOURCE.replace("input_bb when", "when"), "syntax"),
        (
            3,
            SOURCE.replace("available(a)", "available(missing)"),
            "name",
        ),
        (
            4,
            SOURCE.replace("available(a)", "available(input_a)"),
            "name",
        ),
        (5, format!("{SOURCE}\nslot b;"), "name"),
        // A damaged producer for a negated guard must not become an absent fact.
        (
            6,
            "input i, j; slot a, b; a <- ; b <- j when not available(a);".into(),
            "syntax",
        ),
    ] {
        change(&mut c, &u, version, &text);
        assert_paused(&c, &u, kind);
    }
    change(&mut c, &u, 7, SOURCE);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    assert!(codes(&c, &u, "paused").is_empty());
    c.shutdown();
}

#[test]
fn source_semantics_and_scoped_findings_survive_the_protocol_adapter() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "cases.inputmapping");
    open(&mut c, &u, "");
    c.validated(&u, 1);
    for (n, text) in [
        "input i; slot a, b; a <- i; b <- i;",
        "input i; slot a; a <- i; a <- i;",
        "input i, j, k; slot a, b, c; a <- i; b <- j; b <- k when available(c);",
        "input i, j, k; slot a, b; a <- i; b <- j when available(a); b <- k when not available(a);",
        "input i, j, k; slot a, b, c; a <- i; b <- j; b <- k when available(c); c <- k when available(c);",
    ].iter().enumerate() {
        change(&mut c, &u, n as i64 + 2, text);
        assert!(codes(&c, &u, "OverlappingMappings").is_empty());
        assert!(codes(&c, &u, "paused").is_empty());
    }
    let mixed = SOURCE.replace("input_bb;", "input_bb, input_c, input_d, input_dd;").replace("slot a, b;", "slot a, b, c, d;")
        + "c <- input_c when not available(c);\nd <- input_d when not available(c);\nd <- input_dd;\n";
    change(&mut c, &u, 9, &mixed);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    let no_meaning = codes(&c, &u, "NoMeaning");
    assert!(!no_meaning.is_empty());
    assert_eq!(no_meaning[0]["severity"], 1);
    assert_eq!(no_meaning[0]["range"]["start"]["character"], 18);
    // The entire authored condition, not just the `not` keyword.
    assert_eq!(no_meaning[0]["range"]["end"]["character"], 34);
    assert_eq!(
        no_meaning[0]["range"]["start"]["line"],
        no_meaning[0]["range"]["end"]["line"]
    );
    assert!(!codes(&c, &u, "UnsupportedGroup").is_empty());
    c.shutdown();
}

#[test]
fn completed_old_result_cannot_publish_into_a_newer_valid_or_broken_snapshot() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "late.inputmapping");
    open(&mut c, &u, SOURCE);
    c.validated(&u, 1);
    hold(&mut c, "beforeResult");
    c.change_without_waiting(&u, 2, SOURCE);
    ready(&mut c, &u, 2);
    assert_eq!(c.diagnostics(&u), json!([])); // Withdraw before the slow result.
    let held = checkpoint(&mut c, &u, 2);
    let idle_request = c.begin_request("denotate/test/idle", Value::Null);
    c.change_without_waiting(&u, 3, &SOURCE.replace("input_bb when", "when"));
    ready(&mut c, &u, 3);
    c.validated(&u, 3);
    assert_paused(&c, &u, "syntax");
    // Idle is pending, but another request and a paused diagnostic still work.
    assert_eq!(
        c.request("inputmapping/test/stats", Value::Null)["finished"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    release(&mut c, &held);
    c.await_reply(idle_request);
    assert_paused(&c, &u, "syntax");
    let stats = c.request("inputmapping/test/stats", Value::Null);
    assert_eq!(
        stats["finished"].as_array().unwrap().last().unwrap()["status"],
        "discarded"
    );
    assert!(!c.publications().iter().any(|p| p["uri"] == u
        && p["version"] == 2
        && !p["diagnostics"].as_array().unwrap().is_empty()));
    change(&mut c, &u, 4, SOURCE);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    c.shutdown();
}

#[test]
fn cancellation_after_preparation_and_pending_coalescing_are_per_document() {
    let mut c = Client::start("base/00-valid");
    let a = uri(&c, "a.inputmapping");
    let b = uri(&c, "b.inputmapping");
    hold(&mut c, "afterPrepare");
    open(&mut c, &a, SOURCE);
    let held = checkpoint(&mut c, &a, 1);
    open(&mut c, &b, SOURCE); // Queued, not cancelled by edits to a.
    for version in [2, 3] {
        c.change_without_waiting(&a, version, SOURCE);
        ready(&mut c, &a, version);
    }
    let stats = c.request("inputmapping/test/stats", Value::Null);
    assert_eq!(stats["started"].as_array().unwrap().len(), 1);
    assert_eq!(stats["pending"].as_array().unwrap().len(), 2);
    assert!(!stats["pending"]
        .as_array()
        .unwrap()
        .iter()
        .any(|p| p["uri"] == a && p["version"] == 2));
    release(&mut c, &held);
    c.validated(&b, 1);
    c.validated(&a, 3);
    idle(&mut c);
    let stats = c.request("inputmapping/test/stats", Value::Null);
    assert_eq!(stats["finished"][0]["status"], "cancelled");
    assert!(!stats["started"]
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s["uri"] == a && s["version"] == 2));
    assert_eq!(codes(&c, &b, "OverlappingMappings").len(), 2);
    assert_eq!(codes(&c, &a, "OverlappingMappings").len(), 2);
    assert!(codes(&c, &a, "inconclusive").is_empty());
    assert!(!c.publications().iter().any(|p| p["uri"] == a
        && p["version"] == 1
        && !p["diagnostics"].as_array().unwrap().is_empty()));
    c.shutdown();
}

#[test]
fn close_reopen_with_reused_editor_version_rejects_the_old_snapshot() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "reopened.inputmapping");
    hold(&mut c, "beforeResult");
    open(&mut c, &u, SOURCE);
    let held = checkpoint(&mut c, &u, 1);
    c.notify("textDocument/didClose", json!({"textDocument":{"uri":u}}));
    open(&mut c, &u, "input i; slot a; a <- i;");
    release(&mut c, &held);
    c.validated(&u, 1);
    idle(&mut c);
    assert_eq!(c.diagnostics(&u), json!([]));
    let stats = c.request("inputmapping/test/stats", Value::Null);
    assert_eq!(stats["finished"][0]["status"], "discarded");
    assert_ne!(
        stats["started"][0]["revision"],
        stats["started"][1]["revision"]
    );
    assert!(c
        .publications()
        .iter()
        .all(|p| p["diagnostics"] == json!([])));
    c.shutdown();
}

#[test]
fn ranged_edits_recover_from_sync_loss_without_blocking_another_document() {
    let mut c = Client::start("base/00-valid");
    let a = uri(&c, "lost.inputmapping");
    let b = uri(&c, "independent.inputmapping");
    open(&mut c, &a, SOURCE);
    c.validated(&a, 1);
    // Spec-legal past-end column clamps, preserving the other lines.
    c.notify("textDocument/didChange", json!({"textDocument":{"uri":a,"version":2},"contentChanges":[{"range":{"start":{"line":0,"character":999},"end":{"line":0,"character":999}},"text":" // 😀"}]}));
    ready(&mut c, &a, 2);
    c.validated(&a, 2);
    assert_eq!(codes(&c, &a, "OverlappingMappings").len(), 2);
    c.notify("textDocument/didChange", json!({"textDocument":{"uri":a,"version":3},"contentChanges":[{"range":{"start":{"line":1,"character":2},"end":{"line":0,"character":0}},"text":""}]}));
    idle(&mut c);
    assert_eq!(c.diagnostics(&a), json!([]));
    open(&mut c, &b, SOURCE);
    c.validated(&b, 1);
    assert_eq!(codes(&c, &b, "OverlappingMappings").len(), 2);
    change(&mut c, &a, 4, SOURCE);
    assert_eq!(codes(&c, &a, "OverlappingMappings").len(), 2);
    c.shutdown();
}
