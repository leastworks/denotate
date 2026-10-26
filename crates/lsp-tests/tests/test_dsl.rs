#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::{file_uri, Client};

const SOURCE: &str = include_str!("../../test-dsl/fixtures/overlapping-mappings.txt");
fn uri(client: &Client, name: &str) -> String {
    file_uri(&client.workspace.path().join(name))
}
fn open(client: &mut Client, uri: &str, text: &str) {
    client.notify(
        "textDocument/didOpen",
        json!({"textDocument": {"uri": uri, "languageId": "testdsl", "version": 1, "text": text}}),
    );
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
    client.request("denotate/test/checkingIdle", Value::Null);
}
fn hold(client: &mut Client, phase: &str) {
    client.request("denotate/test/hold", json!({"phase": phase}));
}
fn checkpoint(client: &mut Client, uri: &str, version: i64) -> Value {
    let event = client.notification("denotate/test/checkpoint");
    assert_eq!(event["uri"], uri);
    assert_eq!(event["version"], version);
    event
}
fn release(client: &mut Client, event: &Value) {
    client.request(
        "denotate/test/release",
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

fn stats(client: &mut Client) -> Value {
    idle(client);
    client.request("denotate/test/checkingStats", Value::Null)
}

fn queries(stats: &Value, uri: &str) -> [u64; 4] {
    let q = &stats["lowering"][uri]["queries"];
    ["recipe", "declarations", "resolve", "validate"].map(|k| q[k].as_u64().unwrap())
}

#[test]
fn masks_clear_and_restore_overlap_with_current_ranges_and_cached_mapping_recipes() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "masks.testdsl");
    open(&mut c, &u, SOURCE);
    c.validated(&u, 1);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    let initial = queries(&stats(&mut c), &u);
    change(&mut c, &u, 2, &format!("{SOURCE}\nmask b;\n"));
    assert!(c.diagnostics(&u).as_array().unwrap().is_empty());
    assert_eq!(
        queries(&stats(&mut c), &u),
        [initial[0] + 1, initial[1], initial[2], initial[3] + 1]
    );
    change(&mut c, &u, 3, &format!("// shifted\n{SOURCE}"));
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    for d in codes(&c, &u, "OverlappingMappings") {
        assert!([5, 6].contains(&d["range"]["start"]["line"].as_u64().unwrap()));
        assert_eq!(d["range"]["end"]["character"], 1);
    }
    let before = stats(&mut c);
    for (version, mask, code) in [
        (4, "mask missing;", "name"),
        (5, "mask input_a;", "name"),
        (6, "mask b when ;", "syntax"),
        (7, "input mask;", "syntax"),
    ] {
        change(&mut c, &u, version, &format!("{SOURCE}\n{mask}"));
        assert_paused(&c, &u, code);
        assert_eq!(stats(&mut c)["started"], before["started"]);
    }
    change(
        &mut c,
        &u,
        8,
        &format!("{SOURCE}\nmask b;\nmask b when available(a);\n"),
    );
    let warnings = codes(&c, &u, "redundant-mask");
    assert_eq!(warnings.len(), 1);
    assert_eq!(warnings[0]["severity"], 2);
    assert_eq!(
        warnings[0]["message"],
        "This mask adds no effect: Slot b is already masked unconditionally."
    );
    let line = SOURCE.lines().count() + 2;
    assert_eq!(
        warnings[0]["range"],
        json!({"start":{"line":line,"character":0},"end":{"line":line,"character":25}})
    );
    assert_eq!(
        warnings[0]["relatedInformation"][0]["location"]["range"],
        json!({"start":{"line":line-1,"character":0},"end":{"line":line-1,"character":7}})
    );
    c.shutdown();
}

#[test]
fn mask_cycles_report_conditions_and_related_mappings_without_inventing_authored_not() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "mask-cycles.testdsl");
    let single = "input i;\nslot a;\na <- i;\nmask a when available(a);\n";
    open(&mut c, &u, single);
    c.validated(&u, 1);
    let failures = codes(&c, &u, "NoMeaning");
    assert_eq!(failures.len(), 1);
    assert_eq!(failures[0]["severity"], 1);
    assert_eq!(
        failures[0]["range"],
        json!({"start":{"line":3,"character":12},"end":{"line":3,"character":24}})
    );
    assert!(failures[0]["message"].as_str().unwrap().starts_with("Masking Slot a depends on its own availability; no consistent result exists when Input i is present."));
    assert!(failures[0]["message"]
        .as_str()
        .unwrap()
        .contains("Other observations remain unsupported"));
    assert!(failures[0]["relatedInformation"]
        .as_array()
        .unwrap()
        .iter()
        .any(|r| r["location"]["range"]
            == json!({"start":{"line":2,"character":0},"end":{"line":2,"character":7}})));
    change(&mut c,&u,2,"input i, j;\nslot a, b;\na <- i;\nb <- j;\nmask a when available(b);\nmask b when available(a);\n");
    assert!(codes(&c, &u, "NoMeaning").is_empty());
    let cycles = codes(&c, &u, "UnsupportedCycle");
    assert_eq!(cycles.len(), 2);
    for (d, line) in cycles.iter().zip([4, 5]) {
        assert_eq!(d["severity"], 2);
        assert_eq!(
            d["range"],
            json!({"start":{"line":line,"character":12},"end":{"line":line,"character":24}})
        );
        assert!(d["message"].as_str().unwrap().starts_with("Masking Slots a and b depends cyclically on their availability. The checker could not establish a single result."));
        for line in [2, 3] {
            assert!(d["relatedInformation"].as_array().unwrap().iter().any(|r|r["location"]["range"]==json!({"start":{"line":line,"character":0},"end":{"line":line,"character":7}})));
        }
    }
    c.shutdown();
}

#[test]
fn lowering_reuses_forms_across_comments_helpers_reordering_and_duplicates() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "cached.testdsl");
    open(&mut c, &u, SOURCE);
    c.validated(&u, 1);
    let initial = stats(&mut c);
    assert!(queries(&initial, &u).iter().all(|count| *count > 0));
    let commented = format!("// current snapshot\n{SOURCE}");
    change(&mut c, &u, 2, &commented);
    let after = stats(&mut c);
    assert_eq!(queries(&after, &u), queries(&initial, &u));
    assert_eq!(
        after["lowering"][&u]["declaration_updates"],
        initial["lowering"][&u]["declaration_updates"]
    );
    assert!(
        after["lowering"][&u]["assemblies"].as_u64().unwrap()
            > initial["lowering"][&u]["assemblies"].as_u64().unwrap()
    );
    let errors = codes(&c, &u, "OverlappingMappings");
    assert_eq!(errors.len(), 2);
    for line in [5, 6] {
        assert!(errors.iter().any(|d| d["range"]
            == json!({"start":{"line":line,"character":0}, "end":{"line":line,"character":1}})));
        assert!(errors.iter().all(|d| d["relatedInformation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r["location"]["range"]["start"] == json!({"line":line,"character":5}))));
    }
    let helper = "a <- input_a when not (present(input_a) and present(input_b));";
    let inserted = commented.replace("a <- input_a;", &format!("{helper}\na <- input_a;"));
    change(&mut c, &u, 3, &inserted);
    let inserted_queries = queries(&stats(&mut c), &u);
    let initial_queries = queries(&initial, &u);
    assert!(inserted_queries[0] > initial_queries[0]);
    assert_eq!(inserted_queries[1..3], initial_queries[1..3]);
    assert!(inserted_queries[3] > initial_queries[3]);
    change(&mut c, &u, 4, &format!("{commented}\n{helper}\n{helper}\n"));
    assert_eq!(queries(&stats(&mut c), &u), inserted_queries);
    let edited = commented.replace(
        "b <- input_bb when available(a)",
        "b <- input_bb when not not available(a)",
    );
    change(&mut c, &u, 5, &edited);
    let edited_queries = queries(&stats(&mut c), &u);
    assert!(edited_queries[0] > inserted_queries[0]);
    assert_eq!(edited_queries[1..3], inserted_queries[1..3]);
    assert!(edited_queries[3] > inserted_queries[3]);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    c.shutdown();
}

#[test]
fn cached_errors_and_duplicate_checks_block_assembly_and_worker_dispatch() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "cached-errors.testdsl");
    open(&mut c, &u, SOURCE);
    c.validated(&u, 1);
    let initial = stats(&mut c);
    let mut previous_queries = None;
    let bad = SOURCE.replace("b <- input_bb", "b <- missing");
    for (version, text) in [
        (2, bad.clone()),
        (3, format!("// shift\n{bad}")),
        (4, format!("{SOURCE}\nslot b;")),
    ] {
        change(&mut c, &u, version, &text);
        assert_paused(&c, &u, "name");
        let current = stats(&mut c);
        assert_eq!(
            current["lowering"][&u]["assemblies"],
            initial["lowering"][&u]["assemblies"]
        );
        assert_eq!(current["started"], initial["started"]);
        assert_eq!(
            current["lowering"][&u]["queries"]["recipe"],
            initial["lowering"][&u]["queries"]["recipe"]
        );
        if version == 2 || version == 3 {
            let observed = queries(&current, &u);
            if let Some(previous) = previous_queries {
                assert_eq!(observed, previous);
            } else {
                assert!(observed[2] > queries(&initial, &u)[2]);
            }
            previous_queries = Some(observed);
            assert_eq!(
                codes(&c, &u, "name")[0]["range"],
                json!({"start":{"line":version+3,"character":5},"end":{"line":version+3,"character":12}})
            );
        }
    }
    let wrong = SOURCE.replace("available(a)", "available(input_a)");
    change(&mut c, &u, 5, &wrong);
    let previous = stats(&mut c);
    let moved = wrong.replace("input input_a", "input unused, input_a");
    change(&mut c, &u, 6, &moved);
    let current = stats(&mut c);
    assert_eq!(
        current["lowering"][&u]["queries"]["validate"],
        previous["lowering"][&u]["queries"]["validate"]
    );
    assert_eq!(current["started"], initial["started"]);
    for error in codes(&c, &u, "name") {
        assert_eq!(
            error["relatedInformation"][0]["location"]["range"],
            json!({"start":{"line":0,"character":14},"end":{"line":0,"character":21}})
        );
    }
    change(&mut c, &u, 7, SOURCE);
    let repaired = stats(&mut c);
    assert!(
        repaired["lowering"][&u]["assemblies"].as_u64().unwrap()
            > initial["lowering"][&u]["assemblies"].as_u64().unwrap()
    );
    assert_eq!(
        repaired["started"].as_array().unwrap().len(),
        initial["started"].as_array().unwrap().len() + 1
    );
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    c.shutdown();
}

#[test]
fn lowering_sessions_survive_syntax_errors_but_are_isolated_and_dropped_on_close() {
    let mut c = Client::start("base/00-valid");
    let a = uri(&c, "first.testdsl");
    let b = uri(&c, "second.testdsl");
    open(&mut c, &a, SOURCE);
    c.validated(&a, 1);
    let initial = stats(&mut c);
    change(&mut c, &a, 2, &SOURCE.replace("a <- input_a;", "a <- ;"));
    assert_paused(&c, &a, "syntax");
    assert_eq!(stats(&mut c)["lowering"][&a], initial["lowering"][&a]);
    open(&mut c, &b, &SOURCE.replace("slot a, b;", "slot a;"));
    c.validated(&b, 1);
    assert_paused(&c, &b, "name");
    assert_eq!(stats(&mut c)["lowering"][&b]["assemblies"], 0);
    change(&mut c, &a, 3, SOURCE);
    let repaired = stats(&mut c);
    assert_eq!(queries(&repaired, &a), queries(&initial, &a));
    assert!(
        repaired["lowering"][&a]["assemblies"].as_u64().unwrap()
            > initial["lowering"][&a]["assemblies"].as_u64().unwrap()
    );
    c.notify("textDocument/didClose", json!({"textDocument":{"uri":a}}));
    assert!(stats(&mut c)["lowering"].get(&a).is_none());
    open(&mut c, &a, SOURCE);
    c.validated(&a, 1);
    let reopened = stats(&mut c);
    assert_eq!(queries(&reopened, &a), queries(&initial, &a));
    assert_eq!(
        reopened["lowering"][&a]["assemblies"],
        initial["lowering"][&a]["assemblies"]
    );
    assert_eq!(reopened["lowering"][&b], repaired["lowering"][&b]);
    c.shutdown();
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
    let u = uri(&c, "program.testdsl");
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
    let u = uri(&c, "invalid.testdsl");
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
    let u = uri(&c, "cases.testdsl");
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
    let u = uri(&c, "late.testdsl");
    open(&mut c, &u, SOURCE);
    c.validated(&u, 1);
    hold(&mut c, "beforeResult");
    c.change_without_waiting(&u, 2, SOURCE);
    ready(&mut c, &u, 2);
    assert_eq!(c.diagnostics(&u), json!([])); // Withdraw before the slow result.
    let held = checkpoint(&mut c, &u, 2);
    let idle_request = c.begin_request("denotate/test/checkingIdle", Value::Null);
    c.change_without_waiting(&u, 3, &SOURCE.replace("input_bb when", "when"));
    ready(&mut c, &u, 3);
    c.validated(&u, 3);
    assert_paused(&c, &u, "syntax");
    // Idle is pending, but another request and a paused diagnostic still work.
    assert_eq!(
        c.request("denotate/test/checkingStats", Value::Null)["finished"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    release(&mut c, &held);
    c.await_reply(idle_request);
    assert_paused(&c, &u, "syntax");
    let stats = c.request("denotate/test/checkingStats", Value::Null);
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
fn queued_document_edits_keep_fifo_position_and_active_edits_join_the_tail() {
    let mut c = Client::start("base/00-valid");
    let a = uri(&c, "a.testdsl");
    let b = uri(&c, "b.testdsl");
    let d = uri(&c, "c.testdsl");
    hold(&mut c, "duringCheck");
    open(&mut c, &a, SOURCE);
    let held = checkpoint(&mut c, &a, 1);
    open(&mut c, &b, SOURCE);
    open(&mut c, &d, SOURCE);
    for u in [&b, &a] {
        c.change_without_waiting(u, 2, SOURCE);
        ready(&mut c, u, 2);
    }
    let pending = c.request("denotate/test/checkingStats", Value::Null)["pending"].clone();
    assert_eq!(
        pending
            .as_array()
            .unwrap()
            .iter()
            .map(|j| (&j["uri"], &j["version"]))
            .collect::<Vec<_>>(),
        vec![
            (&json!(b), &json!(2)),
            (&json!(d), &json!(1)),
            (&json!(a), &json!(2))
        ]
    );
    release(&mut c, &held);
    let finished = stats(&mut c);
    let started = finished["started"].as_array().unwrap();
    assert_eq!(started.len(), 4);
    assert_eq!(started[1..], pending.as_array().unwrap()[..]);
    for u in [&a, &b, &d] {
        assert_eq!(codes(&c, u, "OverlappingMappings").len(), 2);
    }
    c.shutdown();
}

#[test]
fn shutdown_releases_held_checks_without_a_client_release() {
    for phase in ["duringCheck", "beforeResult"] {
        let mut c = Client::start("base/00-valid");
        let a = uri(&c, "a.testdsl");
        let b = uri(&c, "b.testdsl");
        hold(&mut c, phase);
        open(&mut c, &a, SOURCE);
        checkpoint(&mut c, &a, 1);
        open(&mut c, &b, SOURCE);
        c.shutdown();
    }
}

#[test]
fn cancellation_after_preparation_and_pending_coalescing_are_per_document() {
    let mut c = Client::start("base/00-valid");
    let a = uri(&c, "a.testdsl");
    let b = uri(&c, "b.testdsl");
    hold(&mut c, "duringCheck");
    open(&mut c, &a, SOURCE);
    let held = checkpoint(&mut c, &a, 1);
    open(&mut c, &b, SOURCE); // Queued, not cancelled by edits to a.
    for version in [2, 3] {
        c.change_without_waiting(&a, version, SOURCE);
        ready(&mut c, &a, version);
    }
    let stats = c.request("denotate/test/checkingStats", Value::Null);
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
    let stats = c.request("denotate/test/checkingStats", Value::Null);
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
    let u = uri(&c, "reopened.testdsl");
    hold(&mut c, "beforeResult");
    open(&mut c, &u, SOURCE);
    let held = checkpoint(&mut c, &u, 1);
    c.notify("textDocument/didClose", json!({"textDocument":{"uri":u}}));
    open(&mut c, &u, "input i; slot a; a <- i;");
    release(&mut c, &held);
    c.validated(&u, 1);
    idle(&mut c);
    assert_eq!(c.diagnostics(&u), json!([]));
    let stats = c.request("denotate/test/checkingStats", Value::Null);
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
    let a = uri(&c, "lost.testdsl");
    let b = uri(&c, "independent.testdsl");
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

#[test]
fn value_literals_validate_before_recipes_and_numeric_aliases_reuse_cached_forms() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "values.testdsl");
    let text="input i, j;\nslot a;\na <- i when input_value(i) is 1;\na <- j when input_value(j) is 1;\n";
    open(&mut c, &u, text);
    c.validated(&u, 1);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    let before = queries(&stats(&mut c), &u);
    change(
        &mut c,
        &u,
        2,
        &format!("// moved\n{}", text.replace("is 1", "is 01")),
    );
    assert_eq!(queries(&stats(&mut c), &u), before);
    assert_eq!(
        codes(&c, &u, "OverlappingMappings")[0]["range"]["start"]["line"],
        3
    );
    let before_stats = stats(&mut c);
    let invalid = text.replace(
        "input_value(i) is 1",
        "input_value(i) is 9223372036854775808",
    );
    change(&mut c, &u, 3, &invalid);
    assert_paused(&c, &u, "literal");
    let error = codes(&c, &u, "literal").pop().unwrap();
    assert_eq!(error["range"]["start"], json!({"line":2,"character":30}));
    let after = stats(&mut c);
    assert_eq!(queries(&after, &u)[0], before[0]);
    assert_eq!(
        after["lowering"][&u]["assemblies"],
        before_stats["lowering"][&u]["assemblies"]
    );
    change(&mut c, &u, 4, text);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    let extended = format!("{text}mask a when input_value(i) is 2;\n");
    let before = queries(&stats(&mut c), &u);
    change(&mut c, &u, 5, &extended);
    assert_eq!(queries(&stats(&mut c), &u)[0], before[0] + 1);
    c.shutdown();
}

#[test]
fn values_copy_through_slots_masks_and_w_sensitive_cycles_in_the_server() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "value-copy.testdsl");
    let text="input i, j; slot a, b; a <- i; b <- j when slot_value(a) is 1; b <- i when slot_value(a) is 1;";
    open(&mut c, &u, text);
    c.validated(&u, 1);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    change(
        &mut c,
        &u,
        2,
        &format!("{text} mask a when input_value(i) is 1;"),
    );
    assert!(codes(&c, &u, "OverlappingMappings").is_empty());
    let redundant =
        "input i; slot a; a <- i when input_value(i) is 1 and not (input_value(i) is 2);";
    change(&mut c, &u, 3, redundant);
    let ds = codes(&c, &u, "redundant");
    assert_eq!(ds.len(), 1);
    assert!(ds[0]["message"]
        .as_str()
        .unwrap()
        .contains("cannot also have value 2"));
    let cycle="input t, i, j; slot a, b; a <- i when input_value(t) is 1 and not available(b); b <- j when input_value(t) is 2 and not available(a);";
    change(&mut c, &u, 4, cycle);
    assert_eq!(codes(&c, &u, "redundant").len(), 2);
    assert!(codes(&c, &u, "NoMeaning").is_empty());
    change(
        &mut c,
        &u,
        5,
        "input i; slot a; a <- i when not input_value(i) is 1 and not available(a);",
    );
    assert!(!codes(&c, &u, "NoMeaning").is_empty());
    assert!(codes(&c, &u, "creator-failure").is_empty());
    c.shutdown();
}

#[test]
fn checker_cache_reuses_current_diagnostics_and_drops_on_close() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "checker-cache.testdsl");
    let source = "input i,j,k,l,m; slot a; a <- i when present(j) and present(k) and present(l) and present(m); a <- j;";
    open(&mut c, &u, source);
    c.validated(&u, 1);
    let first = stats(&mut c);
    let cold = first["finished"].as_array().unwrap().last().unwrap();
    assert!(cold["cache"]["evaluation_misses"].as_u64().unwrap() > 0);
    assert!(cold["plans"]["executed"].as_u64().unwrap() > 0);
    let original = codes(&c, &u, "OverlappingMappings");
    assert_eq!(original.len(), 2);
    change(&mut c, &u, 2, &format!("// moved\n{source}"));
    let second = stats(&mut c);
    let warm = second["finished"].as_array().unwrap().last().unwrap();
    assert_eq!(warm["cache"]["evaluation_misses"], 0);
    assert_eq!(warm["plans"]["executed"], 0);
    assert!(warm["plans"]["reused"].as_u64().unwrap() > 0);
    assert!(warm["cache"]["evaluation_hits"].as_u64().unwrap() > 0);
    let moved = codes(&c, &u, "OverlappingMappings");
    assert_eq!(moved.len(), 2);
    assert_eq!(moved[0]["message"], original[0]["message"]);
    assert_eq!(
        moved[0]["range"]["start"]["line"].as_u64().unwrap(),
        original[0]["range"]["start"]["line"].as_u64().unwrap() + 1
    );
    c.notify("textDocument/didClose", json!({"textDocument":{"uri":u}}));
    idle(&mut c);
    open(&mut c, &u, source);
    c.validated(&u, 1);
    let reopened = stats(&mut c);
    let last = reopened["finished"].as_array().unwrap().last().unwrap();
    assert_eq!(last["cache"]["evaluation_hits"], 0);
    assert!(last["plans"]["executed"].as_u64().unwrap() > 0);
    assert!(last["cache"]["evaluation_misses"].as_u64().unwrap() > 0);
}

#[test]
fn published_findings_have_shared_identity_witness_and_current_outcome_summary() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "presenter.testdsl");
    let source = "input i, j; slot a; a <- i; a <- j;";
    open(&mut c, &u, source);
    c.validated(&u, 1);
    let cold = codes(&c, &u, "OverlappingMappings");
    assert_eq!(cold.len(), 2);
    let data = &cold[0]["data"];
    assert_eq!(data["program"], u);
    assert_eq!(data["kind"], "counterexample");
    assert_eq!(data["finding"], cold[1]["data"]["finding"]);
    assert_eq!(data["evidence"]["kind"], "replayed-counterexample");
    assert_eq!(data["evidence"]["tuples"].as_array().unwrap().len(), 2);
    assert!(!data["evidence"]["producers"].as_array().unwrap().is_empty());
    change(&mut c, &u, 2, &format!("// 😀\r\n{source}"));
    let warm = codes(&c, &u, "OverlappingMappings");
    assert_eq!(warm.len(), 2);
    for d in &warm {
        assert_eq!(d["data"], *data);
        assert_eq!(d["range"]["start"]["line"], 1);
    }
    let status = stats(&mut c);
    let last = status["finished"].as_array().unwrap().last().unwrap();
    assert_eq!(last["snapshot"]["version"], 2);
    assert_eq!(last["summary"]["state"], "findings");
    assert_eq!(last["summary"]["backend"]["backend"], "bdd");
    assert_eq!(
        last["summary"]["activeAssumptions"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
}

#[test]
fn shared_checking_barriers_and_cold_reset_keep_document_identity_and_findings() {
    let mut c = Client::start("base/00-valid");
    let u = uri(&c, "shared-hooks.testdsl");
    hold(&mut c, "beforeResult");
    open(&mut c, &u, SOURCE);
    let held = checkpoint(&mut c, &u, 1);
    // The fast barrier must answer even while a completed result is held.
    c.request("denotate/test/idle", Value::Null);
    let waiting = c.begin_request("denotate/test/checkingIdle", Value::Null);
    let reset = c.request_reply("denotate/test/resetChecks", Value::Null);
    assert_eq!(reset["error"]["code"], -32602);
    release(&mut c, &held);
    c.await_reply(waiting);
    let first = c.notification("denotate/test/checked");
    assert_eq!(first, held);
    let diagnostics = c.diagnostics(&u);
    assert_eq!(codes(&c, &u, "OverlappingMappings").len(), 2);
    c.request("denotate/test/resetChecks", Value::Null);
    idle(&mut c);
    let cold = c.notification("denotate/test/checked");
    assert_eq!(cold["uri"], first["uri"]);
    assert_eq!(cold["version"], first["version"]);
    assert_ne!(cold["revision"], first["revision"]);
    assert_eq!(c.diagnostics(&u), diagnostics);
    let records = stats(&mut c);
    assert_eq!(records["started"].as_array().unwrap().len(), 2);
    assert_eq!(records["finished"].as_array().unwrap().len(), 2);
    c.shutdown();
}

#[test]
fn sync_loss_withdraws_once_and_republishes_other_documents_full_findings() {
    let mut c = Client::start("base/00-valid");
    let a = uri(&c, "lost.testdsl");
    let b = uri(&c, "unaffected.testdsl");
    for u in [&a, &b] {
        open(&mut c, u, SOURCE);
        c.validated(u, 1);
    }
    idle(&mut c);
    let other = c.diagnostics(&b);
    assert_eq!(codes(&c, &b, "OverlappingMappings").len(), 2);
    let before = c.publications().len();
    // Malformed range decoding must use document metadata to lose sync.
    for version in [2, 3] {
        c.notify("textDocument/didChange", json!({"textDocument":{"uri":a,"version":version},"contentChanges":[{"range":"malformed","text":""}]}));
        c.request("denotate/test/idle", Value::Null);
    }
    let publications = &c.publications()[before..];
    let cleared = publications
        .iter()
        .filter(|p| p["uri"] == a)
        .collect::<Vec<_>>();
    assert_eq!(cleared.len(), 1);
    assert_eq!(cleared[0]["diagnostics"], json!([]));
    assert!(cleared[0].get("version").is_none());
    let republished = publications
        .iter()
        .filter(|p| p["uri"] == b)
        .collect::<Vec<_>>();
    assert_eq!(republished.len(), 2);
    assert!(republished
        .iter()
        .all(|p| p["version"] == 1 && p["diagnostics"] == other));
    // Recovery must exceed the latest rejected version and use full text.
    c.notify(
        "textDocument/didChange",
        json!({"textDocument":{"uri":a,"version":3},"contentChanges":[{"text":SOURCE}]}),
    );
    c.request("denotate/test/idle", Value::Null);
    assert_eq!(c.diagnostics(&a), json!([]));
    change(&mut c, &a, 4, SOURCE);
    assert_eq!(codes(&c, &a, "OverlappingMappings").len(), 2);
    assert_eq!(c.diagnostics(&b), other);
    c.shutdown();
}
