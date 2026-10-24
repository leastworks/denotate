#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::Client;

fn stats(c: &mut Client) -> Value {
    c.request("denotate/test/analysis", json!({}))
}

fn edit(
    c: &mut Client,
    uri: &str,
    version: i64,
    text: &str,
    range: Option<Value>,
    profiled: bool,
) -> Value {
    c.request("denotate/test/profiling", json!(profiled));
    let before = stats(c);
    if let Some(range) = range {
        c.notify(
            "textDocument/didChange",
            json!({"textDocument":{"uri":uri,"version":version},
            "contentChanges":[{"range":range,"text":text}]}),
        );
        c.validated(uri, version);
    } else {
        c.change(uri, version, text);
    }
    let after = stats(c);
    let executions: serde_json::Map<String, Value> = after
        .as_object()
        .unwrap()
        .iter()
        .filter(|(key, _)| key.ends_with("QueryExecutions"))
        .map(|(key, value)| {
            (
                key.clone(),
                json!(value.as_u64().unwrap() - before[key].as_u64().unwrap()),
            )
        })
        .collect();
    assert_eq!(stats(c).get("timings"), after.get("timings"));
    assert_eq!(after.get("timings").is_some(), profiled);
    json!({"executions":executions,"timings":after.get("timings")})
}

fn check_edits(profiled: bool) {
    let mut c = Client::start("base/00-valid");
    let (uri, mut source) = c.open("example.den");
    source.push_str("\nrelation probe(slot: Slot);\nprobe(D) :- available(D);\n");
    let cold = edit(&mut c, &uri, 2, &source, None, profiled);
    if profiled {
        for phase in [
            "parseAndText",
            "projection",
            "update",
            "query",
            "diagnostics",
        ] {
            assert!(cold["timings"]["rust"][phase]["calls"].as_u64().unwrap() > 0);
        }
    }
    assert_eq!(c.diagnostics(&uri), json!([]));
    let commented = format!("// profiling comment 🦀\n{source}");
    let comment = edit(&mut c, &uri, 3, &commented, None, profiled);
    assert!(comment["executions"]
        .as_object()
        .unwrap()
        .values()
        .all(|n| n == 0));
    let changed = commented.replace("probe(D) :- available(D);", "probe(D) :- available(E);");
    let semantic = edit(&mut c, &uri, 4, &changed, None, profiled);
    assert_eq!(semantic["executions"]["ruleQueryExecutions"], 1);
    assert!(semantic["executions"]
        .as_object()
        .unwrap()
        .iter()
        .all(|(k, v)| k == "ruleQueryExecutions" || v == 0));
    assert_eq!(c.diagnostics(&uri).as_array().unwrap().len(), 2);
    c.change(&uri, 5, &commented);
    for i in 0..2 {
        let result = edit(
            &mut c,
            &uri,
            i + 6,
            &format!("// ranged {i} 🦀"),
            Some(json!({"start":{"line":0,"character":0},"end":{"line":0,"character":999}})),
            profiled,
        );
        assert_eq!(c.diagnostics(&uri), json!([]));
        assert!(result["executions"]
            .as_object()
            .unwrap()
            .values()
            .all(|n| n == 0));
    }
    // Use a current, resolved relation reference. Include both source mapping
    // and reference collection costs, not just parsing and database calls.
    let line = commented
        .lines()
        .position(|line| line.starts_with("mapped_to(input_a"))
        .unwrap();
    for method in ["textDocument/prepareRename", "textDocument/references"] {
        c.request("denotate/test/profiling", json!(profiled));
        let value = c.request(method, json!({"textDocument":{"uri":uri},"position":{"line":line,"character":1}, "context":{"includeDeclaration":true}}));
        if method.ends_with("references") {
            assert!(value.as_array().unwrap().len() >= 4);
        } else {
            assert!(!value.is_null());
        }
    }
    c.shutdown();
}

#[test]
fn comparison_instrumentation_preserves_answers_and_reuse() {
    check_edits(false);
    check_edits(true);
}
