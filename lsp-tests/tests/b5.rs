#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use std::time::Instant;
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
    let start = Instant::now();
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
    let wall = start.elapsed().as_secs_f64() * 1000.0;
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
    json!({"wall_ms":wall,"executions":executions,"timings":after.get("timings")})
}

fn observation(pairs: usize, profiled: bool) -> Value {
    let mut c = Client::start("base/00-valid");
    let (uri, mut source) = c.open("example.den");
    for i in 0..pairs {
        source.push_str(&format!(
            "\nconst extra_{i}: Slot;\navailable(extra_{i});\n"
        ));
    }
    source.push_str("\nrelation probe(slot: Slot);\nprobe(D) :- available(D);\n");
    let cold = edit(&mut c, &uri, 2, &source, None, profiled);
    if profiled && std::env::var("DENOTATE_BACKEND").as_deref() == Ok("tree-sitter") {
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
    let mut ranged = vec![];
    for i in 0..25 {
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
        if i >= 5 {
            ranged.push(result);
        }
    }
    // Use a current, resolved relation reference. Include both source mapping
    // and reference collection costs, not just parsing and database calls.
    let line = commented
        .lines()
        .position(|line| line.starts_with("mapped_to(input_a"))
        .unwrap();
    let mut queries = vec![];
    for method in ["textDocument/prepareRename", "textDocument/references"] {
        c.request("denotate/test/profiling", json!(profiled));
        let mut samples = vec![];
        for i in 0..25 {
            let start = Instant::now();
            let value = c.request(
                method,
                json!({"textDocument":{"uri":uri},"position":{"line":line,"character":1},
                "context":{"includeDeclaration":true}}),
            );
            let wall = start.elapsed().as_secs_f64() * 1000.0;
            if method.ends_with("references") {
                assert!(value.as_array().unwrap().len() >= 4);
            } else {
                assert!(!value.is_null());
            }
            if i >= 5 {
                samples.push(wall);
            }
        }
        queries.push(
            json!({"method":method,"samples_ms":samples,"timings":stats(&mut c).get("timings")}),
        );
    }
    c.shutdown();
    json!({"pairs":pairs,"profiled":profiled,"cold_workload":cold,"comment_edit":comment,
        "semantic_edit":semantic,"ranged_edits":ranged,"queries":queries})
}

#[test]
#[ignore = "manual shared comparison; run just compare-frontends"]
fn comparison_pipeline() {
    for pairs in [0, 100, 1000] {
        for profiled in [false, true] {
            println!("DENOTATE_COMPARISON {}", observation(pairs, profiled));
        }
    }
}

#[test]
fn comparison_instrumentation_preserves_answers_and_reuse() {
    assert_ne!(std::env::var("DENOTATE_BACKEND").as_deref(), Ok("langium"),
        "A1 has no profiling API; exclude this binary rather than counting a skipped test as passed");
    observation(0, false);
    observation(0, true);
}
