#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use std::time::Instant;
use support::Client;

fn stats(client: &mut Client) -> Value {
    client.request("denotate/test/analysis", json!({}))
}

fn workload(base: &str, pairs: usize) -> String {
    let mut source = base.to_owned();
    for i in 0..pairs {
        source.push_str(&format!(
            "\nconst extra_{i}: Slot;\navailable(extra_{i});\n"
        ));
    }
    source.push_str("\nrelation probe(slot: Slot);\nprobe(D) :- available(D);\n");
    source
}

fn measure(client: &mut Client, uri: &str, version: i64, source: &str, profiled: bool) -> Value {
    client.request("denotate/test/profiling", json!(profiled));
    let before = stats(client);
    if profiled {
        for side in ["javascript", "rust"] {
            for sample in before["timings"][side].as_object().unwrap().values() {
                assert_eq!(
                    sample["calls"], 0,
                    "profiling resets counts, not the Salsa cache"
                );
                assert_eq!(sample["ms"], 0.0);
            }
        }
    }
    let start = Instant::now();
    client.change(uri, version, source);
    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    let after = stats(client);
    // Reading metrics must not record itself or change the measured intervals.
    assert_eq!(stats(client)["timings"], after["timings"]);
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
    if !profiled {
        assert!(after.get("timings").is_none());
        return json!({"wall_ms": elapsed, "executions": executions});
    }
    let js = &after["timings"]["javascript"];
    let rust = &after["timings"]["rust"];
    for phase in [
        "projection",
        "encode",
        "nativeCall",
        "decode",
        "materialize",
    ] {
        assert!(
            js[phase]["calls"].as_u64().unwrap() > 0,
            "missing JS {phase}"
        );
    }
    for phase in ["decode", "update", "query", "encode"] {
        assert!(
            rust[phase]["calls"].as_u64().unwrap() > 0,
            "missing Rust {phase}"
        );
    }
    assert_eq!(
        js["nativeCall"]["calls"].as_u64().unwrap(),
        rust["query"]["calls"].as_u64().unwrap() + rust["update"]["calls"].as_u64().unwrap()
    );
    let ms = |value: &Value, phase: &str| value[phase]["ms"].as_f64().unwrap();
    let rust_total: f64 = ["decode", "update", "query", "encode"]
        .iter()
        .map(|p| ms(rust, p))
        .sum();
    let adapter_total: f64 = [
        "projection",
        "encode",
        "nativeCall",
        "decode",
        "materialize",
    ]
    .iter()
    .map(|p| ms(js, p))
    .sum();
    // nativeCall INCLUDES the Rust intervals. Never add both to the total.
    // Residuals are estimates (two clocks and instrumentation overhead), not
    // precise napi-only or parser-only measurements. Retain signed values.
    json!({"wall_ms": elapsed, "timings": after["timings"], "executions": executions,
        "native_residual_ms": ms(js, "nativeCall") - rust_total,
        "other_wall_ms": elapsed - adapter_total})
}

fn phases(pairs: usize, profiled: bool) -> Value {
    let mut client = Client::start("base/00-valid");
    let (uri, base) = client.open("example.den");
    assert!(
        stats(&mut client).get("timings").is_none(),
        "normal sessions start unprofiled"
    );
    let source = workload(&base, pairs);
    let cold = measure(&mut client, &uri, 2, &source, profiled);
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert!(cold["executions"]["ruleQueryExecutions"].as_u64().unwrap() > 0);
    let commented = format!("// profiling comment 🦀\n{source}");
    let comment = measure(&mut client, &uri, 3, &commented, profiled);
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert!(
        comment["executions"]
            .as_object()
            .unwrap()
            .values()
            .all(|value| value == 0),
        "trivia must reuse all instrumented query families: {comment}"
    );
    let changed = commented.replace("probe(D) :- available(D);", "probe(D) :- available(E);");
    assert_ne!(changed, commented);
    let semantic = measure(&mut client, &uri, 4, &changed, profiled);
    let diagnostics = client.diagnostics(&uri);
    assert_eq!(diagnostics.as_array().unwrap().len(), 2);
    for code in ["unsafe-variable", "singleton-variable"] {
        assert!(diagnostics
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["code"] == code));
    }
    assert_eq!(semantic["executions"]["ruleQueryExecutions"], 1);
    assert!(semantic["executions"]
        .as_object()
        .unwrap()
        .iter()
        .all(|(key, value)| key == "ruleQueryExecutions" || value == 0));
    client.request("denotate/test/profiling", json!(false));
    assert!(stats(&mut client).get("timings").is_none());
    client.shutdown();
    json!({"pairs": pairs, "profiled": profiled, "bytes": source.len(), "cold_workload": cold,
        "comment_edit": comment, "semantic_edit": semantic})
}

#[test]
fn profiling_is_opt_in_resets_between_phases_and_observes_cached_work() {
    phases(0, true);
    phases(0, false);
}

#[test]
#[ignore = "manual measurement, no timing thresholds; run just profile-lsp"]
fn profile_edit_pipeline() {
    // A fresh server per observation; the tiny baseline is initialized before
    // the first measured load. This is cold WORKLOAD analysis, not cold startup.
    for pairs in [0, 100, 1000] {
        for sample in 0..5 {
            // Alternate order of fresh-server controls to expose observer cost
            // without treating instrumented timings as normal editor latency.
            for profiled in if sample % 2 == 0 {
                [false, true]
            } else {
                [true, false]
            } {
                println!(
                    "DENOTATE_PROFILE {}",
                    json!({"sample": sample, "result": phases(pairs, profiled)})
                );
            }
        }
    }
}
