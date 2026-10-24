#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::Client;

fn stats(client: &mut Client) -> Value {
    client.request("denotate/test/analysis", json!({}))
}

fn edit(client: &mut Client, uri: &str, version: i64, source: &str, profiled: bool) -> Value {
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
    client.change(uri, version, source);
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
        return json!({"executions": executions});
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
    json!({"executions": executions})
}

fn phases(profiled: bool) {
    let mut client = Client::start("base/00-valid");
    let (uri, base) = client.open("example.den");
    assert!(
        stats(&mut client).get("timings").is_none(),
        "normal sessions start unprofiled"
    );
    let source = format!("{base}\nrelation probe(slot: Slot);\nprobe(D) :- available(D);\n");
    let cold = edit(&mut client, &uri, 2, &source, profiled);
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert!(cold["executions"]["ruleQueryExecutions"].as_u64().unwrap() > 0);
    let commented = format!("// profiling comment 🦀\n{source}");
    let comment = edit(&mut client, &uri, 3, &commented, profiled);
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
    let semantic = edit(&mut client, &uri, 4, &changed, profiled);
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
}

#[test]
fn profiling_is_opt_in_resets_between_phases_and_observes_cached_work() {
    phases(true);
    phases(false);
}
