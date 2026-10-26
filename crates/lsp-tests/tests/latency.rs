#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use std::time::Instant;
use support::Client;

fn summary(mut samples: Vec<f64>) -> Value {
    samples.sort_by(f64::total_cmp);
    json!({"samples": samples.len(), "p50_ms": samples[(samples.len() - 1) / 2],
        "p95_ms": samples[(samples.len() * 95).div_ceil(100) - 1],
        "max_ms": samples.last().unwrap()})
}

fn at(source: &str, needle: &str, delta: usize) -> Value {
    let prefix = &source[..source.find(needle).unwrap() + delta];
    json!({"line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()})
}

#[test]
#[ignore = "manual measurement, not a timing threshold; run just bench-lsp"]
fn editor_latency() {
    // Same two files at every size. Each added pair is one Slot constant and
    // one fact. This intentionally stresses the uncached visible-name scan.
    for pairs in [0, 100, 1000] {
        let start = Instant::now();
        let mut client = Client::start("base/00-valid");
        let (uri, base) = client.open("example.den");
        assert_eq!(client.diagnostics(&uri), json!([]));
        let startup = start.elapsed().as_secs_f64() * 1000.0;
        let mut source = base;
        for i in 0..pairs {
            source.push_str(&format!(
                "\nconst extra_{i}: Slot;\navailable(extra_{i});\n"
            ));
        }
        let load = Instant::now();
        client.change(&uri, 2, &source);
        assert_eq!(client.diagnostics(&uri), json!([]));
        let load_ms = load.elapsed().as_secs_f64() * 1000.0;
        let definition_args = json!({"textDocument":{"uri":uri},
            "position":at(&source, "mapped_to(input_a", 0)});
        let completion_args = json!({"textDocument":{"uri":uri},
            "position":at(&source, "mapped_to(input_a, a)", "mapped_to(input_a, ".len())});
        let mut timings = vec![];
        for (method, args) in [
            ("textDocument/definition", definition_args),
            ("textDocument/completion", completion_args),
            (
                "textDocument/formatting",
                json!({"textDocument":{"uri":uri},
                "options":{"tabSize":4,"insertSpaces":true}}),
            ),
        ] {
            let mut samples = vec![];
            for round in 0..25 {
                let start = Instant::now();
                let result = client.request(method, args.clone());
                let elapsed = start.elapsed().as_secs_f64() * 1000.0;
                match method {
                    "textDocument/definition" => assert_eq!(result.as_array().unwrap().len(), 1),
                    "textDocument/completion" => {
                        let items = result["items"].as_array().unwrap();
                        assert!(items.iter().any(|item| item["label"] == "a"));
                        if pairs > 0 {
                            assert!(items
                                .iter()
                                .any(|item| item["label"] == format!("extra_{}", pairs - 1)));
                        }
                    }
                    _ => assert!(result.is_array()),
                }
                if round >= 5 {
                    samples.push(elapsed);
                }
            }
            timings.push(json!({"method":method,"timing":summary(samples)}));
        }
        let mut edits = vec![];
        for round in 0..25 {
            let changed = format!("{source}\n// observation {round}\n");
            let start = Instant::now();
            client.change(&uri, round + 3, &changed);
            let elapsed = start.elapsed().as_secs_f64() * 1000.0;
            assert_eq!(client.diagnostics(&uri), json!([]));
            if round >= 5 {
                edits.push(elapsed);
            }
        }
        println!(
            "DENOTATE_LATENCY {}",
            json!({"extra_constant_fact_pairs":pairs,
            "program_bytes":source.len(), "startup_fixture_open_ms":startup,
            "scope_load_ms":load_ms, "queries":timings,
            "full_text_change_to_validated":summary(edits)})
        );
        client.shutdown();
    }
}
