mod support;
use serde_json::{json, Value};
use support::Client;

fn errors(client: &Client, uri: &str) -> Vec<Value> {
    client
        .diagnostics(uri)
        .as_array()
        .unwrap()
        .iter()
        .filter(|diagnostic| diagnostic["severity"] == 1)
        .cloned()
        .collect()
}

fn line_of(source: &str, needle: &str) -> usize {
    source[..source.find(needle).unwrap()]
        .bytes()
        .filter(|b| *b == b'\n')
        .count()
}

#[test]
fn input_relation_facts_and_rule_heads_are_rejected_and_repair_clears_errors() {
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/11-input-definitions");
    let (uri, source) = client.open("example.den");
    let diagnostics = errors(&client, &uri);
    assert_eq!(
        diagnostics.len(),
        2,
        "both the input fact and input rule head must fail"
    );
    for needle in ["present(input_a);", "present(S) :-"] {
        assert!(
            diagnostics
                .iter()
                .any(|d| d["range"]["start"]["line"] == line_of(&source, needle)
                    && d["message"]
                        .as_str()
                        .unwrap()
                        .to_lowercase()
                        .contains("input")
                    && d["message"].as_str().unwrap().contains("present")),
            "{diagnostics:?}"
        );
    }
    // Moving both producers to a derived relation fixes them; reading present
    // as a body predicate remains permitted.
    let repaired = source
        .replace("present(input_a);", "seen(input_a);")
        .replace("present(S) :-", "seen(S) :-")
        + "\nrelation seen(source: Source);\nseen(S) :- present(S);\n";
    client.change(&uri, 2, &repaired);
    assert!(errors(&client, &uri).is_empty());
    client.change(&uri, 3, &source);
    assert_eq!(
        errors(&client, &uri).len(),
        2,
        "reintroducing input definitions restores errors"
    );
    client.shutdown();
}

#[test]
fn unsafe_head_and_negative_variables_need_rule_local_positive_support() {
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/16-variable-binding");
    let (uri, source) = client.open("example.den");
    let diagnostics = errors(&client, &uri);
    assert_eq!(
        diagnostics.len(),
        2,
        "safe rules and fresh wildcards must not be rejected"
    );
    for (needle, variable) in [
        ("given(D) :- present(S);", "D"),
        ("given(D) :- supplies(S, D), !mapped_to(Other, D);", "Other"),
    ] {
        assert!(
            diagnostics
                .iter()
                .any(|d| d["range"]["start"]["line"] == line_of(&source, needle)
                    && d["message"].as_str().unwrap().contains(variable)),
            "{diagnostics:?}"
        );
    }
    let repaired = source
        .replace("given(D) :- present(S);", "given(D) :- supplies(S, D);")
        .replace("!mapped_to(Other, D)", "!mapped_to(S, D)");
    client.change(&uri, 2, &repaired);
    assert!(errors(&client, &uri).is_empty());
    client.change(&uri, 3, &source);
    assert_eq!(errors(&client, &uri).len(), 2);
    client.shutdown();
}

#[test]
fn singleton_warning_clears_for_correction_or_deliberate_wildcard() {
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/08-singleton-variable");
    let (uri, source) = client.open("computation.den");
    let diagnostics = client.diagnostics(&uri);
    let warnings: Vec<_> = diagnostics
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["severity"] == 2)
        .collect();
    assert_eq!(
        warnings.len(),
        1,
        "only the singleton Ss, not the separate rule's Ss"
    );
    assert!(warnings[0]["message"].as_str().unwrap().contains("Ss"));
    for (version, replacement) in [(2, "present(S),"), (3, "present(_),")] {
        // Correcting the typo and choosing an existential wildcard have distinct
        // meanings, but neither should retain a named-singleton warning.
        client.change(&uri, version, &source.replace("present(Ss),", replacement));
        assert_eq!(client.diagnostics(&uri), json!([]));
    }
    client.shutdown();
}
