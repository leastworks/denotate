mod support;
use serde_json::{json, Value};
use support::Client;

fn stats(client: &mut Client) -> Value {
    client.request("denotate/test/analysis", json!({}))
}

fn definition(client: &mut Client, uri: &str, source: &str) -> Value {
    let prefix = &source[..source.find("mapped_to(input_a").unwrap()];
    client.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri}, "position": {
                "line": prefix.bytes().filter(|b| *b == b'\n').count(),
                "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()
            }
        }),
    )
}

#[test]
fn native_relation_queries_reuse_semantics_and_refresh_source_ranges() {
    // A1 still runs the frozen suite, but has no native-counter contract.
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    let target = definition(&mut client, &uri, &source);
    assert_eq!(target.as_array().unwrap().len(), 1);
    let before = stats(&mut client);
    assert_eq!(before["backend"], "rust");
    assert!(before["relationQueryExecutions"].as_u64().unwrap() > 0);
    assert_eq!(definition(&mut client, &uri, &source), target);
    assert_eq!(
        stats(&mut client)["relationQueryExecutions"],
        before["relationQueryExecutions"]
    );

    client.change(&lib_uri, 2, &format!("// New comment 🦀\n{library}"));
    let moved = definition(&mut client, &uri, &source);
    assert_eq!(moved[0]["targetUri"], target[0]["targetUri"]);
    assert_eq!(
        moved[0]["targetSelectionRange"]["start"]["line"]
            .as_u64()
            .unwrap(),
        target[0]["targetSelectionRange"]["start"]["line"]
            .as_u64()
            .unwrap()
            + 1
    );
    let after = stats(&mut client);
    assert!(after["projections"].as_u64().unwrap() > before["projections"].as_u64().unwrap());
    assert_eq!(
        after["relationQueryExecutions"], before["relationQueryExecutions"],
        "trivia changes spans, not Salsa semantic inputs"
    );

    // A rule-body edit also leaves relation declarations/imports unchanged.
    client.change(
        &lib_uri,
        3,
        &library.replace("supplies(_, D)", "supplies(S, D)"),
    );
    definition(&mut client, &uri, &source);
    assert_eq!(
        stats(&mut client)["relationQueryExecutions"],
        before["relationQueryExecutions"]
    );

    // Semantic change must invalidate, not preserve a last-good target.
    client.change(&lib_uri, 4, &library.replace("mapped_to", "mapping"));
    let absent = definition(&mut client, &uri, &source);
    assert!(absent.is_null() || absent.as_array().is_some_and(|items| items.is_empty()));
    assert!(
        stats(&mut client)["relationQueryExecutions"]
            .as_u64()
            .unwrap()
            > before["relationQueryExecutions"].as_u64().unwrap()
    );
    client.change(&lib_uri, 5, &library);
    assert_eq!(definition(&mut client, &uri, &source), target);
    client.shutdown();
}

#[test]
fn signature_edits_refresh_editor_help_without_invalidating_relation_visibility() {
    if std::env::var("DENOTATE_BACKEND").as_deref() == Ok("langium") {
        return;
    }
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    let before = stats(&mut client);
    let prefix = &source[..source.find("mapped_to(input_a").unwrap()];
    let position = json!({
        "line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count() + 18
    });
    for (index, (text, expected)) in [
        (
            library.replace("relation mapped_to", "input mapped_to"),
            Some("mapped_to(source: Source, slot: Slot)"),
        ),
        (
            library.replace("source: Source, slot: Slot", "source: Source, slot: Source"),
            Some("mapped_to(source: Source, slot: Source)"),
        ),
        (
            library.replace("source: Source, slot: Slot", "source: Source, slot: "),
            None,
        ),
        (
            library.clone(),
            Some("mapped_to(source: Source, slot: Slot)"),
        ),
    ]
    .iter()
    .enumerate()
    {
        assert!(
            *text != library || index == 3,
            "edit must change the declaration"
        );
        client.change(&lib_uri, (index + 2) as i64, text);
        assert_eq!(
            definition(&mut client, &uri, &source)
                .as_array()
                .unwrap()
                .len(),
            1
        );
        let help = client.request(
            "textDocument/signatureHelp",
            json!({
                "textDocument": {"uri": uri}, "position": position
            }),
        );
        match expected {
            Some(label) => assert_eq!(help["signatures"][0]["label"], *label),
            None => assert!(
                help.is_null()
                    || help["signatures"]
                        .as_array()
                        .is_some_and(|items| items.is_empty())
            ),
        }
        assert_eq!(
            stats(&mut client)["relationQueryExecutions"],
            before["relationQueryExecutions"],
            "signature and kind are not inputs to relation visibility"
        );
    }
    assert!(
        stats(&mut client)["projections"].as_u64().unwrap()
            > before["projections"].as_u64().unwrap()
    );
    client.shutdown();
}
