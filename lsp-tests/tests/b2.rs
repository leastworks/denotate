mod support;
use serde_json::{json, Value};
use support::Client;

fn position(source: &str, needle: &str, offset: usize) -> Value {
    let prefix = &source[..source.find(needle).unwrap() + offset];
    json!({"line": prefix.bytes().filter(|b| *b == b'\n').count(),
        "character": prefix.rsplit('\n').next().unwrap().encode_utf16().count()})
}

fn definition(client: &mut Client, uri: &str, source: &str, needle: &str, offset: usize) -> Value {
    client.request(
        "textDocument/definition",
        json!({"textDocument": {"uri": uri},
        "position": position(source, needle, offset)}),
    )
}

#[test]
fn module_and_sort_lookup_work_before_opening_library_and_in_incomplete_text() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let library = std::fs::read_to_string(client.workspace.path().join("computation.den")).unwrap();
    for (needle, offset, target, target_offset) in [
        ("use computation", 4, "module computation", 7),
        (": Source", 2, "sort Source", 5),
        (": Slot", 2, "sort Slot", 5),
    ] {
        let result = definition(&mut client, &uri, &source, needle, offset);
        assert_eq!(result.as_array().unwrap().len(), 1);
        assert!(result[0]["targetUri"]
            .as_str()
            .unwrap()
            .ends_with("computation.den"));
        assert_eq!(
            result[0]["targetSelectionRange"]["start"],
            position(&library, target, target_offset)
        );
    }
    for (version, suffix, expected, absent) in [
        (2, "use comp", "computation", "Source"),
        (3, "relation extra(x: Sl", "Slot", "Source"),
    ] {
        let text = format!("{source}\n{suffix}");
        client.change(&uri, version, &text);
        let result = client.request(
            "textDocument/completion",
            json!({"textDocument": {"uri": uri},
            "position": position(&text, suffix, suffix.len())}),
        );
        let items = result
            .as_array()
            .or_else(|| result["items"].as_array())
            .unwrap();
        assert!(items.iter().any(|i| i["label"] == expected), "{result}");
        assert!(!items.iter().any(|i| i["label"] == absent), "{result}");
    }
    client.shutdown();
}

#[test]
fn deleted_and_recreated_unopened_import_updates_navigation_and_completion() {
    let mut client = Client::start("base/07-ambiguous-import");
    let (uri, source) = client.open("example.den");
    let right_path = client.workspace.path().join("right.den");
    let right = std::fs::read_to_string(&right_path).unwrap();
    for phase in 0..3 {
        if phase == 1 {
            std::fs::remove_file(&right_path).unwrap();
            client.watched_change("right.den", 3, &uri, 1);
        } else if phase == 2 {
            std::fs::write(&right_path, &right).unwrap();
            client.watched_change("right.den", 1, &uri, 1);
        }
        let result = definition(&mut client, &uri, &source, "masked(a)", 0);
        if phase == 1 {
            assert_eq!(result.as_array().unwrap().len(), 1);
            assert!(result[0]["targetUri"]
                .as_str()
                .unwrap()
                .ends_with("left.den"));
        } else {
            assert!(result.is_null() || result.as_array().is_some_and(|a| a.is_empty()));
        }
        // Successful completion must not materialize a deleted declaration.
        let result = client.request(
            "textDocument/completion",
            json!({"textDocument": {"uri": uri},
            "position": position(&source, "masked(a)", 0)}),
        );
        let items = result
            .as_array()
            .or_else(|| result["items"].as_array())
            .unwrap();
        assert!(items.iter().any(|i| i["label"] == "masked"));
    }
    client.shutdown();
}
