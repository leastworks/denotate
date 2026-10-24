mod support;
use serde_json::{json, Value};
use support::{apply_edits, Client};

fn params(uri: &str, source: &str, needle: &str, name: &str) -> Value {
    let prefix = &source[..source.find(needle).unwrap()];
    json!({"textDocument":{"uri":uri}, "newName":name,
        "position":{"line":prefix.bytes().filter(|b| *b == b'\n').count(),
        "character":prefix.rsplit('\n').next().unwrap().encode_utf16().count()}})
}
fn rejected(client: &mut Client, method: &str, args: Value, message: &str) {
    let reply = client.request_reply(method, args);
    assert!(reply.get("result").is_none(), "{reply}");
    assert!(
        reply["error"]["message"]
            .as_str()
            .unwrap()
            .contains(message),
        "{reply}"
    );
}
fn edits(result: &Value) -> usize {
    result["documentChanges"]
        .as_array()
        .unwrap()
        .iter()
        .map(|file| file["edits"].as_array().unwrap().len())
        .sum()
}

fn apply_file(text: &str, result: &Value, uri: &str) -> String {
    let changes: Vec<_> = result["documentChanges"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|change| change["textDocument"]["uri"] == uri)
        .collect();
    assert_eq!(
        changes.len(),
        1,
        "exactly one edit batch for {uri}: {result}"
    );
    apply_edits(text, changes[0]["edits"].as_array().unwrap())
}

#[test]
fn relation_rename_from_use_and_declaration_is_identical_and_versioned() {
    let mut client = Client::start("base/00-valid");
    assert_eq!(
        client.capabilities["renameProvider"]["prepareProvider"],
        true
    );
    let (uri, source) = client.open("example.den");
    let (lib_uri, library) = client.open("computation.den");
    let args = params(&uri, &source, "mapped_to(input_a", "mapping");
    let range = client.request("textDocument/prepareRename", args.clone());
    assert_eq!(range["start"], args["position"]);
    let result = client.request("textDocument/rename", args);
    let decl = params(&lib_uri, &library, "mapped_to(source", "mapping");
    assert_eq!(result, client.request("textDocument/rename", decl));
    assert_eq!(edits(&result), 4);
    assert_eq!(result["documentChanges"].as_array().unwrap().len(), 2);
    for change in result["documentChanges"].as_array().unwrap() {
        assert_eq!(change["textDocument"]["version"], 1);
        assert!(change["edits"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e["newText"] == "mapping"));
    }
    let renamed_library = apply_file(&library, &result, &lib_uri);
    let renamed_source = apply_file(&source, &result, &uri);
    assert_eq!(renamed_library, library.replace("mapped_to", "mapping"));
    assert_eq!(renamed_source, source.replace("mapped_to", "mapping"));
    std::fs::write(
        client.workspace.path().join("computation.den"),
        &renamed_library,
    )
    .unwrap();
    std::fs::write(client.workspace.path().join("example.den"), &renamed_source).unwrap();
    client.change(&lib_uri, 2, &renamed_library);
    client.change(&uri, 2, &renamed_source);
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert_eq!(client.diagnostics(&lib_uri), json!([]));
    client.shutdown();
}

#[test]
fn unrelated_same_spelling_and_other_constant_sorts_are_not_renamed() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    let independent = "module independent; sort Slot; relation mapped_to(value: Slot);";
    std::fs::write(client.workspace.path().join("independent.den"), independent).unwrap();
    client.open("independent.den");
    let result = client.request(
        "textDocument/rename",
        params(&uri, &source, "mapped_to(input_a", "mapping"),
    );
    assert_eq!(edits(&result), 4);
    assert!(!result.to_string().contains("independent.den"));
    let text = format!("{source}\navailable(a) :- !mapped_to(input_a, a);\n");
    client.change(&uri, 2, &text);
    let result = client.request(
        "textDocument/rename",
        params(&uri, &text, "mapped_to(input_a", "mapping"),
    );
    assert_eq!(edits(&result), 5, "negative use included");
    // A Slot constant may take an existing Source constant's spelling.
    let result = client.request(
        "textDocument/rename",
        params(&uri, &text, "a, b, result", "input_a"),
    );
    assert!(edits(&result) >= 4);
    client.shutdown();
}

#[test]
fn constants_keep_sort_identity_and_variables_stay_rule_local() {
    let mut client = Client::start("base/10-typed-constants");
    let (uri, source) = client.open("example.den");
    let result = client.request(
        "textDocument/rename",
        params(&uri, &source, "shared, shared", "renamed"),
    );
    assert_eq!(
        edits(&result),
        2,
        "only Source declaration and use: {result}"
    );
    assert_eq!(result["documentChanges"].as_array().unwrap().len(), 1);
    let renamed_source = apply_file(&source, &result, &uri);
    assert_eq!(
        renamed_source,
        source
            .replace("const shared: Source;", "const renamed: Source;")
            .replace("mapped_to(shared, shared);", "mapped_to(renamed, shared);")
    );
    let (lib_uri, library) = client.open("computation.den");
    let result = client.request(
        "textDocument/rename",
        params(&lib_uri, &library, "D) :-\n    mapped_to", "SlotValue"),
    );
    assert_eq!(
        edits(&result),
        3,
        "head, mapped_to and masked in one rule: {result}"
    );
    assert_eq!(result["documentChanges"].as_array().unwrap().len(), 1);
    let renamed_library = apply_file(&library, &result, &lib_uri);
    assert_eq!(renamed_library, library.replace(
        "supplies(S, D) :-\n    mapped_to(S, D),\n    present(S),\n    !masked(D);",
        "supplies(S, SlotValue) :-\n    mapped_to(S, SlotValue),\n    present(S),\n    !masked(SlotValue);"));
    for name in ["a", "_", "use", "bad-name"] {
        rejected(
            &mut client,
            "textDocument/rename",
            params(&lib_uri, &library, "D) :-\n    mapped_to", name),
            "lexical class",
        );
    }
    for name in ["D", "_", "module"] {
        rejected(
            &mut client,
            "textDocument/rename",
            params(&uri, &source, "shared, shared", name),
            "lexical class",
        );
    }
    rejected(
        &mut client,
        "textDocument/rename",
        params(&lib_uri, &library, "D) :-\n    mapped_to", "S"),
        "collide",
    );
    rejected(
        &mut client,
        "textDocument/rename",
        params(&uri, &source, "shared, shared", "input_a"),
        "collide",
    );
    rejected(
        &mut client,
        "textDocument/prepareRename",
        params(&lib_uri, &library, "_, D", "X"),
        "_ has no rename target",
    );
    std::fs::write(client.workspace.path().join("example.den"), &renamed_source).unwrap();
    std::fs::write(
        client.workspace.path().join("computation.den"),
        &renamed_library,
    )
    .unwrap();
    client.change(&uri, 2, &renamed_source);
    client.change(&lib_uri, 2, &renamed_library);
    assert_eq!(client.diagnostics(&uri), json!([]));
    assert_eq!(client.diagnostics(&lib_uri), json!([]));
    client.shutdown();
}

#[test]
fn sort_and_input_rename_work_but_capture_and_module_rename_are_rejected() {
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("computation.den");
    for method in ["textDocument/prepareRename", "textDocument/rename"] {
        rejected(
            &mut client,
            method,
            params(&uri, &source, "source: Source", "origin"),
            "Parameter rename is not supported",
        );
        rejected(
            &mut client,
            method,
            params(&uri, &source, "_, D", "X"),
            "_ has no rename target",
        );
    }
    let signature_sort = client.request(
        "textDocument/rename",
        params(&uri, &source, "Source, slot", "Origin"),
    );
    assert!(
        edits(&signature_sort) > 1,
        "sort references within parameters still support rename"
    );
    let result = client.request(
        "textDocument/rename",
        params(&uri, &source, "Slot;", "Cell"),
    );
    assert!(edits(&result) > 3);
    let result = client.request(
        "textDocument/rename",
        params(&uri, &source, "present(source", "observed"),
    );
    assert_eq!(edits(&result), 2);
    rejected(
        &mut client,
        "textDocument/rename",
        params(&uri, &source, "Slot;", "Source"),
        "collide",
    );
    rejected(
        &mut client,
        "textDocument/rename",
        params(&uri, &source, "mapped_to(source", "available"),
        "collide",
    );
    rejected(
        &mut client,
        "textDocument/prepareRename",
        params(&uri, &source, "computation;", "other"),
        "module rename",
    );
    client.shutdown();
}

#[test]
fn unrelated_validation_errors_do_not_block_rename() {
    let mut client = Client::start("base/00-valid");
    client.file_watcher_registration();
    let (uri, source) = client.open("example.den");
    // Variables avoid an additional constant-linking failure in the extra
    // argument, isolating arity from the linking errors that still block rename.
    let other = "module wrong; use computation; sort Extra; sort Extra; masked(A, A);";
    let path = client.workspace.path().join("other.den");
    std::fs::write(&path, other).unwrap();
    let other_uri = support::file_uri(&path);
    client.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":other_uri,"type":1}]}),
    );
    client.validated(&other_uri, 0);
    let diagnostics = client.diagnostics(&other_uri).to_string();
    for message in [
        "expects 1 argument",
        "Duplicate declaration",
        "must match filename",
    ] {
        if message == "must match filename"
            && std::env::var("DENOTATE_BACKEND").as_deref() == Ok("tree-sitter")
        {
            assert!(
                !diagnostics.contains(message),
                "B namespaces are independent of filenames"
            );
        } else {
            assert!(diagnostics.contains(message), "{diagnostics}");
        }
    }
    let args = params(&uri, &source, "mapped_to(input_a", "mapping");
    client.request("textDocument/prepareRename", args.clone());
    let result = client.request("textDocument/rename", args);
    assert_eq!(edits(&result), 4);
    assert!(!result.to_string().contains("other.den"));
    client.shutdown();
}

#[test]
fn ambiguous_or_incomplete_workspaces_never_get_partial_rename() {
    let mut client = Client::start("base/07-ambiguous-import");
    let (uri, source) = client.open("example.den");
    rejected(
        &mut client,
        "textDocument/rename",
        params(&uri, &source, "masked(", "renamed"),
        "unambiguous",
    );
    client.shutdown();
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    client.change(&uri, 2, &format!("{source}\nunknown(a);"));
    rejected(
        &mut client,
        "textDocument/rename",
        params(&uri, &source, "mapped_to(input_a", "mapping"),
        "Repair diagnostics",
    );
    client.shutdown();
}

#[cfg(unix)]
#[test]
fn protected_declaration_or_consumer_rejects_prepare_and_rename() {
    use std::os::unix::fs::PermissionsExt;
    let mut client = Client::start("base/00-valid");
    let (uri, source) = client.open("example.den");
    for file in ["computation.den", "example.den"] {
        let path = client.workspace.path().join(file);
        let original = std::fs::metadata(&path).unwrap().permissions();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o444)).unwrap();
        for method in ["textDocument/prepareRename", "textDocument/rename"] {
            rejected(
                &mut client,
                method,
                params(&uri, &source, "mapped_to(input_a", "mapping"),
                "read-only",
            );
        }
        std::fs::set_permissions(&path, original).unwrap();
    }
    client.shutdown();
}

#[test]
fn generated_and_external_files_are_not_rename_targets() {
    let mut client = Client::start("base/00-valid");
    std::fs::create_dir(client.workspace.path().join("generated")).unwrap();
    let source = "module extra; sort Slot; relation r(value: Slot);";
    std::fs::write(client.workspace.path().join("generated/extra.den"), source).unwrap();
    let (uri, _) = client.open("generated/extra.den");
    rejected(
        &mut client,
        "textDocument/rename",
        params(&uri, source, "r(value", "renamed"),
        "generated",
    );
    let external = tempfile::tempdir().unwrap();
    let path = external.path().join("extra.den");
    std::fs::write(&path, source).unwrap();
    let (uri, _) = client.open(path.to_str().unwrap());
    rejected(
        &mut client,
        "textDocument/prepareRename",
        params(&uri, source, "r(value", "renamed"),
        "outside the workspace",
    );
    client.shutdown();
}
