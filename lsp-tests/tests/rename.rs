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
        client.request(
            "textDocument/rename",
            params(&lib_uri, &library, "D) :-\n    mapped_to", name),
        );
    }
    for name in ["D", "_", "module"] {
        client.request(
            "textDocument/rename",
            params(&uri, &source, "shared, shared", name),
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
        client.request(method, params(&uri, &source, "source: Source", "origin"));

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
    client.request(
        "textDocument/prepareRename",
        params(&uri, &source, "computation;", "other"),
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
        if message == "must match filename" {
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

#[test]
fn full_ir_rename_quotes_by_kind_and_covers_contracts_domains_helpers_and_aliases() {
    let mut c = Client::start("base/00-valid");
    let (uri, _) = c.open("example.den");
    let text = r#"namespace 'a::b' {
sort S; const a, 1:S;
input p(x:S, y:S); relation r(x:S, y:S);
relation $gate(); relation '$gate'(); $gate(); '$gate'();
r(a,1); r(X,Y) :- p(X,Y);
domain S=[a,1];
obligation unique: at_most_one(r, group_by: (x));
assumption inputs: at_most_one(p, group_by: (x));
#src=source("file:///a/r/x.testdsl",view:"r",hash:"sha256:0000000000000000000000000000000000000000000000000000000000000000");
#origin=loc(#src 1:1 to 1:2);
r(a,1) loc(#origin);
}
namespace consumer { use 'a::b'; 'a::b'::r('a::b'::a, 'a::b'::1); }
"#;
    c.change(&uri, 2, text);
    let mut version = 2;
    for (needle, name, replacement, count) in [
        ("r(x:S", "two words", "'two words'", 6),
        ("a, 1:S", "I", "'I'", 5),
        ("1:S", "007", "'007'", 5),
        ("X,Y", "lower case", "?'lower case'", 2),
        ("$gate();", "$condition_2", "$condition_2", 2),
        ("'$gate'();", "$condition_2", "'$condition_2'", 2),
        ("x:S, y:S); relation", "input slot", "'input slot'", 2),
        ("#src=", "renamed", "#renamed", 2),
        ("#origin=", "#renamed", "#renamed", 2),
        ("unique:", "new obligation", "'new obligation'", 1),
    ] {
        let result = c.request("textDocument/rename", params(&uri, text, needle, name));
        assert_eq!(edits(&result), count, "{needle}: {result}");
        assert!(result["documentChanges"][0]["edits"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e["newText"] == replacement));
        let changed = apply_file(text, &result, &uri);
        assert!(changed.contains("file:///a/r/x.testdsl"));
        assert!(changed.contains("view:\"r\""));
        assert!(changed.contains("1:1 to 1:2"));
        version += 1;
        c.change(&uri, version, &changed);
        // Validate the actual applied version, then reset for the next independent rename.
        let errors = c.diagnostics(&uri).to_string();
        assert!(
            !errors.contains("denotate-syntax") && !errors.contains("resolution"),
            "{changed}\n{errors}"
        );
        version += 1;
        c.change(&uri, version, text);
    }
    c.shutdown();
}

fn root_files(c: &mut Client, files: &[(&str, &str)]) {
    for (file, text) in files {
        let path = c.workspace.path().join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    let changes = files
        .iter()
        .map(|(f, _)| json!({"uri":support::file_uri(&c.workspace.path().join(f)),"type":1}))
        .collect::<Vec<_>>();
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":changes}),
    );
    c.request("denotate/test/idle", Value::Null);
}

#[test]
fn shared_library_rename_includes_all_consumers_and_rejects_untouched_reference_capture() {
    let mut c = Client::start("base/00-valid");
    let lib = "namespace shared; relation r(); r();";
    let a = "namespace a; shared::r();";
    let b = "namespace b; use shared; relation q(); q(); shared::r();";
    root_files(
        &mut c,
        &[
            ("lib/den.root", "{}"),
            ("lib/code.den", lib),
            ("a/den.root", r#"{"libraries":["../lib/den.root"]}"#),
            ("a/code.den", a),
            ("b/den.root", r#"{"libraries":["../lib/den.root"]}"#),
            ("b/code.den", b),
            ("other/den.root", "{}"),
            ("other/code.den", "namespace other; broken(;"),
        ],
    );
    let (a_uri, _) = c.open("a/code.den");
    let (lib_uri, _) = c.open("lib/code.den");
    let b_uri = support::file_uri(&c.workspace.path().join("b/code.den"));
    // B is unopened, but its unedited q() would become ambiguous after r -> q.
    let mut args = params(&a_uri, a, "shared::r", "q");
    args["position"]["character"] = json!(a.find("shared::r").unwrap() + 8);
    rejected(&mut c, "textDocument/rename", args.clone(), "collide");
    args["newName"] = json!("renamed");
    let result = c.request("textDocument/rename", args);
    assert_eq!(edits(&result), 4);
    assert_eq!(result["documentChanges"].as_array().unwrap().len(), 3);
    assert_eq!(
        apply_file(lib, &result, &lib_uri),
        lib.replace("r()", "renamed()")
    );
    assert_eq!(
        apply_file(a, &result, &a_uri),
        a.replace("shared::r", "shared::renamed")
    );
    assert_eq!(
        apply_file(b, &result, &b_uri),
        b.replace("shared::r", "shared::renamed")
    );
    let closed = result["documentChanges"]
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["textDocument"]["uri"] == b_uri)
        .unwrap();
    assert!(closed["textDocument"]["version"].is_null());
    // Damage in a consumer must block a library rename even when its home is clean.
    let (b_uri, _) = c.open("b/code.den");
    c.change(&b_uri, 2, "namespace b; shared::r(");
    rejected(
        &mut c,
        "textDocument/prepareRename",
        params(&lib_uri, lib, "r();", "renamed"),
        "Repair diagnostics",
    );
    c.change(&b_uri, 3, b);
    c.notify("textDocument/didChange",json!({"textDocument":{"uri":b_uri,"version":4},"contentChanges":[{"range":{"start":{"line":0,"character":5},"end":{"line":0,"character":1}},"text":"x"}]}));
    rejected(
        &mut c,
        "textDocument/rename",
        params(&lib_uri, lib, "r();", "renamed"),
        "out of sync",
    );
    c.change(&b_uri, 5, b);
    c.request(
        "textDocument/rename",
        params(&lib_uri, lib, "r();", "renamed"),
    );
    c.shutdown();
}

#[test]
fn namespace_segment_rename_covers_split_nested_reopened_and_qualified_paths() {
    let mut c = Client::start("base/00-valid");
    let first = "namespace alpha { namespace child { relation r(); r(); } } namespace alpha::child { relation q(); }";
    let second = "namespace user; use alpha::child; alpha::child::r(); ::alpha::child::q();";
    root_files(
        &mut c,
        &[
            ("ns/den.root", "{}"),
            ("ns/first.den", first),
            ("ns/second.den", second),
        ],
    );
    let (uri, _) = c.open("ns/first.den");
    let (other, _) = c.open("ns/second.den");
    let result = c.request(
        "textDocument/rename",
        params(&uri, first, "alpha {", "new::name"),
    );
    assert_eq!(
        apply_file(first, &result, &uri),
        first.replace("alpha", "'new::name'")
    );
    assert_eq!(
        apply_file(second, &result, &other),
        second.replace("alpha", "'new::name'")
    );
    let result = c.request(
        "textDocument/rename",
        params(&uri, first, "child {", "leaf"),
    );
    assert_eq!(
        apply_file(first, &result, &uri),
        first.replace("child", "leaf")
    );
    assert_eq!(
        apply_file(second, &result, &other),
        second.replace("child", "leaf")
    );
    let quoted = "namespace 'a::b' { relation r(); } 'a::b'::r();";
    c.change(&uri, 2, quoted);
    c.change(&other, 2, "namespace unused;");
    let result = c.request(
        "textDocument/rename",
        params(&uri, quoted, "'a::b' {", "é'new"),
    );
    assert_eq!(
        apply_file(quoted, &result, &uri),
        quoted.replace("'a::b'", "'é\\'new'")
    );
    let collision = "namespace a { relation r(); } namespace b { relation q(); }";
    c.change(&uri, 3, collision);
    rejected(
        &mut c,
        "textDocument/rename",
        params(&uri, collision, "a {", "b"),
        "collide",
    );
    c.shutdown();
}

#[test]
fn aliases_are_file_local_and_parameters_follow_their_relations_grouping_references() {
    let mut c = Client::start("base/00-valid");
    let file = r#"namespace n;
sort S; const a:S; relation r(x:S, y:S); input p(x:S, y:S);
obligation o: at_most_one(r, group_by: (x));
assumption w: at_most_one(p, group_by: (x));
#s=source("file:///source.dsl",view:"dsl",hash:"sha256:0000000000000000000000000000000000000000000000000000000000000000");
#map=loc(#s 1:1 to 1:2); r(a,a) loc(#map);
"#;
    root_files(
        &mut c,
        &[
            ("local/den.root", "{}"),
            ("local/one.den", file),
            (
                "local/two.den",
                &file.replace("namespace n;", "namespace other;"),
            ),
        ],
    );
    let (uri, _) = c.open("local/one.den");
    let result = c.request("textDocument/rename", params(&uri, file, "#s=", "source2"));
    assert_eq!(edits(&result), 2);
    assert_eq!(result["documentChanges"].as_array().unwrap().len(), 1);
    let result = c.request(
        "textDocument/rename",
        params(&uri, file, "x:S, y:S); input", "column"),
    );
    assert_eq!(edits(&result), 2);
    let changed = apply_file(file, &result, &uri);
    assert!(changed.contains("relation r(column:S, y:S)"));
    assert!(changed.contains("at_most_one(r, group_by: (column))"));
    assert!(changed.contains("at_most_one(p, group_by: (x))"));
    for (needle, name) in [("x:S, y:S); input", "y"), ("#map=", "#s")] {
        rejected(
            &mut c,
            "textDocument/rename",
            params(&uri, file, needle, name),
            "collide",
        );
    }
    c.shutdown();
}

#[test]
fn damaged_manifests_and_read_only_consumers_prevent_partial_renames() {
    let mut c = Client::start("base/00-valid");
    let lib = "namespace shared; relation r();";
    root_files(
        &mut c,
        &[
            ("lib/den.root", "{}"),
            ("lib/lib.den", lib),
            ("app/den.root", r#"{"libraries":["../lib/den.root"]}"#),
            ("app/app.den", "shared::r();"),
        ],
    );
    let (uri, _) = c.open("lib/lib.den");
    let manifest = support::file_uri(&c.workspace.path().join("app/den.root"));
    c.notify(
        "denotate/manifest",
        json!({"uri":manifest,"text":"{","version":1}),
    );
    rejected(
        &mut c,
        "textDocument/rename",
        params(&uri, lib, "r();", "new"),
        "manifest",
    );
    c.notify(
        "denotate/manifest",
        json!({"uri":manifest,"text":r#"{"libraries":["../lib/den.root"]}"#,"version":2}),
    );
    c.request("textDocument/rename", params(&uri, lib, "r();", "new"));
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let path = c.workspace.path().join("app/app.den");
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o444)).unwrap();
        rejected(
            &mut c,
            "textDocument/prepareRename",
            params(&uri, lib, "r();", "new"),
            "read-only",
        );
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o644)).unwrap();
    }
    c.shutdown();
}
