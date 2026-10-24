//! Step-3 B services for the full text format. A keeps its module/file grammar.
#[allow(dead_code)]
mod support;
use serde_json::{json, Value};
use support::Client;
fn position(text: &str, needle: &str, delta: usize) -> Value {
    let p = &text[..text.find(needle).unwrap() + delta];
    json!({"line":p.bytes().filter(|b|*b==b'\n').count(),"character":p.rsplit('\n').next().unwrap().encode_utf16().count()})
}
fn query(c: &mut Client, method: &str, uri: &str, text: &str, needle: &str, delta: usize) -> Value {
    c.request(method,json!({"textDocument":{"uri":uri},"position":position(text,needle,delta),"context":{"includeDeclaration":true}}))
}
/// Only B implements the full text format; A's shared runs skip these scenarios.
fn b_only() -> bool {
    std::env::var("DENOTATE_BACKEND").as_deref() == Ok("tree-sitter")
}
#[test]
fn namespaces_quoted_names_helpers_domains_contracts_and_locations_use_one_index() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("base/00-valid");
    let (uri, _) = c.open("example.den");
    let text = r#"namespace a {
 sort S; const '007', 7:S;
 relation r(x:S); input p(x:S);
 relation $gate(); $gate();
 r('007'); r(007);
}
namespace a { relation s(x:S); }
namespace a::nested { relation z(); }
namespace b {
 use a;
 relation q(x:a::S);
 q(X) :- a::r(X), a::p(X), a::$gate();
 domain a::S=[a::'007', a::7];
 obligation unique: at_most_one(q, group_by: x);
 assumption known: at_most_one(a::p, group_by: (x));
 #source = source("file:///source.inputmapping", view: "dsl", hash: "sha256:0000000000000000000000000000000000000000000000000000000000000000");
 #origin = loc(#source 1:1 to 1:2);
 q('007') loc(#source {self: 1:1 to 1:2, head.0: 1:1 to 1:2});
 q(7) loc(#origin);
}
"#;
    c.change(&uri, 2, text);
    assert_eq!(c.diagnostics(&uri), json!([]));
    for (needle, offset, target) in [
        ("a::r(X)", 0, "relation r"),
        ("a::$gate()", 0, "relation $gate"),
        ("a::'007'", 0, "const '007'"),
        ("a::7", 0, "7:S"),
        ("group_by: x", 10, "q(x:a::S)"),
        ("loc(#origin)", 4, "#origin ="),
    ] {
        let result = query(
            &mut c,
            "textDocument/definition",
            &uri,
            text,
            needle,
            offset,
        );
        assert_eq!(result.as_array().unwrap().len(), 1, "{needle}: {result}");
        let expected = match target {
            "relation r" => 9,
            "relation $gate" => 9,
            "const '007'" => 6,
            "q(x:a::S)" => 2,
            _ => 0,
        };
        assert_eq!(
            result[0]["targetSelectionRange"]["start"],
            position(text, target, expected),
            "{needle}"
        );
    }
    let namespace = query(&mut c, "textDocument/definition", &uri, text, "use a", 4);
    assert_eq!(
        namespace.as_array().unwrap().len(),
        2,
        "reopened namespace definitions"
    );
    let namespace_refs = query(&mut c, "textDocument/references", &uri, text, "use a", 4);
    assert_eq!(
        namespace_refs.as_array().unwrap().len(),
        3,
        "both declarations and the use"
    );
    let aliases = query(
        &mut c,
        "textDocument/completion",
        &uri,
        text,
        "loc(#origin)",
        6,
    );
    assert!(aliases["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["textEdit"]["newText"] == "#origin"));
    let namespaces = query(&mut c, "textDocument/completion", &uri, text, "use a", 5);
    assert!(namespaces["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["textEdit"]["newText"] == "a::nested"));
    let help = query(
        &mut c,
        "textDocument/signatureHelp",
        &uri,
        text,
        "q('007')",
        6,
    );
    assert_eq!(help["signatures"][0]["label"], "q(x: S)");
    let refs = query(
        &mut c,
        "textDocument/references",
        &uri,
        text,
        "relation r",
        9,
    );
    assert_eq!(refs.as_array().unwrap().len(), 4);
    let hover = query(&mut c, "textDocument/hover", &uri, text, "a::'007'", 0);
    assert!(hover["contents"]["value"].as_str().unwrap().contains("007"));
    let completion = query(&mut c, "textDocument/completion", &uri, text, "q('007')", 2);
    assert!(completion["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["textEdit"]["newText"] == "'007'"));
    let symbols = c.request(
        "textDocument/documentSymbol",
        json!({"textDocument":{"uri":uri}}),
    );
    assert_eq!(symbols.as_array().unwrap().len(), 4);
    assert!(!symbols[0]["children"].as_array().unwrap().is_empty());
    let guarded = c.request_reply(
        "textDocument/prepareRename",
        json!({"textDocument":{"uri":uri},"position":position(text,"relation r",9)}),
    );
    assert!(guarded["error"]["message"]
        .as_str()
        .unwrap()
        .contains("stage 6"));
    c.shutdown();
}
#[test]
fn no_manifest_means_standalone_even_when_use_names_a_workspace_file() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("ir-text/standalone");
    let (uri, text) = c.open("example.den");
    let diagnostics = c.diagnostics(&uri).to_string();
    assert!(diagnostics.contains("Unknown namespace 'library'"));
    assert!(diagnostics.contains("Unknown relation 'library::r'"));
    assert_eq!(
        query(
            &mut c,
            "textDocument/definition",
            &uri,
            &text,
            "library::r",
            0
        ),
        json!([])
    );
    let (library, _) = c.open("library.den");
    assert_eq!(c.diagnostics(&library), json!([]));
    c.shutdown();
}

#[test]
fn export_folder_without_direct_den_children_loads_sources_and_library() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("ir-text/export-layout");
    let (uri, text) = c.open("sources/example.den");
    assert_eq!(c.diagnostics(&uri), json!([]));
    let definition = query(&mut c, "textDocument/definition", &uri, &text, "r(a)", 0);
    assert_eq!(definition.as_array().unwrap().len(), 1);
    assert_eq!(
        definition[0]["targetUri"],
        support::file_uri(&c.workspace.path().join("library/library.den"))
    );
    let hover = query(&mut c, "textDocument/hover", &uri, &text, "r(a)", 0);
    assert_eq!(hover["contents"]["value"], "relation r(x: S)");
    c.shutdown();
}

fn roots(c: &mut Client, uri: &str) -> Value {
    c.request("denotate/roots", json!({"uri":uri}))
}
fn watched(c: &mut Client, uri: &str, typ: u8) {
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":uri,"type":typ}]}),
    );
    c.request("denotate/test/idle", Value::Null);
}
fn manifest(c: &mut Client, uri: &str, text: &str, version: i64) {
    c.notify(
        "denotate/manifest",
        json!({"uri":uri,"text":text,"version":version}),
    );
    c.request("denotate/test/idle", Value::Null);
}
#[test]
fn home_programs_unsaved_manifests_cycles_nested_boundaries_and_independent_failures() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("ir-text/standalone");
    let base = c.workspace.path().to_owned();
    for (path, text) in [
        ("a/den.root", r#"{"libraries":["../lib/den.root"]}"#),
        ("b/den.root", r#"{"libraries":["../lib/den.root"]}"#),
        ("lib/den.root", "{}"),
        ("a/nested/den.root", "{}"),
        ("a/a.den", "namespace a; relation a(); a();"),
        ("b/b.den", "namespace b; relation b(); b();"),
        ("lib/lib.den", "namespace lib; relation r(); r();"),
        ("a/nested/n.den", "namespace nested; relation r(); r();"),
    ] {
        let path = base.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    let a = support::file_uri(&base.join("a/den.root"));
    let b = support::file_uri(&base.join("b/den.root"));
    let lib = support::file_uri(&base.join("lib/den.root"));
    watched(&mut c, &a, 1);
    let (shared, _) = c.open("lib/lib.den");
    let (a_doc, a_text) = c.open("a/a.den");
    let (b_doc, _) = c.open("b/b.den");
    let (nested, _) = c.open("a/nested/n.den");
    assert!(roots(&mut c, &nested)["homeProgram"]
        .as_str()
        .unwrap()
        .ends_with("/a/nested/den.root"));
    let nested_root = support::file_uri(&base.join("a/nested/den.root"));
    manifest(&mut c, &nested_root, "broken", 1);
    assert_eq!(roots(&mut c, &nested)["state"], "invalid");
    assert_eq!(
        roots(&mut c, &a_doc)["state"],
        "ready",
        "nested root failure is independent"
    );
    manifest(&mut c, &nested_root, "{}", 2);
    let invalid = support::file_uri(&base.join("a/unreadable.den"));
    std::fs::write(base.join("a/unreadable.den"), [0xff]).unwrap();
    watched(&mut c, &invalid, 1);
    assert_eq!(roots(&mut c, &a_doc)["state"], "invalid");
    assert_eq!(roots(&mut c, &b_doc)["state"], "ready");
    std::fs::remove_file(base.join("a/unreadable.den")).unwrap();
    watched(&mut c, &invalid, 3);
    assert_eq!(roots(&mut c, &a_doc)["state"], "ready");
    // Watcher spelling may be canonical while the open buffer uses an alias.
    let canonical_a = support::file_uri(&base.join("a/a.den").canonicalize().unwrap());
    std::fs::write(base.join("a/a.den"), "invalid disk text").unwrap();
    watched(&mut c, &canonical_a, 2);
    assert_eq!(roots(&mut c, &a_doc)["state"], "ready");
    std::fs::write(base.join("a/a.den"), &a_text).unwrap();
    let own_root = json!(support::file_uri(
        &base.join("lib/den.root").canonicalize().unwrap()
    ));
    let a_root = json!(support::file_uri(
        &base.join("a/den.root").canonicalize().unwrap()
    ));
    let home = roots(&mut c, &shared);
    assert_eq!(home["state"], "ready");
    assert_eq!(home["homeProgram"], own_root);
    assert!(home.get("choices").is_none());
    assert!(home.get("selectedRoot").is_none());
    assert!(home.get("activeRoot").is_none());
    assert_eq!(c.diagnostics(&shared), json!([]));
    manifest(&mut c, &a, "{broken", 1);
    assert_eq!(roots(&mut c, &a_doc)["state"], "invalid");
    assert_eq!(roots(&mut c, &b_doc)["state"], "ready");
    assert_eq!(roots(&mut c, &shared)["state"], "ready");
    // Disk events cannot override the open malformed manifest.
    watched(&mut c, &a, 2);
    assert_eq!(roots(&mut c, &a_doc)["state"], "invalid");
    manifest(&mut c, &a, r#"{"libraries":["../missing/den.root"]}"#, 2);
    assert_eq!(roots(&mut c, &a_doc)["state"], "invalid");
    assert_eq!(roots(&mut c, &b_doc)["state"], "ready");
    std::fs::create_dir_all(base.join("missing")).unwrap();
    std::fs::write(base.join("missing/den.root"), "{}").unwrap();
    watched(
        &mut c,
        &support::file_uri(&base.join("missing/den.root")),
        1,
    );
    assert_eq!(
        roots(&mut c, &a_doc)["state"],
        "ready",
        "creating a missing library repairs its consumer"
    );
    // Consumer membership changes never change the library's home view.
    assert_eq!(roots(&mut c, &shared)["homeProgram"], own_root);
    assert_eq!(c.diagnostics(&shared), json!([]));
    manifest(&mut c, &a, r#"{"libraries":["../lib/den.root"]}"#, 3);
    manifest(&mut c, &lib, r#"{"libraries":["../a/den.root"]}"#, 1);
    // Cycles add containing contexts without changing user ownership.
    assert_eq!(roots(&mut c, &a_doc)["homeProgram"], a_root);
    assert_eq!(roots(&mut c, &shared)["homeProgram"], own_root);
    let programs = c.request("denotate/roots", json!({}));
    assert!(programs["programs"]
        .as_array()
        .unwrap()
        .iter()
        .any(|p| p["program"] == own_root));
    manifest(&mut c, &lib, "{}", 2);
    // A syntactically damaged member blocks only its roots, retaining local syntax.
    c.change(&a_doc, 2, "namespace a; relation a(");
    assert_eq!(roots(&mut c, &a_doc)["state"], "invalid");
    assert_eq!(roots(&mut c, &b_doc)["state"], "ready");
    assert!(!c.diagnostics(&a_doc).as_array().unwrap().is_empty());
    c.change(&a_doc, 3, &a_text);
    // Out-of-sync documents likewise do not pause independent roots.
    c.notify("textDocument/didChange",json!({"textDocument":{"uri":a_doc,"version":4},"contentChanges":[{"range":{"start":{"line":0,"character":9},"end":{"line":0,"character":1}},"text":"bad"}]}));
    c.request("denotate/test/idle", Value::Null);
    assert_eq!(roots(&mut c, &a_doc)["state"], "invalid");
    assert_eq!(roots(&mut c, &b_doc)["state"], "ready");
    let symbols = c.request(
        "textDocument/documentSymbol",
        json!({"textDocument":{"uri":b_doc}}),
    );
    assert!(!symbols.as_array().unwrap().is_empty());
    c.change(&a_doc, 5, &a_text);
    assert_eq!(roots(&mut c, &a_doc)["state"], "ready");
    c.notify("denotate/manifest", json!({"uri":a,"closed":true}));
    c.notify("denotate/manifest", json!({"uri":lib,"closed":true}));
    std::fs::remove_file(base.join("a/den.root")).unwrap();
    watched(&mut c, &a, 3);
    assert_eq!(roots(&mut c, &a_doc)["state"], "standalone");
    assert_eq!(roots(&mut c, &b_doc)["state"], "ready");
    // Removing another consumer leaves the library's home unchanged.
    std::fs::remove_file(base.join("b/den.root")).unwrap();
    watched(&mut c, &b, 3);
    assert_eq!(roots(&mut c, &shared)["state"], "ready");
    c.shutdown();
}
#[test]
fn standalone_quick_fix_and_origin_bridge_never_guess_disk_authority() {
    if !b_only() {
        return;
    }
    for bridge in [false, true] {
        let mut c = if bridge {
            Client::start_with_bridge("ir-text/standalone")
        } else {
            Client::start("ir-text/standalone")
        };
        let (uri, _) = c.open("example.den");
        assert_eq!(roots(&mut c, &uri)["state"], "standalone");
        let fixes=c.request("textDocument/codeAction",json!({"textDocument":{"uri":uri},"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},"context":{"diagnostics":[]}}));
        assert_eq!(fixes[0]["command"]["command"], "denotate.createRoot");
        let origin = "file:///test-origin.dsl";
        c.origin_snapshots.insert(
            origin.into(),
            json!({"uri":origin,"text":"","open":true,"dirty":true,"generation":1}),
        );
        let text = format!(
            r#"relation r(); #s=source("{origin}",view:"dsl",hash:"sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"); r() loc(#s 1:1 to 1:1);"#
        );
        c.change(&uri, 2, &text);
        // Drain server-initiated request/reply before reading the status.
        c.request("denotate/test/idle", Value::Null);
        c.request("denotate/test/idle", Value::Null);
        let state = c.request("denotate/originStatus", json!({"uri":origin}));
        assert_eq!(
            state["state"],
            if bridge { "matching" } else { "unavailable" }
        );
        if bridge {
            c.origin_snapshots.insert(
                origin.into(),
                json!({"uri":origin,"text":"dirty","open":true,"dirty":true,"generation":2}),
            );
            c.notify(
                "denotate/originChanged",
                json!({"uri":origin,"generation":2}),
            );
            c.request("denotate/test/idle", Value::Null);
            c.request("denotate/test/idle", Value::Null);
            assert_eq!(
                c.request("denotate/originStatus", json!({"uri":origin}))["state"],
                "hash-mismatch"
            );
            c.origin_snapshots.remove(origin);
            c.notify(
                "denotate/originChanged",
                json!({"uri":origin,"generation":3}),
            );
            c.request("denotate/test/idle", Value::Null);
            c.request("denotate/test/idle", Value::Null);
            assert_eq!(
                c.request("denotate/originStatus", json!({"uri":origin}))["state"],
                "unavailable"
            );
        }
        c.shutdown();
    }
}

#[test]
fn consumer_ambiguity_is_attributed_to_the_app_and_library_home_stays_clean() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("ir-text/standalone");
    let base = c.workspace.path().to_owned();
    for (file, text) in [
        ("a/den.root", r#"{"libraries":["../lib/den.root"]}"#),
        ("b/den.root", r#"{"libraries":["../lib/den.root"]}"#),
        ("lib/den.root", "{}"),
        ("a/a.den", "namespace a; relation r(); r();"),
        ("b/b.den", "namespace b; relation r(); r();"),
        ("lib/lib.den", "namespace lib; sort S; relation r(x:S);"),
    ] {
        let path = base.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    watched(&mut c, &support::file_uri(&base.join("a/den.root")), 1);
    let (a, a_text) = c.open("a/a.den");
    let (b, _) = c.open("b/b.den");
    let (lib, _) = c.open("lib/lib.den");
    c.change(&a, 2, "namespace lib; sort S;");
    let a_status = roots(&mut c, &a);
    assert_eq!(a_status["state"], "invalid");
    assert!(a_status["errors"]
        .to_string()
        .contains("Ambiguous name 'S'"));
    assert_eq!(roots(&mut c, &b)["state"], "ready");
    assert_eq!(roots(&mut c, &lib)["state"], "ready");
    assert_eq!(c.diagnostics(&lib), json!([]));
    let findings = c.diagnostics(&a);
    let attributed = findings
        .as_array()
        .unwrap()
        .iter()
        .find(|d| {
            d["message"]
                .as_str()
                .unwrap()
                .contains("Ambiguous name 'S'")
        })
        .unwrap();
    assert_eq!(
        attributed["range"]["start"],
        json!({"line":0,"character":20})
    );
    assert_eq!(attributed["relatedInformation"][0]["location"]["uri"], lib);
    c.change(&a, 3, &a_text);
    assert_eq!(roots(&mut c, &a)["state"], "ready");
    assert_eq!(c.diagnostics(&a), json!([]));
    // Library-own failure propagates to root status for each consumer, while
    // only the library's home resolution diagnostic is published there.
    c.change(&lib, 2, "namespace lib; sort S; relation r(x:Missing);");
    assert_eq!(roots(&mut c, &a)["state"], "invalid");
    assert_eq!(roots(&mut c, &b)["state"], "invalid");
    assert_eq!(roots(&mut c, &lib)["state"], "invalid");
    assert_eq!(c.diagnostics(&lib).as_array().unwrap().len(), 1);
    assert_eq!(c.diagnostics(&a), json!([]));
    assert_eq!(c.diagnostics(&b), json!([]));
    c.shutdown();
}

const CONFLICT: &str = "sort S; const a,b:S; relation p(x:S); p(a); p(b); obligation unique: at_most_one(p, group_by: ());";
fn checking_idle(c: &mut Client) {
    c.request("denotate/test/checkingIdle", json!({}));
}
fn semantic_findings(c: &Client, uri: &str) -> Vec<Value> {
    c.diagnostics(uri)
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["data"]["finding"].is_object())
        .cloned()
        .collect()
}
#[test]
fn damage_and_repair_preserve_warm_library_and_consumer_sessions() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("base/00-valid");
    let base = c.workspace.path().to_owned();
    for folder in ["lib", "app", "other"] {
        std::fs::create_dir(base.join(folder)).unwrap();
        std::fs::write(
            base.join(folder).join("den.root"),
            if folder == "lib" {
                "{}"
            } else {
                r#"{"libraries":["../lib/den.root"]}"#
            },
        )
        .unwrap();
        std::fs::write(
            base.join(folder).join("code.den"),
            if folder == "lib" {
                CONFLICT
            } else {
                "// library-only finding"
            },
        )
        .unwrap();
    }
    let lib_root = support::file_uri(&base.join("lib/den.root"));
    watched(&mut c, &lib_root, 1);
    let (lib, _) = c.open("lib/code.den");
    checking_idle(&mut c);
    c.request("denotate/test/resetChecks", json!({}));
    checking_idle(&mut c);
    let program_roots = ["lib", "app", "other"].map(|folder| {
        support::file_uri(&base.join(folder).join("den.root").canonicalize().unwrap())
    });
    let latest = |stats: &Value, root: &str| {
        stats["finished"]
            .as_array()
            .unwrap()
            .iter()
            .rev()
            .find(|f| f["program"] == root && f["status"] == "published")
            .unwrap()
            .clone()
    };
    let cold = c.request("denotate/test/checkingStats", json!({}));
    for root in &program_roots {
        assert!(
            latest(&cold, root)["cache"]["evaluationMisses"]
                .as_u64()
                .unwrap()
                > 0
        );
    }
    for damage in ["syntax", "manifest"] {
        let before = c.request("denotate/test/checkingStats", json!({}));
        if damage == "syntax" {
            c.change(&lib, 2, &format!("{CONFLICT} p("));
            // Continuing to type while blocked must neither enqueue work nor
            // lose the retained state/session.
            c.change(&lib, 3, &format!("{CONFLICT} p(a"));
        } else {
            manifest(&mut c, &lib_root, "{", 1);
        }
        checking_idle(&mut c);
        assert!(semantic_findings(&c, &lib).is_empty(), "{damage}");
        if damage == "syntax" {
            assert!(!c.diagnostics(&lib).as_array().unwrap().is_empty());
        }
        for folder in ["lib", "app", "other"] {
            let uri = support::file_uri(&base.join(folder).join("code.den"));
            let status = roots(&mut c, &uri);
            assert_eq!(status["checking"], "blocked", "{damage}: {status}");
            assert_eq!(status["findings"], json!([]));
        }
        let blocked = c.request("denotate/test/checkingStats", json!({}));
        assert_eq!(blocked["started"], before["started"], "{damage}");
        assert_eq!(blocked["pending"], json!([]));
        if damage == "syntax" {
            c.change(&lib, 4, CONFLICT);
        } else {
            manifest(&mut c, &lib_root, "{}", 2);
        }
        checking_idle(&mut c);
        let repaired = c.request("denotate/test/checkingStats", json!({}));
        for root in &program_roots {
            let previous = latest(&before, root);
            let current = latest(&repaired, root);
            assert!(current["revision"].as_u64() > previous["revision"].as_u64());
            assert_eq!(current["summary"], previous["summary"], "{damage}: {root}");
            let cache = &current["cache"];
            assert_eq!(cache["evaluationMisses"], 0, "{damage}: {root}: {cache}");
            assert_eq!(cache["verdictMisses"], 0, "{damage}: {root}: {cache}");
            assert!(cache["evaluationHits"].as_u64().unwrap() > 0, "{cache}");
            assert!(cache["verdictHits"].as_u64().unwrap() > 0, "{cache}");
            assert!(semantic_findings(&c, &lib)
                .iter()
                .any(|d| d["data"]["program"] == *root));
        }
    }
    // Actual catalog removal still releases the session. Rediscovery of the
    // same root starts cold; keeping every session forever would fail this.
    let app_path = base.join("app/den.root");
    let app_root = support::file_uri(&app_path.canonicalize().unwrap());
    let before = c.request("denotate/test/checkingStats", json!({}));
    std::fs::remove_file(&app_path).unwrap();
    watched(&mut c, &app_root, 3);
    checking_idle(&mut c);
    std::fs::write(&app_path, r#"{"libraries":["../lib/den.root"]}"#).unwrap();
    watched(&mut c, &app_root, 1);
    checking_idle(&mut c);
    let restored = c.request("denotate/test/checkingStats", json!({}));
    let current = latest(&restored, &app_root);
    assert!(current["revision"].as_u64() > latest(&before, &app_root)["revision"].as_u64());
    assert!(
        current["cache"]["evaluationMisses"].as_u64().unwrap() > 0,
        "{current}"
    );
    c.shutdown();
}

#[test]
fn background_checks_publish_all_roots_and_preserve_labeled_library_fallbacks() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("base/00-valid");
    let base = c.workspace.path().to_owned();
    for folder in ["lib", "app", "other"] {
        std::fs::create_dir(base.join(folder)).unwrap();
        std::fs::write(
            base.join(folder).join("den.root"),
            if folder == "lib" {
                "{}"
            } else {
                r#"{"libraries":["../lib/den.root"]}"#
            },
        )
        .unwrap();
        std::fs::write(
            base.join(folder).join("code.den"),
            if folder == "lib" {
                CONFLICT
            } else {
                "// library-only finding"
            },
        )
        .unwrap();
    }
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":support::file_uri(&base.join("lib/den.root")),"type":1}]}),
    );
    let (lib, _) = c.open("lib/code.den");
    checking_idle(&mut c);
    let findings = semantic_findings(&c, &lib);
    let programs = findings
        .iter()
        .filter(|d| d["data"]["kind"] == "counterexample")
        .map(|d| d["data"]["program"].as_str().unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(programs.len(), 3, "{findings:?}");
    for d in &findings {
        if d["data"]["fallback"] == true {
            assert!(
                d["message"]
                    .as_str()
                    .unwrap()
                    .starts_with("in app/den.root:")
                    || d["message"]
                        .as_str()
                        .unwrap()
                        .starts_with("in other/den.root:")
            );
        }
    }
    c.change(&lib,2,"sort S; const a:S; relation p(x:S); p(a); obligation unique: at_most_one(p, group_by: ());");
    checking_idle(&mut c);
    assert!(semantic_findings(&c, &lib).is_empty());
    for folder in ["app", "other", "lib"] {
        let status = c.request(
            "denotate/roots",
            json!({"uri":support::file_uri(&base.join(folder).join("code.den"))}),
        );
        assert_eq!(status["checking"], "complete");
        assert_eq!(status["summary"]["state"], "proved");
    }
    c.shutdown();
}
#[test]
fn completed_results_cannot_publish_after_member_manifest_config_dependency_or_home_changes() {
    if !b_only() {
        return;
    }
    for scenario in [
        "member",
        "manifest",
        "config",
        "dependency",
        "home",
        "sync",
        "origin",
        "syntax",
    ] {
        let mut c = Client::start_with_bridge("base/00-valid");
        let base = c.workspace.path().to_owned();
        std::fs::create_dir(base.join("app")).unwrap();
        std::fs::create_dir(base.join("app/nested")).unwrap();
        std::fs::create_dir(base.join("lib")).unwrap();
        std::fs::write(base.join("lib/den.root"), "{}").unwrap();
        std::fs::write(base.join("lib/code.den"), "relation helper();").unwrap();
        std::fs::write(
            base.join("app/den.root"),
            r#"{"libraries":["../lib/den.root"]}"#,
        )
        .unwrap();
        let text = if scenario == "origin" {
            format!(
                "{CONFLICT}\n#s=source(\"file:///changed.dsl\",view:\"dsl\",hash:\"sha256:{}\");",
                "0".repeat(64)
            )
        } else {
            CONFLICT.into()
        };
        std::fs::write(base.join("app/nested/code.den"), &text).unwrap();
        c.notify(
            "workspace/didChangeWatchedFiles",
            json!({"changes":[{"uri":support::file_uri(&base.join("app/den.root")),"type":1}]}),
        );
        let (uri, _) = c.open("app/nested/code.den");
        checking_idle(&mut c);
        c.request("denotate/test/hold", json!({}));
        c.change(&uri, 2, &format!("{text}\n// held"));
        let held = c.notification("denotate/test/checkpoint");
        let before = c.publications().len();
        match scenario {
            "member" => c.change(&uri,3,"relation fine(); fine();"),
            "manifest" => c.notify("denotate/manifest",json!({"uri":support::file_uri(&base.join("app/den.root")),"version":1,"text":"{broken"})),
            "config" => c.notify("workspace/didChangeConfiguration",json!({"settings":{"denotate":{"backend":"sat"}}})),
            "dependency" => {std::fs::remove_file(base.join("lib/den.root")).unwrap(); c.notify("workspace/didChangeWatchedFiles",json!({"changes":[{"uri":support::file_uri(&base.join("lib/den.root")),"type":3}]}));},
            "home" => c.notify("denotate/manifest",json!({"uri":support::file_uri(&base.join("app/nested/den.root")),"version":1,"text":"{}"})),
            "sync" => c.notify("textDocument/didChange",json!({"textDocument":{"uri":uri,"version":3},"contentChanges":[{"range":{"start":{"line":0,"character":10},"end":{"line":0,"character":1}},"text":""}]})),
            "origin" => c.notify("denotate/originChanged",json!({"uri":"file:///changed.dsl","generation":2})),
            "syntax" => c.change(&uri,3,"sort S"),
            _ => unreachable!(),
        }
        c.request("denotate/test/idle", json!({}));
        let withdrawn = c.publications()[before..].iter().find(|p| {
            p["uri"] == uri
                && p["diagnostics"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|d| d["data"]["finding"].is_null())
        });
        assert!(
            withdrawn.is_some(),
            "{scenario}: must withdraw while pending/invalid"
        );
        c.request(
            "denotate/test/release",
            json!({"revision":held["revision"]}),
        );
        checking_idle(&mut c);
        for publication in &c.publications()[before..] {
            assert!(
                publication["diagnostics"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|d| d["data"]["checkRevision"] != held["revision"]),
                "{scenario}: stale diagnostic published"
            );
        }
        if scenario == "syntax" {
            assert!(c
                .diagnostics(&uri)
                .as_array()
                .unwrap()
                .iter()
                .any(|d| d["source"] == "denotate-syntax"));
        }
        let stats = c.request("denotate/test/checkingStats", json!({}));
        let finished = stats["finished"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["revision"] == held["revision"])
            .unwrap();
        assert_eq!(finished["status"], "discarded", "{scenario}");
        c.shutdown();
    }
}
#[test]
fn queued_roots_keep_their_place_and_progress_after_cancellation_and_deadline() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("base/00-valid");
    checking_idle(&mut c);
    c.request("denotate/test/hold", json!({}));
    let (uri, _) = c.open("example.den");
    let held = c.notification("denotate/test/checkpoint");
    let base = c.workspace.path().to_owned();
    for folder in ["waiting-a", "waiting-b"] {
        std::fs::create_dir(base.join(folder)).unwrap();
        std::fs::write(base.join(folder).join("den.root"), "{}").unwrap();
        std::fs::write(base.join(folder).join("code.den"), CONFLICT).unwrap();
    }
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":support::file_uri(&base.join("waiting-a/den.root")),"type":1}]}),
    );
    let (a, _) = c.open("waiting-a/code.den");
    for v in 2..6 {
        c.change(&a, v, &format!("{CONFLICT}\n// {v}"));
    }
    c.change(&uri, 2, "relation replacement(); replacement();");
    let stats = c.request("denotate/test/checkingStats", json!({}));
    let pending = stats["pending"].as_array().unwrap();
    assert_eq!(pending.len(), 3);
    assert!(pending[0]["program"]
        .as_str()
        .unwrap()
        .ends_with("waiting-a/den.root"));
    assert!(pending[1]["program"]
        .as_str()
        .unwrap()
        .ends_with("waiting-b/den.root"));
    c.request(
        "denotate/test/release",
        json!({"revision":held["revision"]}),
    );
    checking_idle(&mut c);
    assert!(!semantic_findings(&c, &a).is_empty());
    c.notify(
        "workspace/didChangeConfiguration",
        json!({"settings":{"denotate":{"timeoutMs":0}}}),
    );
    checking_idle(&mut c);
    let status = c.request("denotate/roots", json!({"uri":a}));
    assert_eq!(status["checking"], "deadline");
    c.notify(
        "workspace/didChangeConfiguration",
        json!({"settings":{"denotate":{"backend":"sat"}}}),
    );
    checking_idle(&mut c);
    let status = c.request("denotate/roots", json!({"uri":a}));
    assert_eq!(status["checking"], "complete");
    assert_eq!(status["backend"], "sat");
    c.shutdown();
}

#[test]
fn empty_roots_and_standalones_have_current_check_status() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("base/00-valid");
    let base = c.workspace.path().to_owned();
    std::fs::create_dir(base.join("empty")).unwrap();
    let empty = support::file_uri(&base.join("empty/den.root"));
    std::fs::write(base.join("empty/den.root"), "{}").unwrap();
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":empty,"type":1}]}),
    );
    let external = tempfile::tempdir().unwrap();
    let uri = support::file_uri(&external.path().join("standalone.den"));
    c.notify(
        "textDocument/didOpen",
        json!({"textDocument":{"uri":uri,"version":1,"languageId":"denotate","text":CONFLICT}}),
    );
    checking_idle(&mut c);
    let status = c.request("denotate/roots", json!({}));
    let programs = status["programs"].as_array().unwrap();
    let standalone = programs.iter().find(|p| p["program"] == uri).unwrap();
    assert_eq!(standalone["state"], "standalone");
    assert_eq!(standalone["checking"], "complete");
    assert_eq!(standalone["summary"]["state"], "findings");
    let empty = programs
        .iter()
        .find(|p| {
            p["program"]
                .as_str()
                .is_some_and(|p| p.ends_with("/empty/den.root"))
        })
        .unwrap();
    assert_eq!(empty["checking"], "complete");
    assert_eq!(empty["summary"]["state"], "proved");
    assert_eq!(empty["activeAssumptions"], json!([]));
    c.shutdown();
}

#[cfg(unix)]
#[test]
fn ambiguous_canonical_home_blocks_only_affected_programs() {
    if !b_only() {
        return;
    }
    let mut c = Client::start("base/00-valid");
    let base = c.workspace.path().to_owned();
    for folder in ["a", "b", "independent"] {
        std::fs::create_dir(base.join(folder)).unwrap();
        std::fs::write(base.join(folder).join("den.root"), "{}").unwrap();
    }
    std::fs::write(base.join("a/code.den"), CONFLICT).unwrap();
    std::os::unix::fs::symlink(base.join("a/code.den"), base.join("b/alias.den")).unwrap();
    std::fs::write(base.join("independent/code.den"), CONFLICT).unwrap();
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":support::file_uri(&base.join("a/den.root")),"type":1}]}),
    );
    let (independent, _) = c.open("independent/code.den");
    checking_idle(&mut c);
    assert!(!semantic_findings(&c, &independent).is_empty());
    let statuses = c.request("denotate/roots", json!({}));
    for folder in ["a", "b"] {
        let status = statuses["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| {
                s["program"]
                    .as_str()
                    .unwrap()
                    .ends_with(&format!("/{folder}/den.root"))
            })
            .unwrap();
        assert_eq!(status["state"], "invalid");
        assert_eq!(status["checking"], "blocked");
        assert!(status["errors"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e.as_str().unwrap().contains("unique home")));
    }
    c.shutdown();
}
