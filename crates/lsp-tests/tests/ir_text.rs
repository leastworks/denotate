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
#[test]
fn namespaces_quoted_names_helpers_domains_contracts_and_locations_use_one_index() {
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
 verification checks { assumptions: [known]; obligations: [unique]; }
 #source = source("file:///source.testdsl", view: "dsl", hash: "sha256:0000000000000000000000000000000000000000000000000000000000000000");
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
    let prepared = c.request(
        "textDocument/prepareRename",
        json!({"textDocument":{"uri":uri},"position":position(text,"relation r",9)}),
    );
    assert_eq!(prepared["start"], position(text, "relation r", 9));
    c.shutdown();
}
#[test]
fn no_manifest_means_standalone_even_when_use_names_a_workspace_file() {
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

const CONFLICT: &str = "sort S; const a,b:S; relation p(x:S); p(a); p(b); obligation unique: at_most_one(p, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }";
fn checking_idle(c: &mut Client) {
    c.request("denotate/test/checkingIdle", json!({}));
}
fn semantic_findings(c: &Client, uri: &str) -> Vec<Value> {
    c.diagnostics(uri)
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["data"]["finding"].is_object() && d["code"] != "unchecked-obligation")
        .cloned()
        .collect()
}
#[test]
fn damage_and_repair_preserve_warm_library_and_consumer_sessions() {
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
    c.change(&lib,2,"sort S; const a:S; relation p(x:S); p(a); obligation unique: at_most_one(p, group_by: ()); verification checks { assumptions: []; obligations: [unique]; }");
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
            "config" => c.notify("workspace/didChangeConfiguration",json!({"settings":{"denotate":{"timeoutMs":20000}}})),
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
        json!({"settings":{"denotate":{"timeoutMs":20000}}}),
    );
    checking_idle(&mut c);
    let status = c.request("denotate/roots", json!({"uri":a}));
    assert_eq!(status["checking"], "complete");
    assert_eq!(status["backend"], "bdd");
    c.shutdown();
}

#[test]
fn empty_roots_and_standalones_have_current_check_status() {
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
    assert_eq!(empty["checking"], "unconfigured");
    assert_eq!(empty["summary"]["state"], "unconfigured");
    assert_eq!(empty["verifications"], json!([]));
    c.shutdown();
}

#[cfg(unix)]
#[test]
fn ambiguous_canonical_home_blocks_only_affected_programs() {
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

#[test]
fn go_to_origin_preserves_occurrence_maps_fused_identities_and_definition_navigation() {
    let mut c = Client::start("base/00-valid");
    let (uri, _) = c.open("example.den");
    let text = r#"sort OriginSort; const origin_a:OriginSort;
input origin_input(x:OriginSort); relation origin_output(x:OriginSort);
#s = source("file:///library/source.dsl", view: "dsl", hash: "sha256:0000000000000000000000000000000000000000000000000000000000000000");
#v = source("file:///library/source.dsl", view: "other", hash: "sha256:1111111111111111111111111111111111111111111111111111111111111111");
origin_output(origin_a) loc(#map);
#map = {self: loc(fused[#s 1:1 to 1:4, #v 2:1 to 2:3, #s 1:1 to 1:4]), head.0: loc(#s 3:2 to 3:4)};
assumption origin_constraint: at_most_one(origin_input, group_by: ()) loc(#v 4:1 to 4:5);
"#;
    c.change(&uri, 2, text);
    let result = query(
        &mut c,
        "denotate/origins",
        &uri,
        text,
        "origin_output(origin_a)",
        0,
    );
    assert_eq!(result["version"], 2);
    let origins = result["origins"].as_array().unwrap();
    assert_eq!(origins.len(), 2, "{result}");
    assert!(origins
        .iter()
        .all(|o| o["uri"] == "file:///library/source.dsl"));
    assert!(origins
        .iter()
        .any(|o| o["view"] == "other" && o["start"]["line"] == 2));
    let term = query(
        &mut c,
        "denotate/origins",
        &uri,
        text,
        "origin_output(origin_a)",
        14,
    );
    assert_eq!(term["origins"].as_array().unwrap().len(), 1, "{term}");
    assert_eq!(term["origins"][0]["start"], json!({"line":3,"column":2}));
    let term_end = query(
        &mut c,
        "denotate/origins",
        &uri,
        text,
        "origin_output(origin_a)",
        "origin_output(origin_a".len(),
    );
    assert_eq!(
        term_end["origins"], term["origins"],
        "caret after the term must retain its specific origin"
    );

    let assumption = query(
        &mut c,
        "denotate/origins",
        &uri,
        text,
        "assumption origin_constraint",
        12,
    );
    assert_eq!(assumption["origins"][0]["start"]["line"], 4);
    let none = query(&mut c, "denotate/origins", &uri, text, "sort OriginSort", 0);
    assert_eq!(none["origins"], json!([]));
    let definition = query(
        &mut c,
        "textDocument/definition",
        &uri,
        text,
        "origin_output(origin_a)",
        0,
    );
    assert_eq!(definition.as_array().unwrap().len(), 1);
    assert_eq!(definition[0]["targetUri"], uri);
    assert_eq!(definition[0]["targetRange"]["start"]["line"], 1);
    // Candidate associations come from the current authoring snapshot, even
    // without an origin resolver or a completed semantic check.
    let changed = text.replace("#s 3:2 to 3:4", "#s 5:1 to 5:2");
    c.change(&uri, 3, &changed);
    let term = query(
        &mut c,
        "denotate/origins",
        &uri,
        &changed,
        "origin_output(origin_a)",
        14,
    );
    assert_eq!(term["origins"][0]["start"]["line"], 5);
    let stale = c.request_reply(
        "denotate/origins",
        json!({"textDocument":{"uri":uri,"version":2},"position":{"line":4,"character":0}}),
    );
    assert!(stale["error"]["message"]
        .as_str()
        .unwrap()
        .contains("changed"));
    c.change(
        &uri,
        4,
        &changed.replace("origin_output(origin_a)", "origin_output(origin_a"),
    );
    let invalid = c.request_reply(
        "denotate/origins",
        json!({"textDocument":{"uri":uri,"version":4},"position":{"line":4,"character":0}}),
    );
    assert!(invalid["error"]["message"]
        .as_str()
        .unwrap()
        .contains("invalid"));
}

#[test]
fn verification_edits_qualify_and_withdraw_every_semantic_finding() {
    let mut c = Client::start("base/00-valid");
    let (uri, _) = c.open("example.den");
    let body = "sort S; const a,b:S; relation p(x:S); p(a); p(b); obligation unique: at_most_one(p, group_by: ()); relation n(); n() :- !n(); relation x(); relation y(); x() :- !y(); y() :- !x(); input guard(); relation redundant(); redundant() :- guard(), !guard(), !redundant();";
    let verification =
        |name| format!("verification {name} {{ assumptions: []; obligations: [unique]; }}");
    c.change(&uri, 2, body);
    checking_idle(&mut c);
    let status = c.request("denotate/roots", json!({"uri":uri}));
    assert_eq!(status["checking"], "unconfigured");
    assert_eq!(status["verifications"], json!([]));
    assert_eq!(status["uncheckedObligations"], json!(["::unique"]));
    assert!(semantic_findings(&c, &uri).is_empty());
    assert!(c
        .diagnostics(&uri)
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d["code"] == "unchecked-obligation" && d["severity"] == 3));
    let single = format!("{body} {}", verification("one"));
    c.change(&uri, 3, &single);
    checking_idle(&mut c);
    let kinds = semantic_findings(&c, &uri)
        .iter()
        .map(|d| d["data"]["kind"].as_str().unwrap().to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    for kind in [
        "counterexample",
        "no-meaning",
        "unsupported-region",
        "redundant",
    ] {
        assert!(kinds.contains(kind), "missing {kind}: {kinds:?}");
    }
    let identities = |c: &Client, verification: &str| {
        semantic_findings(c, &uri)
            .iter()
            .filter(|d| d["data"]["finding"]["verification"] == json!(["", verification]))
            .map(|d| d["data"]["finding"].to_string())
            .collect::<std::collections::BTreeSet<_>>()
    };
    let one = identities(&c, "one");
    assert!(!one.is_empty());
    c.change(&uri, 4, &format!("{single} {}", verification("two")));
    checking_idle(&mut c);
    assert_eq!(identities(&c, "one"), one);
    let two = identities(&c, "two");
    assert_eq!(one.len(), two.len());
    assert!(one.is_disjoint(&two));
    let status = c.request("denotate/roots", json!({"uri":uri}));
    assert_eq!(status["verifications"].as_array().unwrap().len(), 2);
    assert_eq!(status["uncheckedObligations"], json!([]));
    c.change(&uri, 5, &single);
    checking_idle(&mut c);
    assert_eq!(identities(&c, "one"), one);
    assert!(identities(&c, "two").is_empty());
    c.change(
        &uri,
        6,
        &format!("{body} verification broken {{ assumptions: []; obligations: [missing]; }}"),
    );
    checking_idle(&mut c);
    let status = c.request("denotate/roots", json!({"uri":uri}));
    assert_eq!(status["checking"], "blocked");
    assert!(status["verifications"].is_null());
    assert!(status["uncheckedObligations"].is_null());
    assert!(semantic_findings(&c, &uri).is_empty());
    assert!(!c
        .diagnostics(&uri)
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d["code"] == "unchecked-obligation"));
    c.change(&uri, 7, body);
    checking_idle(&mut c);
    assert!(semantic_findings(&c, &uri).is_empty());
    assert_eq!(
        c.request("denotate/roots", json!({"uri":uri}))["checking"],
        "unconfigured"
    );
    c.shutdown();
}

#[test]
fn verification_selections_keep_cold_warm_results_separate() {
    let mut c = Client::start("base/00-valid");
    let (uri, _) = c.open("example.den");
    let body = "sort S; const i,j:S; input value(x:S); relation a(); relation b(); a() :- value(i), !b(); b() :- value(j), !a(); assumption one: at_most_one(value, group_by: ()); obligation unique: at_most_one(value, group_by: ());";
    let mut version = 1;
    for selection in ["one", "", "one"] {
        version += 1;
        c.change(&uri, version, &format!("{body} verification checks {{ assumptions: [{selection}]; obligations: [unique]; }}"));
        checking_idle(&mut c);
        let warm = c.request("denotate/roots", json!({"uri":uri}));
        c.request("denotate/test/resetChecks", json!({}));
        checking_idle(&mut c);
        let cold = c.request("denotate/roots", json!({"uri":uri}));
        assert_eq!(cold["verifications"], warm["verifications"]);
        let verification = &cold["verifications"][0];
        assert_eq!(verification["verification"], "::checks");
        assert_eq!(verification["mode"], "normal");
        assert_eq!(verification["consistency"], "consistent");
        assert_eq!(
            verification["summary"]["state"],
            if selection.is_empty() {
                "findings"
            } else {
                "proved"
            }
        );
        let kinds = semantic_findings(&c, &uri)
            .iter()
            .map(|d| d["data"]["kind"].as_str().unwrap().to_owned())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(kinds.contains("unsupported-region"), selection.is_empty());
    }
    c.shutdown();
}

#[test]
fn library_notices_follow_consumer_selections_and_structural_warnings_are_once_per_declaration() {
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
        std::fs::write(base.join(folder).join("code.den"), if folder == "lib" {
            "namespace lib; sort S; const a,b:S; relation p(x:S); obligation offered: at_most_one(p, group_by: ()); obligation usual: at_most_one(p, group_by: ()); verification normal { assumptions: []; obligations: [usual]; } verification meaning { assumptions: []; obligations: []; }"
        } else { "// user extension" }).unwrap();
    }
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":support::file_uri(&base.join("lib/den.root")),"type":1}]}),
    );
    let (lib, _) = c.open("lib/code.den");
    let (app, _) = c.open("app/code.den");
    checking_idle(&mut c);
    let notices = |c: &Client| {
        c.diagnostics(&lib)
            .as_array()
            .unwrap()
            .iter()
            .filter(|d| d["code"] == "unchecked-obligation")
            .cloned()
            .collect::<Vec<_>>()
    };
    assert_eq!(notices(&c).len(), 3);
    assert_eq!(
        notices(&c)
            .iter()
            .filter(|d| d["data"]["fallback"] == true)
            .count(),
        2
    );
    let structural = c
        .diagnostics(&lib)
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["code"] == "consistency-only")
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(structural.len(), 1);
    assert_eq!(structural[0]["severity"], 2);
    let status = c.request("denotate/roots", json!({"uri":app}));
    assert_eq!(status["summary"]["state"], "incomplete");
    assert_eq!(status["uncheckedObligations"], json!(["lib::offered"]));
    assert_eq!(status["verifications"][0]["mode"], "consistency-only");
    // A pending selected check removes the missing-selection notice immediately.
    c.request("denotate/test/hold", json!({"stage":"beforeResult"}));
    let extension = "lib::p(lib::a); lib::p(lib::b); verification custom { assumptions: []; obligations: [lib::offered]; }";
    c.change(&app, 2, extension);
    let held = c.notification("denotate/test/checkpoint");
    let status = c.request("denotate/roots", json!({"uri":app}));
    assert_eq!(status["uncheckedObligations"], json!([]));
    assert_eq!(notices(&c).len(), 2);
    c.request(
        "denotate/test/release",
        json!({"revision":held["revision"]}),
    );
    checking_idle(&mut c);
    assert!(semantic_findings(&c, &app)
        .iter()
        .any(|d| d["data"]["kind"] == "counterexample"));
    assert_eq!(
        c.diagnostics(&lib)
            .as_array()
            .unwrap()
            .iter()
            .filter(|d| d["code"] == "consistency-only")
            .count(),
        1
    );
    let app_status = c.request("denotate/roots", json!({"uri":app}));
    let lib_status = c.request("denotate/roots", json!({"uri":lib}));
    let normal = |status: &Value| {
        status["verifications"]
            .as_array()
            .unwrap()
            .iter()
            .find(|v| v["verification"] == "lib::normal")
            .unwrap()["summary"]["state"]
            .clone()
    };
    assert_eq!(normal(&app_status), "findings");
    assert_eq!(normal(&lib_status), "proved");
    assert!(semantic_findings(&c, &app)
        .iter()
        .any(|d| d["data"]["finding"]["verification"] == json!(["lib", "normal"])));
    c.change(&app, 3, "// removed extension");
    checking_idle(&mut c);
    assert_eq!(notices(&c).len(), 3);
    c.shutdown();
}

#[test]
fn a_consumer_ambiguity_in_a_library_verification_is_located_on_the_consumer() {
    let mut c = Client::start("base/00-valid");
    let base = c.workspace.path().to_owned();
    for folder in ["lib", "app"] {
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
    }
    std::fs::write(base.join("lib/code.den"), "namespace library { sort S; input p(x:S); assumption allowed: at_most_one(p, group_by: ()); obligation unique: at_most_one(p, group_by: ()); } namespace library::checks { verification checks { assumptions: [allowed]; obligations: [unique]; } }").unwrap();
    std::fs::write(base.join("app/code.den"), "// consumer").unwrap();
    c.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes":[{"uri":support::file_uri(&base.join("app/den.root")),"type":1}]}),
    );
    let (lib, _) = c.open("lib/code.den");
    let (app, _) = c.open("app/code.den");
    checking_idle(&mut c);
    c.change(
        &app,
        2,
        "namespace library::checks; assumption allowed: at_most_one(library::p, group_by: ());",
    );
    checking_idle(&mut c);
    let status = c.request("denotate/roots", json!({"uri":app}));
    assert_eq!(status["checking"], "blocked");
    assert!(status["uncheckedObligations"].is_null());
    let diagnostics = c.diagnostics(&app);
    let conflict = diagnostics
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["code"] == "verification-reference")
        .unwrap();
    assert!(conflict["message"]
        .as_str()
        .unwrap()
        .contains("Ambiguous assumption"));
    assert!(conflict["relatedInformation"]
        .as_array()
        .unwrap()
        .iter()
        .any(|r| r["location"]["uri"] == lib));
    assert!(c.diagnostics(&lib).as_array().unwrap().is_empty());
    assert_eq!(
        c.request("denotate/roots", json!({"uri":lib}))["summary"]["state"],
        "proved"
    );
    c.change(&app, 3, "// consumer repaired");
    checking_idle(&mut c);
    assert!(c.diagnostics(&app).as_array().unwrap().is_empty());
    assert_eq!(
        c.request("denotate/roots", json!({"uri":app}))["summary"]["state"],
        "proved"
    );
    c.shutdown();
}

#[test]
fn verification_navigation_hover_outline_highlighting_and_typed_completion() {
    let mut c = Client::start("base/00-valid");
    let (uri, _) = c.open("example.den");
    let text = "namespace lib { sort S; input p(x:S); assumption same: at_most_one(p, group_by: ()); obligation same: at_most_one(p, group_by: ()); verification same { assumptions: [same]; obligations: [same]; } }\nuse lib; verification custom { assumptions: [lib::same]; obligations: [same]; }";
    c.change(&uri, 2, text);
    for (needle, decl, offset, label) in [
        ("lib::same", "assumption same", 11, "assumption same"),
        ("same]; }", "obligation same", 11, "obligation same"),
        ("custom {", "verification custom", 13, "verification custom"),
    ] {
        let definition = query(&mut c, "textDocument/definition", &uri, text, needle, 0);
        assert_eq!(definition.as_array().unwrap().len(), 1, "{definition}");
        assert_eq!(
            definition[0]["targetSelectionRange"]["start"],
            position(text, decl, offset)
        );
        let hover = query(&mut c, "textDocument/hover", &uri, text, needle, 0);
        assert_eq!(hover["contents"]["value"], label);
        let refs = query(&mut c, "textDocument/references", &uri, text, decl, offset);
        assert_eq!(
            refs.as_array().unwrap().len(),
            if needle == "custom {" { 1 } else { 3 },
            "{refs}"
        );
    }
    let outline = c.request(
        "textDocument/documentSymbol",
        json!({"textDocument":{"uri":uri}}),
    );
    assert!(outline
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s["name"] == "verification custom"));
    assert!(outline[0]["children"]
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s["name"] == "verification same"));
    let legend = c.capabilities["semanticTokensProvider"]["legend"]["tokenTypes"]
        .as_array()
        .unwrap();
    let event = legend.iter().position(|v| v == "event").unwrap() as u64;
    let tokens = c.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument":{"uri":uri}}),
    );
    assert_eq!(
        tokens["data"]
            .as_array()
            .unwrap()
            .chunks(5)
            .filter(|t| t[3] == event)
            .count(),
        8
    );
    let prefix = "namespace lib { sort S; input p(x:S); assumption allowed: at_most_one(p, group_by: ()); obligation unique: at_most_one(p, group_by: ()); verification checks { assumptions: []; obligations: []; } } use lib;";
    for (version, field, expected) in [(3, "assumptions", "allowed"), (4, "obligations", "unique")]
    {
        let source = format!("{prefix} verification custom {{ {field}: [ ]; }}");
        c.change(&uri, version, &source);
        let result = query(&mut c, "textDocument/completion", &uri, &source, "[ ];", 2);
        assert_eq!(
            result["items"]
                .as_array()
                .unwrap()
                .iter()
                .map(|i| i["label"].as_str().unwrap())
                .collect::<Vec<_>>(),
            [expected]
        );
    }
    // Recovery must retain qualification even when the member name is absent.
    for (i, (typed, expected)) in [
        ("lib::", "lib::allowed"),
        ("::lib::a", "::lib::allowed"),
        ("lib::al", "lib::allowed"),
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!("{prefix} verification custom {{ assumptions: [{typed}");
        c.change(&uri, 5 + i as i64, &source);
        let result = query(
            &mut c,
            "textDocument/completion",
            &uri,
            &source,
            &format!("[{typed}"),
            1 + typed.len(),
        );
        assert_eq!(
            result["items"].as_array().unwrap().len(),
            1,
            "{typed}: {result}"
        );
        assert_eq!(result["items"][0]["textEdit"]["newText"], expected);
        assert_eq!(
            result["items"][0]["textEdit"]["range"]["start"],
            position(&source, &format!("[{typed}"), 1)
        );
    }
    // Ambiguous unqualified names are offered with their absolute namespaces.
    let source = "namespace a { sort S; input p(x:S); assumption allowed: at_most_one(p, group_by: ()); } namespace 'b::c' { assumption allowed: at_most_one(a::p, group_by: ()); } use a; use 'b::c'; verification v { assumptions: [ ]; obligations: []; }";
    c.change(&uri, 8, source);
    let result = query(&mut c, "textDocument/completion", &uri, source, "[ ];", 2);
    assert_eq!(
        result["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|i| i["textEdit"]["newText"].as_str().unwrap())
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from(["a::allowed", "'b::c'::allowed"])
    );
    let partial = source.replace("[ ]", "[al]");
    c.change(&uri, 9, &partial);
    let result = query(&mut c, "textDocument/completion", &uri, &partial, "[al]", 3);
    assert_eq!(result["items"].as_array().unwrap().len(), 2, "{result}");
    assert!(result["items"]
        .as_array()
        .unwrap()
        .iter()
        .all(|i| i["kind"] == 23));
    let source = source.replace("[ ]", "['b::c'::]");
    c.change(&uri, 10, &source);
    let result = query(
        &mut c,
        "textDocument/completion",
        &uri,
        &source,
        "['b::c'::]",
        9,
    );
    assert_eq!(result["items"].as_array().unwrap().len(), 1, "{result}");
    assert_eq!(result["items"][0]["textEdit"]["newText"], "'b::c'::allowed");
    c.shutdown();
}

#[test]
fn coverage_publication_services_and_empty_domain_notices_follow_verifications() {
    let mut c = Client::start("ir-text/standalone");
    let (uri, _) = c.open("example.den");
    let body="namespace lib { sort S; const a,b,c,d:S; relation p(x:S); obligation covered: at_least_one(p, group_by: (x)); } use lib;";
    let verification = "verification checks { assumptions: []; obligations: [covered]; }";
    let text = format!("{body} {verification}");
    c.change(&uri, 2, &text);
    checking_idle(&mut c);
    let diagnostics = c.diagnostics(&uri);
    let failures = diagnostics
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["code"] == "counterexample")
        .collect::<Vec<_>>();
    assert_eq!(failures.len(), 1, "{diagnostics}");
    let original_identity = failures[0]["data"]["finding"].clone();
    assert_eq!(original_identity["component"], "coverage");
    assert_eq!(original_identity["obligation"], json!(["lib", "covered"]));
    assert_eq!(
        failures[0]["data"]["evidence"]["missingGroups"],
        json!({"count":4,"exact":true})
    );
    assert_eq!(
        failures[0]["data"]["evidence"]["examples"]
            .as_array()
            .unwrap()
            .len(),
        3
    );
    let definition = query(
        &mut c,
        "textDocument/definition",
        &uri,
        &text,
        "at_least_one(p",
        13,
    );
    assert_eq!(
        definition[0]["targetSelectionRange"]["start"],
        position(&text, "relation p", 9)
    );
    let completion = query(
        &mut c,
        "textDocument/completion",
        &uri,
        &text,
        "group_by: (x)",
        12,
    );
    assert!(completion["items"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["label"] == "x"));
    let hover = query(&mut c, "textDocument/hover", &uri, &text, "covered];", 0);
    assert_eq!(hover["contents"]["value"], "obligation covered");
    let references = query(
        &mut c,
        "textDocument/references",
        &uri,
        &text,
        "covered];",
        0,
    );
    assert_eq!(references.as_array().unwrap().len(), 2);
    let outline = c.request(
        "textDocument/documentSymbol",
        json!({"textDocument":{"uri":uri}}),
    );
    assert!(outline[0]["children"]
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s["name"]
            .as_str()
            .is_some_and(|n| n.starts_with("obligation covered:"))));
    let event = c.capabilities["semanticTokensProvider"]["legend"]["tokenTypes"]
        .as_array()
        .unwrap()
        .iter()
        .position(|v| v == "event")
        .unwrap() as u64;
    let tokens = c.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument":{"uri":uri}}),
    );
    assert_eq!(
        tokens["data"]
            .as_array()
            .unwrap()
            .chunks(5)
            .filter(|t| t[3] == event)
            .count(),
        3
    );
    let edits = c.request(
        "textDocument/formatting",
        json!({"textDocument":{"uri":uri},"options":{"tabSize":4,"insertSpaces":true}}),
    );
    let formatted = support::apply_edits(&text, edits.as_array().unwrap());
    assert_ne!(formatted, text);
    let rename=c.request("textDocument/rename",json!({"textDocument":{"uri":uri},"position":position(&text,"covered];",0),"newName":"complete output"}));
    let changed = support::apply_edits(
        &text,
        rename["documentChanges"][0]["edits"].as_array().unwrap(),
    );
    assert!(changed.contains("obligation 'complete output': at_least_one"));
    assert!(changed.contains("obligations: ['complete output']"));
    c.change(&uri, 3, &changed);
    checking_idle(&mut c);
    assert_eq!(
        c.diagnostics(&uri)
            .as_array()
            .unwrap()
            .iter()
            .filter(|d| d["code"] == "counterexample")
            .count(),
        1
    );
    let two = format!("{text} {}", verification.replace("checks", "again"));
    c.change(&uri, 4, &two);
    checking_idle(&mut c);
    assert_eq!(
        c.diagnostics(&uri)
            .as_array()
            .unwrap()
            .iter()
            .filter(|d| d["code"] == "counterexample")
            .count(),
        2
    );
    c.change(&uri, 5, &format!("{text} p(a); p(b); p(c); p(d);"));
    checking_idle(&mut c);
    assert_eq!(
        c.request("denotate/roots", json!({"uri":uri}))["summary"]["state"],
        "proved"
    );
    assert!(c.diagnostics(&uri).as_array().unwrap().is_empty());
    c.change(&uri, 6, &format!("{text} domain lib::S=[];"));
    checking_idle(&mut c);
    let notes = c.diagnostics(&uri);
    assert_eq!(notes.as_array().unwrap().len(), 1, "{notes}");
    assert_eq!(notes[0]["code"], "empty-grouping-domain");
    assert_eq!(notes[0]["severity"], 3);
    assert_eq!(
        c.request("denotate/roots", json!({"uri":uri}))["summary"]["state"],
        "proved"
    );
    let global = text.replace("group_by: (x)", "group_by: ()");
    c.change(&uri, 7, &format!("{global} domain lib::S=[];"));
    checking_idle(&mut c);
    let failures = c.diagnostics(&uri);
    assert_eq!(failures.as_array().unwrap().len(), 1, "{failures}");
    assert_eq!(failures[0]["code"], "counterexample");
    c.change(
        &uri,
        8,
        &text.replace("obligations: [covered]", "obligations: []"),
    );
    checking_idle(&mut c);
    let unchecked = c.diagnostics(&uri);
    assert!(
        unchecked
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["code"] == "unchecked-obligation"),
        "{unchecked}"
    );
    assert!(unchecked
        .as_array()
        .unwrap()
        .iter()
        .all(|d| d["code"] != "counterexample"));
    c.change(&uri, 9, &formatted);
    checking_idle(&mut c);
    assert_eq!(c.diagnostics(&uri).as_array().unwrap().len(), 1);
    assert_eq!(c.diagnostics(&uri)[0]["data"]["finding"], original_identity);
    assert_eq!(
        c.request(
            "textDocument/formatting",
            json!({"textDocument":{"uri":uri},"options":{"tabSize":4,"insertSpaces":true}})
        ),
        json!([])
    );
    c.shutdown();
}
