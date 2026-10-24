//! Both real editor loops, their workers and actual LSP publications. Structural
//! correspondence translates frontend-local keys; messages/counts are not goldens.
use super::*;
use denotate_check::*;
use denotate_ir::*;
use denotate_ir_text::*;
use denotate_test_dsl::export;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
    thread::JoinHandle,
    time::Duration,
};
#[path = "../../../native/ir-text/tests/support/mod.rs"]
mod correspondence;

struct Client {
    connection: Connection,
    thread: Option<JoinHandle<()>>,
    serial: i32,
    published: BTreeMap<String, Value>,
    origins: BTreeMap<String, String>,
}
impl Client {
    fn start(root: &Path, den: bool, origins: BTreeMap<String, String>) -> Self {
        let (server, connection) = Connection::memory();
        let thread = std::thread::spawn(move || {
            if den {
                run_with_mode(&server, true).unwrap();
            } else {
                denotate_test_dsl::server::run_with_mode(&server, true).unwrap();
            }
        });
        let mut c = Self {
            connection,
            thread: Some(thread),
            serial: 0,
            published: BTreeMap::new(),
            origins,
        };
        c.request("initialize",json!({"capabilities":{},"workspaceFolders":[{"uri":Url::from_directory_path(root).unwrap(),"name":"parity"}],"initializationOptions":{"originSnapshotBridge":true}}));
        c.notify("initialized", json!({}));
        c
    }
    fn notify(&self, method: &str, value: Value) {
        self.connection
            .sender
            .send(Message::Notification(Notification::new(
                method.into(),
                value,
            )))
            .unwrap();
    }
    fn request(&mut self, method: &str, params: Value) -> Value {
        self.serial += 1;
        let id = self.serial.into();
        self.connection
            .sender
            .send(Message::Request(Request::new(id, method.into(), params)))
            .unwrap();
        loop {
            match self
                .connection
                .receiver
                .recv_timeout(Duration::from_secs(30))
                .unwrap_or_else(|e| panic!("{method}: {e}"))
            {
                Message::Response(r) => {
                    assert_eq!(r.id, self.serial.into());
                    assert!(r.error.is_none(), "{:?}", r.error);
                    return r.result.unwrap();
                }
                Message::Notification(n) => {
                    if n.method == "textDocument/publishDiagnostics" {
                        self.published
                            .insert(n.params["uri"].as_str().unwrap().into(), n.params);
                    }
                }
                Message::Request(r) => {
                    assert_eq!(r.method, "denotate/originSnapshot");
                    let uri = r.params["uri"].as_str().unwrap();
                    let snapshot=self.origins.get(uri).map(|text|json!({"uri":uri,"text":text,"open":true,"dirty":true,"generation":1,"version":1})).unwrap_or(json!({"uri":uri,"unavailable":"no test snapshot"}));
                    self.connection
                        .sender
                        .send(Message::Response(lsp_server::Response::new_ok(
                            r.id, snapshot,
                        )))
                        .unwrap();
                }
            }
        }
    }
    fn call(&mut self, method: &str, params: Value) -> Value {
        self.request(method, params)
    }
    fn open(&self, uri: &str, text: &str, version: u64) {
        self.notify("textDocument/didOpen",json!({"textDocument":{"uri":uri,"text":text,"version":version,"languageId":"denotate"}}));
    }
    fn change(&self, uri: &str, text: &str, version: u64) {
        self.notify(
            "textDocument/didChange",
            json!({"textDocument":{"uri":uri,"version":version},"contentChanges":[{"text":text}]}),
        );
    }
    fn shutdown(mut self) {
        self.call("shutdown", Value::Null);
        self.notify("exit", Value::Null);
        self.thread.take().unwrap().join().unwrap();
    }
}
impl Drop for Client {
    fn drop(&mut self) {
        if self.thread.is_some() {
            self.notify("exit", Value::Null);
        }
    }
}
struct Directory(std::path::PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "denotate-publication-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path.canonicalize().unwrap())
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn cases() -> Vec<(String, SourceFile)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../native/test-dsl");
    let mut cases = vec![];
    for (id, path) in [
        ("text/overlap", "fixtures/overlapping-mappings.txt"),
        (
            "text/vscode-overlap",
            "vscode/examples/overlap.inputmapping",
        ),
        ("text/vscode-values", "vscode/examples/values.inputmapping"),
    ] {
        cases.push((
            id.into(),
            SourceFile::new(
                format!("file:///{id}.inputmapping"),
                1,
                std::fs::read_to_string(root.join(path)).unwrap(),
            ),
        ));
    }
    let pre: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("fixtures/pre-normalize.json")).unwrap(),
    )
    .unwrap();
    for i in (0..=13).chain(17..=31).chain(35..=37) {
        cases.push((
            format!("pre-normalize/{i:02}"),
            SourceFile::new(
                "file:///case.inputmapping",
                1,
                pre["cases"][i]["text"].as_str().unwrap(),
            ),
        ));
    }
    let pre: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("fixtures/pre-integration-fingerprints.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(pre["cases"].as_array().unwrap().len(), 84);
    for (i, c) in pre["cases"].as_array().unwrap().iter().enumerate() {
        cases.push((
            format!("pre-integration/{i:02}"),
            SourceFile::new(
                "file:///case.inputmapping",
                c["revision"].as_u64().unwrap(),
                c["text"].as_str().unwrap(),
            ),
        ));
    }
    assert_eq!(cases.len(), 119);
    cases
}
fn protocol_keys(
    original: &Corpus,
    old: &SemanticKeys,
    loaded: &LoadedProgram,
    ids: &BTreeMap<OccurrenceId, OccurrenceId>,
) -> BTreeMap<String, Value> {
    let mut keys = BTreeMap::new();
    let mut bind = |a: Value, b: Value| {
        keys.insert(b.to_string(), a);
    };
    let relation = |keys: &SemanticKeys, id| {
        denotate_presentation::atom_data(&AtomKey {
            relation: keys.relation(id).unwrap().clone(),
            arguments: vec![],
        })["relation"]
            .clone()
    };
    let ckey = |keys: &SemanticKeys, id, r| {
        denotate_presentation::atom_data(&AtomKey {
            relation: keys.relation(r).unwrap().clone(),
            arguments: vec![keys.constant(id).unwrap().clone()],
        })["arguments"][0]
            .clone()
    };
    let first = original.relations().next().unwrap().id;
    let next = loaded
        .corpus
        .relations()
        .find(|r| OccurrenceId::from(r.id) == ids[&first.into()])
        .unwrap()
        .id;
    for a in original.relations() {
        let b = loaded
            .corpus
            .relations()
            .find(|r| OccurrenceId::from(r.id) == ids[&a.id.into()])
            .unwrap();
        bind(relation(old, a.id), relation(&loaded.keys, b.id));
    }
    for a in original.constants() {
        let b = loaded
            .corpus
            .constants()
            .find(|c| OccurrenceId::from(c.id) == ids[&a.id.into()])
            .unwrap();
        bind(ckey(old, a.id, first), ckey(&loaded.keys, b.id, next));
    }
    for a in original.obligations() {
        let b = loaded
            .corpus
            .obligations()
            .find(|o| OccurrenceId::from(o.id) == ids[&a.id.into()])
            .unwrap();
        let key = |id, keys| {
            denotate_presentation::Identity::Group {
                obligation: id,
                tuple: vec![],
            }
            .data(keys)
            .unwrap()["group"]["obligation"]
                .clone()
        };
        bind(key(a.id, old), key(b.id, &loaded.keys));
    }
    keys
}
fn translate(value: &Value, keys: &BTreeMap<String, Value>) -> Value {
    if let Some(mapped) = keys.get(&value.to_string()) {
        return mapped.clone();
    }
    match value {
        Value::Array(a) => json!(a.iter().map(|v| translate(v, keys)).collect::<Vec<_>>()),
        Value::Object(o) => json!(o
            .iter()
            .map(|(k, v)| {
                let mut v = translate(v, keys);
                if [
                    "region",
                    "regions",
                    "groups",
                    "incomplete",
                    "activeAssumptions",
                ]
                .contains(&k.as_str())
                {
                    if let Some(a) = v.as_array_mut() {
                        a.sort_by_key(Value::to_string);
                    }
                }
                (k, v)
            })
            .collect::<BTreeMap<_, _>>()),
        _ => value.clone(),
    }
}
fn findings(
    publications: &BTreeMap<String, Value>,
    root: &str,
    keys: &BTreeMap<String, Value>,
) -> BTreeSet<String> {
    publications
        .values()
        .flat_map(|p| p["diagnostics"].as_array().unwrap())
        .filter(|d| d["data"]["program"] == root && d["data"]["kind"] != "redundant")
        .map(|d| {
            assert!(d["data"]["finding"].is_object());
            translate(
                &json!({"identity":d["data"]["finding"],"kind":d["data"]["kind"]}),
                keys,
            )
            .to_string()
        })
        .collect()
}
fn summary(mut s: Value, keys: &BTreeMap<String, Value>) -> Value {
    let o = s.as_object_mut().unwrap();
    for key in ["program", "findings", "originNotices"] {
        o.remove(key);
    }
    translate(&s, keys)
}

#[test]
fn published_parity_119_programs_bdd_sat_cold_warm_and_exact_origins() {
    let mut entries = cases();
    entries.push((
        "exact-span".into(),
        SourceFile::new(
            "file:///exact.inputmapping",
            1,
            "input i, j; slot a; a <- i; a <- j;",
        ),
    ));
    for (id, source) in entries {
        eprintln!("published parity: {id}");
        let assembled = export::assemble(&[source.clone()]).unwrap();
        let p = &assembled.program;
        let paths = assembled
            .sources
            .snapshots()
            .map(|s| (s.id, "sources/program.den".into()))
            .collect();
        let layout = export::layout(p, &assembled.sources, &paths).unwrap();
        let domains = p.domains();
        let assumptions = export::assumptions(p);
        let export = ExportProgram {
            corpus: &p.corpus,
            domains: &domains,
            sources: &assembled.sources,
            provenance: &p.attribution.provenance,
            assumptions: &assumptions,
            layout: &layout,
        };
        let bundle = print(&export, PrintOptions::default()).unwrap();
        let dir = Directory::new();
        for (path, text) in &bundle.files {
            let path = dir.0.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        }
        let base = Url::from_directory_path(&dir.0).unwrap().to_string();
        let (membership, files) = bundle.documents(base.trim_end_matches('/'));
        let loaded =
            load_with_resolver(&membership, &files, Some(&mut &assembled.sources)).unwrap();
        let map = correspondence::compare(&export, &loaded, base.trim_end_matches('/'), true);
        let keys = protocol_keys(&p.corpus, &p.keys, &loaded, &map.ids);
        let origins = BTreeMap::from([(source.uri.clone(), source.text.to_string())]);
        for backend in ["bdd", "sat"] {
            let mut den = Client::start(&dir.0, true, origins.clone());
            let mut dsl = Client::start(&dir.0, false, BTreeMap::new());
            den.notify(
                "workspace/didChangeConfiguration",
                json!({"settings":{"denotate":{"backend":backend}}}),
            );
            dsl.notify(
                "workspace/didChangeConfiguration",
                json!({"settings":{"inputmapping":{"backend":backend}}}),
            );
            let mut previous = None;
            for warm in 0..2 {
                let version = source.revision + warm;
                if warm == 0 {
                    dsl.open(&source.uri, &source.text, version);
                } else {
                    dsl.change(&source.uri, &source.text, version);
                }
                for file in &files {
                    if warm == 0 {
                        den.open(&file.uri, &file.text, version);
                    } else {
                        den.change(&file.uri, &file.text, version);
                    }
                }
                dsl.call("denotate/test/idle", json!({}));
                den.call("denotate/test/checkingIdle", json!({}));
                if warm == 0 {
                    // Workspace discovery may check disk snapshots before opens.
                    // Reset after synchronization so this is a truly cold session.
                    den.call("denotate/test/resetChecks", json!({}));
                    den.call("denotate/test/checkingIdle", json!({}));
                }
                assert_eq!(dsl.published[&source.uri]["version"], version);
                for file in &files {
                    assert_eq!(den.published[&file.uri]["version"], version);
                }
                let left = findings(&dsl.published, &source.uri, &BTreeMap::new());
                let right = findings(&den.published, &membership.root, &keys);
                assert_eq!(left, right, "{id} {backend} warm={warm}");
                let stats = dsl.call("inputmapping/test/stats", json!({}));
                let ds = summary(
                    stats["finished"].as_array().unwrap().last().unwrap()["summary"].clone(),
                    &BTreeMap::new(),
                );
                let status=den.call("denotate/roots",json!({"uri":files.iter().find(|f|f.uri.ends_with("sources/program.den")).unwrap().uri}));
                assert_eq!(status["checking"], "complete", "{id}: {status}");
                let ns = summary(status["summary"].clone(), &keys);
                assert_eq!(ds, ns, "{id} {backend} summaries");
                if let Some((old_findings, old_summary)) = &previous {
                    assert_eq!(&left, old_findings);
                    assert_eq!(&ds, old_summary);
                }
                previous = Some((left, ds));
                validate_published_witnesses(
                    &den.published,
                    &membership.root,
                    &loaded.corpus,
                    &loaded.keys,
                    &loaded
                        .request(
                            &Limits::default(),
                            if backend == "bdd" {
                                BackendIdentity::bdd()
                            } else {
                                BackendIdentity::sat()
                            },
                        )
                        .unwrap(),
                );
                validate_producer_origins(&den.published, &loaded);
                let mut request = p.request(&Limits::default()).unwrap();
                request.backend = if backend == "bdd" {
                    BackendIdentity::bdd()
                } else {
                    BackendIdentity::sat()
                };
                validate_published_witnesses(
                    &dsl.published,
                    &source.uri,
                    &p.corpus,
                    &p.keys,
                    &request,
                );
                if id == "exact-span" {
                    let dsl_spans = dsl.published[&source.uri]["diagnostics"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .filter(|d| d["data"]["kind"] == "counterexample")
                        .map(|d| json!({"uri":source.uri,"range":d["range"]}).to_string())
                        .collect::<BTreeSet<_>>();
                    assert_eq!(dsl_spans.len(), 2);
                    let den_spans = den
                        .published
                        .values()
                        .flat_map(|p| p["diagnostics"].as_array().unwrap())
                        .filter(|d| {
                            d["data"]["program"] == membership.root
                                && d["data"]["kind"] == "counterexample"
                        })
                        .flat_map(|d| d["relatedInformation"].as_array().unwrap())
                        .map(|r| r["location"].to_string())
                        .collect::<BTreeSet<_>>();
                    assert!(dsl_spans.is_subset(&den_spans));
                    let bytes = |position: &Value| {
                        assert_eq!(position["line"], 0);
                        let col = position["character"].as_u64().unwrap() as usize;
                        assert!(source.text.is_ascii());
                        col
                    };
                    let expected=dsl.published[&source.uri]["diagnostics"].as_array().unwrap().iter().filter(|d|d["data"]["kind"]=="counterexample").map(|d|json!({"uri":source.uri,"view":"test-dsl","hash":origins::content_hash(&source.text),"bytes":[bytes(&d["range"]["start"]),bytes(&d["range"]["end"])]}).to_string()).collect::<BTreeSet<_>>();
                    let generic = den
                        .published
                        .values()
                        .flat_map(|p| p["diagnostics"].as_array().unwrap())
                        .filter(|d| {
                            d["data"]["program"] == membership.root
                                && d["data"]["kind"] == "counterexample"
                        })
                        .collect::<Vec<_>>();
                    let actual = generic
                        .iter()
                        .flat_map(|d| d["data"]["locations"]["related"].as_array().unwrap())
                        .map(Value::to_string)
                        .collect::<BTreeSet<_>>();
                    assert!(expected.is_subset(&actual));
                    for d in generic {
                        let primary = &d["data"]["locations"]["primary"];
                        let file = files.iter().find(|f| primary["uri"] == f.uri).unwrap();
                        assert_eq!(primary["hash"], origins::content_hash(&file.text));
                        let range = primary["bytes"][0].as_u64().unwrap() as usize
                            ..primary["bytes"][1].as_u64().unwrap() as usize;
                        assert!(file.text[range].contains("mapped_to"));
                    }
                    assert!(status["originNotices"].as_array().unwrap().is_empty());
                }
            }
            dsl.shutdown();
            den.shutdown();
        }
    }
}

fn validate_published_witnesses(
    publications: &BTreeMap<String, Value>,
    root: &str,
    corpus: &Corpus,
    keys: &SemanticKeys,
    request: &CheckRequest,
) {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let RequestPreparation::Complete(ground) = request.prepare(corpus, keys, &ops).unwrap() else {
        panic!("default preparation incomplete")
    };
    let ground = ground.admit(&ops).unwrap();
    let program = ground.program();
    let atoms = program
        .atoms()
        .map(|a| {
            (
                denotate_presentation::atom_data(&AtomKey::from_atom(keys, a).unwrap()).to_string(),
                a.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut seen = BTreeSet::new();
    for d in publications
        .values()
        .flat_map(|p| p["diagnostics"].as_array().unwrap())
        .filter(|d| d["data"]["program"] == root)
    {
        let data = &d["data"];
        let e = &data["evidence"];
        if !seen.insert(e.to_string()) {
            continue;
        }
        if e["kind"] == "unfounded-support-world" {
            assert_ne!(data["kind"], "counterexample");
            assert!(e.get("tuples").is_none());
        }
        if data["kind"] != "counterexample" {
            continue;
        }
        assert_eq!(e["kind"], "replayed-counterexample");
        assert!(!e["producers"].as_array().unwrap().is_empty());
        let present = e["observation"]["present"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| atoms[&a.to_string()].clone())
            .collect::<BTreeSet<_>>();
        let absent = e["observation"]["absent"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| atoms[&a.to_string()].clone())
            .collect::<BTreeSet<_>>();
        assert!(present.is_disjoint(&absent));
        assert_eq!(
            present.union(&absent).cloned().collect::<BTreeSet<_>>(),
            program.input_atoms().cloned().collect()
        );
        let replay = program.evaluate(present.iter().cloned(), &limits).unwrap();
        let tuples = e["tuples"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| atoms[&a.to_string()].clone())
            .collect::<BTreeSet<_>>();
        assert!(tuples.len() >= 2);
        for tuple in tuples {
            if !matches!(replay.fact(&tuple).unwrap(), FactState::Settled(true)) {
                let CertificationOutcome::Certified(c) = program
                    .certify_observation(present.iter().cloned(), &limits)
                    .unwrap()
                else {
                    panic!("published witness failed certification")
                };
                assert!(c.facts.contains(&tuple));
            }
        }
    }
}

fn validate_producer_origins(publications: &BTreeMap<String, Value>, program: &LoadedProgram) {
    let producers = program
        .corpus
        .rules()
        .map(|r| {
            let identity = denotate_presentation::Identity::Rewrite {
                rule: r.id,
                literal: Some(r.id.into()),
            }
            .data(&program.keys)
            .unwrap();
            (identity["rewrite"]["literal"].to_string(), r.id)
        })
        .collect::<BTreeMap<_, _>>();
    for d in publications
        .values()
        .flat_map(|p| p["diagnostics"].as_array().unwrap())
        .filter(|d| d["data"]["program"] == program.root && d["data"]["kind"] == "counterexample")
    {
        let locations = &d["data"]["locations"];
        let actual = std::iter::once(locations["primary"].clone())
            .chain(locations["related"].as_array().unwrap().iter().cloned())
            .map(|v| v.to_string())
            .collect::<BTreeSet<_>>();
        for producer in d["data"]["evidence"]["producers"].as_array().unwrap() {
            let rule = producers[&producer.to_string()];
            for origin in program
                .provenance
                .origins(rule)
                .iter()
                .chain(program.embedded.provenance.origins(rule))
            {
                let snapshot = program.sources.snapshot(origin.span.snapshot()).unwrap();
                let range = origin.span.byte_range();
                let expected = json!({"uri":snapshot.uri,"view":snapshot.view,"hash":origins::content_hash(&snapshot.text),"bytes":[range.start,range.end]}).to_string();
                assert!(
                    actual.contains(&expected),
                    "published witness producer missing its own origin"
                );
            }
        }
    }
}
