//! Single-document programs, two-speed diagnostics and a revision-gated worker.
//! B's serial transport loop stays unchanged; this frontend owns scheduling.
mod analysis;
#[cfg(test)]
mod premask;
mod worker;

use analysis::{Failure, diagnostic};
use crossbeam_channel::{Sender, bounded};
use denotate_check::{Cancellation, Limits};
use denotate_editor::{
    Document, Documents, test_support,
    transport::{Result, send},
};
use denotate_test_dsl::{lowering::incremental::Session, syntax};
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, Range, Url,
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, VecDeque},
    sync::Arc,
};
use worker::{Event, Hold, HoldStage, Identity, Job, Worker};

struct OpenDocument {
    document: Arc<Document>,
    revision: u64,
    fast: Vec<Diagnostic>,
}
impl AsRef<Document> for OpenDocument {
    fn as_ref(&self) -> &Document {
        &self.document
    }
}
struct Active {
    id: Identity,
    cancellation: Cancellation,
}

/// Only populated in DENOTATE_TEST_MODE. Hooks hold a worker at explicit phase
/// boundaries; they neither impose sleeps nor alter checker truth/limits.
#[derive(Default)]
struct TestHooks {
    next_hold: Option<HoldStage>,
    releases: BTreeMap<u64, Sender<()>>,
    started: Vec<Value>,
    finished: Vec<Value>,
}
struct Server {
    documents: Documents<OpenDocument>,
    lowering: BTreeMap<Url, Session>,
    parser: tree_sitter::Parser,
    revision: u64,
    worker: Worker,
    active: Option<Active>,
    pending: VecDeque<Job>,
    idle: Vec<RequestId>,
    tests: bool,
    hooks: TestHooks,
    shutdown: bool,
}

pub fn run(connection: &Connection) -> Result<()> {
    connection.initialize(json!({
        "positionEncoding": "utf-16",
        "textDocumentSync": {"openClose": true, "change": 2}
    }))?;
    let mut server = Server {
        documents: Documents::default(),
        lowering: BTreeMap::new(),
        parser: syntax::parser()?,
        revision: 0,
        worker: Worker::spawn()?,
        active: None,
        pending: VecDeque::new(),
        idle: vec![],
        tests: std::env::var("DENOTATE_TEST_MODE").as_deref() == Ok("1"),
        hooks: TestHooks::default(),
        shutdown: false,
    };
    let result = server.serve(connection);
    server.stop();
    server.worker.join();
    result
}

impl Server {
    fn serve(&mut self, connection: &Connection) -> Result<()> {
        loop {
            // Prefer already queued source edits over a completed old result.
            crossbeam_channel::select_biased! {
                recv(connection.receiver) -> message => {
                    let Ok(message) = message else { break };
                    match message {
                        Message::Request(request) => self.request(connection, request)?,
                        Message::Notification(n) if n.method == "exit" => break,
                        Message::Notification(n) if !self.shutdown => {
                            if let Err(error) = self.notification(connection, n) {
                                log(connection, 1, format!("InputMapping notification rejected: {error}"))?;
                            }
                        }
                        _ => (),
                    }
                }
                recv(self.worker.events) -> event => self.completed(connection, event.map_err(|_| "Checking worker stopped unexpectedly")?)?,
            }
            if !self.shutdown {
                self.start_next()?;
            }
            if self.active.is_none() && self.pending.is_empty() {
                for id in self.idle.drain(..) {
                    connection
                        .sender
                        .send(Message::Response(Response::new_ok(id, Value::Null)))?;
                }
            }
        }
        Ok(())
    }

    fn stop(&mut self) {
        if let Some(active) = &self.active {
            active.cancellation.cancel();
        }
        self.pending.clear();
        // Disconnection releases test checkpoints too, including on shutdown.
        self.hooks.releases.clear();
    }
    fn cancel(&mut self, uri: &Url) {
        if let Some(active) = &self.active {
            if &active.id.uri == uri {
                active.cancellation.cancel();
            }
        }
        self.pending.retain(|job| &job.id.uri != uri);
    }
    fn start_next(&mut self) -> Result<()> {
        if self.active.is_some() {
            return Ok(());
        }
        if let Some(mut job) = self.pending.pop_front() {
            if self.tests {
                self.hooks.started.push(identity(&job.id));
                if let Some(stage) = self.hooks.next_hold.take() {
                    let (send, release) = bounded(1);
                    self.hooks.releases.insert(job.id.revision, send);
                    job.hold = Some(Hold { stage, release });
                }
            }
            self.active = Some(Active {
                id: job.id.clone(),
                cancellation: job.limits.cancellation.clone(),
            });
            self.worker.jobs.send(job)?;
        }
        Ok(())
    }

    fn request(&mut self, connection: &Connection, request: Request) -> Result<()> {
        let result = if request.method == "shutdown" {
            self.shutdown = true;
            self.stop();
            Ok(Value::Null)
        } else if self.shutdown {
            Err((-32600, "Server is shutting down"))
        } else if self.tests && request.method == test_support::IDLE {
            self.idle.push(request.id);
            return Ok(());
        } else if self.tests && request.method == "inputmapping/test/hold" {
            match request.params["phase"].as_str() {
                Some("afterPrepare") => {
                    self.hooks.next_hold = Some(HoldStage::AfterPrepare);
                    Ok(Value::Null)
                }
                Some("beforeResult") => {
                    self.hooks.next_hold = Some(HoldStage::BeforeResult);
                    Ok(Value::Null)
                }
                _ => Err((-32602, "Expected afterPrepare or beforeResult")),
            }
        } else if self.tests && request.method == "inputmapping/test/release" {
            match request.params["revision"]
                .as_u64()
                .and_then(|r| self.hooks.releases.remove(&r))
            {
                Some(release) => {
                    let _ = release.send(());
                    Ok(Value::Null)
                }
                None => Err((-32602, "No held worker at that revision")),
            }
        } else if self.tests && request.method == "inputmapping/test/stats" {
            let lowering: BTreeMap<_, _> = self
                .lowering
                .iter()
                .map(|(uri, session)| (uri.as_str(), session.stats()))
                .collect();
            Ok(
                json!({"started": self.hooks.started, "finished": self.hooks.finished, "pending": self.pending.iter().map(|j| identity(&j.id)).collect::<Vec<_>>(), "lowering": lowering }),
            )
        } else {
            Err((-32601, "Unsupported request"))
        };
        let response = match result {
            Ok(value) => Response::new_ok(request.id, value),
            Err((code, message)) => Response::new_err(request.id, code, message.into()),
        };
        connection.sender.send(Message::Response(response))?;
        Ok(())
    }

    fn notification(&mut self, connection: &Connection, n: Notification) -> Result<()> {
        match n.method.as_str() {
            "textDocument/didOpen" => {
                let p: DidOpenTextDocumentParams = serde_json::from_value(n.params)?;
                let t = p.text_document;
                let document = Document::new(&mut self.parser, t.text, t.version, true);
                // An explicit open starts a fresh session, even for a reused URI.
                self.lowering.remove(&t.uri);
                self.install(connection, t.uri, document)?;
            }
            "textDocument/didChange" => {
                let p =
                    match serde_json::from_value::<DidChangeTextDocumentParams>(n.params.clone()) {
                        Ok(p) => p,
                        Err(error) => {
                            if let Some((uri, version)) =
                                self.documents.malformed_change(&n.params["textDocument"])
                            {
                                self.lose_sync(connection, &uri, version)?;
                            }
                            return Err(error.into());
                        }
                    };
                let uri = p.text_document.uri;
                let version = p.text_document.version;
                let updated = (|| -> std::result::Result<Option<Document>, &'static str> {
                    let Some(changes) =
                        self.documents.changes(&uri, version, &p.content_changes)?
                    else {
                        return Ok(None);
                    };
                    self.documents[&uri]
                        .document
                        .changed(&mut self.parser, changes, version)
                        .map(Some)
                })();
                match updated {
                    Ok(Some(document)) => self.install(connection, uri, document)?,
                    Ok(None) => (),
                    Err(error) => {
                        if self.documents.contains_key(&uri) {
                            self.lose_sync(connection, &uri, version)?;
                        }
                        return Err(error.into());
                    }
                }
            }
            "textDocument/didClose" => {
                let p: DidCloseTextDocumentParams = serde_json::from_value(n.params)?;
                let uri = p.text_document.uri;
                self.cancel(&uri);
                self.documents.remove(&uri);
                self.lowering.remove(&uri);
                publish(connection, &uri, None, vec![])?;
            }
            "$/cancelRequest" => {
                // Only idle can be pending as a request. Analysis is cancelled
                // by source revisions, not by an unrelated request's ID.
                if let Some(index) = self.idle.iter().position(|id| json!(id) == n.params["id"]) {
                    connection.sender.send(Message::Response(Response::new_err(
                        self.idle.remove(index),
                        -32800,
                        "Request cancelled".into(),
                    )))?;
                }
            }
            _ => (), // No disk indexing, workspace mutation or language-service requests.
        }
        Ok(())
    }

    fn lose_sync(&mut self, connection: &Connection, uri: &Url, version: i32) -> Result<()> {
        self.cancel(uri);
        if self.documents.lose_sync(uri, version) {
            publish(connection, uri, None, vec![])?;
        }
        Ok(())
    }

    fn install(&mut self, connection: &Connection, uri: Url, document: Document) -> Result<()> {
        self.cancel(&uri);
        self.revision = self
            .revision
            .checked_add(1)
            .ok_or("Snapshot revision overflow")?;
        let revision = self.revision;
        let version = document.version;
        let document = Arc::new(document);
        let lowering = self
            .lowering
            .entry(uri.clone())
            .or_insert_with(|| Session::new(self.tests));
        let (fast, program) = match analysis::prepare(&uri, revision, document.clone(), lowering) {
            Ok(p) => (p.fast, p.program),
            Err(error) => {
                log(
                    connection,
                    1,
                    format!("DSL implementation failure: {error}"),
                )?;
                (vec![creator_failure()], None)
            }
        };
        self.documents.insert(
            uri.clone(),
            OpenDocument {
                document,
                revision,
                fast: fast.clone(),
            },
        );
        publish(connection, &uri, Some(version), fast)?;
        if self.tests {
            test_support::frontend_ready(connection, &uri, version)?;
        }
        if let Some(program) = program {
            self.pending.push_back(Job {
                id: Identity {
                    uri,
                    revision,
                    version,
                },
                program,
                limits: Limits::default(),
                hold: None,
                measure: self.tests,
            });
        } else if self.tests {
            test_support::validated(connection, &uri, version)?;
        }
        Ok(())
    }

    fn completed(&mut self, connection: &Connection, event: Event) -> Result<()> {
        let (id, result, check_ns) = match event {
            Event::Checkpoint(id) => {
                if self.tests {
                    send(connection, "inputmapping/test/checkpoint", identity(&id))?;
                }
                return Ok(());
            }
            Event::Finished(id, result, check_ns) => (id, result, check_ns),
        };
        self.active = None;
        self.hooks.releases.remove(&id.revision);
        let current = !self.shutdown
            && self.documents.rejected_version(&id.uri).is_none()
            && self
                .documents
                .get(&id.uri)
                .is_some_and(|d| d.revision == id.revision && d.document.version == id.version);
        let status = if matches!(result, Err(Failure::Cancelled)) {
            "cancelled"
        } else if !current {
            "discarded"
        } else {
            "published"
        };
        if self.tests {
            self.hooks
                .finished
                .push(json!({"snapshot": identity(&id), "status": status, "check_ns": check_ns}));
        }
        if !current || matches!(result, Err(Failure::Cancelled)) {
            return Ok(());
        }
        let mut diagnostics = self.documents[&id.uri].fast.clone();
        match result {
            Ok(output) => {
                diagnostics.extend(output.diagnostics);
                for message in output.creator_warnings {
                    log(connection, 2, format!("DSL library warning: {message}"))?;
                }
            }
            Err(Failure::Creator(error)) => {
                log(
                    connection,
                    1,
                    format!("DSL implementation failure: {error}"),
                )?;
                diagnostics.push(creator_failure());
            }
            Err(Failure::Cancelled) => return Ok(()),
        }
        publish(connection, &id.uri, Some(id.version), diagnostics)?;
        if self.tests {
            test_support::validated(connection, &id.uri, id.version)?;
        }
        Ok(())
    }
}

fn identity(id: &Identity) -> Value {
    json!({"uri": id.uri, "revision": id.revision, "version": id.version})
}
fn publish(
    connection: &Connection,
    uri: &Url,
    version: Option<i32>,
    diagnostics: Vec<Diagnostic>,
) -> Result<()> {
    send(
        connection,
        "textDocument/publishDiagnostics",
        json!({"uri": uri, "version": version, "diagnostics": diagnostics}),
    )
}
fn log(connection: &Connection, kind: u32, message: String) -> Result<()> {
    send(
        connection,
        "window/logMessage",
        json!({"type": kind, "message": message}),
    )
}
fn creator_failure() -> Diagnostic {
    diagnostic(Range::default(), "creator-failure", "Semantic checking failed inside the DSL implementation; see the server log. This is not an error in a mapping.".into(), DiagnosticSeverity::INFORMATION)
}
