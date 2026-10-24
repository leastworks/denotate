//! Single-document programs, two-speed diagnostics and a revision-gated worker.
//! The shared editor scheduler owns work; this frontend owns document policy.
#[cfg(test)]
mod deadline;
#[cfg(test)]
mod premask;
#[cfg(test)]
mod prenormalize;
mod worker;

use crate::analysis::{self, Failure};
use crate::{lowering::incremental::Session, syntax};
use denotate_check::Limits;
use denotate_editor::{
    Document, Documents,
    checking::{HoldStage, Job},
    test_support,
    transport::{Result, send},
};
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::{
    Diagnostic, DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    Url,
};
use serde_json::{Value, json};
use std::{collections::BTreeMap, sync::Arc};
use worker::{Event, Identity, Payload, Worker};

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
/// Only populated in DENOTATE_TEST_MODE. Hooks hold a worker at explicit phase
/// boundaries; they neither impose sleeps nor alter checker truth/limits.
#[derive(Default)]
struct TestHooks {
    started: Vec<Value>,
    finished: Vec<Value>,
}
struct Server {
    documents: Documents<OpenDocument>,
    lowering: BTreeMap<Url, Session>,
    parser: tree_sitter::Parser,
    worker: Worker,
    idle: Vec<RequestId>,
    tests: bool,
    hooks: TestHooks,
    shutdown: bool,
    backend: denotate_check::BackendIdentity,
}

pub fn run(connection: &Connection) -> Result<()> {
    run_with_mode(
        connection,
        std::env::var("DENOTATE_TEST_MODE").as_deref() == Ok("1"),
    )
}
/// Explicit test-hook mode for in-process clients of the production server.
pub fn run_with_mode(connection: &Connection, tests: bool) -> Result<()> {
    connection.initialize(json!({
        "positionEncoding": "utf-16",
        "textDocumentSync": {"openClose": true, "change": 2}
    }))?;
    let mut server = Server {
        documents: Documents::default(),
        lowering: BTreeMap::new(),
        parser: syntax::parser()?,
        worker: worker::spawn()?,
        idle: vec![],
        tests,
        hooks: TestHooks::default(),
        shutdown: false,
        backend: denotate_check::BackendIdentity::bdd(),
    };
    let result = server.serve(connection);
    server.stop();
    result
}

impl Server {
    fn serve(&mut self, connection: &Connection) -> Result<()> {
        loop {
            // Shutdown has joined the worker; wait only for the client's exit.
            let events = if self.shutdown {
                crossbeam_channel::never()
            } else {
                self.worker.events().clone()
            };
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
                recv(events) -> event => self.completed(connection, event.map_err(|_| "Checking worker stopped unexpectedly")?)?,
            }
            if !self.shutdown {
                self.start_next()?;
            }
            if self.worker.is_idle() {
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
        self.worker.stop();
    }
    fn cancel(&mut self, uri: &Url) {
        self.worker.cancel(uri);
    }
    fn start_next(&mut self) -> Result<()> {
        if let Some(ticket) = self.worker.start()? {
            if self.tests {
                self.hooks.started.push(identity(&ticket));
            }
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
                    self.worker.hold_next(HoldStage::DuringCheck);
                    Ok(Value::Null)
                }
                Some("beforeResult") => {
                    self.worker.hold_next(HoldStage::BeforeResult);
                    Ok(Value::Null)
                }
                _ => Err((-32602, "Expected afterPrepare or beforeResult")),
            }
        } else if self.tests && request.method == "inputmapping/test/release" {
            match request.params["revision"]
                .as_u64()
                .is_some_and(|r| self.worker.release(r))
            {
                true => Ok(Value::Null),
                false => Err((-32602, "No held worker at that revision")),
            }
        } else if self.tests && request.method == "inputmapping/test/stats" {
            let lowering: BTreeMap<_, _> = self
                .lowering
                .iter()
                .map(|(uri, session)| (uri.as_str(), session.stats()))
                .collect();
            Ok(
                json!({"started": self.hooks.started, "finished": self.hooks.finished, "pending": self.worker.pending().map(|j| identity(&j.ticket)).collect::<Vec<_>>(), "lowering": lowering }),
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
            "workspace/didChangeConfiguration" => {
                let backend = match n.params["settings"]["inputmapping"]["backend"]
                    .as_str()
                    .unwrap_or("bdd")
                {
                    "bdd" => denotate_check::BackendIdentity::bdd(),
                    "sat" => denotate_check::BackendIdentity::sat(),
                    _ => return Err("Expected inputmapping.backend to be bdd or sat".into()),
                };
                if self.backend != backend {
                    self.backend = backend;
                    let docs = self
                        .documents
                        .iter()
                        .filter(|(u, _)| self.documents.rejected_version(u).is_none())
                        .map(|(u, d)| (u.clone(), d.document.text.clone(), d.document.version))
                        .collect::<Vec<_>>();
                    for (uri, text, version) in docs {
                        let document = Document::new(&mut self.parser, text, version, true);
                        self.install(connection, uri, document)?;
                    }
                }
            }
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
                self.worker.close(&uri)?;
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
        let ticket = self.worker.ticket(uri.clone(), document.version);
        let revision = ticket.revision;
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
                (vec![analysis::creator_failure()], None)
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
            self.worker.enqueue(Job {
                ticket,
                payload: Payload {
                    program,
                    backend: self.backend.clone(),
                    measure: self.tests,
                },
                limits: Limits::default(),
            });
        } else {
            self.cancel(&uri);
            if self.tests {
                test_support::validated(connection, &uri, version)?;
            }
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
            Event::Finished(id, (result, check_ns)) => (id, result, check_ns),
        };
        let documents = &self.documents;
        let current = self.worker.complete(&id, || {
            !self.shutdown
                && documents.rejected_version(&id.key).is_none()
                && documents
                    .get(&id.key)
                    .is_some_and(|d| d.revision == id.revision && d.document.version == id.metadata)
        });
        let status = if matches!(result, Err(Failure::Cancelled)) {
            "cancelled"
        } else if !current {
            "discarded"
        } else if matches!(result, Err(Failure::Deadline)) {
            "deadline"
        } else {
            "published"
        };
        if self.tests {
            self.hooks
                .finished
                .push(json!({"snapshot": identity(&id), "status": status, "check_ns": check_ns, "key_computation_ns": result.as_ref().ok().map(|o| o.key_computation.as_nanos()),
                    "summary": result.as_ref().ok().map(|o|denotate_presentation::summary(&o.results.value)),
                    "plans": result.as_ref().ok().and_then(|o| o.plans).map(|p| json!({"executed":p.executed,"reused":p.reused,"fallback":p.fallback,"retained_entries":p.retained_entries,"retained_bytes":p.retained_bytes})),
                    "cache": result.as_ref().ok().and_then(|o| o.cache).map(|c| json!({"evaluation_hits":c.evaluation_hits,"evaluation_misses":c.evaluation_misses,"verdict_hits":c.verdict_hits,"verdict_misses":c.verdict_misses,"completion_hits":c.completion_hits,"completion_misses":c.completion_misses,"retained_entries":c.retained_entries})),
                    "local_evaluation_ns": result.as_ref().ok().and_then(|o| o.local_metrics.as_ref()).map(|m| m.evaluation.as_nanos()),
                    "bdd_export_ns": result.as_ref().ok().and_then(|o| o.local_metrics.as_ref()).map(|m| m.export.as_nanos())}));
        }
        if !current || matches!(result, Err(Failure::Cancelled)) {
            return Ok(());
        }
        let mut diagnostics = self.documents[&id.key].fast.clone();
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
                diagnostics.push(analysis::creator_failure());
            }
            Err(Failure::Deadline) => {
                log(
                    connection,
                    3,
                    "Semantic checking interrupted by deadline.".into(),
                )?;
                diagnostics.push(analysis::deadline_notice());
            }
            Err(Failure::Cancelled) => return Ok(()),
        }
        publish(connection, &id.key, Some(id.metadata), diagnostics)?;
        if self.tests {
            test_support::validated(connection, &id.key, id.metadata)?;
        }
        Ok(())
    }
}

fn identity(id: &Identity) -> Value {
    json!({"uri": id.key, "revision": id.revision, "version": id.metadata})
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
