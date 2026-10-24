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
    checking::Job,
    checking_server::{self, CheckingHandler},
    lifecycle, publication,
    publication::publish,
    test_support::{self, CheckingHooks},
    transport::{self, Result, send},
};
use lsp_server::{Connection, Notification, Request, ResponseError};
use lsp_types::{Diagnostic, Url};
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
struct Server {
    documents: Documents<OpenDocument>,
    lowering: BTreeMap<Url, Session>,
    published: BTreeMap<Url, Vec<Diagnostic>>,
    parser: tree_sitter::Parser,
    worker: Worker,
    tests: bool,
    hooks: CheckingHooks,
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
        published: BTreeMap::new(),
        parser: syntax::parser()?,
        worker: worker::spawn()?,
        tests,
        hooks: CheckingHooks::default(),
        backend: denotate_check::BackendIdentity::bdd(),
    };
    checking_server::run(&mut server, connection)
}

impl Server {
    fn cancel(&mut self, uri: &Url) {
        self.worker.cancel(uri);
    }
    fn notification(&mut self, connection: &Connection, n: Notification) -> Result<()> {
        if lifecycle::handles(&n.method) {
            return lifecycle::notification(self, connection, n);
        }
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
            _ => (), // No disk indexing, workspace mutation or language-service requests.
        }
        Ok(())
    }

    fn lose_sync(&mut self, connection: &Connection, uri: &Url, version: i32) -> Result<()> {
        self.cancel(uri);
        publication::lose_sync(connection, &mut self.documents, uri, version)?;
        // Like B, republish the still-current diagnostics of other synchronized
        // documents. Keep their semantic findings, not just the fast diagnostics.
        for (other, document) in self
            .documents
            .iter()
            .filter(|(u, _)| *u != uri && self.documents.rejected_version(u).is_none())
        {
            publish(
                connection,
                other,
                Some(document.document.version),
                self.published.get(other).cloned().unwrap_or_default(),
            )?;
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
        self.published.insert(uri.clone(), fast.clone());
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
                    send(connection, test_support::CHECKPOINT, identity(&id))?;
                }
                return Ok(());
            }
            Event::Finished(id, (result, check_ns)) => (id, result, check_ns),
        };
        let documents = &self.documents;
        let current = self.worker.complete(&id, || {
            documents.rejected_version(&id.key).is_none()
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
        self.published.insert(id.key.clone(), diagnostics.clone());
        publish(connection, &id.key, Some(id.metadata), diagnostics)?;
        if self.tests {
            test_support::validated(connection, &id.key, id.metadata)?;
            send(connection, test_support::CHECKED, identity(&id))?;
        }
        Ok(())
    }
}

impl transport::Handler for Server {
    fn supports_request(&self, method: &str) -> bool {
        self.tests && method == test_support::IDLE
    }
    fn request(&mut self, _: &Request) -> std::result::Result<Value, ResponseError> {
        Ok(Value::Null)
    }
    fn unsupported_request(&self, _: &Request) -> ResponseError {
        ResponseError {
            code: -32601,
            message: "Unsupported request".into(),
            data: None,
        }
    }
    fn notification(&mut self, connection: &Connection, n: Notification) -> Result<()> {
        Server::notification(self, connection, n)
    }
}
impl CheckingHandler for Server {
    type Key = Url;
    type Payload = Payload;
    type Output = worker::Checked;
    type Metadata = i32;
    fn scheduler(&mut self) -> &mut Worker {
        &mut self.worker
    }
    fn hooks(&mut self) -> &mut CheckingHooks {
        &mut self.hooks
    }
    fn test_mode(&self) -> bool {
        self.tests
    }
    fn identity(ticket: &Identity) -> Value {
        identity(ticket)
    }
    fn completed(&mut self, connection: &Connection, event: Event) -> Result<()> {
        Server::completed(self, connection, event)
    }
    fn reset_checks(&mut self, connection: &Connection) -> Result<()> {
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
        Ok(())
    }
    fn extra_stats(&self) -> Value {
        let lowering: BTreeMap<_, _> = self
            .lowering
            .iter()
            .map(|(uri, session)| (uri.as_str(), session.stats()))
            .collect();
        json!({"lowering":lowering})
    }
    fn notification_error(
        &mut self,
        connection: &Connection,
        error: Box<dyn std::error::Error>,
    ) -> Result<()> {
        log(
            connection,
            1,
            format!("InputMapping notification rejected: {error}"),
        )
    }
}
impl lifecycle::Lifecycle for Server {
    type Stored = OpenDocument;
    type Parsed = Document;
    fn documents_and_parser(&mut self) -> (&Documents<OpenDocument>, &mut tree_sitter::Parser) {
        (&self.documents, &mut self.parser)
    }
    fn parse_open(parser: &mut tree_sitter::Parser, text: String, version: i32) -> Document {
        Document::new(parser, text, version, true)
    }
    fn parse_change(
        previous: &OpenDocument,
        parser: &mut tree_sitter::Parser,
        changes: &[lsp_types::TextDocumentContentChangeEvent],
        version: i32,
    ) -> std::result::Result<Document, &'static str> {
        previous.document.changed(parser, changes, version)
    }
    fn stored(
        &mut self,
        connection: &Connection,
        uri: Url,
        document: Document,
        opened: bool,
        _: bool,
    ) -> Result<()> {
        // An explicit open starts fresh lowering, even for a reused URI.
        if opened {
            self.lowering.remove(&uri);
        }
        self.install(connection, uri, document)
    }
    fn removed(&mut self, connection: &Connection, uri: &Url) -> Result<()> {
        self.cancel(uri);
        self.documents.remove(uri);
        self.lowering.remove(uri);
        self.published.remove(uri);
        self.worker.close(uri)?;
        publication::withdraw(connection, uri)
    }
    fn sync_lost(&mut self, connection: &Connection, uri: &Url, version: i32) -> Result<()> {
        self.lose_sync(connection, uri, version)
    }
}

fn identity(id: &Identity) -> Value {
    json!({"uri": id.key, "revision": id.revision, "version": id.metadata})
}
fn log(connection: &Connection, kind: u32, message: String) -> Result<()> {
    send(
        connection,
        "window/logMessage",
        json!({"type": kind, "message": message}),
    )
}
