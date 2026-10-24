//! The editor owns scheduling and immutable observations. The worker owns only
//! root-keyed checker sessions; all publication passes back through the owner.
use crate::{
    bridge::Bridge,
    catalog,
    presentation::{self, Publication},
    Server,
};
use denotate_check::*;
use denotate_editor::checking::{self, HoldStage, Job, Scheduler};
use denotate_editor::transport::{self, send, Result};
use denotate_ir_text::{ProgramMembership, SourceFile};
use lsp_server::{Connection, Message, RequestId, Response};
use lsp_types::{Diagnostic, Url};
use serde_json::{json, Value};
use std::collections::{BTreeMap, VecDeque};

#[derive(Clone, PartialEq, Eq)]
pub struct Config {
    pub backend: BackendIdentity,
    pub timeout_ms: u64,
}
impl Default for Config {
    fn default() -> Self {
        Self {
            backend: BackendIdentity::bdd(),
            timeout_ms: 10_000,
        }
    }
}
impl Config {
    pub fn read(value: &Value) -> std::result::Result<Self, &'static str> {
        let backend = match value["backend"].as_str().unwrap_or("bdd") {
            "bdd" => BackendIdentity::bdd(),
            "sat" => BackendIdentity::sat(),
            _ => return Err("Expected denotate.backend to be bdd or sat"),
        };
        let timeout_ms = value
            .get("timeoutMs")
            .map(|v| v.as_u64().ok_or("Expected nonnegative timeoutMs"))
            .transpose()?
            .unwrap_or(10_000);
        Ok(Self {
            backend,
            timeout_ms,
        })
    }
}
#[derive(Clone)]
struct Snapshot {
    membership: ProgramMembership,
    files: Vec<SourceFile>,
    // Complete authoritative observations, including buffer state, manifests,
    // destination homes, origin epochs and configuration. Equality, not hashes.
    key: Value,
    bridge: Bridge,
    config: Config,
    label: String,
}
struct Payload {
    snapshot: Snapshot,
    measure: bool,
}
type Output = (std::result::Result<Publication, Failure>, Value);
type Worker = Scheduler<String, Payload, Output>;
pub type Event = checking::Event<String, Output>;
#[derive(Debug)]
pub enum Failure {
    Cancelled,
    Deadline,
    Invalid(Vec<denotate_ir_text::Diagnostic>),
    Internal(String),
}
impl From<CheckError> for Failure {
    fn from(e: CheckError) -> Self {
        match e {
            CheckError::Cancelled => Self::Cancelled,
            CheckError::Deadline { .. } => Self::Deadline,
            _ => Self::Internal(e.to_string()),
        }
    }
}
fn check(
    job: &Job<String, Payload>,
    session: &mut denotate_check_session::Session,
) -> std::result::Result<Publication, Failure> {
    job.limits.cancellation.check()?;
    let s = &job.payload.snapshot;
    let program =
        denotate_ir_text::load_with_resolver(&s.membership, &s.files, Some(&mut &s.bridge))
            .map_err(Failure::Invalid)?;
    job.limits.cancellation.check()?;
    let request = program.request(&job.limits, s.config.backend.clone())?;
    let operations = OperationalLimits::from(&job.limits);
    let exhausted = |reason| Publication {
        diagnostics: BTreeMap::new(),
        status: denotate_presentation::summary(&request.exhausted(reason)),
    };
    let ground = match session.prepare(&request, &program.corpus, &program.keys, &operations)? {
        RequestPreparation::Complete(p) => p,
        RequestPreparation::Inconclusive { reason, .. } => return Ok(exhausted(reason)),
    };
    let ground = ground.admit(&operations)?;
    let mut publication = match session.verify(&ground, &operations)? {
        LocalCheckOutcome::Complete(report) => {
            presentation::present(&program, &report.checked).map_err(Failure::Internal)?
        }
        LocalCheckOutcome::Inconclusive { reason, .. } => exhausted(reason),
    };
    publication.status["originNotices"] = json!(program.embedded.notices.iter().map(|n|json!({"uri":n.source.uri,"view":n.source.view,"hash":n.source.hash,"reason":format!("{:?}",n.reason)})).collect::<Vec<_>>());
    for diagnostics in publication.diagnostics.values_mut() {
        for d in diagnostics {
            if d.data.as_ref().is_some_and(|v| v["fallback"] == true) {
                let prefix = format!("in {}: ", program.root);
                if let Some(message) = d.message.strip_prefix(&prefix) {
                    d.message = format!("in {}: {message}", s.label);
                }
            }
        }
    }
    job.limits.cancellation.check()?;
    Ok(publication)
}
struct State {
    // None means the program still exists but cannot currently be checked.
    // Its worker session survives until the program actually disappears.
    snapshot: Option<Snapshot>,
    revision: u64,
    checking: &'static str,
    publication: Option<Publication>,
    errors: Vec<String>,
}
#[derive(Default)]
pub struct Checking {
    worker: Option<Worker>,
    states: BTreeMap<String, State>,
    tests: bool,
    pub config: Config,
    idle: Vec<RequestId>,
    started: Vec<Value>,
    finished: Vec<Value>,
}
impl Checking {
    pub fn enable(&mut self, tests: bool) -> Result<()> {
        self.tests = tests;
        self.worker = Some(Worker::spawn("denotate-check", |job, session, _| {
            let result = check(job, session);
            let cache = if job.payload.measure {
                let c = session.stats();
                json!({"evaluationHits":c.evaluation_hits,"evaluationMisses":c.evaluation_misses,
                    "verdictHits":c.verdict_hits,"verdictMisses":c.verdict_misses})
            } else {
                Value::Null
            };
            (result, cache)
        })?);
        Ok(())
    }
    pub fn status(&self, root: &str, status: &mut Value) {
        status["backend"] = json!(self.config.backend.backend);
        status["checking"] = json!("blocked");
        status["activeAssumptions"] = Value::Null;
        status["findings"] = json!([]);
        if let Some(state) = self.states.get(root) {
            status["checking"] = json!(state.checking);
            status["checkRevision"] = json!(state.revision);
            if !state.errors.is_empty() {
                if status["state"] != "standalone" {
                    status["state"] = json!("invalid");
                }
                status["errors"]
                    .as_array_mut()
                    .unwrap()
                    .extend(state.errors.iter().map(|e| json!(e)));
            }
            if let Some(p) = &state.publication {
                status["activeAssumptions"] = p.status["activeAssumptions"].clone();
                status["findings"] = p.status.get("findings").cloned().unwrap_or(json!([]));
                status["summary"] = p.status.clone();
                status["originNotices"] =
                    p.status.get("originNotices").cloned().unwrap_or(json!([]));
            }
        }
    }
    pub fn diagnostics(&self, uri: &Url) -> Vec<Diagnostic> {
        self.states
            .values()
            .filter_map(|s| s.publication.as_ref())
            .filter_map(|p| p.diagnostics.get(uri))
            .flatten()
            .cloned()
            .collect()
    }
    fn reconcile(&mut self, snapshots: BTreeMap<String, Option<Snapshot>>) -> Result<()> {
        let Some(worker) = &mut self.worker else {
            return Ok(());
        };
        let removed = self
            .states
            .keys()
            .filter(|r| !snapshots.contains_key(*r))
            .cloned()
            .collect::<Vec<_>>();
        for root in removed {
            self.states.remove(&root);
            worker.close(&root)?;
        }
        for (root, snapshot) in snapshots {
            if self.states.get(&root).is_some_and(|s| {
                s.snapshot.as_ref().map(|s| &s.key) == snapshot.as_ref().map(|s| &s.key)
            }) {
                continue;
            }
            let ticket = worker.ticket(root.clone(), ());
            let revision = ticket.revision;
            let Some(snapshot) = snapshot else {
                worker.cancel(&root);
                self.states.insert(
                    root,
                    State {
                        snapshot: None,
                        revision,
                        checking: "blocked",
                        publication: None,
                        errors: vec![],
                    },
                );
                continue;
            };
            let limits = Limits {
                timeout: std::time::Duration::from_millis(snapshot.config.timeout_ms),
                ..Limits::default()
            };
            worker.enqueue(Job {
                ticket,
                payload: Payload {
                    snapshot: snapshot.clone(),
                    measure: self.tests,
                },
                limits,
            });
            self.states.insert(
                root,
                State {
                    snapshot: Some(snapshot),
                    revision,
                    checking: "pending",
                    publication: None,
                    errors: vec![],
                },
            );
        }
        Ok(())
    }
    fn start(&mut self) -> Result<()> {
        if let Some(ticket) = self.worker.as_mut().unwrap().start()? {
            if self.tests {
                self.started
                    .push(json!({"program":ticket.key,"revision":ticket.revision}));
            }
            self.states.get_mut(&ticket.key).unwrap().checking = "checking";
        }
        Ok(())
    }
    fn stop(&mut self) {
        if let Some(mut worker) = self.worker.take() {
            worker.stop();
        }
    }
}

impl Server {
    fn check_snapshots(&self) -> BTreeMap<String, Option<Snapshot>> {
        let aliases = self
            .documents
            .keys()
            .map(|u| (Self::canonical_document(u), u.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut programs = self.catalog.programs.clone();
        for (uri, _) in self.documents.iter() {
            if self.catalog.status(&Self::canonical_document(uri))["state"] == "standalone" {
                programs.insert(
                    uri.to_string(),
                    ProgramMembership::single(uri.to_string(), [Self::canonical_document(uri)]),
                );
            }
        }
        let mut snapshots = BTreeMap::new();
        for (root, mut membership) in programs {
            // Catalog membership and checkability are separate: syntax damage,
            // failed manifest lookups, etc. must not evict a warm session.
            snapshots.insert(root.clone(), None);
            if self.catalog.programs.contains_key(&root)
                && self.catalog.program_status(&root)["state"] != "ready"
            {
                continue;
            }
            let mut files = vec![];
            let mut observations = BTreeMap::new();
            let mut valid = true;
            for canonical in membership
                .roots
                .values()
                .flat_map(|r| &r.files)
                .collect::<std::collections::BTreeSet<_>>()
            {
                let Some(uri) = aliases.get(canonical) else {
                    valid = false;
                    break;
                };
                let doc = &self.documents[uri];
                if self.documents.rejected_version(uri).is_some() || !doc.diagnostics().is_empty() {
                    valid = false;
                    break;
                }
                let home = self
                    .catalog
                    .home(canonical)
                    .unwrap_or_else(|| uri.to_string());
                observations.insert(uri.to_string(), json!({"text":doc.text,"version":doc.version,"open":doc.open,"home":home,"observation":self.observations[uri]}));
                files.push(SourceFile::new(
                    uri.to_string(),
                    self.observations[uri],
                    doc.text.as_str(),
                ));
            }
            if !valid {
                continue;
            }
            let manifests = membership.roots.keys().map(|r| (r.clone(), self.catalog.nodes.get(r).map(|n|json!({"text":n.snapshot.as_ref().map(|m| &m.text),"version":n.snapshot.as_ref().map(|m|m.version),"errors":n.errors,"open":Url::parse(r).ok().and_then(|u|u.to_file_path().ok()).is_some_and(|p|self.catalog.open.contains_key(&p))})))).collect::<BTreeMap<_,_>>();
            for node in membership.roots.values_mut() {
                node.files = node
                    .files
                    .iter()
                    .map(|u| aliases.get(u).map_or_else(|| u.clone(), |a| a.to_string()))
                    .collect();
            }
            let graph = membership
                .roots
                .iter()
                .map(|(r, n)| (r, json!({"files":n.files,"libraries":n.libraries})))
                .collect::<BTreeMap<_, _>>();
            let key = json!({"members":observations,"manifests":manifests,"graph":graph,"origins":self.bridge.snapshot_key(&files.iter().map(|f|f.uri.clone()).collect::<Vec<_>>()),"backend":self.checking.config.backend.backend,"timeoutMs":self.checking.config.timeout_ms});
            let label = Url::parse(&root)
                .ok()
                .and_then(|u| u.to_file_path().ok())
                .map(|p| {
                    self.roots
                        .iter()
                        .find_map(|w| {
                            p.strip_prefix(catalog::identity(w))
                                .ok()
                                .map(|p| p.display().to_string())
                        })
                        .unwrap_or_else(|| p.display().to_string())
                })
                .unwrap_or(root.clone());
            snapshots.insert(
                root,
                Some(Snapshot {
                    membership,
                    files,
                    key,
                    bridge: self.bridge.clone(),
                    config: self.checking.config.clone(),
                    label,
                }),
            );
        }
        snapshots
    }
    pub fn sync_checks(&mut self) -> Result<()> {
        self.refresh_diagnostics();
        self.checking.reconcile(self.check_snapshots())
    }
    fn check_finished(&mut self, connection: &Connection, event: Event) -> Result<()> {
        let (ticket, (result, cache)) = match event {
            Event::Checkpoint(ticket) => {
                send(
                    connection,
                    "denotate/test/checkpoint",
                    json!({"program":ticket.key,"revision":ticket.revision}),
                )?;
                return Ok(());
            }
            Event::Finished(ticket, output) => (ticket, output),
        };
        // Rebuild the entire observation at the publication boundary. This also
        // validates every destination's home, including labeled library fallbacks.
        self.sync_checks()?;
        let states = &self.checking.states;
        let current = self
            .checking
            .worker
            .as_mut()
            .unwrap()
            .complete(&ticket, || {
                states
                    .get(&ticket.key)
                    .is_some_and(|s| s.revision == ticket.revision && s.snapshot.is_some())
            });
        let root = ticket.key;
        let revision = ticket.revision;
        let disposition = if !current {
            "discarded"
        } else if matches!(result, Err(Failure::Cancelled)) {
            "cancelled"
        } else {
            "published"
        };
        if self.test_mode {
            self.checking.finished.push(json!({"program":root,"revision":revision,"status":disposition,"cache":cache,"summary":result.as_ref().ok().map(|p|&p.status)}));
        }
        if !current {
            return Ok(());
        }
        let state = self.checking.states.get_mut(&root).unwrap();
        match result {
            Ok(mut publication) => {
                let valid = state
                    .snapshot
                    .as_ref()
                    .expect("current result must have a checkable snapshot")
                    .membership
                    .members()
                    .ok()
                    .is_some_and(|members| {
                        publication.diagnostics.iter().all(|(uri, diagnostics)| {
                            let Some(ownership) = members.get(uri.as_str()) else {
                                return false;
                            };
                            let home = self
                                .catalog
                                .home(&Self::canonical_document(uri))
                                .unwrap_or_else(|| uri.to_string());
                            diagnostics.iter().all(|diagnostic| {
                                diagnostic.data.as_ref().is_some_and(|data| {
                                    data["program"] == root
                                        && if data["fallback"] == true {
                                            ownership == "library"
                                        } else {
                                            ownership == "user" && home == root
                                        }
                                })
                            })
                        })
                    });
                if valid {
                    for diagnostic in publication.diagnostics.values_mut().flatten() {
                        diagnostic.data.as_mut().unwrap()["checkRevision"] = json!(revision);
                    }
                    state.checking = "complete";
                    state.publication = Some(publication);
                } else {
                    // A failed destination check must never stop independent roots.
                    state.checking = "failed";
                    state
                        .errors
                        .push("Diagnostic destination violates home-program ownership".into());
                }
            }
            Err(Failure::Cancelled) => {
                state.checking = "cancelled";
            }
            Err(Failure::Deadline) => {
                state.checking = "deadline";
            }
            Err(Failure::Invalid(errors)) => {
                state.checking = "blocked";
                state.errors = errors
                    .into_iter()
                    .map(|e| format!("{}: {}", e.uri, e.message))
                    .collect();
            }
            Err(Failure::Internal(error)) => {
                state.checking = "failed";
                state.errors.push(error);
            }
        }
        for uri in self.documents.keys().cloned().collect::<Vec<_>>() {
            self.publish(connection, &uri)?;
        }
        if self.test_mode {
            send(
                connection,
                "denotate/test/checked",
                json!({"program":root,"revision":revision}),
            )?;
        }
        self.announce(connection)?;
        Ok(())
    }
    pub fn serve_checks(&mut self, connection: &Connection) -> Result<()> {
        let events = self.checking.worker.as_ref().unwrap().events().clone();
        let mut pending = VecDeque::new();
        self.sync_checks()?;
        loop {
            // Bounded batches keep edits ahead of old results without starving
            // the worker event queue under a continuous stream of editor requests.
            transport::receive_ready(connection, &mut pending);
            if pending.is_empty() {
                crossbeam_channel::select_biased! {
                    recv(connection.receiver) -> m => match m { Ok(m) => pending.push_back(m), Err(_) => break },
                    recv(events) -> e => self.check_finished(connection, e.map_err(|_|"Checking worker stopped")?)?,
                }
            }
            for _ in 0..256 {
                let Some(message) = pending.pop_front() else {
                    break;
                };
                match message {
                    Message::Request(r) => {
                        if r.method == "shutdown" {
                            self.checking.stop();
                        }
                        if connection.handle_shutdown(&r)? {
                            return Ok(());
                        }
                        if self.test_mode && r.method == "denotate/test/checkingIdle" {
                            self.checking.idle.push(r.id);
                        } else if self.test_mode && r.method == "denotate/test/hold" {
                            self.checking
                                .worker
                                .as_mut()
                                .unwrap()
                                .hold_next(HoldStage::BeforeResult);
                            connection
                                .sender
                                .send(Message::Response(Response::new_ok(r.id, Value::Null)))?;
                        } else if self.test_mode && r.method == "denotate/test/release" {
                            let result = r.params["revision"]
                                .as_u64()
                                .is_some_and(|v| self.checking.worker.as_mut().unwrap().release(v));
                            let response = if result {
                                Response::new_ok(r.id, Value::Null)
                            } else {
                                Response::new_err(r.id, -32602, "No held result".into())
                            };
                            connection.sender.send(Message::Response(response))?;
                        } else if self.test_mode && r.method == "denotate/test/resetChecks" {
                            if !self.checking.worker.as_ref().unwrap().is_idle() {
                                connection.sender.send(Message::Response(Response::new_err(
                                    r.id,
                                    -32602,
                                    "Wait for checkingIdle before resetting sessions".into(),
                                )))?;
                            } else {
                                self.checking.worker.as_mut().unwrap().reset_sessions()?;
                                self.checking.states.clear();
                                self.publish_all(connection)?;
                                connection
                                    .sender
                                    .send(Message::Response(Response::new_ok(r.id, Value::Null)))?;
                            }
                        } else if self.test_mode && r.method == "denotate/test/checkingStats" {
                            connection.sender.send(Message::Response(Response::new_ok(r.id,json!({"started":self.checking.started,"finished":self.checking.finished,"pending":self.checking.worker.as_ref().unwrap().pending().map(|j|json!({"program":j.ticket.key,"revision":j.ticket.revision})).collect::<Vec<_>>()}))))?;
                        } else {
                            transport::dispatch_request(self, r, connection, &mut pending)?;
                        }
                    }
                    Message::Notification(n) if n.method == "exit" => return Ok(()),
                    Message::Notification(n) => {
                        if n.method == "$/cancelRequest" {
                            if let Some(i) = self
                                .checking
                                .idle
                                .iter()
                                .position(|id| json!(id) == n.params["id"])
                            {
                                connection.sender.send(Message::Response(Response::new_err(
                                    self.checking.idle.remove(i),
                                    -32800,
                                    "Request cancelled".into(),
                                )))?;
                            }
                        }
                        if let Err(e) = self.notification(connection, n) {
                            eprintln!("notification rejected: {e}");
                        }
                    }
                    Message::Response(r) => {
                        self.bridge.response(r);
                        self.publish_all(connection)?;
                    }
                }
            }
            // Queued edits have already invalidated their jobs before this gate.
            if let Ok(event) = events.try_recv() {
                self.check_finished(connection, event)?;
            }
            self.sync_checks()?;
            self.checking.start()?;
            if self.checking.worker.as_ref().unwrap().is_idle() && self.bridge.settled() {
                for id in self.checking.idle.drain(..) {
                    connection
                        .sender
                        .send(Message::Response(Response::new_ok(id, Value::Null)))?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_deadline_does_not_drop_a_waiting_valid_root() {
        let snapshot = |root: &str| Snapshot {
            membership: ProgramMembership::single(root, [format!("file:///{root}.den")]),
            files: vec![SourceFile::new(
                format!("file:///{root}.den"),
                1,
                "relation p(); p();",
            )],
            key: json!(root),
            bridge: Bridge::default(),
            config: Config::default(),
            label: root.into(),
        };
        let mut checking = Checking::default();
        checking.enable(false).unwrap();
        checking
            .reconcile(BTreeMap::from([
                ("a".into(), Some(snapshot("a"))),
                ("b".into(), Some(snapshot("b"))),
            ]))
            .unwrap();
        checking
            .worker
            .as_mut()
            .unwrap()
            .pending_limits_mut(&"a".into())
            .unwrap()
            .timeout = std::time::Duration::ZERO;
        checking.start().unwrap();
        let events = checking.worker.as_ref().unwrap().events().clone();
        let Event::Finished(ticket, (Err(Failure::Deadline), _)) = events
            .recv_timeout(std::time::Duration::from_secs(5))
            .unwrap()
        else {
            panic!("expected deadline");
        };
        assert_eq!(ticket.key, "a");
        checking.worker.as_mut().unwrap().complete(&ticket, || true);
        checking.start().unwrap();
        let Event::Finished(ticket, (Ok(publication), _)) = events
            .recv_timeout(std::time::Duration::from_secs(5))
            .unwrap()
        else {
            panic!("waiting root did not finish");
        };
        assert_eq!(ticket.key, "b");
        assert_eq!(publication.status["state"], "proved");
    }
}
