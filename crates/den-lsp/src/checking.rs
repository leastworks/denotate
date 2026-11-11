//! The editor owns scheduling and immutable observations. The worker owns only
//! root-keyed checker sessions; all publication passes back through the owner.
use crate::{
    bridge::Bridge,
    catalog,
    presentation::{self, Publication},
    Server,
};
use denotate_check::*;
use denotate_editor::checking::{self, Job, Scheduler, Ticket};
use denotate_editor::transport::{send, Result};
use denotate_editor::{
    checking_server::{self, CheckingHandler},
    test_support::{self, CheckingHooks},
};
use denotate_ir_text::{
    progress::{CheckProgress, Phase},
    ProgramMembership, SourceFile,
};
use lsp_server::Connection;
use lsp_types::{Diagnostic, Url};
use serde_json::{json, Value};
use std::collections::BTreeMap;

pub use crate::configuration::Config;
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
pub(crate) struct Payload {
    snapshot: Snapshot,
    measure: bool,
}
type Output = (std::result::Result<Publication, Failure>, Value);
type Worker = Scheduler<String, Payload, Output, (), Value>;
pub type Event = checking::Event<String, Output, (), Value>;
#[derive(Debug)]
pub enum Failure {
    Cancelled,
    Deadline(Inconclusive),
    Exhausted(Inconclusive),
    Invalid(Vec<denotate_ir_text::Diagnostic>),
    Internal(String),
}
impl From<CheckError> for Failure {
    fn from(e: CheckError) -> Self {
        match e {
            CheckError::Cancelled => Self::Cancelled,
            CheckError::Deadline { phase, details } => Self::Deadline(Inconclusive {
                phase,
                resource: "deadline",
                details,
            }),
            CheckError::LimitExceeded {
                phase,
                resource,
                details,
            } => Self::Exhausted(Inconclusive {
                phase,
                resource,
                details,
            }),
            _ => Self::Internal(e.to_string()),
        }
    }
}
#[cfg(test)]
fn check(
    job: &Job<String, Payload>,
    session: &mut denotate_check_session::Session,
) -> std::result::Result<Publication, Failure> {
    check_with_progress(job, session, None)
}
fn check_with_progress(
    job: &Job<String, Payload>,
    session: &mut denotate_check_session::Session,
    report: Option<&dyn Fn(Value)>,
) -> std::result::Result<Publication, Failure> {
    let observed = |mut detail: Value| {
        detail["memory"] =
            serde_json::to_value(denotate_check_session::profiling::process_memory()).unwrap();
        if let Some(report) = report {
            report(detail);
        }
    };
    let progress = CheckProgress::new(report.map(|_| &observed as &dyn Fn(Value)));
    job.limits.cancellation.check()?;
    let s = &job.payload.snapshot;
    progress.emit(
        Phase::Loading,
        json!({"files":s.files.len(),"configuration":s.config.data()}),
    );
    let program =
        denotate_ir_text::load_with_resolver(&s.membership, &s.files, Some(&mut &s.bridge))
            .map_err(Failure::Invalid)?;
    job.limits.cancellation.check()?;
    let mut publication = presentation::configuration(&program).map_err(Failure::Internal)?;
    progress.emit(Phase::AssumptionValidation, json!({}));
    let validated = validate_assumption_cones_for_run(
        &program.corpus,
        &program.domains,
        &program.keys,
        &job.limits,
    )?;
    let validation = validated.result();
    let validation_publication =
        presentation::assumption_validation(&program, &validation).map_err(Failure::Internal)?;
    publication.status["assumptionValidation"] = validation_publication.status.clone();
    for (uri, diagnostics) in validation_publication.diagnostics {
        publication
            .diagnostics
            .entry(uri)
            .or_default()
            .extend(diagnostics);
    }
    publication.status["findings"] = validation_publication.status["findings"].clone();
    let requests = program.verification_requests(&job.limits)?;
    let fixed = std::cell::OnceCell::new();
    for (i, (key, request)) in requests.iter().enumerate() {
        let context = progress.verification(&program, key, i + 1, requests.len())?;
        job.limits.cancellation.check()?;
        // Each context gets its own operation limits; a failed context cannot
        // consume another verification's deadline or prevent its execution.
        let operations = OperationalLimits::from(&job.limits);
        let exhausted = |reason| Publication {
            diagnostics: BTreeMap::new(),
            status: denotate_presentation::summary(&request.exhausted(reason)),
        };
        let mut run = || -> std::result::Result<Publication, Failure> {
            if let Some(state) =
                validation.selected_failure(&program.corpus, &program.keys, request)?
            {
                return Ok(Publication {
                    diagnostics: BTreeMap::new(),
                    status: json!({"state":"incomplete","consistency":"unknown","assumptionValidation":denotate_presentation::assumption_validity_data(state)}),
                });
            }
            let fixed = fixed.get_or_init(|| {
                progress.emit(Phase::FixedFacts, json!({}));
                session.prepare_fixed_with_validation(&validated, &job.limits)
            });
            progress.emit(Phase::Preparation, context.clone());
            let fixed = fixed.as_ref().map_err(|e| Failure::from(e.clone()))?;
            let ground = match session.prepare_with_fixed(
                request,
                &program.corpus,
                &program.keys,
                &operations,
                fixed,
            )? {
                RequestPreparation::Complete(p) => p,
                RequestPreparation::Inconclusive { reason, .. } => return Ok(exhausted(reason)),
            };
            let mut detail = context.clone();
            progress.prepared(
                &mut detail,
                ground.program(),
                session.fixed_stats().retained_bytes,
            );
            progress.emit(Phase::Admission, detail.clone());
            let ground = ground.admit(&operations)?;
            progress.emit(Phase::Checking, detail.clone());
            match session.verify(&ground, &operations)? {
                LocalCheckOutcome::Complete(report) => {
                    progress.emit(Phase::Presentation, detail);
                    presentation::present(&program, &report.checked, s.config.show_library_rewrites)
                        .map_err(Failure::Internal)
                }
                LocalCheckOutcome::Inconclusive { reason, .. } => Ok(exhausted(reason)),
            }
        };
        let (checking, result) = match run() {
            Ok(result) => ("complete", result),
            Err(Failure::Cancelled) => return Err(Failure::Cancelled),
            Err(Failure::Exhausted(reason)) => ("complete", exhausted(reason)),
            Err(Failure::Deadline(reason)) => ("deadline", exhausted(reason)),
            Err(error) => (
                "failed",
                Publication {
                    diagnostics: BTreeMap::new(),
                    status: json!({"state":"incomplete","error":format!("{error:?}")}),
                },
            ),
        };
        let entry = &mut publication.status["verifications"][i];
        entry["checking"] = json!(checking);
        entry["consistency"] = result
            .status
            .get("consistency")
            .cloned()
            .unwrap_or(json!("unknown"));
        entry["summary"] = result.status.clone();
        for (uri, diagnostics) in result.diagnostics {
            publication
                .diagnostics
                .entry(uri)
                .or_default()
                .extend(diagnostics);
        }
        if let Some(findings) = result.status["findings"].as_array() {
            publication.status["findings"]
                .as_array_mut()
                .unwrap()
                .extend(findings.iter().cloned());
        }
    }
    progress.emit(
        Phase::Publication,
        json!({"verificationTotal":requests.len()}),
    );
    let verifications = publication.status["verifications"].as_array().unwrap();
    let checking = if verifications.is_empty() {
        "unconfigured"
    } else if verifications.iter().any(|v| v["checking"] == "failed") {
        "failed"
    } else if verifications.iter().any(|v| v["checking"] == "deadline") {
        "deadline"
    } else {
        "complete"
    };
    let state = if !validation.is_valid() {
        "incomplete"
    } else if verifications.is_empty() {
        "unconfigured"
    } else if checking != "complete"
        || !publication.status["uncheckedObligations"]
            .as_array()
            .unwrap()
            .is_empty()
        || verifications
            .iter()
            .any(|v| v["summary"]["state"] == "incomplete")
    {
        "incomplete"
    } else if verifications.iter().any(|v| {
        v["summary"]["state"] == "findings" || v["summary"]["state"] == "inconsistent-assumptions"
    }) {
        "findings"
    } else {
        "proved"
    };
    publication.status["checking"] = json!(checking);
    publication.status["state"] = json!(state);
    publication.status["originNotices"] = json!(program.embedded.notices.iter().map(|n|json!({"uri":n.source.uri,"view":n.source.view,"hash":n.source.hash,"reason":format!("{:?}",n.reason)})).collect::<Vec<_>>());
    for diagnostics in publication.diagnostics.values_mut() {
        for d in diagnostics {
            if let (Some(related), Some(locations)) = (
                d.related_information.as_mut(),
                d.data
                    .as_ref()
                    .and_then(|data| data["locations"]["related"].as_array()),
            ) {
                for (r, identity) in related.iter_mut().zip(locations) {
                    if let Some(hash) = identity["hash"].as_str() {
                        r.location.range =
                            s.bridge
                                .editor_range(r.location.uri.as_str(), hash, r.location.range);
                    }
                }
            }
            label_fallback(d, &program.root, &s.label);
        }
    }
    job.limits.cancellation.check()?;
    Ok(publication)
}
fn label_fallback(d: &mut Diagnostic, root: &str, label: &str) {
    if d.data.as_ref().is_some_and(|v| v["fallback"] == true) {
        if let Some(message) = d.message.strip_prefix(&format!("in {root}: ")) {
            d.message = format!("in {label}: {message}");
        }
    }
}
struct State {
    // None means the program still exists but cannot currently be checked.
    // Its worker session survives until the program actually disappears.
    snapshot: Option<Snapshot>,
    revision: u64,
    checking: &'static str,
    publication: Option<Publication>,
    configuration: Option<Publication>,
    errors: Vec<String>,
    progress: Option<Value>,
}
#[derive(Default)]
pub struct Checking {
    worker: Option<Worker>,
    states: BTreeMap<String, State>,
    tests: bool,
    pub config: Config,
    hooks: CheckingHooks,
    pub progress_enabled: bool,
    last_progress: Option<Value>,
}
impl Checking {
    fn record_progress(&mut self, ticket: &Ticket<String>, detail: Value) {
        if let Some(state) = self.states.get_mut(&ticket.key) {
            if state.revision == ticket.revision && state.checking == "checking" {
                state.progress = Some(detail);
            }
        }
    }
    fn progress(&self, awaiting_snapshots: bool) -> Value {
        let mut counts = BTreeMap::from([
            ("pending", 0usize),
            ("checking", 0),
            ("complete", 0),
            ("blocked", 0),
            ("unconfigured", 0),
            ("deadline", 0),
            ("failed", 0),
            ("cancelled", 0),
        ]);
        let mut active = vec![];
        for (program, state) in &self.states {
            *counts.entry(state.checking).or_default() += 1;
            if state.checking == "checking" {
                active.push(
                    json!({"program":program,"revision":state.revision,"detail":state.progress,
                    "label":state.snapshot.as_ref().map(|s|s.label.as_str()).unwrap_or(program)}),
                );
            }
        }
        json!({"total":self.states.len(),
            "processed":self.states.len() - counts["pending"] - counts["checking"],
            "counts":counts,"active":active,"awaitingSnapshots":awaiting_snapshots})
    }
    fn announce_progress(
        &mut self,
        connection: &Connection,
        awaiting_snapshots: bool,
    ) -> Result<()> {
        if !self.progress_enabled {
            return Ok(());
        }
        let progress = self.progress(awaiting_snapshots);
        if self.last_progress.as_ref() != Some(&progress) {
            send(connection, "denotate/checkingProgress", progress.clone())?;
            self.last_progress = Some(progress);
        }
        Ok(())
    }
    pub fn enable(&mut self, tests: bool) -> Result<()> {
        self.tests = tests;
        let progress_enabled = self.progress_enabled;
        self.worker = Some(Worker::spawn_with_progress(
            "denotate-check",
            move |job, session, checkpoint, progress| {
                checkpoint();
                let result =
                    check_with_progress(job, session, progress_enabled.then_some(progress));
                let cache = if job.payload.measure {
                    let c = session.stats();
                    json!({"evaluationHits":c.evaluation_hits,"evaluationMisses":c.evaluation_misses,
                    "verdictHits":c.verdict_hits,"verdictMisses":c.verdict_misses})
                } else {
                    Value::Null
                };
                (result, cache)
            },
        )?);
        Ok(())
    }
    pub fn status(&self, root: &str, status: &mut Value) {
        status["backend"] = json!("bdd");
        status["checking"] = json!("blocked");
        status["verifications"] = Value::Null;
        status["uncheckedObligations"] = Value::Null;
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
            if let Some(p) = state.publication.as_ref().or(state.configuration.as_ref()) {
                status["verifications"] = p.status["verifications"].clone();
                status["uncheckedObligations"] = p.status["uncheckedObligations"].clone();
                if state.publication.is_none() {
                    for v in status["verifications"].as_array_mut().unwrap() {
                        v["checking"] = json!(state.checking);
                    }
                }
                status["findings"] = p.status.get("findings").cloned().unwrap_or(json!([]));
                status["summary"] = p.status.clone();
                status["summary"]["verifications"] = status["verifications"].clone();
                status["summary"]["checking"] = status["checking"].clone();
                status["originNotices"] =
                    p.status.get("originNotices").cloned().unwrap_or(json!([]));
            }
        }
    }
    pub fn diagnostics(&self, uri: &Url) -> Vec<Diagnostic> {
        self.states
            .values()
            .filter_map(|s| s.publication.as_ref().or(s.configuration.as_ref()))
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
                        configuration: None,
                        errors: vec![],
                        progress: None,
                    },
                );
                continue;
            };
            let limits = snapshot.config.checker_limits();
            let mut configuration = denotate_ir_text::load(&snapshot.membership, &snapshot.files)
                .ok()
                .and_then(|p| presentation::configuration(&p).ok());
            if let Some(config) = &mut configuration {
                for d in config.diagnostics.values_mut().flatten() {
                    d.data.as_mut().unwrap()["checkRevision"] = json!(revision);
                    label_fallback(d, &root, &snapshot.label);
                }
            }
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
                    configuration,
                    errors: vec![],
                    progress: None,
                },
            );
        }
        Ok(())
    }
    #[cfg(test)]
    fn start(&mut self) -> Result<()> {
        if let Some(ticket) = self.worker.as_mut().unwrap().start()? {
            if self.tests {
                self.hooks
                    .started
                    .push(json!({"program":ticket.key,"revision":ticket.revision}));
            }
            self.states.get_mut(&ticket.key).unwrap().checking = "checking";
        }
        Ok(())
    }
}

impl Server {
    pub fn origin_candidates(&mut self, params: &Value) -> Result<Value> {
        let uri = Url::parse(
            params["textDocument"]["uri"]
                .as_str()
                .ok_or("Missing uri")?,
        )?;
        if self.documents.rejected_version(&uri).is_some() {
            return Err("Document is out of sync; reopen it or send a full-text change.".into());
        }
        self.refresh_diagnostics();
        let doc = self.documents.get(&uri).ok_or("Document is not loaded")?;
        if params["textDocument"]["version"]
            .as_i64()
            .is_some_and(|v| v != i64::from(doc.version))
        {
            return Err("Document changed; request origins again.".into());
        }
        let byte = doc
            .offset(serde_json::from_value(params["position"].clone())?)
            .ok_or("Invalid position")?;
        let root = self
            .catalog
            .home(&Self::canonical_document(&uri))
            .unwrap_or_else(|| uri.to_string());
        let snapshot = self
            .check_snapshots()
            .remove(&root)
            .flatten()
            .ok_or("Origins unavailable while the home program is invalid or out of sync.")?;
        // Resolve associations from current authoring text, without using cached
        // checker output or resolving source content on the server's authority.
        let program = denotate_ir_text::load(&snapshot.membership, &snapshot.files)
            .map_err(|_| "Origins unavailable while the home program cannot be loaded.")?;
        Ok(
            json!({"version":doc.version,"origins":program.origins_at(uri.as_str(), byte).iter().map(|o| json!({
            "uri":o.source.uri,"view":o.source.view,"hash":o.source.hash,
            "start":{"line":o.start.line,"column":o.start.column},
            "end":{"line":o.end.line,"column":o.end.column}
        })).collect::<Vec<_>>()}),
        )
    }
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
            let key = json!({"members":observations,"manifests":manifests,"graph":graph,"origins":self.bridge.snapshot_key(&files.iter().map(|f|f.uri.clone()).collect::<Vec<_>>()),"configuration":self.checking.config.data()});
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
            Event::Progress(ticket, detail) => {
                self.checking.record_progress(&ticket, detail);
                return Ok(());
            }
            Event::Checkpoint(ticket) => {
                send(
                    connection,
                    test_support::CHECKPOINT,
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
            self.checking.hooks.finished.push(json!({"program":root,"revision":revision,"status":disposition,"cache":cache,"summary":result.as_ref().ok().map(|p|&p.status)}));
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
                    state.checking = match publication.status["checking"].as_str() {
                        Some("unconfigured") => "unconfigured",
                        Some("deadline") => "deadline",
                        Some("failed") => "failed",
                        _ => "complete",
                    };
                    for message in denotate_presentation::exhaustion_messages(
                        &publication.status["assumptionValidation"],
                    ) {
                        send(
                            connection,
                            "window/logMessage",
                            json!({"type":2,"message":format!("{root}: {message}")}),
                        )?;
                    }
                    for verification in publication.status["verifications"]
                        .as_array()
                        .into_iter()
                        .flatten()
                    {
                        let name = verification["verification"]
                            .as_str()
                            .unwrap_or("verification");
                        for message in
                            denotate_presentation::exhaustion_messages(&verification["summary"])
                        {
                            send(
                                connection,
                                "window/logMessage",
                                json!({"type":2,"message":format!("{root}, {name}: {message}")}),
                            )?;
                        }
                    }
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
            Err(Failure::Deadline(reason)) => {
                state.checking = "deadline";
                state.errors.push(denotate_presentation::exhaustion_text(
                    reason.phase,
                    reason.resource,
                    reason.details,
                ));
            }
            Err(Failure::Invalid(errors)) => {
                state.checking = "blocked";
                state.errors = errors
                    .into_iter()
                    .map(|e| format!("{}: {}", e.uri, e.message))
                    .collect();
            }
            Err(Failure::Exhausted(reason)) => {
                state.checking = "failed";
                state.errors.push(format!(
                    "Configuration exhausted: {}",
                    denotate_presentation::exhaustion_text(
                        reason.phase,
                        reason.resource,
                        reason.details,
                    )
                ));
            }
            Err(Failure::Internal(error)) => {
                state.checking = "failed";
                state.errors.push(error);
            }
        }
        if matches!(state.checking, "failed" | "deadline") {
            let label = state
                .snapshot
                .as_ref()
                .map(|s| s.label.as_str())
                .unwrap_or(&root);
            let mut details = state.errors.clone();
            if let Some(publication) = &state.publication {
                for verification in publication.status["verifications"]
                    .as_array()
                    .into_iter()
                    .flatten()
                {
                    if let Some(error) = verification["summary"]["error"].as_str() {
                        details.push(error.to_owned());
                    }
                }
            }
            send(
                connection,
                "window/logMessage",
                json!({"type":2,
                "message":format!("{label}: checking {}{}", state.checking,
                    if details.is_empty() { String::new() } else { format!(": {}", details.join("; ")) })}),
            )?;
        }
        for uri in self.documents.keys().cloned().collect::<Vec<_>>() {
            self.publish(connection, &uri)?;
        }
        if self.test_mode {
            send(
                connection,
                test_support::CHECKED,
                json!({"program":root,"revision":revision}),
            )?;
        }
        self.announce(connection)?;
        Ok(())
    }
    pub fn serve_checks(&mut self, connection: &Connection) -> Result<()> {
        checking_server::run(self, connection)
    }
}
impl CheckingHandler for Server {
    type Key = String;
    type Payload = Payload;
    type Output = Output;
    type Metadata = ();
    type Progress = Value;
    fn scheduler(&mut self) -> &mut Worker {
        self.checking.worker.as_mut().unwrap()
    }
    fn hooks(&mut self) -> &mut CheckingHooks {
        &mut self.checking.hooks
    }
    fn test_mode(&self) -> bool {
        self.test_mode
    }
    fn identity(ticket: &Ticket<String>) -> Value {
        json!({"program": ticket.key, "revision": ticket.revision})
    }
    fn completed(&mut self, connection: &Connection, event: Event) -> Result<()> {
        self.check_finished(connection, event)
    }
    fn before_start(&mut self, _: &Connection) -> Result<()> {
        self.sync_checks()
    }
    fn started(&mut self, ticket: &Ticket<String>) {
        self.checking.states.get_mut(&ticket.key).unwrap().checking = "checking";
    }
    fn checking_status(&mut self, connection: &Connection) -> Result<()> {
        self.checking
            .announce_progress(connection, !self.bridge.settled())
    }
    fn settled(&self) -> bool {
        self.bridge.settled()
    }
    fn reset_checks(&mut self, connection: &Connection) -> Result<()> {
        self.checking.states.clear();
        self.publish_all(connection)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn progress_distinguishes_terminal_states_and_deduplicates_current_snapshots() {
        let (server, client) = Connection::memory();
        let mut checking = Checking::default();
        checking.announce_progress(&server, false).unwrap();
        assert!(client.receiver.try_recv().is_err()); // Opt in explicitly.
        checking.progress_enabled = true;
        for (program, phase) in [
            ("a", "complete"),
            ("b", "checking"),
            ("c", "blocked"),
            ("d", "unconfigured"),
            ("e", "deadline"),
            ("f", "failed"),
            ("g", "cancelled"),
        ] {
            checking.states.insert(
                program.into(),
                State {
                    snapshot: None,
                    revision: 1,
                    checking: phase,
                    publication: None,
                    configuration: None,
                    errors: vec![],
                    progress: None,
                },
            );
        }
        let snapshot = checking.progress(false);
        assert_eq!(snapshot["total"], 7);
        assert_eq!(snapshot["processed"], 6);
        assert_eq!(snapshot["counts"]["complete"], 1);
        assert_eq!(snapshot["active"][0]["program"], "b");
        checking.announce_progress(&server, false).unwrap();
        let lsp_server::Message::Notification(n) = client.receiver.try_recv().unwrap() else {
            panic!()
        };
        assert_eq!(n.method, "denotate/checkingProgress");
        assert_eq!(n.params, snapshot);
        checking.announce_progress(&server, false).unwrap();
        assert!(client.receiver.try_recv().is_err());
        checking.announce_progress(&server, true).unwrap();
        assert!(client.receiver.try_recv().is_ok());
        checking.states.remove("a");
        checking.states.get_mut("b").unwrap().checking = "pending";
        let changed = checking.progress(false);
        assert_eq!(changed["total"], 6);
        assert_eq!(changed["processed"], 5);
        assert_eq!(changed["active"], json!([]));
        assert_eq!(changed["counts"]["pending"], 1);
        let ticket = Ticket {
            key: "b".into(),
            revision: 1,
            metadata: (),
        };
        checking.record_progress(&ticket, json!({"phase":"admission"}));
        assert!(checking.states["b"].progress.is_none()); // Queued replacement.
        let state = checking.states.get_mut("b").unwrap();
        state.checking = "checking";
        state.revision = 2;
        checking.record_progress(&ticket, json!({"phase":"admission"}));
        assert!(checking.states["b"].progress.is_none()); // Obsolete worker.
        checking.record_progress(
            &Ticket {
                revision: 2,
                ..ticket
            },
            json!({"phase":"checking"}),
        );
        assert_eq!(
            checking.progress(false)["active"][0]["detail"]["phase"],
            "checking"
        );
    }
    fn assumption_job(text: &str, limits: Limits) -> Job<String, Payload> {
        Job {
            ticket: Ticket {
                key: "file:///den.root".into(),
                revision: 1,
                metadata: (),
            },
            payload: Payload {
                snapshot: Snapshot {
                    membership: ProgramMembership::single(
                        "file:///den.root",
                        ["file:///p.den".into()],
                    ),
                    files: vec![SourceFile::new("file:///p.den", 1, text)],
                    key: Value::Null,
                    bridge: Bridge::default(),
                    config: Config::default(),
                    label: "p".into(),
                },
                measure: false,
            },
            limits,
        }
    }
    #[test]
    fn phase_reports_describe_prepared_work_without_changing_cold_or_warm_results() {
        let job = assumption_job("sort S; const a,b:S; input p(x:S); obligation o:empty(p); verification v{assumptions:[];obligations:[o];}", Limits::default());
        let mut session = denotate_check_session::Session::default();
        let expected = check(&job, &mut session).unwrap();
        for session in [
            &mut session,
            &mut denotate_check_session::Session::default(),
        ] {
            let updates = std::cell::RefCell::new(vec![]);
            let actual =
                check_with_progress(&job, session, Some(&|p| updates.borrow_mut().push(p)))
                    .unwrap();
            assert_eq!(actual.status, expected.status);
            assert_eq!(actual.diagnostics, expected.diagnostics);
            let updates = updates.into_inner();
            assert_eq!(
                updates
                    .iter()
                    .map(|p| p["phase"].as_str().unwrap())
                    .collect::<Vec<_>>(),
                [
                    "loading",
                    "assumption-validation",
                    "fixed-facts",
                    "preparation",
                    "admission",
                    "checking",
                    "presentation",
                    "publication"
                ]
            );
            let prepared = &updates[4];
            assert!(updates
                .iter()
                .all(|p| p["memory"].get("rssBytes").is_some()));
            assert_eq!(prepared["verification"], "::v");
            assert_eq!(prepared["verificationIndex"], 1);
            assert_eq!(prepared["verificationTotal"], 1);
            assert_eq!(prepared["obligations"], 1);
            assert!(prepared["ground"]["inputAtoms"].as_u64().unwrap() > 0);
            assert!(prepared["ground"]["atoms"].as_u64().unwrap() > 0);
            assert!(prepared["ground"]["components"].as_u64().unwrap() > 0);
            assert_eq!(
                prepared["fold"]["retainedBytes"],
                session.fixed_stats().retained_bytes
            );
            assert!(session.fixed_stats().retained_bytes > 0);
        }
    }
    #[test]
    fn fixed_preparation_runs_once_across_verifications() {
        let job = assumption_job("relation fixed(); fixed(); input i(); relation r(); r():-fixed(),i(); obligation o:empty(r); verification a{assumptions:[];obligations:[o];} verification b{assumptions:[];obligations:[o];}", Limits::default());
        let updates = std::cell::RefCell::new(vec![]);
        check_with_progress(
            &job,
            &mut denotate_check_session::Session::default(),
            Some(&|p| updates.borrow_mut().push(p)),
        )
        .unwrap();
        let updates = updates.into_inner();
        assert_eq!(
            updates
                .iter()
                .filter(|p| p["phase"] == "fixed-facts")
                .count(),
            1
        );
        let prepared = updates
            .iter()
            .filter(|p| p["phase"] == "admission")
            .collect::<Vec<_>>();
        assert_eq!(prepared.len(), 2);
        for detail in prepared {
            assert_eq!(detail["fold"]["presentFacts"], 1);
            assert!(detail["fold"]["residual"]["atoms"].as_u64().unwrap() > 0);
        }
    }
    #[test]
    fn assumption_validation_publishes_without_verifications_and_clears_on_edit() {
        let mut session = denotate_check_session::Session::with_grounding();
        for fact in ["", "eligible();", ""] {
            let text = format!("relation eligible(); {fact} input i() within eligible; relation p(); p():-i(),!p(); assumption invalid:empty(p);");
            let job = assumption_job(&text, Limits::default());
            let warm = check(&job, &mut session).unwrap();
            let cold = check(&job, &mut denotate_check_session::Session::default()).unwrap();
            assert_eq!(warm.status, cold.status);
            assert_eq!(warm.diagnostics, cold.diagnostics);
            if fact.is_empty() {
                assert_eq!(warm.status["state"], "unconfigured");
                assert!(warm.diagnostics.values().all(Vec::is_empty));
            } else {
                assert_eq!(warm.status["state"], "incomplete");
                let ds = warm.diagnostics.values().flatten().collect::<Vec<_>>();
                assert_eq!(ds.len(), 1);
                let data = ds[0].data.as_ref().unwrap();
                assert_eq!(data["kind"], "invalid-assumption");
                assert_eq!(data["finding"]["verification"], Value::Null);
                assert!(!ds[0].related_information.as_ref().unwrap().is_empty());
            }
        }
    }
    #[test]
    fn invalid_assumptions_skip_their_verifications_but_not_independent_ones() {
        let job = assumption_job("input i(); relation p(); p():-i(),!p(); assumption invalid:empty(p); assumption exclude:empty(i); verification bad { assumptions:[invalid]; obligations:[]; } verification good { assumptions:[exclude]; obligations:[]; }",Limits::default());
        let result = check(&job, &mut denotate_check_session::Session::default()).unwrap();
        assert_eq!(
            result.status["verifications"][0]["summary"]["assumptionValidation"]["state"],
            "invalid"
        );
        assert_eq!(
            result.status["verifications"][1]["summary"]["state"],
            "proved"
        );
        assert_eq!(
            result
                .diagnostics
                .values()
                .flatten()
                .filter(|d| d
                    .data
                    .as_ref()
                    .is_some_and(|d| d["kind"] == "invalid-assumption"))
                .count(),
            1
        );
    }
    #[test]
    fn exhausted_assumption_validation_is_visible_without_a_verification() {
        let job = assumption_job(
            "input i(); relation p(); p():-i(),!p(); assumption a:empty(p);",
            Limits {
                max_atoms: 0,
                ..Limits::default()
            },
        );
        let result = check(&job, &mut denotate_check_session::Session::default()).unwrap();
        assert_eq!(result.status["state"], "incomplete");
        assert_eq!(
            result.status["assumptionValidation"]["state"],
            "inconclusive"
        );
        let d = result.diagnostics.values().flatten().next().unwrap();
        assert_eq!(d.data.as_ref().unwrap()["kind"], "unvalidated-assumption");
    }
    #[test]
    fn an_exhausted_verification_does_not_prevent_the_next_one() {
        let text = "sort S; const a,b,c:S; input p(x:S); relation single(); single(); obligation expensive: at_most_one(p, group_by: ()); obligation trivial: at_most_one(single, group_by: ()); verification first { assumptions: []; obligations: [expensive]; } verification second { assumptions: []; obligations: [trivial]; }";
        let job = Job {
            ticket: Ticket {
                key: "file:///den.root".into(),
                revision: 1,
                metadata: (),
            },
            payload: Payload {
                snapshot: Snapshot {
                    membership: ProgramMembership::single(
                        "file:///den.root",
                        ["file:///p.den".into()],
                    ),
                    files: vec![SourceFile::new("file:///p.den", 1, text)],
                    key: Value::Null,
                    bridge: Bridge::default(),
                    config: Config::default(),
                    label: "p".into(),
                },
                measure: false,
            },
            limits: Limits {
                max_bdd_nodes: 2,
                ..Limits::default()
            },
        };
        let mut session = denotate_check_session::Session::default();
        let cold = check(&job, &mut session).unwrap();
        let statuses = &cold.status["verifications"];
        assert_eq!(statuses[0]["verification"], "::first");
        assert_eq!(
            statuses[0]["summary"]["state"], "incomplete",
            "{}",
            cold.status
        );
        assert_eq!(statuses[1]["verification"], "::second");
        assert_eq!(statuses[1]["checking"], "complete");
        assert_eq!(statuses[1]["summary"]["state"], "proved", "{}", cold.status);
        assert_eq!(cold.status["state"], "incomplete");
        assert_eq!(cold.status["uncheckedObligations"], json!([]));
        assert_eq!(check(&job, &mut session).unwrap().status, cold.status);
    }
    #[test]
    fn a_deadline_does_not_drop_a_waiting_valid_root() {
        let snapshot = |root: &str| Snapshot {
            membership: ProgramMembership::single(root, [format!("file:///{root}.den")]),
            files: vec![SourceFile::new(
                format!("file:///{root}.den"),
                1,
                "relation p(); p(); verification checks { assumptions: []; obligations: []; }",
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
        let Event::Finished(ticket, (Ok(deadline), _)) = events
            .recv_timeout(std::time::Duration::from_secs(5))
            .unwrap()
        else {
            panic!("expected deadline");
        };
        assert_eq!(ticket.key, "a");
        assert_eq!(deadline.status["checking"], "deadline");
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
