//! Observational phase reporting shared by `.den` checking frontends. Callbacks
//! own delivery; this module performs no IO, scheduling or additional checking.
use crate::{LoadedProgram, index};
use denotate_check::{AdmissionComponent, AdmissionProgress, CheckError, GroundProgram};
use denotate_ir::VerificationKey;
use serde_json::{Value, json};
use std::{sync::Arc, time::Instant};

#[derive(Clone, Copy)]
pub enum Phase {
    Discovery,
    Loading,
    AssumptionValidation,
    FixedFacts,
    Preparation,
    Admission,
    Checking,
    Presentation,
    Publication,
}
impl Phase {
    pub fn name(self) -> &'static str {
        match self {
            Self::Discovery => "discovery",
            Self::Loading => "loading",
            Self::AssumptionValidation => "assumption-validation",
            Self::FixedFacts => "fixed-facts",
            Self::Preparation => "preparation",
            Self::Admission => "admission",
            Self::Checking => "checking",
            Self::Presentation => "presentation",
            Self::Publication => "publication",
        }
    }
}

#[derive(Clone)]
pub struct CheckProgress {
    report: Option<Arc<dyn Fn(Value) + Send + Sync>>,
    started: Instant,
}
impl CheckProgress {
    pub fn new(report: Option<Arc<dyn Fn(Value) + Send + Sync>>) -> Self {
        Self {
            report,
            started: Instant::now(),
        }
    }
    pub fn emit(&self, phase: Phase, mut detail: Value) {
        if let Some(report) = &self.report {
            detail["phase"] = json!(phase.name());
            detail["elapsedMs"] = json!(self.started.elapsed().as_millis() as u64);
            report(detail);
        }
    }
    pub fn enabled(&self) -> bool {
        self.report.is_some()
    }
    /// Frontend boundaries that finish before per-query checking starts.
    pub fn exhaustion(&self, phase: Phase, context: &Value, message: String, continues: bool) {
        let mut detail = context.clone();
        detail["checking"] = json!({"stage":phase.name(),"state":"exhausted","target":null,"failure":message,"continues":continues});
        self.emit(phase, detail);
    }
    /// Counts selections, not completed work. Indices are one-based in the
    /// frontend's selected run (which may contain only one verification).
    pub fn verification(
        &self,
        program: &LoadedProgram,
        key: &VerificationKey,
        index: usize,
        total: usize,
    ) -> Result<Value, CheckError> {
        if self.report.is_none() {
            return Ok(json!({}));
        }
        let v = program
            .corpus
            .verifications()
            .find(|v| program.keys.verification(v.id).is_ok_and(|k| k == key))
            .ok_or(CheckError::InvalidRequest("unknown progress verification"))?;
        let name = index::Name {
            namespace: program.corpus.namespace(v.id).cloned(),
            text: v.name.clone(),
            generated: false,
        }
        .spelling();
        Ok(
            json!({"verification":name,"verificationIndex":index,"verificationTotal":total,
            "assumptions":v.assumptions.len(),"obligations":v.obligations.len(),"notices":v.notices.len()}),
        )
    }
    /// Inspect the existing prepared program once, before admission. Keep the
    /// resulting detail for later phases; don't ground or evaluate to get sizes.
    pub fn prepared(
        &self,
        detail: &mut Value,
        program: &GroundProgram,
        retained_fold_bytes: usize,
    ) {
        if self.report.is_some() {
            detail["ground"] = json!({"atoms":program.atoms().count(),
                "inputAtoms":program.input_atoms().count(),"ruleInstances":program.rules().count(),
                "components":program.components().count(),
                "largestComponentAtoms":program.components().map(|c| c.atoms.len()).max().unwrap_or(0)});
            let (atoms, present, rules, components, dependencies) = program.fixed_size();
            let (residual_atoms, residual_rules, residual_components) = program.residual_size();
            detail["fold"] = json!({"presentFacts":present,"absentFacts":atoms-present,
                "retainedBytes":retained_fold_bytes,
                "retainedEvidence":{"atoms":atoms,"ruleInstances":rules,"components":components,"dependencies":dependencies},
                "residual":{"atoms":residual_atoms,"ruleInstances":residual_rules,"components":residual_components}});
        }
    }
}

/// Invocation-local formatting caches. Never rebuild all names or rescan a source
/// prefix for each reported component; nothing here is retained across edits.
pub struct AdmissionDetails<'a> {
    program: &'a LoadedProgram,
    names: std::cell::OnceCell<Arc<dyn Fn(denotate_ir::OccurrenceId) -> String + Send + Sync>>,
    locations: std::cell::RefCell<std::collections::BTreeMap<denotate_ir::RuleId, Value>>,
}
impl<'a> AdmissionDetails<'a> {
    pub fn new(program: &'a LoadedProgram) -> Self {
        Self {
            program,
            names: Default::default(),
            locations: Default::default(),
        }
    }
    pub fn report(&self, progress: &CheckProgress, context: &Value, event: &AdmissionProgress) {
        if !progress.enabled() {
            return;
        }
        let mut detail = context.clone();
        detail["admission"] = json!({
            "phase": event.phase.label(),
            "round": event.round,
            "stage": event.stage,
            "unresolvedComponents": event.unresolved_components,
            "blockedAtoms": event.blocked_atoms,
            "current": event.current.as_ref().map(|c| self.component(c)),
            "rule": event.rule,
            "rules": event.rules,
            "iteration": event.iteration,
            "removedRules": event.removed_rules,
            "dischargedNegations": event.discharged_negations,
            "skippedAttempts": event.skipped_attempts,
            "attempts": event.attempts.iter().map(|(kind, a)| json!({
                "kind":kind.label(), "new":a.new, "rerunNegative":a.rerun_negative,
                "retriedSkip":a.retried_skip, "reusedNegative":a.reused_negative,
                "reusedSkip":a.reused_skip, "completed":a.completed, "negative":a.negative,
                "skipped":a.skipped, "failed":a.failed, "cutoffs":a.cutoffs, "elapsedMs":a.elapsed.as_secs_f64()*1000.,
                "retryCauses":a.retry_causes,
            })).collect::<Vec<_>>(),
            "prerequisiteMs": event.prerequisites.iter().map(|(k, d)| ((*k).to_string(), json!(d.as_secs_f64()*1000.))).collect::<serde_json::Map<_, _>>(),
            "skipped": event.skipped.as_ref().map(|s| s.kind.label()),
            "skipTarget": event.skipped.as_ref().map(|s| {
                let names = self.names.get_or_init(|| Arc::new(crate::presentation::diagnostic_names(&self.program.corpus)));
                json!({"head":atom_text(&s.head, &**names)})
            }),
            "failure": event
                .failure
                .map(|r| denotate_presentation::exhaustion_text(r.phase, r.resource, r.details)),
        });
        progress.emit(Phase::Admission, detail);
    }
    fn component(&self, c: &AdmissionComponent) -> Value {
        let names = self
            .names
            .get_or_init(|| Arc::new(crate::presentation::diagnostic_names(&self.program.corpus)));
        let arguments = c.representative.arguments.iter();
        let atom = format!(
            "{}({})",
            names(c.representative.relation.into()),
            arguments
                .map(|id| names((*id).into()))
                .collect::<Vec<_>>()
                .join(", ")
        );
        json!({
            "index": c.index,
            "atoms": c.atoms,
            "ruleInstances": c.rules,
            "atom": atom,
            "location": c.source.map(|id| self.location(id)),
        })
    }
    fn location(&self, rule: denotate_ir::RuleId) -> Value {
        let mut locations = self.locations.borrow_mut();
        let location = locations.entry(rule).or_insert_with(|| {
            let origins = self.program.provenance.origins(rule);
            origins
                .first()
                .and_then(|origin| {
                    let span = origin.span;
                    let source = self.program.sources.snapshot(span.snapshot()).ok()?;
                    let at = crate::origins::coordinate(&source.text, span.byte_range().start)?;
                    Some(json!({"uri": source.uri, "line": at.line, "column": at.column}))
                })
                .unwrap_or(Value::Null)
        });
        location.clone()
    }
}

pub fn admission_text(a: &Value) -> String {
    let mut text = format!(
        "Admission ({}) round {} · {}: {} unresolved negation components; {} blocked atoms; {} rules removed, {} negations discharged",
        a["phase"].as_str().unwrap_or("relevant"),
        a["round"],
        a["stage"].as_str().unwrap_or("unknown"),
        a["unresolvedComponents"],
        a["blockedAtoms"],
        a["removedRules"],
        a["dischargedNegations"]
    );
    if a["skippedAttempts"].as_u64().unwrap_or(0) > 0 {
        text.push_str(&format!(
            "; {} proof attempts skipped",
            a["skippedAttempts"]
        ));
    }
    if a["stage"] == "attempt-summary" {
        if let Some(times) = a["prerequisiteMs"].as_object() {
            for (kind, ms) in times {
                text.push_str(&format!("; {kind} {:.1} ms", ms.as_f64().unwrap_or(0.)));
            }
        }
        for counts in a["attempts"].as_array().into_iter().flatten() {
            text.push_str(&format!(
                "; {}: {} new, {} rerun negative, {} retry skip, {} reused negative, {} reused skip; outcomes {} completed, {} negative, {} skipped, {} failed, {} expansion cutoffs ({:.1} ms, retry causes {})",
                counts["kind"].as_str().unwrap_or("?"), counts["new"], counts["rerunNegative"],
                counts["retriedSkip"], counts["reusedNegative"], counts["reusedSkip"],
                counts["completed"], counts["negative"], counts["skipped"], counts["failed"], counts["cutoffs"],
                counts["elapsedMs"].as_f64().unwrap_or(0.), counts["retryCauses"],
            ));
        }
    }
    if a["rule"].as_u64().unwrap_or(0) > 0 {
        text.push_str(&format!("; rule {}/{}", a["rule"], a["rules"]));
    }
    if let Some(iteration) = a["iteration"].as_u64() {
        text.push_str(&format!("; iteration {iteration}"));
    }
    if let Some(c) = a.get("current").filter(|c| c.is_object()) {
        text.push_str(&format!(
            "; component {} ({} atoms, {} rule instances), {}",
            c["index"],
            c["atoms"],
            c["ruleInstances"],
            c["atom"].as_str().unwrap_or("?")
        ));
        if let Some(uri) = c["location"]["uri"].as_str() {
            text.push_str(&format!(
                " at {uri}:{}:{}",
                c["location"]["line"], c["location"]["column"]
            ));
        }
    }
    if let Some(failure) = a["failure"].as_str() {
        if let Some(kind) = a["skipped"].as_str() {
            text.push_str(&format!(
                "; skipped {kind} for {}: {failure}; continuing admission",
                a["skipTarget"]["head"].as_str().unwrap_or("current target")
            ));
        } else {
            text.push_str(&format!("; stopped: {failure}"));
        }
    }
    text
}

impl AdmissionDetails<'_> {
    /// Snapshot declaration labels and bounded cycle locations. No
    /// complete provenance/key graph is copied into the invocation callback.
    pub fn checking(
        &self,
        progress: &CheckProgress,
        context: &Value,
        ground: &GroundProgram,
    ) -> denotate_check::CheckingProgress {
        if !progress.enabled() {
            return Default::default();
        }
        let names = self
            .names
            .get_or_init(|| Arc::new(crate::presentation::diagnostic_names(&self.program.corpus)))
            .clone();
        let mut declarations = std::collections::BTreeMap::new();
        let mut locations = std::collections::BTreeMap::new();
        for (id, name) in self
            .program
            .corpus
            .obligations()
            .map(|o| (denotate_ir::OccurrenceId::from(o.id), o.name.clone()))
            .chain(
                self.program
                    .corpus
                    .notices()
                    .map(|n| (denotate_ir::OccurrenceId::from(n.id), n.name.clone())),
            )
        {
            let name = index::Name {
                namespace: self.program.corpus.namespace(id).cloned(),
                text: name,
                generated: false,
            }
            .spelling();
            let location = self
                .program
                .provenance
                .origins(id)
                .first()
                .and_then(|origin| {
                    let source = self.program.sources.snapshot(origin.span.snapshot()).ok()?;
                    let at =
                        crate::origins::coordinate(&source.text, origin.span.byte_range().start)?;
                    Some(json!({"uri":source.uri,"line":at.line,"column":at.column}))
                });
            declarations.insert(id, json!({"name":name,"location":location}));
        }
        let remaining = ground
            .components()
            .filter(|c| c.cycle.is_some())
            .collect::<Vec<_>>();
        for (position, c) in remaining.iter().enumerate() {
            let Some(summary) = ground.progress_component(c.id) else {
                continue;
            };
            let cycle = c.cycle.as_ref().unwrap();
            let edges = cycle.edges.iter().take(12).map(|e| {
                let source = ground.rule(e.rule).map(|r| r.source);
                if let Some(source) = source { locations.insert(source, self.location(source)); }
                json!({"from": atom_text(&e.consumer, &*names), "negative": e.polarity == denotate_check::Polarity::Negative,
                    "to": atom_text(&e.provider, &*names), "location": source.and_then(|s| locations.get(&s).cloned())})
            }).collect::<Vec<_>>();
            if let Some(source) = summary.source {
                locations.insert(source, self.location(source));
            }
            let mut detail = context.clone();
            detail["remainingComponent"] = json!({"position":position+1,"total":remaining.len(),"component":self.component(&summary),
                "cycle":edges,"cycleEdges":cycle.edges.len(),"truncated":cycle.edges.len()>12,
                "admissionFailure":ground.admission_limit().map(|r| denotate_presentation::exhaustion_text(r.phase,r.resource,r.details))});
            detail["remainingComponent"]["admissionSkips"] = json!(ground.admission_skips_for(c).map(|s| {
                json!({"attempt":s.kind.label(),"head":atom_text(&s.head, &*names),"reason":denotate_presentation::exhaustion_text(s.reason.phase,s.reason.resource,s.reason.details)})
            }).collect::<Vec<_>>());
            progress.emit(Phase::Admission, detail);
        }
        let progress = progress.clone();
        let context = context.clone();
        denotate_check::CheckingProgress::new(move |e| {
            let target = match e.target {
                Some(denotate_check::CheckingTarget::Obligation(id)) => {
                    declarations.get(&id.into()).map(
                        |v| json!({"kind":"obligation","name":v["name"],"location":v["location"]}),
                    )
                }
                Some(denotate_check::CheckingTarget::Notice(id)) => declarations
                    .get(&id.into())
                    .map(|v| json!({"kind":"notice","name":v["name"],"location":v["location"]})),
                Some(denotate_check::CheckingTarget::Component(c)) => Some(
                    json!({"kind":"component","index":c.index,"atoms":c.atoms,"ruleInstances":c.rules,
                    "atom":atom_text(&c.representative,&*names),"location":c.source.and_then(|s|locations.get(&s).cloned())}),
                ),
                None => None,
            };
            let failure = e.failure.as_ref().and_then(|e| match e {
                CheckError::LimitExceeded {
                    phase,
                    resource,
                    details,
                } => Some(denotate_presentation::exhaustion_text(
                    phase, resource, *details,
                )),
                CheckError::Deadline { phase, details } => Some(
                    denotate_presentation::exhaustion_text(phase, "deadline", *details),
                ),
                _ => None,
            });
            let mut detail = context.clone();
            detail["checking"] = json!({"stage":e.stage,"state":e.state,"target":target,"failure":failure,"continues":e.continues});
            progress.emit(Phase::Checking, detail);
        })
    }
}
fn atom_text(
    atom: &denotate_check::GroundAtom,
    names: &dyn Fn(denotate_ir::OccurrenceId) -> String,
) -> String {
    format!(
        "{}({})",
        names(atom.relation.into()),
        atom.arguments
            .iter()
            .map(|id| names((*id).into()))
            .collect::<Vec<_>>()
            .join(", ")
    )
}
pub fn checking_text(v: &Value) -> String {
    let mut text = format!(
        "Checking {} · {}",
        v["stage"].as_str().unwrap_or("unknown"),
        v["state"].as_str().unwrap_or("unknown")
    );
    let t = &v["target"];
    if t["kind"] == "component" {
        text.push_str(&format!(
            ": component {} ({} atoms, {} rule instances), {}",
            t["index"],
            t["atoms"],
            t["ruleInstances"],
            t["atom"].as_str().unwrap_or("?")
        ));
    } else if let Some(name) = t["name"].as_str() {
        text.push_str(&format!(
            ": {} {name}",
            t["kind"].as_str().unwrap_or("check")
        ));
    }
    if let Some(uri) = t["location"]["uri"].as_str() {
        text.push_str(&format!(
            " at {uri}:{}:{}",
            t["location"]["line"], t["location"]["column"]
        ));
    }
    if let Some(failure) = v["failure"].as_str() {
        if v["state"] == "exhausted" {
            text.push_str(&format!(
                "; {failure}; {}",
                if v["continues"] == true {
                    "current operation incomplete; continuing other checking work"
                } else {
                    "stopping this verification"
                }
            ));
        } else {
            text.push_str("; operation incomplete");
        }
    }
    text
}
pub fn remaining_text(v: &Value) -> String {
    let c = &v["component"];
    let mut text = format!(
        "Unresolved component {}/{}: component {} ({} atoms, {} rule instances), {}",
        v["position"],
        v["total"],
        c["index"],
        c["atoms"],
        c["ruleInstances"],
        c["atom"].as_str().unwrap_or("?")
    );
    if let Some(reason) = v["admissionFailure"].as_str() {
        text.push_str(&format!("; admission stopped: {reason}"));
    }
    if let Some(skips) = v["admissionSkips"].as_array() {
        for skip in skips {
            text.push_str(&format!(
                "; skipped {} for {}: {}",
                skip["attempt"].as_str().unwrap_or("proof"),
                skip["head"].as_str().unwrap_or("?"),
                skip["reason"].as_str().unwrap_or("limit")
            ));
        }
    }
    if let Some(edges) = v["cycle"].as_array() {
        for e in edges {
            text.push_str(&format!(
                "\n  {} {} {}",
                e["from"].as_str().unwrap_or("?"),
                if e["negative"] == true {
                    "-not->"
                } else {
                    "->"
                },
                e["to"].as_str().unwrap_or("?")
            ));
            if let Some(uri) = e["location"]["uri"].as_str() {
                text.push_str(&format!(
                    " at {uri}:{}:{}",
                    e["location"]["line"], e["location"]["column"]
                ));
            }
        }
    }
    if v["truncated"] == true {
        text.push_str(&format!("\n  ... {} cycle edges in total", v["cycleEdges"]));
    }
    text
}
