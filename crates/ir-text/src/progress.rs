//! Observational phase reporting shared by `.den` checking frontends. Callbacks
//! own delivery; this module performs no IO, scheduling or additional checking.
use crate::{LoadedProgram, index};
use denotate_check::{AdmissionComponent, AdmissionProgress, CheckError, GroundProgram};
use denotate_ir::VerificationKey;
use serde_json::{Value, json};
use std::time::Instant;

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

pub struct CheckProgress<'a> {
    report: Option<&'a dyn Fn(Value)>,
    started: Instant,
}
impl<'a> CheckProgress<'a> {
    pub fn new(report: Option<&'a dyn Fn(Value)>) -> Self {
        Self {
            report,
            started: Instant::now(),
        }
    }
    pub fn emit(&self, phase: Phase, mut detail: Value) {
        if let Some(report) = self.report {
            detail["phase"] = json!(phase.name());
            detail["elapsedMs"] = json!(self.started.elapsed().as_millis() as u64);
            report(detail);
        }
    }
    pub fn enabled(&self) -> bool {
        self.report.is_some()
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
    names: std::cell::OnceCell<Box<dyn Fn(denotate_ir::OccurrenceId) -> String + 'a>>,
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
    pub fn report(&self, progress: &CheckProgress<'_>, context: &Value, event: &AdmissionProgress) {
        if !progress.enabled() {
            return;
        }
        let mut detail = context.clone();
        detail["admission"] = json!({
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
            "failure": event
                .failure
                .map(|r| denotate_presentation::exhaustion_text(r.phase, r.resource, r.details)),
        });
        progress.emit(Phase::Admission, detail);
    }
    fn component(&self, c: &AdmissionComponent) -> Value {
        let names = self
            .names
            .get_or_init(|| Box::new(crate::presentation::diagnostic_names(&self.program.corpus)));
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
        "Admission round {} · {}: {} unresolved negation components; {} blocked atoms; {} rules removed, {} negations discharged",
        a["round"],
        a["stage"].as_str().unwrap_or("unknown"),
        a["unresolvedComponents"],
        a["blockedAtoms"],
        a["removedRules"],
        a["dischargedNegations"]
    );
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
        text.push_str(&format!("; stopped: {failure}"));
    }
    text
}
