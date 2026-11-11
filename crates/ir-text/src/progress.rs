//! Observational phase reporting shared by `.den` checking frontends. Callbacks
//! own delivery; this module performs no IO, scheduling or additional checking.
use crate::{LoadedProgram, index};
use denotate_check::{CheckError, GroundProgram};
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
    pub fn prepared(&self, detail: &mut Value, program: &GroundProgram) {
        if self.report.is_some() {
            detail["ground"] = json!({"atoms":program.atoms().count(),
                "inputAtoms":program.input_atoms().count(),"ruleInstances":program.rules().count(),
                "components":program.components().count(),
                "largestComponentAtoms":program.components().map(|c| c.atoms.len()).max().unwrap_or(0)});
            let (atoms, present, rules, components, dependencies) = program.fixed_size();
            let (residual_atoms, residual_rules, residual_components) = program.residual_size();
            detail["fold"] = json!({"presentFacts":present,"absentFacts":atoms-present,
                "retainedEvidence":{"atoms":atoms,"ruleInstances":rules,"components":components,"dependencies":dependencies},
                "residual":{"atoms":residual_atoms,"ruleInstances":residual_rules,"components":residual_components}});
        }
    }
}
