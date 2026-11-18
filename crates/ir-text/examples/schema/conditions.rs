//! Workload classification is outside the checker. The JSONL remains the complete
//! stream; this bounded summary survives interrupted checks and report recovery.
use serde_json::{Value, json};
use std::collections::BTreeMap;

pub struct Conditions {
    kinds: BTreeMap<String, String>,
    largest: BTreeMap<String, Vec<Value>>,
    failures: Vec<Value>,
    steps: Vec<Value>,
    omitted_failures: usize,
    omitted_steps: usize,
    order: Value,
    recursive: Vec<Value>,
    recursive_shapes: Vec<Value>,
    omitted_recursive: usize,
}
impl Conditions {
    pub fn new(source: &str) -> Self {
        let kinds = source
            .lines()
            .filter_map(|l| {
                let mut parts = l.strip_prefix("// profile-kind ")?.split_whitespace();
                Some((
                    format!("workload::{}", parts.next()?),
                    parts.next()?.to_owned(),
                ))
            })
            .collect();
        Self {
            kinds,
            largest: BTreeMap::new(),
            failures: vec![],
            steps: vec![],
            omitted_failures: 0,
            omitted_steps: 0,
            order: Value::Null,
            recursive: vec![],
            recursive_shapes: vec![],
            omitted_recursive: 0,
        }
    }
    fn kind(&self, atom: &Value) -> String {
        let relation = atom["relation"].as_str().unwrap_or("unknown");
        if relation.ends_with("::unknown_decision") {
            return "unknown-decision-audit".into();
        }
        if relation.ends_with("::conflicting_knowledge") {
            return "consistency-audit".into();
        }
        atom["arguments"]
            .as_array()
            .and_then(|a| a.first())
            .and_then(Value::as_str)
            .and_then(|a| self.kinds.get(a))
            .cloned()
            .unwrap_or_else(|| "other".into())
    }
    pub fn observe(&mut self, mut v: Value) {
        match v["kind"].as_str() {
            Some("input-order") => self.order = v,
            Some("recursive-component") | Some("recursive-component-shape") => {
                // Keep bounded recent records, including a final/interrupted snapshot.
                // Runtime component IDs belong only to this invocation, not a stable key.
                let list = if v["kind"] == "recursive-component" {
                    &mut self.recursive
                } else {
                    &mut self.recursive_shapes
                };
                if list.len() == 64 {
                    list.remove(0);
                    self.omitted_recursive += 1;
                }
                list.push(v);
            }
            Some("retained-condition") => {
                v["decisionKind"] = json!(self.kind(&v["atom"]));
                // Relation distinguishes known_true/known_false. Stages distinguish
                // assumptions, admission and checking; do not sum nested spans.
                let key = format!(
                    "{} / {} / {}",
                    v["stages"], v["atom"]["relation"], v["decisionKind"]
                );
                let top = self.largest.entry(key).or_default();
                if let Some(old) = top.iter_mut().find(|old| old["atom"] == v["atom"]) {
                    if old["nodes"].as_u64() < v["nodes"].as_u64() {
                        *old = v;
                    }
                } else {
                    top.push(v);
                }
                top.sort_by(|a, b| {
                    b["nodes"]
                        .as_u64()
                        .cmp(&a["nodes"].as_u64())
                        .then_with(|| a["atom"].to_string().cmp(&b["atom"].to_string()))
                });
                top.truncate(5);
            }
            Some("failed-operation") => {
                v["decisionKind"] = json!(self.kind(&v["target"]));
                if self.failures.len() < 64 {
                    self.failures.push(v);
                } else {
                    self.omitted_failures += 1;
                }
            }
            Some("assumption-step") => {
                if self.steps.len() < 4096 {
                    self.steps.push(v);
                } else {
                    self.omitted_steps += 1;
                }
            }
            _ => {}
        }
    }
    pub fn finish(self) -> Value {
        let mut alternatives = BTreeMap::<String, Vec<usize>>::new();
        if let Some(atoms) = self.order["atoms"].as_array() {
            for (i, a) in atoms.iter().enumerate() {
                if a["relation"]
                    .as_str()
                    .is_some_and(|s| s.ends_with("::result"))
                {
                    if let Some(writer) = a["arguments"][0].as_str() {
                        alternatives.entry(writer.into()).or_default().push(i);
                    }
                }
            }
        }
        let spans: Vec<_> = alternatives
            .into_iter()
            .map(|(writer, positions)| {
                let span = positions.last().unwrap() - positions[0] + 1;
                json!({"writer":writer,"positions":positions,"span":span})
            })
            .collect();
        json!({"recursiveComponents":self.recursive,"recursiveShapes":self.recursive_shapes,"omittedRecursiveRecords":self.omitted_recursive,"largest":self.largest,"minimumConditionNodes":64,"failedOperations":self.failures,"omittedFailures":self.omitted_failures,"assumptionSteps":self.steps,"omittedAssumptionSteps":self.omitted_steps,"inputOrder":self.order,"resultAlternativeSpans":spans})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn recursive_recovery_keeps_interrupted_approximations_separate_from_exact_conditions() {
        let mut c = Conditions::new("");
        c.observe(
            json!({"kind":"recursive-component-shape","component":3,"atoms":200,"cycles":[]}),
        );
        c.observe(json!({"kind":"recursive-component","component":3,"state":"running","completedRounds":2}));
        c.observe(json!({"kind":"recursive-component","component":3,"state":"exhausted","largest":[{"atom":{"relation":"known_true"},"nodes":100}]}));
        let r = c.finish();
        assert_eq!(
            r["recursiveComponents"].as_array().unwrap().last().unwrap()["state"],
            "exhausted"
        );
        assert!(r["largest"].as_object().unwrap().is_empty());
        assert_eq!(r["recursiveShapes"][0]["atoms"], 200);
    }
    #[test]
    fn classification_separates_polarities_and_recovers_preparation_failure() {
        let mut c = Conditions::new("// profile-kind gate1 coverage\n");
        for relation in ["schema::known_true", "schema::known_false"] {
            c.observe(json!({"kind":"retained-condition","stages":["checking"],"atom":{"relation":relation,"arguments":["workload::gate1"]},"nodes":100}));
        }
        c.observe(json!({"kind":"failed-operation","target":{"relation":"schema::known_false","arguments":["workload::gate1"]},"error":"limit"}));
        c.observe(json!({"kind":"input-order","effective":"key","atoms":[{"relation":"workload::result","arguments":["workload::u0","v0"]},{"relation":"workload::w","arguments":[]},{"relation":"workload::result","arguments":["workload::u0","v1"]}]}));
        let r = c.finish();
        assert_eq!(r["largest"].as_object().unwrap().len(), 2);
        assert_eq!(r["failedOperations"][0]["decisionKind"], "coverage");
        assert_eq!(r["resultAlternativeSpans"][0]["span"], 3);
    }
}
