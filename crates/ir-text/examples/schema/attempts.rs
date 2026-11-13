//! Reporting from cumulative observations, without changing admission or its clocks.
use serde_json::{Value, json};
use std::collections::BTreeMap;

#[derive(Default)]
pub(super) struct Attempts {
    rounds: BTreeMap<(String, String, u64), Value>,
    previous: BTreeMap<(String, String, u64, String), ([u64; 4], f64)>,
    samples: Vec<Value>,
}
impl Attempts {
    pub fn observe(&mut self, detail: &Value) {
        let a = &detail["admission"];
        // Terminal snapshots can relabel the preceding round as downstream even
        // when that phase had no work. Its counters were finalized already.
        if matches!(
            a["stage"].as_str(),
            Some("starting" | "complete" | "inconsistent-assumptions")
        ) {
            return;
        }
        let Some(round) = a["round"].as_u64() else {
            return;
        };
        let verification = detail["verification"].as_str().unwrap_or("").to_owned();
        let phase = a["phase"].as_str().unwrap_or("").to_owned();
        let key = (verification.clone(), phase.clone(), round);
        let finalized = a["stage"] == "attempt-summary";
        if !self.rounds.get(&key).is_some_and(|v| v["complete"] == true) {
            let mut value = a.clone();
            value["verification"] = json!(verification);
            value["complete"] = json!(finalized);
            self.rounds.insert(key, value);
        }
        for count in a["attempts"].as_array().into_iter().flatten() {
            let Some(kind) = count["kind"].as_str() else {
                continue;
            };
            let names = ["completed", "negative", "skipped", "failed"];
            let totals = names.map(|name| count[name].as_u64().unwrap_or(0));
            let elapsed = count["elapsedMs"].as_f64().unwrap_or(0.);
            let prior = self
                .previous
                .insert(
                    (verification.clone(), phase.clone(), round, kind.to_owned()),
                    (totals, elapsed),
                )
                .unwrap_or(([0; 4], 0.));
            // A reset/damaged stream cannot supply an elapsed delta.
            if elapsed < prior.1 || totals.iter().zip(prior.0).any(|(n, old)| *n < old) {
                continue;
            }
            let changes = std::array::from_fn::<_, 4, _>(|i| totals[i] - prior.0[i]);
            let n: u64 = changes.iter().sum();
            if n == 0 {
                continue;
            }
            let outcomes: BTreeMap<_, _> = names.into_iter().zip(changes).collect();
            self.samples.push(json!({
                "verification":verification, "phase":phase, "round":round, "kind":kind,
                "count":n, "measurement":if n == 1 {"individual"} else {"batch"},
                "elapsedMs":elapsed-prior.1, "outcomes":outcomes,
                // Only a single skipped attempt identifies its own target here.
                // A component's representative rule is not the attempted rule.
                "target":if n==1 && changes[2]==1 && a["skipped"]==kind {a["skipTarget"].clone()} else {Value::Null},
                "failure":if n==1 && changes[2]==1 {a["failure"].clone()} else {Value::Null},
            }));
        }
    }
    pub fn finish(self) -> (Vec<Value>, Vec<Value>) {
        (self.rounds.into_values().collect(), self.samples)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn event(v: &str, phase: &str, round: u64, stage: &str, skipped: u64, ms: f64) -> Value {
        json!({"verification":v,"admission":{"phase":phase,"round":round,"stage":stage,
            "skipped":"guarded-bounds","skipTarget":{"head":"h()"},"failure":"BDD nodes",
            "attempts":[{"kind":"guarded-bounds","skipped":skipped,"elapsedMs":ms}]}})
    }
    #[test]
    fn summaries_survive_later_progress_and_contexts_do_not_collide() {
        let mut a = Attempts::default();
        a.observe(&event("a", "relevant", 1, "attempt-summary", 2, 10.));
        a.observe(&event("a", "relevant", 1, "complete", 0, 0.));
        a.observe(&event("a", "downstream", 1, "complete", 2, 10.));
        a.observe(&event("b", "relevant", 1, "attempt-summary", 1, 1.));
        a.observe(&event("a", "downstream", 1, "candidates", 1, 3.));
        let (rounds, _) = a.finish();
        assert_eq!(rounds.len(), 3);
        assert_eq!(rounds[1]["attempts"][0]["skipped"], 2);
        assert_eq!(rounds[1]["complete"], true);
        assert_eq!(rounds[0]["complete"], false);
    }
    #[test]
    fn deltas_are_individual_only_when_exactly_one_attempt_finished() {
        let mut a = Attempts::default();
        a.observe(&event("a", "relevant", 1, "guarded-bounds", 1, 3.));
        a.observe(&event("a", "relevant", 1, "guarded-bounds", 1, 3.));
        a.observe(&event("a", "relevant", 1, "attempt-summary", 3, 12.));
        let (_, samples) = a.finish();
        assert_eq!(samples.len(), 2);
        assert_eq!(samples[0]["measurement"], "individual");
        assert_eq!(samples[0]["elapsedMs"], 3.);
        assert_eq!(samples[0]["target"]["head"], "h()");
        assert_eq!(samples[1]["measurement"], "batch");
        assert_eq!(samples[1]["count"], 2);
        assert_eq!(samples[1]["elapsedMs"], 9.);
        assert!(samples[1]["target"].is_null());
    }
}
