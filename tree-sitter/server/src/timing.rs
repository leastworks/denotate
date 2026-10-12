//! Opt-in B5 instrumentation, not part of semantic state. Inclusive intervals:
//! diagnostics/references contain core queries; never add those totals together.
use denotate_analysis::*;
use serde_json::{json, Value};
use std::{cell::RefCell, collections::BTreeMap, time::Instant};

#[derive(Default)]
struct State {
    enabled: bool,
    samples: BTreeMap<&'static str, (u64, f64)>,
}
thread_local! { static STATE: RefCell<State> = RefCell::new(State::default()); }

pub fn reset(enabled: bool) {
    STATE.with(|s| {
        *s.borrow_mut() = State {
            enabled,
            ..State::default()
        }
    });
}

pub fn snapshot() -> Option<Value> {
    STATE.with(|s| {
        let s = s.borrow();
        s.enabled.then(|| {
            json!(s
                .samples
                .iter()
                .map(|(name, (calls, ms))| (*name, json!({"calls": calls, "ms": ms})))
                .collect::<BTreeMap<_, _>>())
        })
    })
}

pub struct Interval(&'static str, Option<Instant>);
pub fn interval(name: &'static str) -> Interval {
    Interval(name, STATE.with(|s| s.borrow().enabled.then(Instant::now)))
}
impl Drop for Interval {
    fn drop(&mut self) {
        if let Some(start) = self.1 {
            STATE.with(|s| {
                let mut s = s.borrow_mut();
                let sample = s.samples.entry(self.0).or_default();
                sample.0 += 1;
                sample.1 += start.elapsed().as_secs_f64() * 1000.0;
            });
        }
    }
}

// A's bridge measures outer Analysis calls, including cached-result cloning.
// This decorator measures that same boundary without changing the shared core.
#[derive(Default)]
pub struct Core(Analysis);
macro_rules! queries {
    ($($name:ident($($arg:ident: $ty:ty),*) -> $ret:ty;)*) => {$(
        pub fn $name(&self, $($arg: $ty),*) -> $ret {
            let _timer = interval("query");
            self.0.$name($($arg),*)
        }
    )*};
}
impl Core {
    pub fn update(&mut self, doc: Document) {
        let _timer = interval("update");
        self.0.update(doc);
    }
    pub fn remove(&mut self, uri: &str) {
        self.0.remove(uri);
    }
    pub fn query_counts(&self) -> QueryCounts {
        self.0.query_counts()
    }
    queries! {
        visible_relations(uri: &str) -> Vec<Symbol>;
        visible_sorts(uri: &str) -> Vec<Symbol>;
        module_candidates(uri: &str) -> Vec<Symbol>;
        resolve_sort(uri: &str, name: String) -> Option<Symbol>;
        expected_sort(uri: &str, relation: String, index: usize) -> Option<Symbol>;
        constant_candidates(uri: &str, relation: String, index: usize, name: Option<&str>) -> Vec<Symbol>;
        rule_analysis(uri: &str, id: &str) -> RuleAnalysis;
        declaration_diagnostics(uri: &str) -> Vec<DeclarationDiagnostic>;
        name_diagnostic(uri: &str, kind: NameKind, name: String, relation: String, index: usize) -> Option<String>;
        sort_label(uri: &str, owner_uri: &str, id: String) -> Option<String>;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn opt_in_and_reset_do_not_change_analysis() {
        let core = Core::default();
        reset(false);
        core.visible_relations("missing");
        assert!(snapshot().is_none());
        reset(true);
        core.visible_relations("missing");
        assert_eq!(snapshot().unwrap()["query"]["calls"], 1);
        reset(true);
        assert_eq!(snapshot().unwrap(), json!({}));
        reset(false);
    }
}
