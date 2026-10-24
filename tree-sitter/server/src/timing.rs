//! Opt-in B5 instrumentation, not part of semantic state. Inclusive intervals:
//! diagnostics/references contain core queries; never add those totals together.
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
