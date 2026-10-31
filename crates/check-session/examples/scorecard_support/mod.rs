//! Shared scorecard variants; no changes to production policies.
use denotate_check_session::{Retention, Session};
pub const MODES: [&str; 6] = [
    "global-bdd",
    "fresh-local-bdd",
    "cached-bdd",
    "grounding-bdd",
    "bdd-no-plans",
    "fresh-grounding-bdd",
];

pub fn session(mode: &str, unconstrained: bool) -> Option<Session> {
    let s = match mode {
        "global-bdd" => return None,
        "fresh-local-bdd" => {
            return Some(Session::new(Retention {
                max_entries: 0,
                max_bytes: 0,
                max_condition_nodes: 0,
            }));
        }
        "grounding-bdd" => Session::with_grounding(),
        "fresh-grounding-bdd" => Session::with_fresh_grounding(),
        "bdd-no-plans" => Session::with_fresh_planning(),
        _ => Session::default(),
    };
    Some(if unconstrained {
        s.without_retention_limits()
    } else {
        s
    })
}
