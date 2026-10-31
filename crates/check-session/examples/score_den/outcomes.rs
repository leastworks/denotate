//! Witness-free comparison, keyed before rendering. Totals alone cannot detect a
//! failure moving between obligations, uniqueness groups, regions or notices.
use denotate_check::*;
use denotate_ir::*;
use denotate_ir_text::LoadedProgram;
use serde_json::{Value, json};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scope {
    Obligation(ObligationKey),
    Group(GroupKey),
    Region(ComponentKey),
    Notice(NoticeKey),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcomes {
    pub consistency: &'static str,
    pub keyed: BTreeMap<Scope, Value>,
    pub unfinished: Option<ResourceReason>,
}

pub fn name(key: &QualifiedKey) -> String {
    let local = denotate_ir_text::spelling(&key.name, denotate_ir_text::NameKind::Identifier);
    if key.namespace.is_empty() {
        local
    } else {
        format!("{}::{local}", key.namespace)
    }
}
pub fn kind(k: Cardinality) -> &'static str {
    match k {
        Cardinality::AtMostOne => "at_most_one",
        Cardinality::AtLeastOne => "at_least_one",
        Cardinality::ExactlyOne => "exactly_one",
        Cardinality::Empty => "empty",
    }
}
fn reason(r: &ResourceReason) -> Value {
    json!({"phase":r.phase,"resource":r.resource})
}
fn limit(r: Inconclusive) -> Value {
    reason(&r.into())
}
fn scoped(s: &ScopedResult) -> Value {
    match s {
        ScopedResult::Proved => json!({"state":"proved"}),
        ScopedResult::Counterexample(..) => json!({"state":"counterexample"}),
        ScopedResult::Unsupported(_) => json!({"state":"unsupported"}),
        ScopedResult::Inconclusive(r) => json!({"state":"inconclusive","reason":reason(r)}),
    }
}
fn state(failed: bool, unsupported: bool, inconclusive: bool) -> &'static str {
    if failed {
        "counterexample"
    } else if inconclusive {
        "inconclusive"
    } else if unsupported {
        "unsupported"
    } else {
        "proved"
    }
}
fn unavailable(inconsistent: bool) -> Value {
    json!({"state":if inconsistent {"not-checked"} else {"inconclusive"},"complete":false,"findings":0})
}
impl Outcomes {
    pub fn from_results(p: &LoadedProgram, r: &ScopedResults) -> Self {
        let mut keyed = BTreeMap::new();
        for (key, value) in &r.groups {
            keyed.insert(Scope::Group(key.clone()), scoped(value));
        }
        for (key, value) in &r.regions {
            let completion = match &value.completion {
                RegionCompletion::NoContradiction => json!({"state":"no-contradiction"}),
                RegionCompletion::NoMeaning { .. } => json!({"state":"no-meaning"}),
                RegionCompletion::Deferred(_) => json!({"state":"deferred"}),
                RegionCompletion::Inconclusive(r) => {
                    json!({"state":"inconclusive","reason":reason(r)})
                }
            };
            keyed.insert(
                Scope::Region(key.clone()),
                json!({"result":scoped(&value.outcome),"completion":completion}),
            );
        }
        for (key, reason_) in &r.incomplete {
            keyed.entry(Scope::Region(key.clone())).or_insert_with(
                || json!({"result":{"state":"inconclusive","reason":reason(reason_)}}),
            );
        }
        for key in &r.context.notices {
            let value = match r.notices.get(key) {
                None => {
                    json!({"state":"unknown", "reason":{"kind":if r.inconsistent_assumptions {"inconsistent-assumptions"}else{"not-checked"}}})
                }
                Some(n) => {
                    let reason = match &n.state {
                        NoticeState::Unknown(NoticeUnknown::Inconclusive(r)) => limit(*r),
                        NoticeState::Unknown(other) => {
                            json!({"kind":match other {NoticeUnknown::Unsupported=>"unsupported",NoticeUnknown::Deadline=>"deadline",NoticeUnknown::InconsistentAssumptions=>"inconsistent-assumptions",NoticeUnknown::Inconclusive(_)=>unreachable!()}})
                        }
                        _ => Value::Null,
                    };
                    json!({"state":n.state.label(),"reason":reason})
                }
            };
            keyed.insert(Scope::Notice(key.clone()), value);
        }
        for o in p.corpus.obligations() {
            let key = p.keys.obligation(o.id).unwrap();
            if !r.context.obligations.contains(key) {
                continue;
            }
            let k = o.requirement.kind();
            let mut components = BTreeMap::new();
            if k.has_uniqueness() {
                let mut uniqueness = unavailable(r.inconsistent_assumptions);
                if !r.inconsistent_assumptions {
                    if let Some(domain) = r.group_domains.get(key) {
                        // No Cartesian enumeration. Trivial groups are proved even
                        // when no explicit query/finding was needed for them.
                        let total = if domain.domains.iter().any(|d| d.is_empty()) {
                            Some(0)
                        } else {
                            domain
                                .domains
                                .iter()
                                .try_fold(1usize, |n, d| n.checked_mul(d.len()))
                        };
                        let required = domain
                            .members
                            .iter()
                            .filter(|(_, m)| m.len() > 1)
                            .collect::<Vec<_>>();
                        let mut counts = BTreeMap::<String, usize>::new();
                        for (tuple, _) in &required {
                            let group = GroupKey {
                                obligation: key.clone(),
                                tuple: (*tuple).clone(),
                            };
                            let value = r
                                .groups
                                .get(&group)
                                .map(scoped)
                                .unwrap_or_else(|| json!({"state":"inconclusive"}));
                            *counts
                                .entry(value["state"].as_str().unwrap().to_owned())
                                .or_default() += 1;
                            keyed.insert(Scope::Group(group), value);
                        }
                        let count = |s: &str| counts.get(s).copied().unwrap_or(0);
                        let failed = count("counterexample");
                        let unsupported = count("unsupported");
                        let inconclusive = count("inconclusive");
                        uniqueness = json!({"state":state(failed>0,unsupported>0,inconclusive>0),
                            "complete":unsupported==0 && inconclusive==0,"findings":failed,
                            "groups":total,"implicit_proved_groups":total.map(|n|n-required.len()),
                            "explicit_groups":counts});
                    }
                }
                components.insert("uniqueness", uniqueness);
            }
            if k.has_coverage() {
                components.insert("coverage", r.coverage.get(key).map(|c| json!({
                    "state":state(c.missing>0,c.unsupported>0,c.inconclusive.is_some()),
                    "complete":c.complete(),"findings":usize::from(c.missing>0),
                    "missing_groups":c.missing,"count_kind":if c.complete(){"exact"}else{"lower-bound"},
                    "examined_groups":c.examined,"unsupported_groups":c.unsupported,
                    "inconclusive":c.inconclusive.map(limit),"no_groups":c.no_groups,
                })).unwrap_or_else(|| unavailable(r.inconsistent_assumptions)));
            }
            if k == Cardinality::Empty {
                components.insert("emptiness",r.emptiness.get(key).map(|e| json!({
                    "state":state(e.present>0,false,e.unresolved || e.inconclusive.is_some()),"complete":e.complete(),
                    "findings":usize::from(e.present>0),"present_tuples":e.present,
                    "count_kind":if e.complete(){"exact"}else{"lower-bound"},
                    "unresolved":e.unresolved,"inconclusive":e.inconclusive.map(limit),
                })).unwrap_or_else(|| unavailable(r.inconsistent_assumptions)));
            }
            let has = |s| components.values().any(|v| v["state"] == s);
            let verdict = if r.inconsistent_assumptions {
                "not-checked"
            } else {
                state(
                    has("counterexample"),
                    has("unsupported"),
                    has("inconclusive"),
                )
            };
            let complete = components.values().all(|v| v["complete"] == true);
            let findings: u64 = components
                .values()
                .map(|v| v["findings"].as_u64().unwrap())
                .sum();
            keyed.insert(Scope::Obligation(key.clone()),json!({"kind":kind(k),"state":verdict,"complete":complete,"findings":findings,"components":components}));
        }
        Self {
            consistency: if r.inconsistent_assumptions {
                "inconsistent"
            } else {
                "consistent"
            },
            keyed,
            unfinished: r.unfinished.clone(),
        }
    }
    pub fn contradicts(&self, other: &Self) -> bool {
        // A conclusive whole-program proof also rules out a finding in a scope
        // absent from its explicit maps (for example an extra no-meaning region).
        if matches!(
            (
                self.json()["state"].as_str(),
                other.json()["state"].as_str()
            ),
            (Some("proved"), Some("findings")) | (Some("findings"), Some("proved"))
        ) {
            return true;
        }
        fn opposite(a: &Value, b: &Value) -> bool {
            matches!(
                (a["state"].as_str(), b["state"].as_str()),
                (Some("proved"), Some("counterexample")) | (Some("counterexample"), Some("proved"))
            )
        }
        if matches!(
            (self.consistency, other.consistency),
            ("consistent", "inconsistent") | ("inconsistent", "consistent")
        ) {
            return true;
        }
        self.keyed.iter().any(|(key, a)| {
            other.keyed.get(key).is_some_and(|b| {
                if opposite(a, b) {
                    return true;
                }
                match key {
                    Scope::Notice(_) => {
                        let conclusive = |v: &Value| {
                            matches!(
                                v["state"].as_str(),
                                Some(
                                    "impossible" | "always-true" | "varying" | "parent-unreachable"
                                )
                            )
                        };
                        conclusive(a) && conclusive(b) && a["state"] != b["state"]
                    }
                    Scope::Obligation(_) => ["coverage", "uniqueness", "emptiness"]
                        .iter()
                        .any(|c| opposite(&a["components"][c], &b["components"][c])),
                    Scope::Region(_) => matches!(
                        (
                            a["completion"]["state"].as_str(),
                            b["completion"]["state"].as_str()
                        ),
                        (Some("no-contradiction"), Some("no-meaning"))
                            | (Some("no-meaning"), Some("no-contradiction"))
                    ),
                    _ => false,
                }
            })
        })
    }
    pub fn json(&self) -> Value {
        let mut obligations = Vec::new();
        let mut notices = Vec::new();
        let mut by_kind = BTreeMap::<String, BTreeMap<String, usize>>::new();
        let mut by_state = BTreeMap::<String, usize>::new();
        let (mut unsupported, mut no_meaning, mut incomplete_regions) = (0, 0, 0);
        let mut reasons = Vec::new();
        for (key, value) in &self.keyed {
            match key {
                Scope::Obligation(k) => {
                    let mut v = value.clone();
                    v["name"] = json!(name(&k.0));
                    obligations.push(v);
                    *by_kind
                        .entry(value["kind"].as_str().unwrap().into())
                        .or_default()
                        .entry(value["state"].as_str().unwrap().into())
                        .or_default() += 1;
                }
                Scope::Notice(k) => {
                    let mut v = value.clone();
                    v["name"] = json!(name(&k.0));
                    notices.push(v);
                    *by_state
                        .entry(value["state"].as_str().unwrap().into())
                        .or_default() += 1;
                }
                Scope::Region(_) => {
                    unsupported += usize::from(value["result"]["state"] == "unsupported");
                    no_meaning += usize::from(value["completion"]["state"] == "no-meaning");
                    incomplete_regions += usize::from(
                        value["result"]["state"] == "inconclusive"
                            || value["completion"]["state"] == "inconclusive",
                    );
                }
                Scope::Group(_) => {}
            }
            collect_reasons(value, &mut reasons);
        }
        if let Some(r) = &self.unfinished {
            reasons.push(reason(r));
        }
        reasons.sort_by_key(Value::to_string);
        reasons.dedup();
        let findings: u64 = obligations
            .iter()
            .map(|o| o["findings"].as_u64().unwrap())
            .sum();
        let complete = self.consistency == "consistent"
            && self.unfinished.is_none()
            && incomplete_regions == 0
            && unsupported == 0
            && obligations.iter().all(|o| o["complete"] == true);
        json!({"consistency":self.consistency,"complete":complete,
            "state":if self.consistency=="inconsistent" {"inconsistent-assumptions"}
                else if findings>0||no_meaning>0 {"findings"} else if !complete {"incomplete"} else {"proved"},
            "obligations":obligations,"obligations_by_kind":by_kind,"obligation_findings":findings,
            "regions":{"unsupported":unsupported,"no_meaning":no_meaning,"inconclusive":incomplete_regions},
            "notices":notices,"notices_by_state":by_state,"inconclusive":reasons})
    }
}
fn collect_reasons(v: &Value, out: &mut Vec<Value>) {
    match v {
        Value::Object(m) if m.contains_key("phase") && m.contains_key("resource") => {
            out.push(v.clone())
        }
        Value::Object(m) => {
            for value in m.values() {
                collect_reasons(value, out);
            }
        }
        Value::Array(a) => {
            for value in a {
                collect_reasons(value, out);
            }
        }
        _ => {}
    }
}
