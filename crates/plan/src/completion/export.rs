use super::*;
use crate::export::{atom, expression, nodes_json, qualified};
use serde_json::{Value, json};
fn terminal(t: &Terminal) -> Value {
    match t {
        Terminal::Accept => json!({"kind":"accept"}),
        Terminal::Reject => json!({"kind":"reject"}),
        Terminal::Test(h) => json!({"kind":"classify","on":atom(h)}),
    }
}
fn region(r: &Region) -> Value {
    let next = match &r.next {
        Next::Split {
            on,
            then,
            otherwise,
        } => json!({"kind":"split","on":atom(on),"then":region(then),"else":region(otherwise)}),
        Next::Leaf {
            checks,
            terminal: t,
            accepted: a,
        } => json!({"kind":"leaf",
            "checks":checks.iter().map(|c| json!({"atom":atom(&c.atom),"value":c.value,"definition":expression(&c.definition)})).collect::<Vec<_>>(),
            "terminal":terminal(t),
            "accepted":a.as_deref().map(accepted)}),
    };
    json!({"nodes":nodes_json(&r.nodes),"next":next})
}
fn accepted(a: &Accepted) -> Value {
    let next = match &a.next {
        AcceptedNext::Return => json!({"kind":"return"}),
        AcceptedNext::Unreachable => json!({"kind":"unreachable"}),
        AcceptedNext::Split {
            on,
            then,
            otherwise,
        } => json!({"kind":"split","on":atom(on),"then":accepted(then),"else":accepted(otherwise)}),
    };
    json!({"nodes":nodes_json(&a.nodes),"next":next})
}
impl Plan {
    pub fn to_json(&self) -> Value {
        json!({"version":5,"state":"ready","semantics":"completion",
            "verification":qualified(&self.verification.0),"hypothesis":self.hypothesis.as_ref().map(atom),
            "decisions":self.decisions.as_ref().map(|rs| rs.iter().map(|r| {
                atom(&AtomKey { relation: r.clone(), arguments: vec![] })["relation"].clone()
            }).collect::<Vec<_>>()),
            "contract":"caller-certified W; on every permitted observation the plan accepts exactly when a classification interpretation with H exists (unique on the decisions), rejects otherwise (genuine rejection or invalid input), and returns the unique requested values when it accepts; outside output scopes not analysed",
            "assumptions":self.assumptions.iter().map(|a|qualified(&a.0)).collect::<Vec<_>>(),
            "inputs":self.inputs.iter().map(atom).collect::<Vec<_>>(),"producedInputs":[],
            "outputs":self.outputs.iter().map(|(a,p)|json!({"atom":atom(a),"priority":p})).collect::<Vec<_>>(),
            "meaningScope":{"kind":"completion-live-cones","classificationAtoms":self.classification_scope,"outputUnionAtoms":self.output_scope,"outsideAnalysed":false},
            "plan":region(&self.root),
            "size":{"computations":self.nodes().len(),"schedulingSplits":self.splits()}
        })
    }
}
