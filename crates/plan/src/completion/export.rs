use super::*;
use crate::export::{atom, nodes_json, qualified};
use serde_json::{Value, json};
impl Plan {
    pub fn to_json(&self) -> Value {
        let terminal = match &self.terminal {
            Terminal::Accept => json!({"kind":"accept","next":"accepted"}),
            Terminal::Reject => json!({"kind":"reject"}),
            Terminal::Test(h) => {
                json!({"kind":"classify","on":atom(h),"then":{"kind":"accept","next":"accepted"},"else":{"kind":"reject"}})
            }
        };
        json!({"version":5,"state":"ready","semantics":"completion",
            "verification":qualified(&self.verification.0),"hypothesis":self.hypothesis.as_ref().map(atom),
            "decisions":self.decisions.as_ref().map(|rs| rs.iter().map(|r| {
                atom(&AtomKey { relation: r.clone(), arguments: vec![] })["relation"].clone()
            }).collect::<Vec<_>>()),
            "contract":"caller-certified W; classification on every permitted observation; unique requested values on accepted observations; outside output scopes not analysed",
            "assumptions":self.assumptions.iter().map(|a|qualified(&a.0)).collect::<Vec<_>>(),
            "inputs":self.inputs.iter().map(atom).collect::<Vec<_>>(),"producedInputs":[],
            "outputs":self.outputs.iter().map(|(a,p)|json!({"atom":atom(a),"priority":p})).collect::<Vec<_>>(),
            "meaningScope":{"kind":"completion-live-cones","classificationAtoms":self.classification_scope,"outputUnionAtoms":self.output_scope,"outsideAnalysed":false},
            "conditionalConstants":self.conditional_constants.iter().map(|(a,v)|json!({"atom":atom(a),"value":v,"scope":"accepted-output-cone"})).collect::<Vec<_>>(),
            "classification":{"nodes":nodes_json(&self.classification),"terminal":terminal},
            "accepted":{"controlPredecessor":"classification.accept","nodes":nodes_json(&self.accepted),"terminal":{"kind":"return"}},
            "size":{"computations":self.classification.len()+self.accepted.len(),"schedulingSplits":0}
        })
    }
}
