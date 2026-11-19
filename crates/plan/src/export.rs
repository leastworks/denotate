use super::*;
use denotate_ir::{OwnerKey, QualifiedKey, RelationKey};
use serde_json::{Value, json};

fn qualified(k: &QualifiedKey) -> Value {
    json!({"namespace":k.namespace.as_ref(),"name":k.name.as_ref()})
}
fn owner(k: &OwnerKey) -> Value {
    json!({"namespace":k.namespace(),"bytes":k.value()})
}
pub fn atom(k: &AtomKey) -> Value {
    let relation = match &k.relation {
        RelationKey::Named(q) => json!({"named":qualified(q)}),
        RelationKey::Generated { owner: o, local } => {
            json!({"generated":{"owner":owner(o),"local":local}})
        }
    };
    json!({"relation":relation,"arguments":k.arguments.iter().map(|c| json!({"sort":qualified(&c.sort.0),"name":c.name.as_ref()})).collect::<Vec<_>>()})
}
fn rule(k: &RuleKey) -> Value {
    match k {
        RuleKey::Library(q) => json!({"library":qualified(q)}),
        RuleKey::Installed { owner: o, local } => {
            json!({"installed":{"owner":owner(o),"local":local}})
        }
    }
}
impl Plan {
    /// Versioned, deterministic language-neutral export. Source rule keys link to
    /// frontend provenance; arena IDs, spans and solver witnesses are not identities.
    pub fn to_json(&self) -> Value {
        let nodes: Vec<_> = self.nodes.values().map(|n| {
            let operation = match &n.operation {
                Operation::Compute { output,expression } => json!({"kind":"compute","output":atom(output),"expression":{
                    "root":expression.root,"nodes":expression.nodes.iter().map(|n| match n {
                        Term::Constant(v) => json!({"constant":v}), Term::Read(k) => json!({"read":atom(k)}),
                        Term::Not(i) => json!({"not":i}), Term::And(xs) => json!({"and":xs}), Term::Or(xs) => json!({"or":xs}),
                        Term::If {atom:k,when_true,when_false} => json!({"if":atom(k),"then":when_true,"else":when_false})
                    }).collect::<Vec<_>>()}}),
                Operation::Fixpoint {outputs,rules} => json!({"kind":"least-fixpoint","outputs":outputs.iter().map(atom).collect::<Vec<_>>(),
                    "rules":rules.iter().map(|r| json!({"head":atom(&r.head),"body":r.body.iter().map(|(k,p)| json!({"atom":atom(k),"positive":p})).collect::<Vec<_>>(),"source":rule(&r.source)})).collect::<Vec<_>>() }),
            };
            json!({"id":atom(&n.id),"inputs":n.inputs.iter().map(atom).collect::<Vec<_>>(),"sources":n.sources.iter().map(rule).collect::<Vec<_>>(),"operation":operation})
        }).collect();
        let providers: BTreeMap<_, _> = self
            .nodes
            .iter()
            .flat_map(|(id, n)| n.outputs().into_iter().map(move |k| (k, id)))
            .collect();
        let mut depths = BTreeMap::<AtomKey, usize>::new();
        while depths.len() < self.nodes.len() {
            let mut progress = false;
            for (id, n) in &self.nodes {
                if depths.contains_key(id) {
                    continue;
                }
                let ds = n
                    .inputs
                    .iter()
                    .filter_map(|k| providers.get(k))
                    .map(|p| depths.get(*p).copied())
                    .collect::<Option<Vec<_>>>();
                if let Some(ds) = ds {
                    depths.insert(id.clone(), ds.into_iter().max().unwrap_or(0) + 1);
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }
        json!({"version":1,"state":"ready","verification":qualified(&self.verification.0),
            "contract":"permitted-inputs; whole-program unique meaning checked",
            "assumptions":self.assumptions.iter().map(|k| qualified(&k.0)).collect::<Vec<_>>(),
            "inputs":self.inputs.iter().map(atom).collect::<Vec<_>>(),
            "outputs":self.outputs.iter().map(|(k,p)| json!({"atom":atom(k),"priority":p})).collect::<Vec<_>>(),
            "nodes":nodes,"size":{"nodes":self.nodes.len(),"branches":0,"joins":0,"depth":depths.values().max().copied().unwrap_or(0)}})
    }
}
