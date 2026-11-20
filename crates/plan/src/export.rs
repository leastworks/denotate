use super::*;
use denotate_ir::{OwnerKey, QualifiedKey, RelationKey};
use serde_json::{Value, json};
fn qualified(k: &QualifiedKey) -> Value {
    json!({"namespace":k.namespace.as_ref(),"name":k.name.as_ref()})
}
fn owner(k: &OwnerKey) -> Value {
    json!({"namespace":k.namespace(),"bytes":k.value()})
}
/// Generic semantic-key encoding. Frontends may render their own constant-name
/// encoding as qualified names; the driver never guesses how an opaque key is encoded.
pub fn atom(k: &AtomKey) -> Value {
    let relation = match &k.relation {
        RelationKey::Named(q) => json!({"named":qualified(q)}),
        RelationKey::Generated { owner: o, local } => {
            json!({"generated":{"owner":owner(o),"local":local}})
        }
    };
    json!({"relation":relation,"arguments":k.arguments.iter().map(|c|json!({"sort":qualified(&c.sort.0),"name":c.name.as_ref()})).collect::<Vec<_>>()})
}
fn rule(k: &RuleKey) -> Value {
    match k {
        RuleKey::Library(q) => json!({"library":qualified(q)}),
        RuleKey::Installed { owner: o, local } => {
            json!({"installed":{"owner":owner(o),"local":local}})
        }
    }
}
fn expression(e: &Expression) -> Value {
    json!({"root":e.root,"nodes":e.nodes.iter().map(|n|match n {
        Term::Constant(v)=>json!({"constant":v}),Term::Read(k)=>json!({"read":atom(k)}),Term::Not(i)=>json!({"not":i}),Term::And(xs)=>json!({"and":xs}),Term::Or(xs)=>json!({"or":xs}),Term::If {atom:k,when_true,when_false}=>json!({"if":atom(k),"then":when_true,"else":when_false})
    }).collect::<Vec<_>>()})
}
fn nodes_json(nodes: &BTreeMap<AtomKey, Node>) -> Value {
    json!(nodes.values().map(|n| {
        let operation=match &n.operation {
            Operation::Compute {output,expression:e}=>json!({"kind":"compute","output":atom(output),"expression":expression(e)}),
            Operation::Fixpoint {outputs,rules}=>json!({"kind":"least-fixpoint","outputs":outputs.iter().map(atom).collect::<Vec<_>>(),"rules":rules.iter().map(|r|json!({"head":atom(&r.head),"body":r.body.iter().map(|(k,p)|json!({"atom":atom(k),"positive":p})).collect::<Vec<_>>(),"source":rule(&r.source)})).collect::<Vec<_>>()}),
            Operation::Split {on,outputs,when_true,when_false}=>json!({"kind":"split","on":atom(on),"then":when_true.as_ref().map(|r|nodes_json(&r.nodes)),"else":when_false.as_ref().map(|r|nodes_json(&r.nodes)),"join":{"outputs":outputs.iter().map(atom).collect::<Vec<_>>()}}),
        };
        json!({"id":atom(&n.id),"inputs":n.inputs.iter().map(atom).collect::<Vec<_>>(),"sources":n.sources.iter().map(rule).collect::<Vec<_>>(),"operation":operation})
    }).collect::<Vec<_>>())
}
#[derive(Default)]
struct Size {
    nodes: usize,
    branches: usize,
    joins: usize,
    depth: usize,
}
fn size(nodes: &BTreeMap<AtomKey, Node>) -> Size {
    let providers: BTreeMap<_, _> = nodes
        .iter()
        .flat_map(|(id, n)| n.outputs().into_iter().map(move |k| (k, id)))
        .collect();
    let mut out = Size::default();
    let mut costs = BTreeMap::new();
    for (id, n) in nodes {
        out.nodes += 1;
        let mut cost = 1;
        if let Operation::Split {
            when_true,
            when_false,
            ..
        } = &n.operation
        {
            out.nodes += 1;
            out.branches += 1;
            out.joins += 1;
            let mut depth = 0;
            for r in [when_true, when_false].into_iter().flatten() {
                let s = size(&r.nodes);
                out.nodes += s.nodes;
                out.branches += s.branches;
                out.joins += s.joins;
                depth = depth.max(s.depth);
            }
            cost = 2 + depth;
        }
        costs.insert(id, cost);
    }
    let mut depths = BTreeMap::<AtomKey, usize>::new();
    while depths.len() < nodes.len() {
        let mut progress = false;
        for (id, n) in nodes {
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
                depths.insert(id.clone(), ds.into_iter().max().unwrap_or(0) + costs[id]);
                progress = true;
            }
        }
        assert!(progress, "constructed plan is acyclic");
    }
    out.depth = depths.values().max().copied().unwrap_or(0);
    out
}
impl Plan {
    /// Version 3 states the output-cone guarantee. An ID is local to its containing
    /// region; its complete address is the semantic branch path plus that ID.
    pub fn to_json(&self) -> Value {
        let s = size(&self.nodes);
        json!({"version":3,"state":"ready","verification":qualified(&self.verification.0),"contract":"permitted-inputs; unique output-cone meaning checked; outside not analysed",
            "meaningScope":scope_json(Some(&self.scope)),"assumptions":self.assumptions.iter().map(|k|qualified(&k.0)).collect::<Vec<_>>(),"inputs":self.inputs.iter().map(atom).collect::<Vec<_>>(),"outputs":self.outputs.iter().map(|(k,p)|json!({"atom":atom(k),"priority":p})).collect::<Vec<_>>(),
            "nodes":nodes_json(&self.nodes),"size":{"nodes":s.nodes,"branches":s.branches,"joins":s.joins,"depth":s.depth}})
    }
}

/// Scope metadata for successful and unsuccessful planning attempts. An absent
/// summary means scope preparation did not finish, not an empty cone.
pub fn scope_json(scope: Option<&stable_query::ScopeSummary>) -> Value {
    json!({"kind":"output-cones","outsideAnalysed":false,
        "requirement":"existence-and-uniqueness",
        "coneSize":scope.map(|s|json!({"atoms":s.atoms,"ruleInstances":s.rule_instances}))})
}
