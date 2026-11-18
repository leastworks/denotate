//! Synthetic knowledge lowering. Shapes are explicit; no checker, filesystem or
//! private reproduction is needed to generate either side of the comparison.
use super::Shape;
use std::{collections::BTreeSet, fmt::Write};

#[derive(Clone, Debug)]
pub struct Knowledge {
    pub trees: usize,
    pub fields_per_leaf: usize,
    pub unlocked_fields: usize,
    pub writers_per_field: usize,
    pub chain_length: usize,
    pub self_dependent: bool,
    pub ring_terms: usize,
    pub ring_writers: usize,
    pub ring_lanes: usize,
    pub result_values: usize,
}
impl Knowledge {
    pub fn metadata(&self) -> serde_json::Value {
        serde_json::json!({"trees":self.trees,"fieldsPerLeaf":self.fields_per_leaf,"unlockedFields":self.unlocked_fields,"writersPerField":self.writers_per_field,"chainLength":self.chain_length,"selfDependent":self.self_dependent,"ringTerms":self.ring_terms,"ringWriters":self.ring_writers,"ringLanes":self.ring_lanes,"resultValues":self.result_values})
    }
}
impl Default for Knowledge {
    fn default() -> Self {
        Self {
            trees: 1,
            fields_per_leaf: 1,
            unlocked_fields: 1,
            writers_per_field: 1,
            chain_length: 0,
            self_dependent: false,
            ring_terms: 0,
            ring_writers: 4,
            ring_lanes: 1,
            result_values: 3,
        }
    }
}
pub fn validate(s: &Shape, plain: bool) -> Result<(), String> {
    let k = &s.knowledge;
    if k.writers_per_field == 0 || k.ring_writers == 0 || k.ring_lanes == 0 || k.result_values == 0
    {
        return Err("writer counts, ring-lanes and result-values must be positive".into());
    }
    if plain && (k.trees != 0 || k.chain_length != 0 || k.ring_terms == 0 || k.self_dependent) {
        return Err("plain-term-ring requires --trees 0, positive --ring-terms, no chain or self-dependent flag".into());
    }
    if k.trees == 0 && k.chain_length == 0 && k.ring_terms == 0 {
        return Err("select a forest, chain or term ring".into());
    }
    if k.self_dependent && k.chain_length == 0 {
        return Err("self-dependent requires a positive chain-length".into());
    }
    if s.overlaps && k.ring_terms == 0 {
        return Err("knowledge --overlaps requires a term ring".into());
    }
    // Bound generated source, not semantic checking. Use conservative checked
    // arithmetic before allocating trees, gates or Cartesian coverage tables.
    let nodes = if k.trees > 0 { s.tree()?.len() } else { 0 };
    let cost = (|| {
        let forest = nodes.checked_mul(k.trees)?;
        let fields = forest.checked_mul(
            k.fields_per_leaf
                .checked_add(k.unlocked_fields)?
                .checked_add(1)?,
        )?;
        let gates = forest
            .checked_mul(fields)?
            .checked_mul(k.writers_per_field.checked_add(20)?)?;
        let chain = k
            .chain_length
            .checked_mul(k.writers_per_field)?
            .checked_mul(30)?;
        let ring = k
            .ring_terms
            .checked_mul(k.ring_writers)?
            .checked_mul(k.ring_lanes.checked_add(k.result_values)?.checked_add(20)?)?;
        gates.checked_add(chain)?.checked_add(ring)
    })()
    .ok_or("knowledge shape overflow")?;
    if cost > 5_000_000 {
        return Err(
            "knowledge source expansion exceeds 5000000 units; reduce shape dimensions".into(),
        );
    }
    Ok(())
}

struct Gates {
    text: String,
    names: BTreeSet<String>,
    serial: usize,
    required: Vec<String>,
}
impl Gates {
    fn new() -> Self {
        let mut g = Self { text: include_str!("../../../../editors/den/examples/shipping-news/11-incremental-schema/library/knowledge.den").replace("namespace schema;", "namespace schema {"), names: BTreeSet::new(), serial: 0, required: vec![] };
        g.text += "\n}\nuse schema;\nnamespace workload {\n";
        g.constant("yes", true);
        g.constant("no", false);
        g
    }
    fn line(&mut self, text: impl AsRef<str>) {
        self.text.push_str(text.as_ref());
        self.text.push('\n');
    }
    fn name(&mut self, n: &str) -> String {
        if self.names.insert(n.into()) {
            self.line(format!("const {n}: Decision;"));
        }
        n.into()
    }
    fn fresh(&mut self) -> String {
        let n = format!("gate{}", self.serial);
        self.serial += 1;
        self.name(&n)
    }
    fn constant(&mut self, n: &str, v: bool) {
        self.name(n);
        self.line(format!("always_{}({n});", if v { "true" } else { "false" }));
    }
    fn gate(&mut self, kind: &str, n: &str, a: &str, b: Option<&str>) -> String {
        self.name(n);
        self.name(a);
        if let Some(b) = b {
            self.name(b);
            self.line(format!("{kind}({n}, {a}, {b});"));
        } else {
            self.line(format!("{kind}({n}, {a});"));
        }
        n.into()
    }
    fn binary(&mut self, kind: &str, a: &str, b: &str) -> String {
        let n = self.fresh();
        self.gate(kind, &n, a, Some(b))
    }
    fn fold(&mut self, kind: &str, xs: Vec<String>) -> String {
        // Balanced gates avoid introducing a linear gate chain for a wide OR/AND.
        if xs.is_empty() {
            return if kind == "both" { "yes" } else { "no" }.into();
        }
        let mut level = xs;
        while level.len() > 1 {
            level = level
                .chunks(2)
                .map(|p| {
                    if p.len() == 1 {
                        p[0].clone()
                    } else {
                        self.binary(kind, &p[0], &p[1])
                    }
                })
                .collect();
        }
        level.pop().unwrap()
    }
    fn not(&mut self, a: &str) -> String {
        let n = self.fresh();
        self.gate("opposite", &n, a, None)
    }
    fn observe(&mut self, name: &str, atom: &str) -> String {
        self.name(name);
        self.line(format!(
            "known_true({name}) :- {atom};\nknown_false({name}) :- !{atom};"
        ));
        name.into()
    }
    fn ready(&mut self, a: &str) -> String {
        let n = self.fresh();
        self.line(format!(
            "known_true({n}) :- known_true({a});\nknown_true({n}) :- known_false({a});"
        ));
        n
    }
    fn audit(&mut self, n: &str) {
        self.name(n);
        self.required.push(n.into());
    }
    fn finish(mut self, assumptions: &[&str]) -> String {
        for n in self.required.clone() {
            self.line(format!("required_decision({n});"));
        }
        self.line(format!("verification checks {{ assumptions: [{}]; obligations: [no_conflicting_knowledge, no_unknown_decisions, at_most_one_path, at_most_one_set_value, no_message_writes]; }}",assumptions.join(", ")));
        self.text.push_str("}\n");
        self.text
    }
}

// Identical open inputs and restrictions in the plain and knowledge ring.
fn ring_inputs(s: &Shape) -> String {
    let k = &s.knowledge;
    let mut o = String::new();
    o += "sort RingTerm; sort RingUse; sort RingFlow; sort Lane; sort ResultValue;\nrelation flows(f: RingFlow); relation lanes(l: Lane); relation result_candidate(u: RingUse, v: ResultValue);\ninput selector(f: RingFlow) within flows; input fa(l: Lane) within lanes; input fb(l: Lane) within lanes; input result(u: RingUse, v: ResultValue) within result_candidate; input w();\nassumption one_selector: at_most_one(selector, group_by: ());\nassumption has_result: at_least_one(result, group_by: u); assumption one_result: at_most_one(result, group_by: u);\n";
    for v in 0..k.result_values {
        writeln!(o, "const v{v}: ResultValue;").unwrap();
    }
    for t in 0..k.ring_terms {
        writeln!(o, "const t{t}: RingTerm;").unwrap();
        for w in 0..k.ring_writers {
            writeln!(
                o,
                "const u{t}_{w}: RingUse; const f{t}_{w}: RingFlow; flows(f{t}_{w});"
            )
            .unwrap();
            for v in 0..k.result_values {
                writeln!(o, "result_candidate(u{t}_{w}, v{v});").unwrap();
            }
            for l in 0..k.ring_lanes {
                writeln!(o, "const l{t}_{w}_{l}: Lane; lanes(l{t}_{w}_{l});").unwrap();
            }
        }
    }
    o
}
pub fn plain_ring(s: &Shape) -> Result<String, String> {
    validate(s, true)?;
    let k = &s.knowledge;
    let mut o = String::from(
        "// Plain term ring, with the original constraint/use/flow indirections.\nnamespace workload;\n",
    );
    o += &ring_inputs(s);
    o += "sort Constraint; sort Element;\nrelation terms(t: RingTerm); relation term_constraint(t: RingTerm, c: Constraint); relation constraint_element(c: Constraint, e: Element);\nrelation lane_flow(l: Lane, f: RingFlow); relation flow_holds(f: RingFlow);\nflow_holds(F) :- lane_flow(L, F), selector(F), fa(L), !fb(L);\nrelation element_value(e: Element, v: ResultValue); relation element_present(e: Element); element_present(E) :- element_value(E, _);\nrelation value_ok(c: Constraint); relation satisfies(c: Constraint); satisfies(C) :- constraint_element(C, E), element_present(E), value_ok(C);\nrelation unsatisfied(t: RingTerm); unsatisfied(T) :- term_constraint(T, C), !satisfies(C);\nrelation term_holds(t: RingTerm); term_holds(T) :- terms(T), !unsatisfied(T);\nrelation use_flow(u: RingUse, f: RingFlow); relation use_reads(u: RingUse, t: RingTerm); relation use_writes(u: RingUse, e: Element);\nrelation use_context(u: RingUse); use_context(U) :- use_flow(U, F), flow_holds(F), use_reads(U, T), term_holds(T);\nrelation written_value(e: Element, v: ResultValue); written_value(E, V) :- use_writes(U, E), use_context(U), result(U, V); element_value(E, V) :- written_value(E, V);\n";
    for t in 0..k.ring_terms {
        writeln!(o,"const c{t}: Constraint; const e{t}: Element; terms(t{t}); term_constraint(t{t}, c{t}); constraint_element(c{t}, e{t}); value_ok(c{t}) :- element_value(e{t}, v0);").unwrap();
        for w in 0..k.ring_writers {
            for l in 0..k.ring_lanes {
                writeln!(o, "lane_flow(l{t}_{w}_{l}, f{t}_{w});").unwrap();
            }
            writeln!(o,"use_flow(u{t}_{w}, f{t}_{w}); use_reads(u{t}_{w}, t{}); use_writes(u{t}_{w}, e{t});",(t+1)%k.ring_terms).unwrap();
        }
    }
    o += "relation invalid(t: RingTerm); invalid(T) :- term_holds(T), term_constraint(T, C), !satisfies(C); obligation term_has_its_element: empty(invalid);\nrelation downstream(); downstream() :- term_holds(t0), w(); notice downstream_varies: varies(downstream);\n";
    writeln!(o,"verification checks {{ assumptions: [has_result, one_result{}]; obligations: [term_has_its_element]; notices: [downstream_varies]; }}",if s.overlaps {""} else {", one_selector"}).unwrap();
    Ok(o)
}

pub fn source(s: &Shape) -> Result<String, String> {
    validate(s, false)?;
    let mut g = Gates::new();
    let k = &s.knowledge;
    let mut assumptions = vec!["scalar_inputs"];
    if k.trees > 0 {
        forest(s, &mut g)?;
    }
    if k.chain_length > 0 {
        chain(s, &mut g);
    }
    if k.ring_terms > 0 {
        ring(s, &mut g);
        assumptions.extend(["has_result", "one_result"]);
        if !s.overlaps {
            assumptions.push("one_selector");
        }
    }
    Ok(g.finish(&assumptions))
}
fn ring(s: &Shape, g: &mut Gates) {
    let k = &s.knowledge;
    g.line(ring_inputs(s));
    for t in 0..k.ring_terms {
        g.name(&format!("term{t}"));
    }
    for t in 0..k.ring_terms {
        let mut values = vec![];
        let mut readiness = vec![];
        for w in 0..k.ring_writers {
            let selected = g.observe(&format!("selected{t}_{w}"), &format!("selector(f{t}_{w})"));
            let mut lanes = vec![];
            for l in 0..k.ring_lanes {
                let a = g.observe(&format!("fa{t}_{w}_{l}"), &format!("fa(l{t}_{w}_{l})"));
                let b = g.observe(&format!("fb{t}_{w}_{l}"), &format!("fb(l{t}_{w}_{l})"));
                let nb = g.not(&b);
                lanes.push(g.binary("both", &a, &nb));
            }
            let lane = g.fold("either", lanes);
            let flow = g.binary("both", &selected, &lane);
            let writer = g.gate(
                "both",
                &format!("writer{t}_{w}"),
                &flow,
                Some(&format!("term{}", (t + 1) % k.ring_terms)),
            );
            let raw = g.observe(&format!("result{t}_{w}"), &format!("result(u{t}_{w}, v0)"));
            values.push(g.binary("reads", &writer, &raw));
            readiness.push(g.ready(&writer));
            g.audit(&writer);
        }
        // Reading a multiply-written slot waits for all possible writers. No
        // result value can make a term false while an applicability is unknown.
        let ready = g.fold("both", readiness);
        let value = g.fold("either", values);
        g.gate("reads", &format!("term{t}"), &ready, Some(&value));
        g.audit(&format!("term{t}"));
    }
    let w = g.observe("raw_w", "w()");
    g.gate("both", "downstream", "term0", Some(&w));
    g.audit("downstream");
}
fn chain(s: &Shape, g: &mut Gates) {
    let k = &s.knowledge;
    g.line("input chain_start();");
    let seed = g.observe("chain_seed", "chain_start()");
    for i in 0..k.chain_length {
        g.name(&format!("chain{i}"));
    }
    for i in 0..k.chain_length {
        let before = if i > 0 {
            format!("chain{}", i - 1)
        } else if k.self_dependent {
            format!("chain{}", k.chain_length - 1)
        } else {
            seed.clone()
        };
        let mut writers = vec![];
        for w in 0..k.writers_per_field {
            let n = g.gate(
                "both",
                &format!("chain_writer{i}_{w}"),
                &before,
                Some(&seed),
            );
            g.audit(&n);
            writers.push(n);
        }
        let value = g.fold("either", writers);
        g.gate("same", &format!("chain{i}"), &value, None);
        g.audit(&format!("chain{i}"));
    }
}
fn forest(s: &Shape, g: &mut Gates) -> Result<(), String> {
    let k = &s.knowledge;
    let nodes = s.tree()?;
    // The top selector chooses a tree; each internal node owns the next selector.
    // Coverage through still-possible leaves makes those selectors readable.
    g.line("const tree_selector: Field;");
    for t in 0..k.trees {
        g.line(format!(
            "const tree_value{t}: Value; candidate(tree_selector, tree_value{t});"
        ));
    }
    for v in 0..s.width {
        g.line(format!("const branch{v}: Value;"));
    }
    g.line("const payload: Value;");
    let mut leaves = vec![];
    for tree in 0..k.trees {
        for (i, node) in nodes.iter().enumerate() {
            let name = format!("path{tree}_{i}");
            g.name(&name);
            if node.level == s.depth {
                leaves.push((tree, i, name));
                g.line(format!(
                    "const leaf{tree}_{i}: Format; leaf(leaf{tree}_{i}, path{tree}_{i});"
                ));
            }
        }
    }
    let accept = g.name("accept_tree");
    g.constant(&accept, true);
    let mut fields = vec![];
    for tree in 0..k.trees {
        let raw = g.observe(
            &format!("raw_tree{tree}"),
            &format!("raw_value(tree_selector, tree_value{tree})"),
        );
        g.gate("reads", &format!("path{tree}_0"), &accept, Some(&raw));
        for (i, node) in nodes.iter().enumerate() {
            if node.level < s.depth {
                fields.push((tree, i, format!("select{tree}_{i}"), true));
                for f in 0..k.unlocked_fields {
                    fields.push((tree, i, format!("unlocked{tree}_{i}_{f}"), false));
                }
            } else {
                for f in 0..k.fields_per_leaf {
                    fields.push((tree, i, format!("field{tree}_{i}_{f}"), false));
                }
            }
        }
    }
    let mut validations = vec![];
    for (tree, owner, field, selector) in &fields {
        g.line(format!("const {field}: Field;"));
        let mut cover = vec![];
        let mut matching_leaves = vec![];
        for (lt, li, path) in &leaves {
            let mut ancestor = Some(*li);
            let mut owns = false;
            while let Some(a) = ancestor {
                if *tree == *lt && a == *owner {
                    owns = true;
                    break;
                }
                ancestor = nodes[a].parent;
            }
            if owns {
                matching_leaves.push(path.clone());
            }
            cover.push(if owns { "yes".into() } else { g.not(path) });
        }
        let coverage = g.fold("both", cover);
        let accepted = g.gate("same", &format!("accept_{field}"), &coverage, None);
        g.audit(&accepted);
        if *selector {
            for branch in 0..s.width {
                g.line(format!("candidate({field}, branch{branch});"));
                let raw = g.observe(
                    &format!("raw_{field}_{branch}"),
                    &format!("raw_value({field}, branch{branch})"),
                );
                let visible = g.binary("reads", &accepted, &raw);
                let guard = g.binary("both", &format!("path{tree}_{owner}"), &visible);
                let mut writers = vec![];
                for w in 0..k.writers_per_field {
                    writers.push(g.gate(
                        "same",
                        &format!("set{tree}_{owner}_{branch}_{w}"),
                        &guard,
                        None,
                    ));
                }
                let value = g.fold("either", writers);
                g.gate(
                    "same",
                    &format!("path{tree}_{}", owner * s.width + 1 + branch),
                    &value,
                    None,
                );
            }
        } else {
            g.line(format!("candidate({field}, payload);"));
            let raw = g.observe(
                &format!("raw_{field}"),
                &format!("raw_value({field}, payload)"),
            );
            let visible = g.gate("reads", &format!("present_{field}"), &accepted, Some(&raw));
            g.audit(&visible);
            // Alternate required/absent checks. Validation never feeds path terms.
            let failure = if owner % 2 == 0 {
                visible
            } else {
                g.not(&visible)
            };
            let matched = g.fold("either", matching_leaves);
            validations.push(g.binary("both", &matched, &failure));
        }
    }
    let paths = g.fold("either", leaves.iter().map(|(_, _, p)| p.clone()).collect());
    let invalid = g.fold("either", validations);
    let valid = g.not(&invalid);
    g.gate("same", "path_matches", &paths, None);
    g.audit("path_matches");
    g.gate("same", "invalid_message", &invalid, None);
    g.audit("invalid_message");
    g.gate("both", "recognized", &paths, Some(&valid));
    g.audit("recognized");
    Ok(())
}
