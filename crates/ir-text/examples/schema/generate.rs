//! Pure, deterministic synthetic lowering. No checker or IO dependencies.
use std::fmt::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Encoding {
    Ambiguous,
    Coverage,
    Negated,
    Assumed,
}
impl Encoding {
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "ambiguous" => Ok(Self::Ambiguous),
            "coverage" => Ok(Self::Coverage),
            "negated" => Ok(Self::Negated),
            "assumed" => Ok(Self::Assumed),
            _ => Err(format!("unknown encoding {s}")),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Topology {
    Independent,
    Coupled,
    Mixed,
    Layered,
}
impl Topology {
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "independent" => Ok(Self::Independent),
            "coupled" => Ok(Self::Coupled),
            "mixed" => Ok(Self::Mixed),
            "layered" => Ok(Self::Layered),
            _ => Err(format!("unknown topology {s}")),
        }
    }
}
#[derive(Clone, Debug)]
pub struct Shape {
    /// All message fields, including one selector per tree level.
    pub fields: usize,
    /// Payload fields read by leaf terms, in addition to the selectors.
    pub reads: usize,
    pub depth: usize,
    pub width: usize,
    pub encoding: Encoding,
    pub topology: Topology,
    pub overlaps: bool,
    pub coupling_percent: usize,
    pub shadowed: usize,
    pub wide_heads: usize,
    pub producers: usize,
    pub computed: usize,
    pub catalog: usize,
    pub catalog_layers: usize,
}
impl Default for Shape {
    fn default() -> Self {
        Self {
            fields: 6,
            reads: 2,
            depth: 1,
            width: 2,
            encoding: Encoding::Coverage,
            topology: Topology::Independent,
            overlaps: false,
            coupling_percent: 50,
            shadowed: 2,
            wide_heads: 0,
            producers: 0,
            computed: 1,
            catalog: 4,
            catalog_layers: 2,
        }
    }
}
impl Shape {
    pub fn validate(&self) -> Result<(), String> {
        if self.depth == 0 || self.width < 2 || self.reads == 0 {
            return Err("depth and reads must be positive; width must be at least two".into());
        }
        if self
            .depth
            .checked_add(self.reads)
            .is_none_or(|n| n > self.fields)
        {
            return Err(
                "fields must include depth selector fields and reads payload fields".into(),
            );
        }
        if (self.wide_heads == 0) != (self.producers == 0) {
            return Err(
                "wide-heads and producers must either both be zero or both positive".into(),
            );
        }
        if self.wide_heads > 0 && self.catalog == 0 {
            return Err("wide producers need a nonempty catalog".into());
        }
        if self.coupling_percent > 100 {
            return Err("coupling-percent must be 0..100".into());
        }
        self.tree()?;
        Ok(())
    }
    pub fn tree(&self) -> Result<Vec<Node>, String> {
        // Bound generator expansion independently of checker limits; never silently
        // truncate a requested tree. This is a source-size guard, not a check verdict.
        let mut count = 1usize;
        let mut level = 1usize;
        for _ in 0..self.depth {
            level = level
                .checked_mul(self.width)
                .ok_or("format tree overflow")?;
            count = count.checked_add(level).ok_or("format tree overflow")?;
            if count > 100_000 {
                return Err("format tree exceeds 100000 nodes; reduce depth/width".into());
            }
        }
        let mut nodes = vec![Node {
            parent: None,
            level: 0,
            branch: 0,
        }];
        let mut first = 0;
        let mut last = 1;
        for level in 1..=self.depth {
            for parent in first..last {
                for branch in 0..self.width {
                    nodes.push(Node {
                        parent: Some(parent),
                        level,
                        branch,
                    });
                }
            }
            first = last;
            last = nodes.len();
        }
        Ok(nodes)
    }
}
#[derive(Clone, Debug)]
pub struct Node {
    pub parent: Option<usize>,
    pub level: usize,
    pub branch: usize,
}

pub fn source(s: &Shape) -> Result<String, String> {
    s.validate()?;
    let nodes = s.tree()?;
    let leaves: Vec<_> = nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| n.level == s.depth)
        .map(|(i, _)| i)
        .collect();
    let mut out = String::from(
        "// Generated Shipping News benchmark; synthetic semantics, not a DSL runtime.\nsort Field;\nsort Value;\nsort Format;\nsort DeclarationKind;\nconst required, optional, absent: DeclarationKind;\nconst present: Value;\n",
    );
    for v in 0..s.width {
        writeln!(out, "const choice{v}: Value;").unwrap();
    }
    for f in 0..s.fields {
        writeln!(out, "const f{f}: Field;").unwrap();
    }
    for t in 0..nodes.len() {
        writeln!(out, "const format{t}: Format;").unwrap();
    }
    out += "relation field_candidates(field: Field, value: Value);\nrelation expectable(field: Field);\nrelation unguessed(field: Field);\ninput raw_value(field: Field, value: Value) within field_candidates;\nrelation accepted(field: Field);\nrelation visible(field: Field, value: Value);\nvisible(F, V) :- raw_value(F, V), accepted(F);\nrelation expected(field: Field);\nrelation declaration(format: Format, field: Field, kind: DeclarationKind);\nrelation matches(format: Format);\nrelation leaf(format: Format);\nrelation recognized();\nrecognized() :- leaf(T), matches(T);\nrelation may_lack(field: Field);\nrelation leaf_expects(format: Format, field: Field);\n";
    for f in 0..s.fields {
        if f < s.depth {
            for v in 0..s.width {
                writeln!(out, "field_candidates(f{f}, choice{v});").unwrap();
            }
        } else {
            writeln!(out, "field_candidates(f{f}, present);").unwrap();
        }
        if f >= s.depth && f < s.depth + s.reads {
            writeln!(out, "expectable(f{f});").unwrap();
        } else {
            // Optional root declarations allocate the source even for an absent raw value.
            writeln!(
                out,
                "declaration(format0, f{f}, optional);\nunguessed(f{f});"
            )
            .unwrap();
        }
    }
    out += "relation inherits(leaf: Format, ancestor: Format);\nleaf_expects(T, F) :- inherits(T, A), declaration(A, F, K);\n";
    for leaf in &leaves {
        writeln!(out, "leaf(format{leaf});").unwrap();
        let mut ancestor = Some(*leaf);
        while let Some(t) = ancestor {
            writeln!(out, "inherits(format{leaf}, format{t});").unwrap();
            ancestor = nodes[t].parent;
        }
    }
    for i in 0..s.reads {
        writeln!(
            out,
            "declaration(format{}, f{}, {});",
            owner(s, &nodes, &leaves, i),
            s.depth + i,
            if s.topology == Topology::Layered {
                "optional"
            } else if i % 3 == 2 {
                "absent"
            } else {
                "required"
            }
        )
        .unwrap();
    }
    out += "expected(F) :- declaration(T, F, K), matches(T);\nmay_lack(F) :- expectable(F), leaf(T), matches(T), !leaf_expects(T, F);\n";
    match s.encoding {
        Encoding::Assumed => {
            out += "input assumed_accepted(field: Field) within expectable;\naccepted(F) :- assumed_accepted(F);\naccepted(F) :- unguessed(F), expected(F);\nrelation inconsistent_acceptance();\ninconsistent_acceptance() :- assumed_accepted(F), !expected(F);\ninconsistent_acceptance() :- expectable(F), expected(F), !assumed_accepted(F);\nassumption consistent_acceptance: empty(inconsistent_acceptance);\nassumption recognized_message: at_least_one(recognized, group_by: ());\n";
        }
        _ => {
            out += "accepted(F) :- expected(F);\n";
            if s.encoding != Encoding::Ambiguous {
                out += "accepted(F) :- expectable(F), !may_lack(F);\n";
            }
        }
    }
    // Generate each authored term separately, but expose one generic observation relation.
    // Parent/selector constraints are shared; payload constraints supply the cycle.
    for (t, node) in nodes.iter().enumerate() {
        writeln!(out, "relation term{t}();\nrelation unsatisfied{t}();\nterm{t}() :- !unsatisfied{t}();\nmatches(format{t}) :- term{t}();").unwrap();
        if let Some(parent) = node.parent {
            writeln!(out, "unsatisfied{t}() :- !term{parent}();").unwrap();
            let branch = if s.overlaps && node.level == s.depth && node.branch == 1 {
                0
            } else {
                node.branch
            };
            writeln!(
                out,
                "unsatisfied{t}() :- !visible(f{}, choice{branch});",
                node.level - 1
            )
            .unwrap();
            if s.encoding == Encoding::Negated && node.branch > 0 && !s.overlaps {
                writeln!(out, "unsatisfied{t}() :- term{}();", t - 1).unwrap();
            }
        }
        if node.level == s.depth {
            let leaf_index = t - leaves[0];
            for i in 0..s.reads {
                if (i % (leaves.len() / s.width)) * s.width == leaf_index {
                    writeln!(
                        out,
                        "unsatisfied{t}() :- {}visible(f{}, present);",
                        if i % 3 == 2 { "" } else { "!" },
                        s.depth + i
                    )
                    .unwrap();
                    let couple = s.topology == Topology::Coupled
                        || (s.topology == Topology::Mixed && i % 2 == 0);
                    if couple && s.reads > 1 {
                        writeln!(
                            out,
                            "unsatisfied{t}() :- !visible(f{}, present);",
                            s.depth + (i + 1) % s.reads
                        )
                        .unwrap();
                    }
                }
            }
            // A sibling consumes an earlier parent's optional allocation. It has
            // no own required/absent test on that field, so this cross read can
            // change recognition rather than duplicate or contradict a local test.
            for i in 0..s.reads {
                if let Some(j) = cross_read(s, i) {
                    if leaves[(j % (leaves.len() / s.width)) * s.width] + 1 == t {
                        writeln!(
                            out,
                            "unsatisfied{t}() :- !visible(f{}, present);",
                            s.depth + j
                        )
                        .unwrap();
                    }
                }
            }
        }
    }
    // Duplicates add producers. The existing declaration is never overridden.
    for i in 0..s.shadowed {
        let f = s.depth + i % s.reads;
        let t = owner(s, &nodes, &leaves, i % s.reads);
        writeln!(out, "relation shadow{i}();\nshadow{i}() :- {}visible(f{f}, present);\nexpected(f{f}) :- term{t}(), shadow{i}();", if (i % s.reads) % 3 == 2 { "!" } else { "" }).unwrap();
    }
    let mut obligations = Vec::new();
    for (parent, _) in nodes.iter().enumerate().filter(|(_, n)| n.level < s.depth) {
        writeln!(out, "relation overlap{parent}();").unwrap();
        let children: Vec<_> = (parent * s.width + 1..=parent * s.width + s.width).collect();
        for (i, a) in children.iter().enumerate() {
            for b in &children[i + 1..] {
                writeln!(out, "overlap{parent}() :- term{a}(), term{b}();").unwrap();
            }
        }
        writeln!(
            out,
            "obligation no_overlapping_formats{parent}: empty(overlap{parent});"
        )
        .unwrap();
        obligations.push(format!("no_overlapping_formats{parent}"));
    }
    if s.catalog > 0 {
        out += "sort CatalogEntry;\nrelation catalog0(entry: CatalogEntry);\n";
        for i in 0..s.catalog {
            writeln!(out, "const entry{i}: CatalogEntry;\ncatalog0(entry{i});").unwrap();
        }
        for layer in 1..=s.catalog_layers {
            writeln!(
                out,
                "relation catalog{layer}(entry: CatalogEntry);\ncatalog{layer}(E) :- catalog{}(E);",
                layer - 1
            )
            .unwrap();
        }
        for h in 0..s.wide_heads {
            writeln!(out, "relation wide{h}();").unwrap();
            for i in 0..s.producers {
                // Distinct source producers even when their normalized bodies agree.
                writeln!(
                    out,
                    "wide{h}() :- visible(f{}, present), catalog{}(entry{});",
                    s.depth + i % s.reads,
                    s.catalog_layers,
                    i % s.catalog
                )
                .unwrap();
            }
            let owner = owner(s, &nodes, &leaves, h % s.reads);
            writeln!(
                out,
                "expected(f{}) :- term{owner}(), wide{h}();",
                s.depth + h % s.reads
            )
            .unwrap();
        }
    }
    if s.computed > 0 {
        out += "sort Element;\nrelation result_candidates(element: Element, value: Value);\ninput task_result(element: Element, value: Value) within result_candidates;\nrelation computed_value(element: Element, value: Value);\ncomputed_value(E, V) :- task_result(E, V);\n";
        for e in 0..s.computed {
            writeln!(
                out,
                "const computed{e}: Element;\nresult_candidates(computed{e}, present);"
            )
            .unwrap();
        }
    }
    out += "assumption one_value_per_field: at_most_one(raw_value, group_by: (field));\nverification checks {\n  assumptions: [one_value_per_field";
    if s.encoding == Encoding::Assumed {
        out += ", consistent_acceptance, recognized_message";
    }
    writeln!(out, " ];\n  obligations: [{}];\n}}", obligations.join(", ")).unwrap();
    Ok(out)
}

fn owner(s: &Shape, nodes: &[Node], leaves: &[usize], i: usize) -> usize {
    let leaf = leaves[(i % (leaves.len() / s.width)) * s.width];
    if s.topology == Topology::Layered {
        nodes[leaf].parent.unwrap()
    } else {
        leaf
    }
}
pub fn cross_read(s: &Shape, i: usize) -> Option<usize> {
    (s.topology == Topology::Layered && s.reads > 1 && i * 100 / s.reads < s.coupling_percent)
        .then_some((i + 1) % s.reads)
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Step {
    Classify(usize),
    Accept(usize),
}
/// Explicit prerequisites: all alternative expected producers are subordinate
/// to the same owner, so a nonmatching owner rules all of them out.
pub fn layout(s: &Shape) -> Result<Vec<(Step, Vec<Step>)>, String> {
    if s.topology != Topology::Layered {
        return Ok(vec![]);
    }
    let nodes = s.tree()?;
    let leaves: Vec<_> = nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| n.level == s.depth)
        .map(|(i, _)| i)
        .collect();
    let mut steps = Vec::new();
    for (t, n) in nodes.iter().enumerate().filter(|(_, n)| n.level < s.depth) {
        steps.push((
            Step::Classify(t),
            n.parent.into_iter().map(Step::Classify).collect(),
        ));
    }
    for i in 0..s.reads {
        steps.push((
            Step::Accept(i),
            vec![Step::Classify(owner(s, &nodes, &leaves, i))],
        ));
    }
    for t in &leaves {
        let mut deps = vec![Step::Classify(nodes[*t].parent.unwrap())];
        for i in 0..s.reads {
            if leaves[(i % (leaves.len() / s.width)) * s.width] == *t {
                deps.push(Step::Accept(i));
            }
            if let Some(j) = cross_read(s, i) {
                if leaves[(j % (leaves.len() / s.width)) * s.width] + 1 == *t {
                    deps.push(Step::Accept(j));
                }
            }
        }

        steps.push((Step::Classify(*t), deps));
    }
    check_layout(&steps)?;
    Ok(steps)
}
pub fn check_layout(steps: &[(Step, Vec<Step>)]) -> Result<(), String> {
    if !has_layout(steps) {
        return Err("no layout exists".into());
    }
    check_order(steps)
}
pub fn check_order(steps: &[(Step, Vec<Step>)]) -> Result<(), String> {
    let mut done = std::collections::BTreeSet::new();
    for (i, (step, deps)) in steps.iter().enumerate() {
        if let Some(d) = deps.iter().find(|d| !done.contains(*d)) {
            return Err(format!("step {i} {step:?} reads undecided {d:?}"));
        }
        done.insert(*step);
    }
    Ok(())
}
pub fn has_layout(steps: &[(Step, Vec<Step>)]) -> bool {
    let mut done = std::collections::BTreeSet::new();
    loop {
        let before = done.len();
        for (s, ds) in steps {
            if ds.iter().all(|d| done.contains(d)) {
                done.insert(*s);
            }
        }
        if done.len() == steps.len() {
            return true;
        }
        if before == done.len() {
            return false;
        }
    }
}
