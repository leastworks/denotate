//! Bounded streaming export of one verification's committed ground program.
//! No discovery or filesystem access: callers own atomic publication and metadata.
use crate::{NameKind, print::relation_names, spelling};
use denotate_check::{
    Cancellation, GroundAtom, GroundProgram, GroundRule, Polarity, SettledExpression,
};
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    io::{self, Write},
    time::{Duration, Instant},
};

#[derive(Clone, Debug)]
pub struct ExportLimits {
    pub max_work: usize,
    pub max_bytes: usize,
    pub timeout: Duration,
    pub cancellation: Cancellation,
}
impl Default for ExportLimits {
    fn default() -> Self {
        Self {
            max_work: 100_000_000,
            max_bytes: 1 << 30,
            timeout: Duration::from_secs(120),
            cancellation: Cancellation::default(),
        }
    }
}
pub struct Metadata<'a> {
    pub source_digest: &'a str,
    pub checker_commit: &'a str,
    pub round: usize,
    pub state: &'a str,
}
#[derive(Debug)]
pub struct ExportStats {
    pub bytes: usize,
    pub work: usize,
    pub helpers: usize,
    pub elapsed: Duration,
}
struct Output<'a, W> {
    writer: W,
    limits: &'a ExportLimits,
    start: Instant,
    work: usize,
    bytes: usize,
}
fn error(text: impl Into<String>) -> io::Error {
    io::Error::other(text.into())
}
impl<W: Write> Output<'_, W> {
    fn check(&self) -> io::Result<()> {
        self.limits
            .cancellation
            .check()
            .map_err(|e| error(e.to_string()))?;
        if self.start.elapsed() >= self.limits.timeout {
            return Err(error("committed export deadline reached"));
        }
        Ok(())
    }
    fn tick(&mut self) -> io::Result<()> {
        self.check()?;
        if self.work >= self.limits.max_work {
            return Err(error("committed export work limit reached"));
        }
        self.work += 1;
        Ok(())
    }
}
impl<W: Write> Write for Output<'_, W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.check()?;
        if bytes.len() > self.limits.max_bytes.saturating_sub(self.bytes) {
            return Err(error("committed export byte limit reached"));
        }
        let n = self.writer.write(bytes)?;
        self.bytes += n;
        Ok(n)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.check()?;
        self.writer.flush()
    }
}
fn namespace(ns: &Namespace) -> String {
    ns.segments()
        .iter()
        .map(|s| spelling(s, NameKind::Identifier))
        .collect::<Vec<_>>()
        .join("::")
}
fn qualified(c: &Corpus, id: impl Into<OccurrenceId>, name: &str) -> String {
    format!("{}::{name}", namespace(c.namespace(id).unwrap()))
}
struct Names {
    all: BTreeMap<OccurrenceId, String>,
    relations: BTreeMap<RelationId, String>,
    original: BTreeMap<RelationId, String>,
    inputs: BTreeMap<RelationId, String>,
    private: String,
}
impl Names {
    fn atom(&self, out: &mut impl Write, a: &GroundAtom, original: bool) -> io::Result<()> {
        let name = if original {
            self.original.get(&a.relation)
        } else {
            None
        }
        .unwrap_or(&self.all[&a.relation.into()]);
        write!(out, "{name}(")?;
        for (i, id) in a.arguments.iter().enumerate() {
            if i > 0 {
                write!(out, ", ")?;
            }
            write!(out, "{}", self.all[&(*id).into()])?;
        }
        write!(out, ")")
    }
    fn expression(&self, id: usize) -> String {
        format!("{}::$expr_{id}", self.private)
    }
}
// Intern compact nodes across every replacement. Pointer lookup avoids traversing
// shared subtrees again; structural interning also merges independently built DAGs.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Node<'a> {
    Constant(bool),
    Atom(&'a GroundAtom),
    Not(usize),
    All(Vec<usize>),
    Any(Vec<usize>),
}
#[derive(Default)]
struct Expressions<'a> {
    pointers: BTreeMap<usize, usize>,
    interned: BTreeMap<Node<'a>, usize>,
    nodes: Vec<Node<'a>>,
}
impl<'a> Expressions<'a> {
    fn id(&self, e: &SettledExpression<GroundAtom>) -> usize {
        self.pointers[&(e as *const _ as usize)]
    }
    fn add(
        &mut self,
        root: &'a SettledExpression<GroundAtom>,
        out: &mut Output<'_, impl Write>,
    ) -> io::Result<()> {
        let mut stack = vec![(root, false)];
        while let Some((e, ready)) = stack.pop() {
            out.tick()?;
            let pointer = e as *const _ as usize;
            if self.pointers.contains_key(&pointer) {
                continue;
            }
            if !ready {
                stack.push((e, true));
                match e {
                    SettledExpression::Not(child) => stack.push((child, false)),
                    SettledExpression::All(children) | SettledExpression::Any(children) => {
                        for child in children.iter().rev() {
                            out.tick()?;
                            stack.push((child, false));
                        }
                    }
                    _ => {}
                }
                continue;
            }
            let node = match e {
                SettledExpression::Constant(b) => Node::Constant(*b),
                SettledExpression::Atom(a) => Node::Atom(a),
                SettledExpression::Not(child) => Node::Not(self.id(child)),
                SettledExpression::All(children) => {
                    Node::All(children.iter().map(|c| self.id(c)).collect())
                }
                SettledExpression::Any(children) => {
                    Node::Any(children.iter().map(|c| self.id(c)).collect())
                }
            };
            let id = *self.interned.entry(node.clone()).or_insert_with(|| {
                let id = self.nodes.len();
                self.nodes.push(node);
                id
            });
            self.pointers.insert(pointer, id);
        }
        Ok(())
    }
}
fn open(out: &mut impl Write, c: &Corpus, id: impl Into<OccurrenceId>) -> io::Result<bool> {
    let ns = c.namespace(id).unwrap();
    if ns.is_global() {
        return Ok(false);
    }
    write!(out, "namespace {} {{ ", namespace(ns))?;
    Ok(true)
}
fn close(out: &mut impl Write, block: bool) -> io::Result<()> {
    writeln!(out, "{}", if block { " }" } else { "" })
}
fn parameters(out: &mut impl Write, r: &Relation, names: &Names) -> io::Result<()> {
    write!(out, "(")?;
    for (i, p) in r.parameters.iter().enumerate() {
        if i > 0 {
            write!(out, ", ")?;
        }
        write!(
            out,
            "{}: {}",
            spelling(&p.name, NameKind::Parameter),
            names.all[&p.sort.into()]
        )?;
    }
    write!(out, ")")
}
fn contract(
    out: &mut impl Write,
    c: &Corpus,
    requirement: &Requirement,
    names: &Names,
    original: bool,
) -> io::Result<()> {
    let relation = requirement.relation();
    let name = if original {
        names.original.get(&relation)
    } else {
        None
    }
    .unwrap_or(&names.all[&relation.into()]);
    let kind = match requirement.kind() {
        Cardinality::Empty => "empty",
        Cardinality::AtMostOne => "at_most_one",
        Cardinality::AtLeastOne => "at_least_one",
        Cardinality::ExactlyOne => "exactly_one",
    };
    write!(out, "{kind}({name}")?;
    if requirement.kind() != Cardinality::Empty {
        write!(out, ", group_by: (")?;
        for (i, col) in requirement.group_by().iter().enumerate() {
            if i > 0 {
                write!(out, ", ")?;
            }
            write!(
                out,
                "{}",
                spelling(
                    &c.relation(relation).unwrap().parameters[*col].name,
                    NameKind::Parameter
                )
            )?;
        }
        write!(out, ")")?;
    }
    write!(out, ")")
}
fn rule(
    out: &mut Output<'_, impl Write>,
    r: &GroundRule,
    names: &Names,
    expressions: &Expressions<'_>,
    original: bool,
) -> io::Result<()> {
    out.tick()?;
    names.atom(out, &r.head.atom, original)?;
    let mut separator = " :- ";
    for literal in &r.body {
        out.tick()?;
        write!(
            out,
            "{separator}{}",
            if literal.polarity == Polarity::Negative {
                "!"
            } else {
                ""
            }
        )?;
        names.atom(out, &literal.term.atom, original)?;
        separator = ", ";
    }
    for replacement in &r.replacements {
        out.tick()?;
        // Expressions denote the signed premise's truth, not its positive atom.
        write!(
            out,
            "{separator}{}()",
            names.expression(expressions.id(&replacement.expression))
        )?;
        separator = ", ";
    }
    writeln!(out, ";")
}

// Atom reachability matters: a relation-level cone can contain unrelated cycles
// at other tuples. Duplicating those would invent extra program-wide findings.
fn assumption_atoms<'a>(
    program: &'a GroundProgram,
    roots: &BTreeSet<RelationId>,
    out: &mut Output<'_, impl Write>,
) -> io::Result<BTreeSet<&'a GroundAtom>> {
    let mut cone = BTreeSet::new();
    if roots.is_empty() {
        return Ok(cone);
    }
    let mut producers = BTreeMap::<&GroundAtom, Vec<&GroundRule>>::new();
    for r in program.original_residual_rules() {
        out.tick()?;
        producers.entry(&r.head.atom).or_default().push(r);
    }
    let mut pending = Vec::new();
    for atom in program.atoms() {
        out.tick()?;
        if roots.contains(&atom.relation) {
            pending.push(atom);
        }
    }
    while let Some(atom) = pending.pop() {
        out.tick()?;
        if !cone.insert(atom) {
            continue;
        }
        for r in producers.get(atom).into_iter().flatten() {
            out.tick()?;
            for l in &r.body {
                out.tick()?;
                pending.push(&l.term.atom);
            }
        }
    }
    Ok(cone)
}

/// Writes a derived, self-contained source file. Load it in a fresh folder with
/// an empty `den.root`. Original source origins deliberately are not copied:
/// ground instances and helpers have new locations and diagnostic identities.
pub fn write_committed(
    writer: impl Write,
    c: &Corpus,
    program: &GroundProgram,
    verification: &VerificationDeclaration,
    metadata: &Metadata<'_>,
    limits: &ExportLimits,
) -> io::Result<ExportStats> {
    let mut out = Output {
        writer,
        limits,
        start: Instant::now(),
        work: 0,
        bytes: 0,
    };
    out.tick()?;
    let roots = verification
        .assumptions
        .iter()
        .map(|a| c.assumption(*a).unwrap().restriction.relation())
        .filter(|r| c.relation(*r).unwrap().role == RelationRole::Derived)
        .collect::<BTreeSet<_>>();
    let cone = assumption_atoms(program, &roots, &mut out)?;
    let mut original_relations = roots;
    original_relations.extend(cone.iter().map(|a| a.relation));
    let mut reserved = BTreeSet::new();
    for r in c.relations() {
        out.tick()?;
        reserved.insert(r.name.clone());
    }
    for s in c.sorts() {
        out.tick()?;
        reserved.insert(s.name.clone());
    }
    for k in c.constants() {
        out.tick()?;
        reserved.insert(k.name.clone());
    }
    for ns in c
        .relations()
        .map(|r| c.namespace(r.id).unwrap())
        .chain(c.sorts().map(|s| c.namespace(s.id).unwrap()))
        .chain(c.constants().map(|k| c.namespace(k.id).unwrap()))
    {
        out.tick()?;
        if let Some(first) = ns.segments().first() {
            reserved.insert(first.clone());
        }
    }
    let private = (0..)
        .map(|i| format!("denotate_resume_{i}"))
        .find(|n| !reserved.contains(n))
        .unwrap();
    let mut names = Names {
        all: BTreeMap::new(),
        relations: relation_names(c),
        original: BTreeMap::new(),
        inputs: BTreeMap::new(),
        private,
    };
    for s in c.sorts() {
        out.tick()?;
        names.all.insert(
            s.id.into(),
            qualified(c, s.id, &spelling(&s.name, NameKind::Identifier)),
        );
    }
    for k in c.constants() {
        out.tick()?;
        names.all.insert(
            k.id.into(),
            qualified(c, k.id, &spelling(&k.name, NameKind::Constant)),
        );
    }
    for (i, r) in c.relations().enumerate() {
        out.tick()?;
        names
            .all
            .insert(r.id.into(), qualified(c, r.id, &names.relations[&r.id]));
        if r.role == RelationRole::Input {
            names
                .inputs
                .insert(r.id, format!("{}::input_{i}", names.private));
        } else if original_relations.contains(&r.id) {
            names
                .original
                .insert(r.id, format!("{}::original_{i}", names.private));
        }
    }
    let mut expressions = Expressions::default();
    for r in program.residual_rules() {
        out.tick()?;
        for replacement in &r.replacements {
            expressions.add(&replacement.expression, &mut out)?;
        }
    }
    writeln!(
        out,
        "// Derived experimental program, not an authoritative verdict or original source."
    )?;
    writeln!(
        out,
        "// Locations and identities refer to this export; no original loc(...) origins."
    )?;
    writeln!(
        out,
        "// checkerCommit is the binary build base revision; local code changes may be present."
    )?;
    let selection = serde_json::json!({"sourceDigest": metadata.source_digest, "checkerCommit": metadata.checker_commit, "round": metadata.round, "state": metadata.state,
        "verification": qualified(c, verification.id, &spelling(&verification.name, NameKind::Identifier)),
        "assumptions": verification.assumptions.iter().map(|id| qualified(c, *id, &spelling(&c.assumption(*id).unwrap().name, NameKind::Identifier))).collect::<Vec<_>>(),
        "obligations": verification.obligations.iter().map(|id| qualified(c, *id, &spelling(&c.obligation(*id).unwrap().name, NameKind::Identifier))).collect::<Vec<_>>(),
        "notices": verification.notices.iter().map(|id| qualified(c, *id, &spelling(&c.notice(*id).unwrap().name, NameKind::Identifier))).collect::<Vec<_>>() });
    writeln!(out, "// {selection}")?;
    for s in c.sorts() {
        out.tick()?;
        let block = open(&mut out, c, s.id)?;
        write!(out, "sort {};", spelling(&s.name, NameKind::Identifier))?;
        close(&mut out, block)?;
    }
    for k in c.constants() {
        out.tick()?;
        let block = open(&mut out, c, k.id)?;
        write!(
            out,
            "const {}: {};",
            spelling(&k.name, NameKind::Constant),
            names.all[&k.sort.into()]
        )?;
        close(&mut out, block)?;
    }
    for s in c.sorts() {
        out.tick()?;
        write!(out, "domain {} = [", names.all[&s.id.into()])?;
        for (i, k) in program
            .domain(s.id)
            .ok_or_else(|| error("missing resolved domain"))?
            .iter()
            .enumerate()
        {
            out.tick()?;
            if i > 0 {
                write!(out, ", ")?;
            }
            write!(out, "{}", names.all[&(*k).into()])?;
        }
        writeln!(out, "];")?;
    }
    for r in c.relations() {
        out.tick()?;
        let block = open(&mut out, c, r.id)?;
        write!(
            out,
            "{} {}",
            if r.role == RelationRole::Input {
                "input"
            } else {
                "relation"
            },
            names.relations[&r.id]
        )?;
        parameters(&mut out, r, &names)?;
        if let Some(provider) = names.inputs.get(&r.id) {
            write!(out, " within {provider}")?;
        }
        write!(out, ";")?;
        close(&mut out, block)?;
    }
    writeln!(out, "namespace {} {{", names.private)?;
    for (id, name) in names.original.iter().chain(names.inputs.iter()) {
        out.tick()?;
        write!(out, "relation {}", name.rsplit("::").next().unwrap())?;
        parameters(&mut out, c.relation(*id).unwrap(), &names)?;
        writeln!(out, ";")?;
    }
    for id in 0..expressions.nodes.len() {
        out.tick()?;
        writeln!(out, "relation $expr_{id}();")?;
    }
    writeln!(out, "}}")?;
    for a in program.input_atoms() {
        out.tick()?;
        write!(out, "{}(", names.inputs[&a.relation])?;
        for (i, k) in a.arguments.iter().enumerate() {
            out.tick()?;
            if i > 0 {
                write!(out, ", ")?;
            }
            write!(out, "{}", names.all[&(*k).into()])?;
        }
        writeln!(out, ");")?;
    }
    for a in program.fixed_true_atoms() {
        out.tick()?;
        names.atom(&mut out, a, false)?;
        writeln!(out, ";")?;
        if cone.contains(a) && names.original.contains_key(&a.relation) {
            names.atom(&mut out, a, true)?;
            writeln!(out, ";")?;
        }
    }
    for r in program.original_residual_rules() {
        out.tick()?;
        if cone.contains(&r.head.atom) && names.original.contains_key(&r.head.atom.relation) {
            if !r.replacements.is_empty() {
                return Err(error(
                    "original assumption cone contains an admission replacement",
                ));
            }
            rule(&mut out, r, &names, &expressions, true)?;
        }
    }
    for (id, node) in expressions.nodes.iter().enumerate() {
        out.tick()?;
        let head = names.expression(id);
        match node {
            Node::Constant(false) => {}
            Node::Constant(true) => writeln!(out, "{head}();")?,
            Node::Atom(atom) => {
                write!(out, "{head}() :- ")?;
                names.atom(&mut out, atom, false)?;
                writeln!(out, ";")?;
            }
            Node::Not(child) => writeln!(out, "{head}() :- !{}();", names.expression(*child))?,
            Node::All(children) => {
                write!(out, "{head}()")?;
                for (i, child) in children.iter().enumerate() {
                    out.tick()?;
                    write!(
                        out,
                        "{}{}()",
                        if i == 0 { " :- " } else { ", " },
                        names.expression(*child)
                    )?;
                }
                writeln!(out, ";")?;
            }
            Node::Any(children) => {
                for child in children {
                    out.tick()?;
                    writeln!(out, "{head}() :- {}();", names.expression(*child))?;
                }
            }
        }
    }
    for r in program.residual_rules() {
        rule(&mut out, r, &names, &expressions, false)?;
    }
    for id in &verification.assumptions {
        out.tick()?;
        let a = c.assumption(*id).unwrap();
        let block = open(&mut out, c, *id)?;
        write!(
            out,
            "assumption {}: ",
            spelling(&a.name, NameKind::Identifier)
        )?;
        contract(&mut out, c, &a.restriction, &names, true)?;
        write!(out, ";")?;
        close(&mut out, block)?;
    }
    for id in &verification.obligations {
        out.tick()?;
        let o = c.obligation(*id).unwrap();
        let block = open(&mut out, c, *id)?;
        write!(
            out,
            "obligation {}: ",
            spelling(&o.name, NameKind::Identifier)
        )?;
        contract(&mut out, c, &o.requirement, &names, false)?;
        write!(
            out,
            " message {};",
            serde_json::to_string(&o.message_template)?
        )?;
        close(&mut out, block)?;
    }
    for id in &verification.notices {
        out.tick()?;
        let n = c.notice(*id).unwrap();
        let block = open(&mut out, c, *id)?;
        write!(
            out,
            "notice {}: varies({}",
            spelling(&n.name, NameKind::Identifier),
            names.all[&n.condition.into()]
        )?;
        if let Some(within) = n.within {
            write!(out, ", within: {}", names.all[&within.into()])?;
        }
        write!(out, ") message {};", serde_json::to_string(&n.message)?)?;
        close(&mut out, block)?;
    }
    let block = open(&mut out, c, verification.id)?;
    write!(
        out,
        "verification {} {{ assumptions: [",
        spelling(&verification.name, NameKind::Identifier)
    )?;
    for (i, id) in verification.assumptions.iter().enumerate() {
        out.tick()?;
        if i > 0 {
            write!(out, ", ")?;
        }
        write!(
            out,
            "{}",
            qualified(
                c,
                *id,
                &spelling(&c.assumption(*id).unwrap().name, NameKind::Identifier)
            )
        )?;
    }
    write!(out, "]; obligations: [")?;
    for (i, id) in verification.obligations.iter().enumerate() {
        out.tick()?;
        if i > 0 {
            write!(out, ", ")?;
        }
        write!(
            out,
            "{}",
            qualified(
                c,
                *id,
                &spelling(&c.obligation(*id).unwrap().name, NameKind::Identifier)
            )
        )?;
    }
    write!(out, "]; notices: [")?;
    for (i, id) in verification.notices.iter().enumerate() {
        out.tick()?;
        if i > 0 {
            write!(out, ", ")?;
        }
        write!(
            out,
            "{}",
            qualified(
                c,
                *id,
                &spelling(&c.notice(*id).unwrap().name, NameKind::Identifier)
            )
        )?;
    }
    write!(out, "]; }}")?;
    close(&mut out, block)?;
    out.flush()?;
    out.check()?;
    Ok(ExportStats {
        bytes: out.bytes,
        work: out.work,
        helpers: expressions.nodes.len(),
        elapsed: out.start.elapsed(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    #[test]
    fn deeply_shared_expressions_are_traversed_and_interned_once() {
        let depth = 40;
        let mut root = Arc::new(SettledExpression::Constant(true));
        for _ in 0..depth {
            root = Arc::new(SettledExpression::Any(vec![root.clone(), root]));
        }
        let duplicate = Arc::new((*root).clone());
        let limits = ExportLimits::default();
        let mut output = Output {
            writer: Vec::new(),
            limits: &limits,
            start: Instant::now(),
            work: 0,
            bytes: 0,
        };
        let mut expressions = Expressions::default();
        expressions.add(&root, &mut output).unwrap();
        expressions.add(&duplicate, &mut output).unwrap();
        assert_eq!(expressions.id(&root), expressions.id(&duplicate));
        assert!(expressions.nodes.len() <= depth + 1);
        assert!(
            output.work < depth * 10,
            "sharing must prevent exponential traversal"
        );
    }
}
