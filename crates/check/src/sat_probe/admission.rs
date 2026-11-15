//! Snapshot-local component probes. The ordinary checker supplies exact settled
//! functions; this module only reads their BDDs and never performs BDD operations.
use super::*;
use biodivine_lib_bdd::BddPointer;

/// Borrowed diagnostic event, delivered synchronously before/after a query.
/// Component indices are local to the graph revision, not persistent identities.
pub struct SatProbeEvent<'a> {
    pub program: &'a GroundProgram,
    pub snapshot: u64,
    pub round: usize,
    pub component: ComponentId,
    /// One-based component position in this snapshot, matching admission progress.
    pub index: usize,
    pub report: Option<&'a SatProbeReport>,
}
pub type SatProbeObserver<'a> = dyn Fn(SatProbeEvent<'_>) + 'a;

pub(crate) struct Diagnosis<'a> {
    config: SatProbeLimits,
    limits: Limits,
    observer: &'a SatProbeObserver<'a>,
}
impl<'a> Diagnosis<'a> {
    pub fn new(
        config: SatProbeLimits,
        mut limits: Limits,
        observer: &'a SatProbeObserver<'a>,
    ) -> Self {
        limits.timeout = config.timeout;
        limits.progress = Default::default();
        limits.profile = Default::default();
        Self {
            config,
            limits,
            observer,
        }
    }

    pub fn run(
        &self,
        p: &GroundProgram,
        round: usize,
        components: &[(ComponentId, BTreeSet<GroundRuleId>)],
        summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
        ctx: &ConditionContext,
    ) -> Result<()> {
        // Reuse admission's provider-first schedule, without changing its order
        // or charging its budget. Each snapshot gets fresh diagnostic queries.
        for (component, rules) in components {
            self.limits.cancellation.check()?;
            if p.component(*component).is_none_or(|c| c.cycle.is_none()) {
                continue;
            }
            let emit = |report| {
                (self.observer)(SatProbeEvent {
                    program: p,
                    snapshot: p.graph_revision,
                    round,
                    component: *component,
                    index: component.index + 1,
                    report,
                })
            };
            emit(None);
            let report = probe_built(*component, &self.config, &self.limits, true, &|b| {
                compact_cone(p, *component, rules, summaries, ctx, b)
            })?;
            emit(Some(&report));
        }
        Ok(())
    }
}

fn compact_cone(
    p: &GroundProgram,
    component: ComponentId,
    rules: &BTreeSet<GroundRuleId>,
    summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
    ctx: &ConditionContext,
    b: &mut Budget<'_>,
) -> Result<Cone> {
    let target = p
        .component(component)
        .ok_or(CheckError::InvalidRequest("unknown SAT probe component"))?;
    b.charge(target.atoms.len(), "SAT probe target")?;
    let mut c = Cone {
        atoms: target.atoms.clone(),
        rules: Vec::new(),
        fixed: vec![None; target.atoms.len()],
        input: vec![false; target.atoms.len()],
        target: vec![true; target.atoms.len()],
        duplicated: vec![true; target.atoms.len()],
        groups: Vec::new(),
        source_rules: rules.len(),
    };
    let ids = c
        .atoms
        .iter()
        .enumerate()
        .map(|(i, a)| (a.clone(), i))
        .collect::<BTreeMap<_, _>>();
    let domain = ctx.permitted_worlds();
    let mut conditions = vec![&domain];
    let mut bodies = Vec::new();
    for id in rules {
        b.tick("SAT probe target rule")?;
        let s = summaries
            .get(id)
            .ok_or(CheckError::Internal("missing SAT probe summary"))?;
        b.charge(s.settled.len(), "SAT probe settled premises")?;
        let settled = s
            .settled
            .iter()
            .map(|v| v.literal.term.occurrence)
            .collect::<BTreeSet<_>>();
        let mut body = Vec::new();
        for literal in &s.rule.body {
            b.tick("SAT probe boundary")?;
            if settled.contains(&literal.term.occurrence) {
                continue;
            }
            let Some(index) = ids.get(&literal.term.atom) else {
                return Err(CheckError::InvalidRequest("SAT probe upstream unresolved"));
            };
            body.push((*index, literal.polarity == Polarity::Positive));
        }
        // Includes settled premises AND already-installed replacement expressions.
        conditions.push(&s.condition);
        bodies.push(Rule {
            head: ids[&s.rule.head.atom],
            body,
        });
    }

    let mut variables = BTreeSet::new();
    for condition in &conditions {
        let bdd = condition.diagnostic_bdd();
        b.charge(bdd.size(), "SAT probe settled BDD nodes")?;
        for i in 2..bdd.size() {
            variables.insert(bdd.var_of(BddPointer::from_index(i)).to_index());
        }
    }
    let mut inputs = BTreeMap::new();
    for (atom, var) in ctx.diagnostic_inputs() {
        b.tick("SAT probe input identities")?;
        if variables.contains(&var.to_index()) {
            let index = c.node(None, true, b)?;
            c.atoms.push(atom.clone());
            inputs.insert(var.to_index(), index);
        }
    }
    let no = c.node(Some(false), false, b)?;
    let yes = c.node(Some(true), false, b)?;
    let mut interned = BTreeMap::new();
    let mut roots = Vec::new();
    for condition in conditions {
        let bdd = condition.diagnostic_bdd();
        b.charge(bdd.size(), "SAT probe settled BDD encoding")?;
        let mut nodes = vec![no, yes];
        for i in 2..bdd.size() {
            let ptr = BddPointer::from_index(i);
            let input = inputs[&bdd.var_of(ptr).to_index()];
            let lo = nodes[bdd.low_link_of(ptr).to_index()];
            let hi = nodes[bdd.high_link_of(ptr).to_index()];
            let node = match interned.get(&(input, lo, hi)) {
                Some(node) => *node,
                None => {
                    let node = c.node(None, false, b)?;
                    // Read-only Tseitin via two acyclic definitions. Keeping
                    // these definitions in the reduct and model-cover checks
                    // also preserves guards of disabled alternative producers.
                    c.push_rule(
                        Rule {
                            head: node,
                            body: vec![(input, false), (lo, true)],
                        },
                        b,
                    )?;
                    c.push_rule(
                        Rule {
                            head: node,
                            body: vec![(input, true), (hi, true)],
                        },
                        b,
                    )?;
                    interned.insert((input, lo, hi), node);
                    node
                }
            };
            nodes.push(node);
        }
        roots.push(nodes[bdd.root_pointer().to_index()]);
    }
    c.groups.push((Cardinality::AtLeastOne, vec![roots[0]]));
    for (mut rule, root) in bodies.into_iter().zip(roots.into_iter().skip(1)) {
        rule.body.push((root, true));
        c.push_rule(rule, b)?;
    }
    Ok(c)
}

impl Cone {
    fn node(&mut self, fixed: Option<bool>, input: bool, b: &mut Budget<'_>) -> Result<usize> {
        b.room(
            self.fixed.len(),
            b.limits.max_atoms,
            "SAT probe settled encoding",
            "atoms",
        )?;
        let id = self.fixed.len();
        self.fixed.push(fixed);
        self.input.push(input);
        self.target.push(false);
        self.duplicated.push(false);
        Ok(id)
    }
    fn push_rule(&mut self, rule: Rule, b: &mut Budget<'_>) -> Result<()> {
        b.room(
            self.rules.len(),
            b.limits.max_rules,
            "SAT probe settled encoding",
            "rules",
        )?;
        b.charge(1 + rule.body.len(), "SAT probe settled encoding")?;
        self.rules.push(rule);
        Ok(())
    }
}

#[cfg(test)]
mod tests;
