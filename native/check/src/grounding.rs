//! Relation-level positive SCC grounding. The fresh and retained drivers call
//! the same owned function, which uses the existing indexed sparse kernel.
use super::*;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GroundingKey(pub BTreeSet<RelationKey>);
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundingInput {
    pub key: GroundingKey,
    pub providers: BTreeSet<GroundingKey>,
    pub relations: BTreeMap<RelationKey, RelationSchema>,
    pub domains: BTreeMap<SortKey, BTreeSet<ConstantKey>>,
    pub rules: BTreeMap<RuleKey, RuleSchema>,
    pub plans: BTreeMap<RuleKey, Arc<OwnedJoinPlan>>,
    pub limits: DeterministicLimits,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundingValue {
    pub possible: Arc<BTreeSet<AtomKey>>,
    pub instances: Arc<BTreeMap<InstanceKey, GroundInstance>>,
}
pub type GroundingProvider = (Option<Arc<BTreeSet<AtomKey>>>, Option<Inconclusive>);
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundingResult {
    pub value: Option<Arc<GroundingValue>>,
    pub failure: Option<Inconclusive>,
    pub receipt: WorkReceipt,
}
impl GroundingResult {
    pub fn provider(&self) -> GroundingProvider {
        (
            self.value.as_ref().map(|v| v.possible.clone()),
            self.failure,
        )
    }
}
#[derive(Debug, Default, Clone, Copy)]
pub struct GroundingMetrics {
    pub reconstruction_ns: u64,
    pub closure_ns: u64,
    pub export_ns: u64,
}
fn nanos(t: Instant) -> u64 {
    t.elapsed().as_nanos().min(u64::MAX as u128) as u64
}
#[derive(Debug, Clone)]
pub struct GroundingGraph {
    pub inputs: BTreeMap<GroundingKey, Arc<GroundingInput>>,
    pub order: Vec<GroundingKey>,
}
impl GroundingGraph {
    pub(crate) fn project(
        corpus: &Corpus,
        keys: &SemanticKeys,
        domains: &Domains,
        budget: &mut Budget<'_>,
        plans: &mut dyn JoinPlanStore,
    ) -> Result<Self> {
        let relations = corpus
            .relations()
            .map(|r| {
                Ok((
                    keys.relation(r.id).map_err(CheckError::Keys)?.clone(),
                    keys.relation_schema(r).map_err(CheckError::Keys)?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        let rules = corpus
            .rules()
            .map(|r| {
                Ok((
                    keys.rule(r.id).map_err(CheckError::Keys)?.clone(),
                    keys.rule_schema(r).map_err(CheckError::Keys)?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        let mut edges: BTreeMap<_, BTreeSet<_>> = relations
            .keys()
            .map(|r| (r.clone(), BTreeSet::new()))
            .collect();
        for rule in rules.values() {
            budget.tick("grounding relation graph")?;
            for (negative, a) in &rule.body {
                budget.tick("grounding relation graph")?;
                if !negative {
                    edges
                        .get_mut(&rule.head.relation)
                        .unwrap()
                        .insert(a.relation.clone());
                }
            }
        }
        // Iterative Kosaraju, followed by a deterministic provider-first walk.
        let mut reverse: BTreeMap<_, BTreeSet<_>> = relations
            .keys()
            .map(|r| (r.clone(), BTreeSet::new()))
            .collect();
        for (r, deps) in &edges {
            for d in deps {
                reverse.get_mut(d).unwrap().insert(r.clone());
            }
        }
        let mut seen = BTreeSet::new();
        let mut finish = Vec::new();
        for root in edges.keys() {
            let mut stack = vec![(root.clone(), false)];
            while let Some((r, exit)) = stack.pop() {
                budget.tick("grounding relation graph")?;
                if exit {
                    finish.push(r);
                    continue;
                }
                if !seen.insert(r.clone()) {
                    continue;
                }
                stack.push((r.clone(), true));
                stack.extend(edges[&r].iter().rev().cloned().map(|r| (r, false)));
            }
        }
        seen.clear();
        let mut owners = BTreeMap::new();
        for root in finish.into_iter().rev() {
            if seen.contains(&root) {
                continue;
            }
            let mut members = BTreeSet::new();
            let mut stack = vec![root];
            while let Some(r) = stack.pop() {
                budget.tick("grounding relation graph")?;
                if !seen.insert(r.clone()) {
                    continue;
                }
                members.insert(r.clone());
                stack.extend(reverse[&r].iter().cloned());
            }
            let key = GroundingKey(members);
            for r in &key.0 {
                owners.insert(r.clone(), key.clone());
            }
        }
        let mut grouped: BTreeMap<GroundingKey, BTreeMap<RuleKey, RuleSchema>> = BTreeMap::new();
        for (key, rule) in rules {
            grouped
                .entry(owners[&rule.head.relation].clone())
                .or_default()
                .insert(key, rule);
        }
        let mut inputs = BTreeMap::new();
        for key in owners.values().cloned().collect::<BTreeSet<_>>() {
            budget.tick("grounding projection")?;
            let own_rules = grouped.remove(&key).unwrap_or_default();
            let providers = key
                .0
                .iter()
                .flat_map(|r| &edges[r])
                .map(|r| owners[r].clone())
                .filter(|p| p != &key)
                .collect();
            let mut needed = key.0.clone();
            for r in own_rules.values() {
                needed.extend(r.body.iter().map(|(_, a)| a.relation.clone()));
            }
            let selected: BTreeMap<_, _> = needed
                .into_iter()
                .map(|r| (r.clone(), relations[&r].clone()))
                .collect();
            let sorts = selected
                .values()
                .flat_map(|r| r.parameters.iter().map(|(_, s)| s.clone()))
                .collect::<BTreeSet<_>>();
            // Only input relations enumerate domains. Safe derived rules bind
            // every variable through positive providers; unrelated constants
            // must not invalidate every derived unit sharing a sort.
            let enumerated = key
                .0
                .iter()
                .filter(|r| relations[*r].input)
                .flat_map(|r| relations[r].parameters.iter().map(|(_, s)| s.clone()))
                .collect::<BTreeSet<_>>();
            let mut selected_domains: BTreeMap<SortKey, BTreeSet<ConstantKey>> =
                sorts.into_iter().map(|s| (s, BTreeSet::new())).collect();
            for (s, domain) in domains {
                let k = keys.sort(*s).map_err(CheckError::Keys)?;
                if enumerated.contains(k) {
                    budget.charge(domain.len() + 1, "grounding projection")?;
                    selected_domains.insert(
                        k.clone(),
                        domain
                            .iter()
                            .map(|c| keys.constant(*c).cloned().map_err(CheckError::Keys))
                            .collect::<Result<_>>()?,
                    );
                }
            }
            for rule in own_rules.values() {
                for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(|(_, a)| a)) {
                    for (_, t) in &atom.arguments {
                        budget.tick("grounding projection")?;
                        if let TermKey::Constant(c) = t {
                            selected_domains.get_mut(&c.sort).unwrap().insert(c.clone());
                        }
                    }
                }
            }
            let mut prepared_plans = BTreeMap::new();
            for (k, r) in &own_rules {
                // Same threshold in fresh and cached input projection. Plans are
                // immutable explicit inputs; no mutable plan store enters a query.
                let shape = JoinPlanSchema::from_schema(r);
                if shape.positives.len() < 4
                    || shape
                        .work_bound()
                        .is_none_or(|w| w > budget.limits.max_work)
                {
                    continue;
                }
                budget.check("grounding plan projection")?;
                let p = plans
                    .plan(k.clone(), r.clone(), budget.limits.max_work)?
                    .map_or_else(|| OwnedJoinPlan::compute(shape).map(Arc::new), Ok)?;
                prepared_plans.insert(k.clone(), p);
            }
            inputs.insert(
                key.clone(),
                Arc::new(GroundingInput {
                    key,
                    providers,
                    relations: selected,
                    domains: selected_domains,
                    rules: own_rules,
                    plans: prepared_plans,
                    limits: budget.limits.into(),
                }),
            );
        }
        let mut order = Vec::new();
        let mut done = BTreeSet::new();
        for key in inputs.keys() {
            let mut stack = vec![(key.clone(), false)];
            while let Some((key, exit)) = stack.pop() {
                budget.tick("grounding relation graph")?;
                if exit {
                    done.insert(key.clone());
                    order.push(key);
                    continue;
                }
                if done.contains(&key) {
                    continue;
                }
                stack.push((key.clone(), true));
                stack.extend(
                    inputs[&key]
                        .providers
                        .iter()
                        .rev()
                        .cloned()
                        .map(|k| (k, false)),
                );
            }
        }
        Ok(Self { inputs, order })
    }
}

struct InstalledPlans<'a>(&'a BTreeMap<RuleKey, Arc<OwnedJoinPlan>>);
impl JoinPlanStore for InstalledPlans<'_> {
    fn plan(
        &mut self,
        key: RuleKey,
        _: RuleSchema,
        _: usize,
    ) -> Result<Option<Arc<OwnedJoinPlan>>> {
        Ok(self.0.get(&key).cloned())
    }
}
/// No arena IDs or borrowed current snapshot enter this computation.
pub fn ground_owned_unit(
    input: &GroundingInput,
    providers: &BTreeMap<GroundingKey, Arc<GroundingProvider>>,
    operations: &OperationalLimits,
    metrics: &mut GroundingMetrics,
) -> Result<GroundingResult> {
    let limits = input.limits.with_operations(operations);
    let mut budget = Budget::tracked(&limits);
    let result = (|| {
        if providers.keys().cloned().collect::<BTreeSet<_>>() != input.providers {
            return Err(CheckError::Internal("missing grounding provider"));
        }
        let required = input
            .rules
            .values()
            .flat_map(|r| r.body.iter())
            .filter(|(negative, a)| !negative && !input.key.0.contains(&a.relation))
            .map(|(_, a)| a.relation.clone())
            .collect::<BTreeSet<_>>();
        if required
            .iter()
            .any(|r| input.providers.iter().filter(|p| p.0.contains(r)).count() != 1)
            || input
                .providers
                .iter()
                .any(|p| !p.0.is_disjoint(&input.key.0) || p.0.is_disjoint(&required))
        {
            return Err(CheckError::Internal("incomplete grounding provider edges"));
        }
        let start = Instant::now();
        let mut corpus = Corpus::new();
        let mut keys = SemanticKeys::default();
        let mut sorts = BTreeMap::new();
        let mut constants = BTreeMap::new();
        let mut relations = BTreeMap::new();
        let mut domains = Domains::new();
        let invalid = |_| CheckError::Internal("invalid owned grounding structure");
        let mut runtime_domains = input.domains.clone();
        for provider in providers.values() {
            if let Some(possible) = &provider.0 {
                for atom in possible
                    .iter()
                    .filter(|a| input.relations.contains_key(&a.relation))
                {
                    for c in &atom.arguments {
                        budget.tick("grounding provider domains")?;
                        runtime_domains
                            .get_mut(&c.sort)
                            .ok_or(CheckError::Internal("foreign grounding sort"))?
                            .insert(c.clone());
                    }
                }
            }
        }
        for (s, values) in &runtime_domains {
            budget.tick("grounding runtime")?;
            let id = corpus
                .declare_sort(format!("s{}", sorts.len()))
                .map_err(invalid)?;
            keys.bind_sort(&corpus, id, s.clone())
                .map_err(CheckError::Keys)?;
            sorts.insert(s.clone(), id);
            let mut values_ids = Vec::new();
            for v in values {
                budget.tick("grounding runtime")?;
                if &v.sort != s {
                    return Err(CheckError::Internal("grounding domain sort mismatch"));
                }
                let c = corpus
                    .declare_constant(format!("c{}", constants.len()), id)
                    .map_err(invalid)?;
                keys.bind_constant(&corpus, c, v.clone())
                    .map_err(CheckError::Keys)?;
                constants.insert(v.clone(), c);
                values_ids.push(c);
            }
            domains.insert(id, values_ids);
        }
        for (r, schema) in &input.relations {
            budget.charge(schema.parameters.len() + 1, "grounding runtime")?;
            let role = if schema.input && input.key.0.contains(r) {
                RelationRole::Input
            } else {
                RelationRole::Derived
            };
            let id = if matches!(r, RelationKey::Generated { .. }) {
                if !schema.parameters.is_empty() || schema.input {
                    return Err(CheckError::Internal("invalid generated grounding relation"));
                }
                corpus.declare_generated_relation()
            } else {
                corpus
                    .declare_relation(
                        format!("r{}", relations.len()),
                        role,
                        schema
                            .parameters
                            .iter()
                            .map(|(n, s)| Parameter::new(n.as_ref(), sorts[s])),
                    )
                    .map_err(invalid)?
            };
            keys.bind_relation(&corpus, id, r.clone())
                .map_err(CheckError::Keys)?;
            relations.insert(r.clone(), id);
        }
        for (key, schema) in &input.rules {
            if !input.key.0.contains(&schema.head.relation) {
                return Err(CheckError::Internal("foreign grounding rule"));
            }
            let mut bindings = Vec::new();
            let mut atom = |a: &AtomSchema| -> Result<Atom> {
                budget.charge(a.arguments.len() + 1, "grounding runtime")?;
                let terms = a.arguments.iter().map(|(_, t)| match t {
                    TermKey::Constant(c) => Term::Constant(constants[c]),
                    TermKey::Variable(v) => Term::Variable {
                        name: v.name.as_ref().into(),
                        sort: sorts[&v.sort],
                    },
                });
                let ir = corpus
                    .atom(relations[&a.relation], terms)
                    .map_err(invalid)?;
                bindings.push((ir.id(), a.occurrence.clone()));
                for ((k, _), t) in a.arguments.iter().zip(ir.arguments()) {
                    bindings.push((t.id(), k.clone()));
                }
                Ok(ir)
            };
            let head = atom(&schema.head)?;
            let body = schema
                .body
                .iter()
                .map(|(neg, a)| {
                    atom(a).map(|a| {
                        if *neg {
                            Literal::Negative(a)
                        } else {
                            Literal::Positive(a)
                        }
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let id = corpus.add_rule(head, body).map_err(invalid)?;
            keys.bind_rule(&corpus, id, key.clone())
                .map_err(CheckError::Keys)?;
            for (id, key) in bindings {
                keys.bind_occurrence(&corpus, id, key)
                    .map_err(CheckError::Keys)?;
            }
        }
        let mut external = Vec::new();
        for (key, provider) in providers {
            let Some(possible) = &provider.0 else {
                let cause = provider
                    .1
                    .ok_or(CheckError::Internal("missing grounding failure"))?;
                return Err(CheckError::LimitExceeded {
                    phase: cause.phase,
                    resource: cause.resource,
                });
            };
            for a in possible.iter() {
                budget.tick("grounding providers")?;
                if !key.0.contains(&a.relation) {
                    return Err(CheckError::Internal("foreign grounding tuple"));
                }
                // A relation SCC can export other relations unused by this unit.
                if let Some(r) = relations.get(&a.relation) {
                    external.push(GroundAtom::new(
                        *r,
                        a.arguments
                            .iter()
                            .map(|c| {
                                constants.get(c).copied().ok_or(CheckError::Internal(
                                    "grounding provider outside domain",
                                ))
                            })
                            .collect::<Result<Vec<_>>>()?,
                    ));
                }
            }
        }
        let mut p = GroundProgram::empty(&corpus, domains);
        metrics.reconstruction_ns += nanos(start);
        let start = Instant::now();
        sparse::populate_seeded(
            &corpus,
            &mut p,
            &mut budget,
            &keys,
            &mut InstalledPlans(&input.plans),
            &external,
        )?;
        metrics.closure_ns += nanos(start);
        let start = Instant::now();
        // Reuse the checked structural exporter, without signed-graph analysis.
        budget.charge(p.rules.len() + p.atoms.len(), "grounding export")?;
        let index = GroundKeyIndex::build(&corpus, &keys, &p).map_err(CheckError::Keys)?;
        let possible = p
            .atoms
            .iter()
            .map(|a| AtomKey::from_atom(&keys, a).map_err(CheckError::Keys))
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .filter(|a| input.key.0.contains(&a.relation))
            .collect();
        metrics.export_ns += nanos(start);
        Ok(Arc::new(GroundingValue {
            possible: Arc::new(possible),
            instances: Arc::new(index.content),
        }))
    })();
    let (value, failure) = match result {
        Ok(v) => (Some(v), None),
        Err(e) => {
            budget.failure(&e);
            (None, Some(Inconclusive::from_error(e)?))
        }
    };
    Ok(GroundingResult {
        value,
        failure,
        receipt: WorkReceipt {
            allowance: input.limits.clone(),
            own: budget.snapshot(),
            dependencies: input
                .providers
                .iter()
                .cloned()
                .map(QueryKey::Grounding)
                .collect(),
        },
    })
}
/// One graph result includes current receipts, independently of semantic cutoff.
pub trait GroundingStore {
    fn ground(
        &mut self,
        graph: &GroundingGraph,
        operations: &OperationalLimits,
    ) -> Result<BTreeMap<GroundingKey, Arc<GroundingResult>>>;
}
#[derive(Default)]
pub struct FreshGrounding;
impl GroundingStore for FreshGrounding {
    fn ground(
        &mut self,
        graph: &GroundingGraph,
        operations: &OperationalLimits,
    ) -> Result<BTreeMap<GroundingKey, Arc<GroundingResult>>> {
        let mut results: BTreeMap<GroundingKey, Arc<GroundingResult>> = BTreeMap::new();
        let started = Instant::now();
        for key in &graph.order {
            operations.cancellation.check()?;
            if started.elapsed() >= operations.timeout {
                return Err(CheckError::Deadline {
                    phase: "fresh grounding queries",
                });
            }
            let input = &graph.inputs[key];
            let providers = input
                .providers
                .iter()
                .map(|k| (k.clone(), Arc::new(results[k].provider())))
                .collect();
            results.insert(
                key.clone(),
                Arc::new(ground_owned_unit(
                    input,
                    &providers,
                    operations,
                    &mut GroundingMetrics::default(),
                )?),
            );
        }
        Ok(results)
    }
}
impl GroundProgram {
    pub(crate) fn prepare_grounding(
        corpus: &Corpus,
        keys: &SemanticKeys,
        domains: &Domains,
        constraints: &[InputAtMostOne],
        obligations: &BTreeSet<ObligationId>,
        budget: &mut Budget<'_>,
        plans: &mut dyn JoinPlanStore,
        store: &mut dyn GroundingStore,
        receipts: &mut WorkReceipts,
    ) -> Result<Self> {
        let start = Instant::now();
        let domains = validate_domains(corpus, domains, budget)?;
        let graph = GroundingGraph::project(corpus, keys, &domains, budget, plans)?;
        let projection = start.elapsed();
        let query_start = Instant::now();
        let operations = OperationalLimits::from(budget.limits);
        let results = store.ground(&graph, &operations)?;
        if results.keys().ne(graph.inputs.keys()) {
            return Err(CheckError::Internal("grounding graph result mismatch"));
        }
        let mut failure = None;
        for key in &graph.order {
            let result = results
                .get(key)
                .ok_or(CheckError::Internal("missing grounded unit"))?;
            receipts
                .record(QueryKey::Grounding(key.clone()), result.receipt.clone())
                .map_err(CheckError::Receipts)?;
            if failure.is_none() {
                failure = result.failure;
            }
        }
        if let Some(c) = failure {
            return Err(CheckError::LimitExceeded {
                phase: c.phase,
                resource: c.resource,
            });
        }
        let queries = query_start.elapsed();
        let assembly_start = Instant::now();
        let mut p = Self::empty(corpus, domains);
        // Cached relation units contain possible tuples/rules only. Selection and
        // permitted-world constraints are applied freshly after their assembly.
        p.obligations = obligations.clone();
        let relations = corpus
            .relations()
            .map(|r| Ok((keys.relation(r.id).map_err(CheckError::Keys)?.clone(), r.id)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let constants = corpus
            .constants()
            .map(|c| Ok((keys.constant(c.id).map_err(CheckError::Keys)?.clone(), c.id)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let rules = corpus
            .rules()
            .map(|r| Ok((keys.rule(r.id).map_err(CheckError::Keys)?.clone(), r)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let mut atoms = BTreeSet::new();
        let mut installed = BTreeMap::new();
        for result in results.values() {
            let value = result
                .value
                .as_ref()
                .ok_or(CheckError::Internal("missing grounded value"))?;
            for a in value.possible.iter() {
                budget.tick("grounding assembly")?;
                let atom = GroundAtom::new(
                    relations[&a.relation],
                    a.arguments.iter().map(|c| constants[c]),
                );
                budget.room(
                    atoms.len(),
                    budget.limits.max_atoms,
                    "grounding assembly",
                    "atoms",
                )?;
                if corpus.relation(atom.relation).unwrap().role == RelationRole::Input {
                    p.inputs.insert(atom.clone());
                }
                atoms.insert(atom);
            }
            for (key, value) in value.instances.iter() {
                budget.tick("grounding assembly")?;
                let source = rules
                    .get(&key.rule)
                    .ok_or(CheckError::Internal("stale grounding rule"))?;
                if keys.rule_schema(source).map_err(CheckError::Keys)? != *value.schema {
                    return Err(CheckError::Internal("stale grounding schema"));
                }
                let binding = key
                    .substitution
                    .iter()
                    .map(|(v, c)| (v.name.as_ref(), constants[c]))
                    .collect::<BTreeMap<_, _>>();
                budget.room(
                    installed.len(),
                    budget.limits.max_rules,
                    "grounding assembly",
                    "rules",
                )?;
                let head = ground_atom(&source.head, &binding, budget)?;
                let body = source
                    .body
                    .iter()
                    .map(|l| {
                        Ok(GroundLiteral {
                            polarity: if matches!(l, Literal::Negative(_)) {
                                Polarity::Negative
                            } else {
                                Polarity::Positive
                            },
                            term: ground_atom(l.atom(), &binding, budget)?,
                        })
                    })
                    .collect::<Result<_>>()?;
                installed.insert(
                    (source.id, binding.values().copied().collect::<Vec<_>>()),
                    GroundRule {
                        id: GroundRuleId {
                            preparation: p.preparation,
                            index: 0,
                        },
                        source: source.id,
                        head,
                        body,
                    },
                );
            }
        }
        p.atoms = atoms.into_iter().collect();
        p.atom_index = p
            .atoms
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, a)| (a, i))
            .collect();
        for (_, mut r) in installed {
            r.id.index = p.rules.len();
            p.rules.push(r);
        }
        p.build_groups(corpus, budget)?;
        p.build_input_groups(corpus, constraints, budget)?;
        p.metrics.grounding_projection = projection;
        p.metrics.grounding_queries = queries;
        p.metrics.grounding_assembly = assembly_start.elapsed();
        p.metrics.grounding = start.elapsed();
        let start = Instant::now();
        graph::analyze(&mut p, budget)?;
        p.metrics.admissibility = start.elapsed();
        budget.check("grounding assembly")?;
        Ok(p)
    }
}
