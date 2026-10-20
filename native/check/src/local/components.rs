//! Owned SCC equations with explicit provider dependencies. Each component has
//! its own allowance; cones import results with checked variable/context transfer.
use super::owned::{Runtime, receipt};
use super::*;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComponentInput {
    /// Only this component's rules; dependency membership and projected W are
    /// retained, but provider implementation/evidence is not a downstream input.
    pub local: LocalInput,
    pub key: ComponentKey,
    pub providers: BTreeSet<ComponentKey>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComponentGraph {
    pub inputs: BTreeMap<ComponentKey, Arc<ComponentInput>>,
    pub order: Vec<ComponentKey>,
}
impl ComponentGraph {
    pub fn project(input: &LocalInput) -> Result<Self> {
        validate_local_constraints(&input.constraints)?;
        let mut owners = BTreeMap::new();
        for key in input.components.keys() {
            for atom in key.0.iter() {
                if !input.facts.contains(atom) || owners.insert(atom.clone(), key.clone()).is_some()
                {
                    return Err(CheckError::Internal("invalid component ownership"));
                }
            }
        }
        let mut rules: BTreeMap<ComponentKey, Vec<(&InstanceKey, &GroundInstance)>> =
            BTreeMap::new();
        let mut edges: BTreeMap<ComponentKey, BTreeSet<ComponentKey>> = input
            .components
            .keys()
            .map(|k| (k.clone(), BTreeSet::new()))
            .collect();
        for (key, rule) in &input.rules {
            let owner = owners
                .get(&rule.head.atom)
                .ok_or(CheckError::Internal("missing rule component"))?;
            rules.entry(owner.clone()).or_default().push((key, rule));
            for (_, premise) in &rule.body {
                if !input.facts.contains(&premise.atom) {
                    return Err(CheckError::Internal(
                        "local premise outside dependency cone",
                    ));
                }
                if let Some(provider) = owners.get(&premise.atom) {
                    if provider != owner {
                        edges.get_mut(owner).unwrap().insert(provider.clone());
                    }
                } else if input.possible.contains(&premise.atom)
                    || input.inputs.contains(&premise.atom)
                {
                    return Err(CheckError::Internal("missing possible premise provider"));
                }
            }
        }
        // Iterative, deterministic topological traversal; no recursion on long chains.
        let mut order = Vec::new();
        let mut done = BTreeSet::new();
        let mut active = BTreeSet::new();
        for root in edges.keys() {
            let mut pending = vec![(root.clone(), false)];
            while let Some((key, exit)) = pending.pop() {
                if exit {
                    active.remove(&key);
                    done.insert(key.clone());
                    order.push(key);
                    continue;
                }
                if done.contains(&key) {
                    continue;
                }
                if !active.insert(key.clone()) {
                    return Err(CheckError::Internal("component dependency cycle"));
                }
                pending.push((key.clone(), true));
                pending.extend(edges[&key].iter().rev().cloned().map(|k| (k, false)));
            }
        }
        let mut closures: BTreeMap<ComponentKey, BTreeSet<ComponentKey>> = BTreeMap::new();
        let mut projected = BTreeMap::new();
        for key in &order {
            let mut closure = BTreeSet::from([key.clone()]);
            for provider in &edges[key] {
                closure.extend(closures[provider].iter().cloned());
            }
            let mut facts: BTreeSet<_> = closure.iter().flat_map(|k| k.0.iter().cloned()).collect();
            for member in &closure {
                for (_, rule) in rules.get(member).into_iter().flatten() {
                    facts.extend(rule.body.iter().map(|(_, p)| p.atom.clone()));
                }
            }
            let sorts: BTreeSet<_> = facts
                .iter()
                .flat_map(|a| a.arguments.iter().map(|c| &c.sort))
                .collect();
            let relations: BTreeSet<_> = facts.iter().map(|a| &a.relation).collect();
            let local = LocalInput {
                completion_context: None,
                scope: LocalScope::Region(key.clone()),
                roots: key.0.iter().cloned().collect(),
                obligation: None,
                possible: input.possible.intersection(&facts).cloned().collect(),
                inputs: input.inputs.intersection(&facts).cloned().collect(),
                components: closure
                    .iter()
                    .map(|k| (k.clone(), input.components[k].clone()))
                    .collect(),
                rules: rules
                    .get(key)
                    .into_iter()
                    .flatten()
                    .map(|(k, r)| ((*k).clone(), (*r).clone()))
                    .collect(),
                original_dependencies: BTreeMap::new(),
                rewrites: BTreeSet::new(),
                domains: input
                    .domains
                    .iter()
                    .filter(|(s, _)| sorts.contains(s))
                    .map(|(s, d)| (s.clone(), d.clone()))
                    .collect(),
                constraints: input
                    .constraints
                    .iter()
                    .filter(|c| match c {
                        InputConstraint::AtMostOne { relation, .. } => relations.contains(relation),
                    })
                    .cloned()
                    .collect(),
                input_groups: input
                    .input_groups
                    .iter()
                    .map(|g| g.intersection(&facts).cloned().collect::<BTreeSet<_>>())
                    .filter(|g| !g.is_empty())
                    .collect(),
                facts,
                request_scope: input.request_scope.clone(),
                backend: input.backend.clone(),
                limits: input.limits.clone(),
                admission_limit: input.admission_limit,
            };
            projected.insert(
                key.clone(),
                Arc::new(ComponentInput {
                    local,
                    key: key.clone(),
                    providers: edges[key].clone(),
                }),
            );
            closures.insert(key.clone(), closure);
        }
        Ok(Self {
            inputs: projected,
            order,
        })
    }
}

/// Semantic projection only. Receipts are resolved independently by canonical
/// component identity, even if Salsa backdates this value after recomputation.
pub type ProviderValue = (Option<Arc<LocalEvaluation>>, Option<Inconclusive>);

fn failure_error(cause: Inconclusive) -> CheckError {
    CheckError::LimitExceeded {
        phase: cause.phase,
        resource: cause.resource,
    }
}
fn check_context(
    context: &ConditionContext,
    rt: &Runtime,
    value: &LocalEvaluation,
    budget: &mut Budget<'_>,
) -> Result<()> {
    let provider_w = context.import(&value.permitted, &rt.atoms, budget)?;
    if !context
        .apply(
            &context.permitted_worlds(),
            &provider_w,
            biodivine_lib_bdd::op_function::and_not,
            budget,
        )?
        .is_false()
    {
        return Err(CheckError::Internal(
            "provider constraint context does not cover consumer",
        ));
    }
    Ok(())
}

pub fn evaluate_owned_component(
    input: &ComponentInput,
    providers: &BTreeMap<ComponentKey, Arc<ProviderValue>>,
    operations: &OperationalLimits,
    metrics: &mut LocalMetrics,
) -> Result<OwnedEvaluation> {
    let limits = input.local.limits.with_operations(operations);
    let mut budget = Budget::tracked(&limits);
    let start = Instant::now();
    let export_before = metrics.export;
    let evaluated = (|| {
        if providers.keys().cloned().collect::<BTreeSet<_>>() != input.providers {
            return Err(CheckError::Internal("missing component provider"));
        }
        let mut required = BTreeSet::new();
        for rule in input.local.rules.values() {
            for (_, premise) in &rule.body {
                budget.tick("component dependency validation")?;
                if let Some(owner) = input
                    .local
                    .components
                    .keys()
                    .find(|k| k.0.contains(&premise.atom))
                {
                    if owner != &input.key {
                        required.insert(owner.clone());
                    }
                } else if input.local.possible.contains(&premise.atom)
                    || input.local.inputs.contains(&premise.atom)
                {
                    return Err(CheckError::Internal("missing possible premise provider"));
                }
            }
        }
        if required != input.providers {
            return Err(CheckError::Internal(
                "incomplete component dependency edges",
            ));
        }
        let rt = Runtime::new(&input.local, &mut budget, false)?;
        let context =
            ConditionContext::build_selected(&rt.program, Some(&rt.cone.facts), &mut budget)?;
        let own: BTreeSet<_> = input.key.0.iter().cloned().collect();
        let mut conditions = BTreeMap::new();
        let mut retained = context.permitted_worlds().node_count();
        let blocked = !input.local.components[&input.key].blocked_by.is_empty();
        // Blocked components publish no settled derived conditions. Their
        // consumers carry explicit blocking metadata; completion stays separate.
        if !blocked {
            for (key, provider) in providers {
                let Some(value) = &provider.0 else {
                    return Err(failure_error(
                        provider
                            .1
                            .ok_or(CheckError::Internal("missing provider failure"))?,
                    ));
                };
                check_context(&context, &rt, value, &mut budget)?;
                for (atom, value) in &value.conditions {
                    if !key.0.contains(atom) || !input.local.facts.contains(atom) {
                        return Err(CheckError::Internal(
                            "provider fact outside dependency closure",
                        ));
                    }
                    let value = context.import(value, &rt.atoms, &mut budget)?;
                    retained =
                        crate::symbolic::retain(retained, 0, value.node_count(), &mut budget)?;
                    conditions.insert(rt.atoms[atom].clone(), value);
                }
            }
            for key in own.intersection(&input.local.inputs) {
                let value = context.input_with_budget(&rt.atoms[key], &mut budget)?;
                retained = crate::symbolic::retain(retained, 0, value.node_count(), &mut budget)?;
                conditions.insert(rt.atoms[key].clone(), value);
            }
            loop {
                let mut changed = false;
                for rule in &rt.program.rules {
                    budget.tick("component evaluation")?;
                    if !own.contains(
                        &AtomKey::from_atom(&rt.keys, &rule.head.atom).map_err(CheckError::Keys)?,
                    ) {
                        return Err(CheckError::Internal("foreign component equation"));
                    }
                    let old = conditions
                        .get(&rule.head.atom)
                        .cloned()
                        .unwrap_or_else(|| context.false_condition());
                    if old.is_true() {
                        continue;
                    }
                    let mut body = context.true_condition();
                    for literal in &rule.body {
                        budget.tick("component evaluation")?;
                        if !rt.cone.facts.contains(&literal.term.atom) {
                            return Err(CheckError::Internal(
                                "local premise outside dependency cone",
                            ));
                        }
                        let mut premise = conditions
                            .get(&literal.term.atom)
                            .cloned()
                            .unwrap_or_else(|| context.false_condition());
                        if literal.polarity == Polarity::Negative {
                            let key = AtomKey::from_atom(&rt.keys, &literal.term.atom)
                                .map_err(CheckError::Keys)?;
                            if own.contains(&key) {
                                return Err(CheckError::Internal(
                                    "unblocked negative component cycle",
                                ));
                            }
                            premise = context.complement(&premise, &mut budget)?;
                        }
                        body = context.apply(
                            &body,
                            &premise,
                            biodivine_lib_bdd::op_function::and,
                            &mut budget,
                        )?;
                        if body.is_false() {
                            break;
                        }
                    }
                    if context
                        .apply(
                            &body,
                            &old,
                            biodivine_lib_bdd::op_function::and_not,
                            &mut budget,
                        )?
                        .is_false()
                    {
                        continue;
                    }
                    let next = context.apply(
                        &old,
                        &body,
                        biodivine_lib_bdd::op_function::or,
                        &mut budget,
                    )?;
                    let previous = conditions
                        .get(&rule.head.atom)
                        .map_or(0, Condition::node_count);
                    retained = crate::symbolic::retain(
                        retained,
                        previous,
                        next.node_count(),
                        &mut budget,
                    )?;
                    conditions.insert(rule.head.atom.clone(), next);
                    changed = true;
                }
                if !input.local.components[&input.key].recursive || !changed {
                    break;
                }
            }
        }
        // Publish only this SCC, not the transitive provider conditions.
        conditions.retain(|a, _| input.key.0.iter().any(|k| rt.atoms[k] == *a));
        let meaning = SymbolicMeaning {
            program: &rt.program,
            context,
            conditions,
            inconclusive: BTreeMap::new(),
            metrics: SymbolicMetrics {
                elapsed: Duration::ZERO,
                work: budget.used(),
                retained_condition_nodes: retained,
            },
        };
        let start = Instant::now();
        let value = rt.export_evaluation(&meaning, &mut budget);
        metrics.export += start.elapsed();
        value
    })();
    metrics.evaluation += start
        .elapsed()
        .saturating_sub(metrics.export - export_before);
    let (value, failure) = match evaluated {
        Ok(v) => (Some(Arc::new(v)), None),
        Err(e) => {
            budget.failure(&e);
            (None, Some(Inconclusive::from_error(e)?))
        }
    };
    Ok(OwnedEvaluation {
        value,
        failure,
        receipt: WorkReceipt {
            allowance: input.local.limits.clone(),
            own: budget.snapshot(),
            dependencies: input
                .providers
                .iter()
                .cloned()
                .map(QueryKey::ComponentEvaluation)
                .collect(),
        },
    })
}

pub fn assemble_owned_components(
    input: &LocalInput,
    values: &BTreeMap<ComponentKey, Arc<ProviderValue>>,
    operations: &OperationalLimits,
    metrics: &mut LocalMetrics,
) -> Result<OwnedEvaluation> {
    let limits = input.limits.with_operations(operations);
    let mut budget = Budget::tracked(&limits);
    let start = Instant::now();
    let export_before = metrics.export;
    let evaluated = (|| {
        if values.keys().ne(input.components.keys()) {
            return Err(CheckError::Internal("missing cone component"));
        }
        let projected = input.for_component_assembly();
        let rt = Runtime::new(&projected, &mut budget, false)?;
        let context =
            ConditionContext::build_selected(&rt.program, Some(&rt.cone.facts), &mut budget)?;
        let mut conditions = BTreeMap::new();
        let mut incomplete = BTreeMap::new();
        let mut retained = context.permitted_worlds().node_count();
        for (key, provider) in values {
            if let Some(cause) = provider.1 {
                incomplete.insert(key.clone(), cause);
            }
            if let Some(value) = &provider.0 {
                check_context(&context, &rt, value, &mut budget)?;
                for (atom, c) in &value.conditions {
                    if !key.0.contains(atom) {
                        return Err(CheckError::Internal("foreign assembled component fact"));
                    }
                    let c = context.import(c, &rt.atoms, &mut budget)?;
                    retained = crate::symbolic::retain(retained, 0, c.node_count(), &mut budget)?;
                    conditions.insert(rt.atoms[atom].clone(), c);
                }
            }
        }
        let meaning = SymbolicMeaning {
            program: &rt.program,
            context,
            conditions,
            inconclusive: BTreeMap::new(),
            metrics: SymbolicMetrics {
                elapsed: Duration::ZERO,
                work: budget.used(),
                retained_condition_nodes: retained,
            },
        };
        let start = Instant::now();
        let exported = rt.export_evaluation(&meaning, &mut budget);
        metrics.export += start.elapsed();
        let mut exported = exported?;
        exported.incomplete = incomplete;
        Ok(exported)
    })();
    metrics.evaluation += start
        .elapsed()
        .saturating_sub(metrics.export - export_before);
    let (value, failure) = match evaluated {
        Ok(v) => (Some(Arc::new(v)), None),
        Err(e) => {
            budget.failure(&e);
            (None, Some(Inconclusive::from_error(e)?))
        }
    };
    let mut own = receipt(input, &budget, false);
    own.dependencies
        .extend(values.keys().cloned().map(QueryKey::ComponentEvaluation));
    Ok(OwnedEvaluation {
        value,
        failure,
        receipt: own,
    })
}

/// Fresh graph oracle for the new accounting contract; no retained state.
pub fn evaluate_fresh_components(
    input: &LocalInput,
    graph: &ComponentGraph,
    operations: &OperationalLimits,
    metrics: &mut LocalMetrics,
) -> Result<(OwnedEvaluation, WorkReceipts)> {
    let mut values: BTreeMap<ComponentKey, Arc<ProviderValue>> = BTreeMap::new();
    let mut receipts = WorkReceipts::default();
    for key in &graph.order {
        let query = &graph.inputs[key];
        let providers = query
            .providers
            .iter()
            .map(|k| (k.clone(), values[k].clone()))
            .collect();
        let result = evaluate_owned_component(query, &providers, operations, metrics)?;
        receipts
            .record(QueryKey::ComponentEvaluation(key.clone()), result.receipt)
            .map_err(CheckError::Receipts)?;
        values.insert(key.clone(), Arc::new((result.value, result.failure)));
    }
    Ok((
        assemble_owned_components(input, &values, operations, metrics)?,
        receipts,
    ))
}

#[derive(Default)]
pub struct NoComponentMemo;
impl LocalMemoStore for NoComponentMemo {
    fn execute(
        &mut self,
        input: &LocalInput,
        operations: &OperationalLimits,
        metrics: &mut LocalMetrics,
    ) -> Result<Arc<LocalMemo>> {
        let graph = ComponentGraph::project(input)?;
        let (evaluation, dependencies) =
            evaluate_fresh_components(input, &graph, operations, metrics)?;
        let answer = answer_owned_local(
            input,
            evaluation.value.as_deref(),
            evaluation.failure,
            operations,
            metrics,
        )?;
        Ok(Arc::new(LocalMemo {
            dependencies,
            evaluation: evaluation.value.as_deref().cloned(),
            answer: answer.value,
            failure: answer.failure.or(evaluation.failure),
            evaluation_receipt: evaluation.receipt,
            answer_receipt: answer.receipt,
        }))
    }
}
