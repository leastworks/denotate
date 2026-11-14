//! Owned query computation. A private canonical runtime is reconstructed solely
//! from this query's inputs; no source snapshot or current arena ID enters here.
use super::*;

pub(super) struct Runtime {
    pub(super) program: GroundProgram,
    pub(super) keys: SemanticKeys,
    pub(super) atoms: BTreeMap<AtomKey, GroundAtom>,
    pub(super) components: BTreeMap<ComponentId, ComponentKey>,
    pub(super) instances: BTreeMap<GroundRuleId, InstanceKey>,
    pub(super) cone: DependencyCone,
}
impl Runtime {
    pub(super) fn new(input: &LocalInput, budget: &mut Budget<'_>, graph: bool) -> Result<Self> {
        validate_local_constraints(&input.constraints)?;
        let mut all = input.facts.clone();
        if let Some(c) = &input.completion_context {
            all.extend(c.inputs.iter().cloned());
        }
        for rule in input
            .rules
            .values()
            .chain(input.original_dependencies.values())
        {
            all.insert(rule.head.atom.clone());
            all.extend(rule.body.iter().map(|(_, l)| l.atom.clone()));
            all.extend(
                rule.replacements
                    .iter()
                    .flat_map(|r| r.expression.atoms())
                    .cloned(),
            );
        }
        let mut corpus = Corpus::new();
        let mut keys = SemanticKeys::default();
        let mut sorts = BTreeMap::new();
        let mut constants = BTreeMap::new();
        let mut relations = BTreeMap::new();
        let build_error = |_| CheckError::Internal("invalid owned local structure");
        let constant_keys = all
            .iter()
            .flat_map(|a| a.arguments.iter().cloned())
            .collect::<BTreeSet<_>>();
        for k in &constant_keys {
            budget.tick("owned local reconstruction")?;
            if !sorts.contains_key(&k.sort) {
                let id = corpus
                    .declare_sort(format!("s{}", sorts.len()))
                    .map_err(build_error)?;
                keys.bind_sort(&corpus, id, k.sort.clone())
                    .map_err(CheckError::Keys)?;
                sorts.insert(k.sort.clone(), id);
            }
            let id = corpus
                .declare_constant(format!("c{}", constants.len()), sorts[&k.sort])
                .map_err(build_error)?;
            keys.bind_constant(&corpus, id, k.clone())
                .map_err(CheckError::Keys)?;
            constants.insert(k.clone(), id);
        }
        for a in &all {
            budget.tick("owned local reconstruction")?;
            if !relations.contains_key(&a.relation) {
                let id = corpus
                    .declare_relation(
                        format!("r{}", relations.len()),
                        RelationRole::Derived,
                        a.arguments
                            .iter()
                            .enumerate()
                            .map(|(i, c)| Parameter::new(format!("p{i}"), sorts[&c.sort])),
                    )
                    .map_err(build_error)?;
                keys.bind_relation(&corpus, id, a.relation.clone())
                    .map_err(CheckError::Keys)?;
                relations.insert(a.relation.clone(), id);
            }
        }
        let atoms: BTreeMap<_, _> = all
            .iter()
            .map(|a| {
                (
                    a.clone(),
                    GroundAtom::new(
                        relations[&a.relation],
                        a.arguments.iter().map(|c| constants[c]),
                    ),
                )
            })
            .collect();
        let mut domains = Domains::new();
        for (k, id) in &constants {
            domains.entry(sorts[&k.sort]).or_default().push(*id);
        }
        for d in domains.values_mut() {
            d.sort();
        }
        let mut program = GroundProgram::empty(&corpus, domains);
        program.inputs = input.inputs.iter().map(|k| atoms[k].clone()).collect();
        if let Some(c) = &input.completion_context {
            program
                .inputs
                .extend(c.inputs.iter().map(|k| atoms[k].clone()));
        }
        let order = input
            .input_order
            .iter()
            .map(|k| {
                atoms
                    .get(k)
                    .cloned()
                    .ok_or(CheckError::InvalidRequest("unknown ordered local input"))
            })
            .collect::<Result<Vec<_>>>()?;
        if order.len() != program.inputs.len()
            || order.iter().cloned().collect::<BTreeSet<_>>() != program.inputs
        {
            return Err(CheckError::InvalidRequest(
                "local input order does not match inputs",
            ));
        }
        program.input_order = Some(order);
        program.input_groups = input
            .completion_context
            .as_ref()
            .map_or(&input.input_groups, |c| &c.input_groups)
            .iter()
            .map(|g| g.iter().map(|k| atoms[k].clone()).collect())
            .collect();
        program.atoms = input
            .possible
            .iter()
            .map(|k| atoms[k].clone())
            .chain(program.inputs.iter().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        program.atom_index = program
            .atoms
            .iter()
            .enumerate()
            .map(|(i, a)| (a.clone(), i))
            .collect();
        program.rewrites.inconclusive = input.admission_limit;
        let mut instances = BTreeMap::new();
        let mut originals = BTreeMap::new();
        let mut original_occurrences = BTreeMap::new();
        for (key, rule) in &input.rules {
            budget.charge(1 + rule.body.len(), "owned local reconstruction")?;
            if !input.facts.contains(&rule.head.atom)
                || rule
                    .body
                    .iter()
                    .any(|(_, l)| !input.facts.contains(&l.atom))
            {
                return Err(CheckError::Internal(
                    "local premise outside dependency cone",
                ));
            }
            if rule
                .replacements
                .iter()
                .flat_map(|r| r.expression.atoms())
                .any(|a| !input.facts.contains(a))
            {
                return Err(CheckError::Internal(
                    "local replacement outside dependency cone",
                ));
            }
            let mut make = |r: &GroundInstance| -> Result<(
                RuleId,
                GroundOccurrence,
                Vec<GroundLiteral>,
                BTreeMap<OccurrenceKey, OccurrenceId>,
            )> {
                let mut occurrences = BTreeMap::new();
                let mut atom = |o: &KeyedGroundOccurrence| -> Result<(Atom, GroundOccurrence)> {
                    let a = &atoms[&o.atom];
                    let ir = corpus
                        .atom(a.relation, a.arguments.iter().copied().map(Term::Constant))
                        .map_err(build_error)?;
                    occurrences.insert(o.occurrence.clone(), ir.id());
                    let g = GroundOccurrence {
                        atom: a.clone(),
                        occurrence: ir.id(),
                        arguments: ir.arguments().iter().map(|a| a.id()).collect(),
                    };
                    Ok((ir, g))
                };
                let (head, ghead) = atom(&r.head)?;
                let mut body = Vec::new();
                let mut ground = Vec::new();
                for (neg, o) in &r.body {
                    let (ir, g) = atom(o)?;
                    body.push(if *neg {
                        Literal::Negative(ir)
                    } else {
                        Literal::Positive(ir)
                    });
                    ground.push(GroundLiteral {
                        polarity: if *neg {
                            Polarity::Negative
                        } else {
                            Polarity::Positive
                        },
                        term: g,
                    });
                }
                for replacement in &r.replacements {
                    let original = input
                        .original_dependencies
                        .get(key)
                        .and_then(|r| {
                            r.body
                                .iter()
                                .find(|(_, o)| o.occurrence == replacement.occurrence)
                        })
                        .ok_or(CheckError::Internal("missing replaced occurrence"))?;
                    atom(&original.1)?;
                }
                let source = corpus.add_rule(head, body).map_err(build_error)?;
                Ok((source, ghead, ground, occurrences))
            };
            let (source, head, body, occurrences) = make(rule)?;
            let id = GroundRuleId {
                preparation: program.preparation,
                index: program.rules.len(),
            };
            let replacements = rule
                .replacements
                .iter()
                .map(|r| {
                    Ok(SettledReplacement {
                        occurrence: occurrences[&r.occurrence],
                        expression: r.expression.map(&mut |a| Ok(atoms[a].clone()))?,
                    })
                })
                .collect::<Result<_>>()?;
            program.rules.push(GroundRule {
                replacements,
                id,
                source,
                head,
                body,
            });
            instances.insert(id, key.clone());
            if input
                .completion_context
                .as_ref()
                .is_some_and(|c| c.proofs.keys().any(|p| &p.candidate == key))
            {
                let original = input
                    .original_dependencies
                    .get(key)
                    .ok_or(CheckError::Internal("missing owned original rule"))?;
                let (_, head, body, occurrences) = make(original)?;
                originals.insert(
                    key.clone(),
                    GroundRule {
                        replacements: vec![],
                        id,
                        source,
                        head,
                        body,
                    },
                );
                original_occurrences.insert(key.clone(), occurrences);
            }
        }
        if graph {
            crate::graph::analyze(&mut program, budget)?;
        } else {
            // Verdicts only inspect root conditions and blocking status. They
            // need component identities for incomplete causes, no producer graph.
            for (key, c) in &input.components {
                let id = ComponentId {
                    preparation: program.preparation,
                    index: program.components.len(),
                };
                program.components.push(Component {
                    id,
                    atoms: key.0.iter().map(|a| atoms[a].clone()).collect(),
                    dependencies: BTreeSet::new(),
                    recursive: c.recursive,
                    blocked_by: BTreeSet::new(),
                    cycle: None,
                });
            }
        }
        let components: BTreeMap<_, _> = program
            .components
            .iter()
            .map(|c| {
                Ok((
                    c.id,
                    ComponentKey(
                        c.atoms
                            .iter()
                            .map(|a| AtomKey::from_atom(&keys, a).map_err(CheckError::Keys))
                            .collect::<Result<Vec<_>>>()?
                            .into(),
                    ),
                ))
            })
            .collect::<Result<_>>()?;
        let component_ids: BTreeMap<_, _> =
            components.iter().map(|(id, k)| (k.clone(), *id)).collect();
        for (key, expected) in &input.components {
            let id = component_ids
                .get(key)
                .ok_or(CheckError::Internal("owned component membership changed"))?;
            let c = &program.components[id.index];
            let blocked: BTreeSet<_> = c
                .blocked_by
                .iter()
                .map(|id| components[id].clone())
                .collect();
            if graph && (c.recursive != expected.recursive || blocked != expected.blocked_by) {
                return Err(CheckError::Internal("owned component dependencies changed"));
            }
        }
        if let Some(c) = &input.completion_context {
            let ctx = ConditionContext::build(&program, budget)?;
            for (key, (candidate, coverage)) in &c.proofs {
                let KeyedRewriteKind::Discharge(occurrence) = &key.kind else {
                    return Err(CheckError::Internal("unexpected owned proof kind"));
                };
                let original = originals[&key.candidate].clone();
                let occurrence = original_occurrences[&key.candidate][occurrence];
                program.install_local_discharge(
                    original,
                    occurrence,
                    ctx.import(candidate, &atoms, budget)?,
                    ctx.import(coverage, &atoms, budget)?,
                );
            }
        }
        let cone = DependencyCone {
            roots: input.roots.iter().map(|a| atoms[a].clone()).collect(),
            facts: input.facts.iter().map(|a| atoms[a].clone()).collect(),
            rules: instances.keys().copied().collect(),
            components: input.components.keys().map(|k| component_ids[k]).collect(),
            blocked_by: input
                .components
                .values()
                .flat_map(|c| c.blocked_by.iter().map(|k| component_ids[k]))
                .collect(),
        };
        Ok(Self {
            program,
            keys,
            atoms,
            components,
            instances,
            cone,
        })
    }
    fn component(&self, key: &ComponentKey) -> Result<&Component> {
        self.components
            .iter()
            .find_map(|(id, k)| (k == key).then(|| &self.program.components[id.index]))
            .ok_or(CheckError::Internal("missing owned region"))
    }
    pub(super) fn export_evaluation(
        &self,
        meaning: &SymbolicMeaning<'_>,
        budget: &mut Budget<'_>,
    ) -> Result<LocalEvaluation> {
        let permitted =
            meaning
                .context
                .export(&meaning.context.permitted_worlds(), &self.keys, budget)?;
        let mut retained = crate::symbolic::retain(
            meaning.metrics.retained_condition_nodes,
            0,
            permitted.node_count(),
            budget,
        )?;
        let mut conditions = BTreeMap::new();
        for (a, c) in &meaning.conditions {
            let value = meaning.context.export(c, &self.keys, budget)?;
            retained = crate::symbolic::retain(retained, 0, value.node_count(), budget)?;
            conditions.insert(
                AtomKey::from_atom(&self.keys, a).map_err(CheckError::Keys)?,
                value,
            );
        }
        Ok(LocalEvaluation {
            permitted,
            conditions,
            incomplete: meaning
                .inconclusive
                .iter()
                .map(|(id, c)| (self.components[id].clone(), *c))
                .collect(),
        })
    }
}
pub(super) fn receipt(input: &LocalInput, budget: &Budget<'_>, answer: bool) -> WorkReceipt {
    WorkReceipt {
        allowance: input.limits.clone(),
        own: budget.snapshot(),
        dependencies: if answer {
            BTreeSet::from([match &input.scope {
                LocalScope::Group(k) => QueryKey::ConeEvaluation(k.clone()),
                LocalScope::Region(k) => QueryKey::RegionEvaluation(k.clone()),
            }])
        } else {
            BTreeSet::from([match &input.scope {
                LocalScope::Group(k) => QueryKey::ConeDiscovery(k.clone()),
                LocalScope::Region(k) => QueryKey::RegionDiscovery(k.clone()),
            }])
        },
    }
}
pub fn evaluate_owned_local(
    input: &LocalInput,
    operations: &OperationalLimits,
    metrics: &mut LocalMetrics,
) -> Result<OwnedEvaluation> {
    let limits = input.limits.with_operations(operations);
    let mut budget = Budget::tracked(&limits);
    let start = Instant::now();
    let _stage = limits.progress.private_scope("local-symbolic-evaluation");
    let evaluated = (|| {
        let rt = Runtime::new(input, &mut budget, true)?;
        #[cfg(any(test, feature = "test-support"))]
        let meaning = if matches!(input.scope, LocalScope::Group(_)) {
            let mut measured = |id, elapsed| {
                let work = metrics
                    .scc_work
                    .entry(rt.components[&id].clone())
                    .or_default();
                work.cone_evaluations += 1;
                work.elapsed += elapsed;
            };
            rt.program.symbolic_selected_measured(
                &mut budget,
                true,
                Some(&rt.cone),
                &mut measured,
            )?
        } else {
            rt.program
                .symbolic_selected(&mut budget, true, Some(&rt.cone))?
        };
        #[cfg(not(any(test, feature = "test-support")))]
        let meaning = rt
            .program
            .symbolic_selected(&mut budget, true, Some(&rt.cone))?;
        metrics.evaluation += start.elapsed();
        let start = Instant::now();
        let value = rt.export_evaluation(&meaning, &mut budget);
        metrics.export += start.elapsed();
        value
    })();
    let (value, failure) = match evaluated {
        Ok(v) => (Some(v), None),
        Err(e) => {
            budget.failure(&e);
            (None, Some(Inconclusive::from_error(e)?))
        }
    };
    Ok(OwnedEvaluation {
        value: value.map(std::sync::Arc::new),
        failure,
        receipt: receipt(input, &budget, false),
    })
}
pub fn answer_owned_local(
    input: &LocalInput,
    value: Option<&LocalEvaluation>,
    failure: Option<Inconclusive>,
    operations: &OperationalLimits,
    metrics: &mut LocalMetrics,
) -> Result<OwnedAnswer> {
    let limits = input.limits.with_operations(operations);
    let mut budget = Budget::tracked(&limits);
    let start = Instant::now();
    let exports_before = metrics.export;
    let _stage = limits.progress.private_scope(match input.scope {
        LocalScope::Group(_) => "uniqueness",
        LocalScope::Region(_) => "no-meaning",
    });
    let computed = (|| -> Result<LocalAnswer> {
        let Some(value) = value else {
            let f = failure.ok_or(CheckError::Internal("missing owned evaluation failure"))?;
            return Err(CheckError::from(f));
        };
        let projected = input.for_answer();
        let rt = Runtime::new(
            &projected,
            &mut budget,
            matches!(input.scope, LocalScope::Region(_)),
        )?;
        let context =
            ConditionContext::build_selected(&rt.program, Some(&rt.cone.facts), &mut budget)?;
        let mut conditions = BTreeMap::new();
        let mut retained = context.permitted_worlds().node_count();
        for (key, c) in &value.conditions {
            let imported = context.import(c, &rt.atoms, &mut budget)?;
            retained = crate::symbolic::retain(retained, 0, imported.node_count(), &mut budget)?;
            conditions.insert(rt.atoms[key].clone(), imported);
        }
        let mut meaning = SymbolicMeaning {
            program: &rt.program,
            context,
            conditions,
            inconclusive: BTreeMap::new(),
            metrics: SymbolicMetrics {
                elapsed: Duration::ZERO,
                work: 0,
                retained_condition_nodes: retained,
            },
        };
        for (key, c) in &value.incomplete {
            meaning.inconclusive.insert(rt.component(key)?.id, *c);
        }
        match &input.scope {
            LocalScope::Group(_) => {
                // The property algorithm needs only tuple membership, never its
                // source obligation ID; compute directly in canonical key order.
                budget.tick("property checks")?;
                if let Some(c) = meaning.inconclusive.values().next() {
                    return Err(CheckError::from(*c));
                }
                if !rt.cone.blocked_by.is_empty() {
                    return Ok(LocalAnswer::Group(match input.admission_limit {
                        Some(c) => {
                            return Err(CheckError::from(c));
                        }
                        None => LocalVerdict::Unsupported(UnsupportedReason::DependsOnUnsettled(
                            input
                                .components
                                .values()
                                .flat_map(|c| c.blocked_by.iter().cloned())
                                .collect(),
                        )),
                    }));
                }
                let tuples = input.roots.iter().collect::<Vec<_>>();
                let ctx = &meaning.context;
                let mut violation = ctx.false_condition();
                for (i, left) in tuples.iter().enumerate() {
                    for right in &tuples[i + 1..] {
                        budget.tick("property checks")?;
                        let pair = ctx.apply(
                            &meaning.known(&rt.atoms[*left]),
                            &meaning.known(&rt.atoms[*right]),
                            biodivine_lib_bdd::op_function::and,
                            &mut budget,
                        )?;
                        violation = ctx.apply(
                            &violation,
                            &pair,
                            biodivine_lib_bdd::op_function::or,
                            &mut budget,
                        )?;
                    }
                }
                let violation = ctx.restrict(&violation, &mut budget)?;
                Ok(LocalAnswer::Group(if violation.is_false() {
                    LocalVerdict::Proved
                } else {
                    crate::symbolic::retain(0, 0, violation.node_count(), &mut budget)?;
                    LocalVerdict::Overlap(timed_export(
                        ctx,
                        &violation,
                        &rt.keys,
                        &mut budget,
                        &mut metrics.export,
                    )?)
                }))
            }
            LocalScope::Region(key) => {
                let component = rt.component(key)?;
                let completion = meaning.complete_component(component, 0, &mut budget)?;
                let mut boundary = BTreeMap::new();
                let mut bad_input = None;
                let outcome = match completion {
                    CompletionOutcome::NoContradiction => RegionCompletion::NoContradiction,
                    CompletionOutcome::Inconclusive(c) => {
                        return Err(CheckError::from(c));
                    }
                    CompletionOutcome::Deferred { blocked_by } => RegionCompletion::Deferred(
                        blocked_by
                            .iter()
                            .map(|id| rt.components[id].clone())
                            .collect(),
                    ),
                    CompletionOutcome::NoMeaning(f) => {
                        let mut evidence = EvidenceKeys::default();
                        for r in &f.rules {
                            let key = &rt.instances[&r.id];
                            evidence.instances.insert(key.clone());
                            let instance = &input.rules[key];
                            for o in std::iter::once(&instance.head)
                                .chain(instance.body.iter().map(|(_, o)| o))
                            {
                                evidence.occurrences.insert(o.occurrence.clone());
                                evidence.occurrences.extend(o.arguments.iter().cloned());
                            }
                        }
                        evidence.rewrites = input
                            .rewrites
                            .iter()
                            .filter(|p| {
                                input
                                    .original_dependencies
                                    .get(&p.candidate)
                                    .is_some_and(|r| key.0.contains(&r.head.atom))
                            })
                            .cloned()
                            .collect();
                        for (a, b) in &f.upstream {
                            boundary.insert(
                                AtomKey::from_atom(&rt.keys, a).map_err(CheckError::Keys)?,
                                timed_export(
                                    &meaning.context,
                                    &b.condition,
                                    &rt.keys,
                                    &mut budget,
                                    &mut metrics.export,
                                )?,
                            );
                            if let CompletedProvider::Component(id) = b.provider {
                                evidence.providers.insert(rt.components[&id].clone());
                            }
                        }
                        bad_input = Some(timed_export(
                            &meaning.context,
                            &f.bad_input,
                            &rt.keys,
                            &mut budget,
                            &mut metrics.export,
                        )?);
                        let atom = |a: &GroundAtom| {
                            AtomKey::from_atom(&rt.keys, a).map_err(CheckError::Keys)
                        };
                        RegionCompletion::NoMeaning {
                            candidate: Candidate {
                                present: f
                                    .observation
                                    .present
                                    .iter()
                                    .map(&atom)
                                    .collect::<Result<_>>()?,
                                absent: f
                                    .observation
                                    .absent
                                    .iter()
                                    .map(&atom)
                                    .collect::<Result<_>>()?,
                            },
                            evidence,
                        }
                    }
                };
                Ok(LocalAnswer::Completion {
                    outcome,
                    bad_input,
                    boundary,
                })
            }
        }
    })();
    let (value, failure) = match computed {
        Ok(v) => (Some(v), None),
        Err(e) => {
            budget.failure(&e);
            (None, Some(Inconclusive::from_error(e)?))
        }
    };
    match input.scope {
        LocalScope::Group(_) => {
            metrics.property += start
                .elapsed()
                .saturating_sub(metrics.export - exports_before)
        }
        LocalScope::Region(_) => {
            metrics.completion += start
                .elapsed()
                .saturating_sub(metrics.export - exports_before)
        }
    };
    Ok(OwnedAnswer {
        value,
        failure,
        receipt: receipt(input, &budget, true),
    })
}
