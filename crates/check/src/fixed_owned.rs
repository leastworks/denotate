//! Source-independent fold query. Only semantic keys cross a session boundary;
//! the imported evidence always uses the current corpus and occurrences.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixedInput {
    pub relations: BTreeMap<RelationKey, RelationSchema>,
    pub rules: BTreeMap<RuleKey, RuleSchema>,
    pub domains: BTreeMap<SortKey, BTreeSet<ConstantKey>>,
    pub limits: DeterministicLimits,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixedValue {
    pub possible: BTreeSet<AtomKey>,
    pub instances: BTreeSet<InstanceKey>,
    /// One original producer for each true atom, in replay order. False possible
    /// atoms remain in `possible`, including their original producers.
    pub present: BTreeMap<AtomKey, (usize, InstanceKey)>,
    pub relations: BTreeSet<RelationKey>,
    pub receipt: WorkReceipt,
    pub runtime_receipt: WorkReceipt,
}

pub trait FixedStore {
    fn fold(
        &mut self,
        input: FixedInput,
        operations: &OperationalLimits,
    ) -> Result<Arc<FixedValue>>;
}

impl<'a> FixedPreparation<'a> {
    /// Session-backed fold. The query excludes input-dependent rule bodies,
    /// obligations, notices, source spans and verification selections.
    pub fn prepare_cached(
        corpus: &'a Corpus,
        keys: &SemanticKeys,
        domains: &Domains,
        limits: &Limits,
        store: &mut dyn FixedStore,
    ) -> Result<Self> {
        keys.validate(corpus)?;
        let mut budget = Budget::tracked(limits);
        let domains = validate_domains(corpus, domains, &mut budget)?;
        let input_domains = input_domains::evaluate(corpus, &domains, &mut budget)?;
        let result = (|| {
            let cone = fixed_relations(corpus, &mut budget)?;
            let relations = cone
                .iter()
                .map(|id| {
                    Ok((
                        keys.relation(*id)?.clone(),
                        keys.relation_schema(corpus.relation(*id).unwrap())?,
                    ))
                })
                .collect::<Result<BTreeMap<_, _>>>()?;
            let rules = corpus
                .rules()
                .filter(|r| cone.contains(&r.head.relation()))
                .map(|r| {
                    budget.tick("fixed projection")?;
                    for a in std::iter::once(&r.head).chain(r.body.iter().map(Literal::atom)) {
                        for arg in a.arguments() {
                            if let Term::Constant(c) = arg.value() {
                                let sort = corpus.constant(*c).unwrap().sort;
                                if !domains[&sort].contains(c) {
                                    return Err(CheckError::ConstantOutsideDomain(*c));
                                }
                            }
                        }
                    }
                    Ok((keys.rule(r.id)?.clone(), keys.rule_schema(r)?))
                })
                .collect::<Result<_>>()?;
            let sorts: BTreeSet<_> = cone
                .iter()
                .flat_map(|r| {
                    corpus
                        .relation(*r)
                        .unwrap()
                        .parameters
                        .iter()
                        .map(|p| p.sort)
                })
                .collect();
            let keyed_domains = sorts
                .iter()
                .map(|id| {
                    budget.charge(domains[id].len(), "fixed projection")?;
                    Ok((
                        keys.sort(*id)?.clone(),
                        domains[id]
                            .iter()
                            .map(|c| keys.constant(*c).cloned().map_err(CheckError::Keys))
                            .collect::<Result<_>>()?,
                    ))
                })
                .collect::<Result<_>>()?;
            let value = store.fold(
                FixedInput {
                    relations,
                    rules,
                    domains: keyed_domains,
                    limits: limits.into(),
                },
                &limits.into(),
            )?;
            let facts = {
                let _profile = limits.profile.span("fixed-binding", None);
                value.bind(corpus, keys, &domains, &mut budget)?
            };
            budget.check("fixed binding")?;
            let mut transfer_receipts = WorkReceipts::default();
            transfer_receipts
                .record(QueryKey::FixedRuntime, value.runtime_receipt.clone())
                .map_err(CheckError::Receipts)?;
            budget.record(
                &mut transfer_receipts,
                QueryKey::FixedBinding,
                [QueryKey::FixedFacts],
            )?;
            Ok(Self {
                transfer_receipts,
                corpus,
                domains,
                limits: limits.into(),
                facts,
                input_domains,
                receipt: value.receipt.clone(),
                validation: OnceCell::new(),
                contexts: Default::default(),
            })
        })();
        result.map_err(|error: CheckError| error.in_phase("fixed facts", None))
    }

    pub fn prepare_cached_with_validation(
        validation: &ValidatedAssumptions<'a>,
        limits: &Limits,
        store: &mut dyn FixedStore,
    ) -> Result<Self> {
        if validation.limits != DeterministicLimits::from(limits) {
            return Err(CheckError::InvalidRequest(
                "assumption validation limits do not match fixed preparation",
            ));
        }
        limits.cancellation.check()?;
        if let Some(fixed) = &validation.fixed {
            return Ok(fixed.share());
        }
        Self::prepare_cached(
            validation.corpus,
            validation.keys,
            &validation.domains,
            limits,
            store,
        )
    }
}

/// Pure kernel used by Salsa and the fresh control. Reconstructing in key order
/// makes the retained producer choice independent of the source's arena order.
pub fn fold_owned(input: &FixedInput, operations: &OperationalLimits) -> Result<FixedValue> {
    let limits = input.limits.with_operations(operations);
    let mut budget = Budget::tracked(&limits);
    let (corpus, keys, domains) = {
        let _profile = limits.profile.span("fixed-runtime", None);
        input.runtime(&mut budget)?
    };
    let fixed = FixedPreparation::prepare(&corpus, &domains, &limits)?;
    let _profile = limits.profile.span("fixed-export", None);
    let mut value = FixedValue {
        possible: BTreeSet::new(),
        instances: BTreeSet::new(),
        present: BTreeMap::new(),
        relations: BTreeSet::new(),
        receipt: fixed.receipt.clone(),
        runtime_receipt: WorkReceipt {
            allowance: (&limits).into(),
            own: WorkCharges::default(),
            dependencies: BTreeSet::new(),
        },
    };
    if let Some(facts) = fixed.facts {
        let instances = facts
            .program
            .rules
            .iter()
            .map(|r| {
                budget.charge(r.body.len() + 1, "fixed export")?;
                Ok((r.id, InstanceKey::from_rule(&corpus, &keys, r)?))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        for atom in &facts.program.atoms {
            budget.tick("fixed export")?;
            value.possible.insert(AtomKey::from_atom(&keys, atom)?);
        }
        for (atom, derivation) in &facts.derivations {
            budget.tick("fixed export")?;
            let Evidence::Derived { rule, .. } = &derivation.evidence else {
                return Err(CheckError::Internal("input in fixed facts"));
            };
            value.present.insert(
                AtomKey::from_atom(&keys, atom)?,
                (derivation.order, instances[rule].clone()),
            );
        }
        value.relations = facts
            .relations
            .iter()
            .map(|r| keys.relation(*r).cloned().map_err(CheckError::Keys))
            .collect::<Result<_>>()?;
        value.instances = instances.into_values().collect();
    }
    budget.check("fixed export")?;
    value.runtime_receipt.own = budget.snapshot();
    value.receipt.dependencies.insert(QueryKey::FixedRuntime);
    Ok(value)
}

impl FixedValue {
    fn bind(
        &self,
        corpus: &Corpus,
        keys: &SemanticKeys,
        domains: &Domains,
        budget: &mut Budget<'_>,
    ) -> Result<Option<Arc<FixedFacts>>> {
        if self.possible.is_empty() {
            return Ok(None);
        }
        let relations: BTreeMap<_, _> = corpus
            .relations()
            .map(|r| Ok((keys.relation(r.id)?.clone(), r.id)))
            .collect::<Result<_>>()?;
        let constants: BTreeMap<_, _> = corpus
            .constants()
            .map(|c| Ok((keys.constant(c.id)?.clone(), c.id)))
            .collect::<Result<_>>()?;
        let rules: BTreeMap<_, _> = corpus
            .rules()
            .map(|r| Ok((keys.rule(r.id)?.clone(), r)))
            .collect::<Result<_>>()?;
        let atom = |a: &AtomKey| -> Result<GroundAtom> {
            Ok(GroundAtom::new(
                *relations
                    .get(&a.relation)
                    .ok_or(CheckError::Internal("stale fixed relation"))?,
                a.arguments
                    .iter()
                    .map(|c| {
                        constants
                            .get(c)
                            .copied()
                            .ok_or(CheckError::Internal("stale fixed constant"))
                    })
                    .collect::<Result<Vec<_>>>()?,
            ))
        };
        let mut program = GroundProgram::empty(corpus, domains.clone());
        for a in &self.possible {
            budget.tick("fixed binding")?;
            program.atoms.push(atom(a)?);
        }
        program.atoms.sort();
        program.atom_index = program
            .atoms
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, a)| (a, i))
            .collect();
        let mut instances = BTreeMap::new();
        for key in &self.instances {
            let source = rules
                .get(&key.rule)
                .ok_or(CheckError::Internal("stale fixed rule"))?;
            budget.charge(1 + source.body.len(), "fixed binding")?;
            let binding = key
                .substitution
                .iter()
                .map(|(v, c)| (v.name.as_ref(), constants[c]))
                .collect::<BTreeMap<_, _>>();
            let id = GroundRuleId {
                preparation: program.preparation,
                index: program.rules.len(),
            };
            let rule = GroundRule {
                id,
                source: source.id,
                head: ground_atom(&source.head, &binding, budget)?,
                body: source
                    .body
                    .iter()
                    .map(|literal| {
                        Ok(GroundLiteral {
                            polarity: if matches!(literal, Literal::Negative(_)) {
                                Polarity::Negative
                            } else {
                                Polarity::Positive
                            },
                            term: ground_atom(literal.atom(), &binding, budget)?,
                        })
                    })
                    .collect::<Result<_>>()?,
            };
            instances.insert(key, id);
            program.rules.push(rule);
        }
        graph::analyze(&mut program, budget)?;
        let mut derivations = BTreeMap::new();
        for (a, (order, key)) in &self.present {
            budget.tick("fixed binding")?;
            let id = instances[key];
            let rule = &program.rules[id.index];
            let premises = rule
                .body
                .iter()
                .map(|literal| {
                    let fact = literal.term.atom.clone();
                    let occurrence = literal.term.occurrence;
                    Ok(if literal.polarity == Polarity::Positive {
                        PremiseEvidence::Positive { fact, occurrence }
                    } else {
                        let provider = if program.atom_index.contains_key(&fact) {
                            CompletedProvider::Component(program.component_for(&fact)?.id)
                        } else {
                            CompletedProvider::NoPossibleProducer
                        };
                        PremiseEvidence::Absent {
                            fact,
                            occurrence,
                            provider,
                        }
                    })
                })
                .collect::<Result<_>>()?;
            derivations.insert(
                atom(a)?,
                Derivation {
                    order: *order,
                    evidence: Evidence::Derived { rule: id, premises },
                },
            );
        }
        Ok(Some(Arc::new(FixedFacts {
            program,
            derivations,
            relations: self.relations.iter().map(|r| relations[r]).collect(),
        })))
    }
}

impl FixedInput {
    fn runtime(&self, budget: &mut Budget<'_>) -> Result<(Corpus, SemanticKeys, Domains)> {
        let mut corpus = Corpus::new();
        let mut keys = SemanticKeys::default();
        let mut sorts = BTreeMap::new();
        let mut constants = BTreeMap::new();
        let mut relations = BTreeMap::new();
        let mut domains = Domains::new();
        let invalid = |_| CheckError::Internal("invalid owned fixed structure");
        for (s, values) in &self.domains {
            budget.tick("fixed runtime")?;
            let id = corpus
                .declare_sort(format!("s{}", sorts.len()))
                .map_err(invalid)?;
            keys.bind_sort(&corpus, id, s.clone())
                .map_err(CheckError::Keys)?;
            sorts.insert(s.clone(), id);
            let mut values_ids = Vec::new();
            for v in values {
                budget.tick("fixed runtime")?;
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
        for (r, schema) in &self.relations {
            budget.charge(schema.parameters.len() + 1, "fixed runtime")?;
            let role = if schema.input {
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
        for (key, schema) in &self.rules {
            let mut bindings = Vec::new();
            let mut atom = |a: &AtomSchema| -> Result<Atom> {
                budget.charge(a.arguments.len() + 1, "fixed runtime")?;
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
        Ok((corpus, keys, domains))
    }
}
