//! Provider-first positive SCCs, with anchored coordinate updates inside an SCC.
//! Concrete tuples only ever shrink. A coordinate may be updated immediately:
//! monotonicity preserves every fixed point below the current upper bound.
use super::*;

// True if every producer can be joined without expanding an unbound variable
// over a domain. An empty concrete premise/domain kills the producer outright.
fn anchored(
    rules: &[&Rule],
    tables: &Upper,
    domains: &Domains,
    b: &mut Budget<'_>,
) -> Result<bool> {
    for rule in rules {
        let mut variables = BTreeSet::new();
        let mut bound = BTreeSet::new();
        let mut empty = false;
        for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
            for t in atom.arguments() {
                b.tick("completion descent anchoring")?;
                if let Term::Variable { name, sort } = t.value() {
                    variables.insert(name.as_str());
                    empty |= domains[sort].is_empty();
                }
            }
        }
        for l in &rule.body {
            b.tick("completion descent anchoring")?;
            if let Literal::Positive(a) = l {
                if let Some(table) = &tables[&a.relation()] {
                    empty |= table.rows.is_empty();
                    for t in a.arguments() {
                        if let Term::Variable { name, .. } = t.value() {
                            bound.insert(name.as_str());
                        }
                    }
                }
            }
        }
        if !empty && !variables.is_subset(&bound) {
            return Ok(false);
        }
    }
    Ok(true)
}

// Full rechecks are needed for transitions from symbolic domains. Afterwards,
// only heads reached by a removed binding can lose support. Pending head sets
// are subsets of existing possibility tables, not retained rule instances.
enum Pending {
    Full,
    Heads(BTreeSet<GroundAtom>),
}

fn full_table(corpus: &Corpus, domains: &Domains, relation: RelationId, size: usize) -> bool {
    corpus
        .relation(relation)
        .unwrap()
        .parameters
        .iter()
        .try_fold(1usize, |n, p| n.checked_mul(domains[&p.sort].len()))
        == Some(size)
}

pub(super) fn descend(
    corpus: &Corpus,
    domains: &Domains,
    producers: &BTreeMap<RelationId, Vec<&Rule>>,
    tables: &mut Upper,
    input_count: usize,
    measurement: &mut sizes::Measurement,
    b: &mut Budget<'_>,
) -> Result<()> {
    let mut readers = BTreeMap::<RelationId, BTreeSet<RelationId>>::new();
    for rules in producers.values() {
        for rule in rules {
            for literal in &rule.body {
                b.tick("completion descent readers")?;
                if let Literal::Positive(a) = literal {
                    readers
                        .entry(a.relation())
                        .or_default()
                        .insert(rule.head.relation());
                }
            }
        }
    }
    let mut fixed_count = input_count;
    let components = positive_components(corpus, b)?;
    if measurement.enabled() {
        measurement.data.components = components.clone();
    }
    for component in components {
        if component
            .iter()
            .all(|r| corpus.relation(*r).unwrap().role == RelationRole::Input)
        {
            continue;
        }
        let members: BTreeSet<_> = component.iter().copied().collect();
        let mut pending = BTreeMap::<RelationId, Pending>::new();
        let mut ready = BTreeSet::new();
        let mut anchored_relations = BTreeSet::new();
        let mut deferred = BTreeSet::new();
        for r in &component {
            pending.insert(*r, Pending::Full);
            if anchored(
                producers.get(r).map(Vec::as_slice).unwrap_or(&[]),
                tables,
                domains,
                b,
            )? {
                anchored_relations.insert(*r);
                ready.insert(*r);
            } else {
                deferred.insert(*r);
            }
        }
        let mut concrete_count = 0usize;
        while let Some(relation) = ready.pop_first().or_else(|| deferred.pop_first()) {
            b.tick("completion descent worklist")?;
            let old_size = tables[&relation].as_ref().map_or(0, |t| t.rows.len());
            if measurement.enabled() {
                b.excluding_time(|| measurement.round(&[relation]));
            }
            let changed_heads = match pending.remove(&relation).unwrap() {
                Pending::Full => None,
                Pending::Heads(heads) => Some(Table::new(heads)),
            };
            let mut out = BTreeSet::new();
            if let Some(heads) = &changed_heads {
                for a in &tables[&relation].as_ref().unwrap().rows {
                    b.tick("completion descent retained heads")?;
                    if heads.rows.binary_search(a).is_err() {
                        out.insert(a.clone());
                    }
                }
            }
            let result: Result<()> = (|| {
                for rule in producers.get(&relation).into_iter().flatten() {
                    b.completion_rule(rule.id, |b| {
                        join_bindings(
                            rule,
                            tables,
                            domains,
                            b,
                            true,
                            changed_heads.as_ref().map(JoinSeed::Head),
                            |binding, b| {
                                let atom = ground_atom(&rule.head, binding, b)?.atom;
                                if !out.contains(&atom) {
                                    let demand =
                                        fixed_count + concrete_count - old_size + out.len();
                                    if measurement.enabled() {
                                        measurement.data.peak_possibility_atoms = measurement
                                            .data
                                            .peak_possibility_atoms
                                            .max(demand.saturating_add(1));
                                    }
                                    b.room(
                                        demand,
                                        b.limits.max_atoms,
                                        "completion possibility",
                                        "atoms",
                                    )?;
                                    out.insert(atom);
                                }
                                Ok(())
                            },
                        )
                    })?;
                }
                Ok(())
            })();
            if measurement.enabled() {
                b.excluding_time(|| measurement.relation(relation, &out, result.is_ok()));
            }
            result?;
            b.charge(out.len() + 1, "completion possibility")?;
            let equal = tables[&relation]
                .as_ref()
                .is_some_and(|old| old.rows.iter().eq(out.iter()));
            if equal {
                continue;
            }
            concrete_count = concrete_count - old_size + out.len();
            let old = tables[&relation].as_ref();
            let unchanged_top = old.is_none() && full_table(corpus, domains, relation, out.len());
            let delta = if let Some(old) = old {
                let mut removed = Vec::new();
                for a in &old.rows {
                    b.tick("completion descent delta")?;
                    if !out.contains(a) {
                        removed.push(a.clone());
                    }
                }
                Some(Table::new(removed))
            } else if out.is_empty() && corpus.relation(relation).unwrap().parameters.is_empty() {
                // The full zero-arity domain is exactly one tuple. No product
                // enumeration is needed to represent its first removal.
                Some(Table::new([GroundAtom {
                    relation,
                    arguments: vec![],
                }]))
            } else {
                None
            };
            // Use OLD tables here, including every occurrence of the changed
            // relation. Joining the delta against new tables would miss bindings
            // where two premises disappear together. Negative literals have no
            // role in this positive-support greatest fixpoint.
            for r in readers
                .get(&relation)
                .into_iter()
                .flatten()
                .filter(|r| members.contains(r))
            {
                b.tick("completion descent reschedule")?;
                if unchanged_top {
                    // Still reclassify already-pending work after installation:
                    // a concrete full table can anchor a join without changing it.
                    continue;
                }
                if !matches!(pending.get(r), Some(Pending::Full)) {
                    let rules = producers.get(r).map(Vec::as_slice).unwrap_or(&[]);
                    if let Some(delta) = delta.as_ref().filter(|_| tables[r].is_some()) {
                        let entry = pending
                            .entry(*r)
                            .or_insert_with(|| Pending::Heads(BTreeSet::new()));
                        let Pending::Heads(heads) = entry else {
                            unreachable!()
                        };
                        for rule in rules {
                            for (i, literal) in rule.body.iter().enumerate() {
                                b.tick("completion descent delta readers")?;
                                if matches!(literal, Literal::Positive(a) if a.relation() == relation)
                                {
                                    b.completion_rule(rule.id, |b| {
                                        join_bindings(
                                            rule,
                                            tables,
                                            domains,
                                            b,
                                            true,
                                            Some(JoinSeed::Body(i, delta)),
                                            |binding, b| {
                                                let a = ground_atom(&rule.head, binding, b)?.atom;
                                                if tables[r]
                                                    .as_ref()
                                                    .unwrap()
                                                    .rows
                                                    .binary_search(&a)
                                                    .is_ok()
                                                {
                                                    heads.insert(a);
                                                }
                                                Ok(())
                                            },
                                        )
                                    })?;
                                }
                            }
                        }
                        if heads.is_empty() {
                            pending.remove(r);
                        }
                    } else {
                        pending.insert(*r, Pending::Full);
                    }
                }
            }
            tables.insert(relation, Some(Table::new(out)));
            for r in readers
                .get(&relation)
                .into_iter()
                .flatten()
                .filter(|r| members.contains(r))
            {
                if !pending.contains_key(r) {
                    continue;
                }
                ready.remove(r);
                deferred.remove(r);
                if anchored_relations.contains(r)
                    || anchored(
                        producers.get(r).map(Vec::as_slice).unwrap_or(&[]),
                        tables,
                        domains,
                        b,
                    )?
                {
                    anchored_relations.insert(*r);
                    ready.insert(*r);
                } else {
                    deferred.insert(*r);
                }
            }
        }
        if measurement.enabled() {
            b.excluding_time(|| measurement.fixed(&component));
        }
        fixed_count += concrete_count;
    }
    Ok(())
}
