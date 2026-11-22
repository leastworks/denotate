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
    for component in positive_components(corpus, b)? {
        if component
            .iter()
            .all(|r| corpus.relation(*r).unwrap().role == RelationRole::Input)
        {
            continue;
        }
        let members: BTreeSet<_> = component.iter().copied().collect();
        let mut ready = BTreeSet::new();
        let mut deferred = BTreeSet::new();
        for r in &component {
            if anchored(
                producers.get(r).map(Vec::as_slice).unwrap_or(&[]),
                tables,
                domains,
                b,
            )? {
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
            let mut out = BTreeSet::new();
            let result: Result<()> = (|| {
                for rule in producers.get(&relation).into_iter().flatten() {
                    bindings(rule, tables, domains, b, |binding, b| {
                        let atom = ground_atom(&rule.head, binding, b)?.atom;
                        if !out.contains(&atom) {
                            let demand = fixed_count + concrete_count - old_size + out.len();
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
            tables.insert(relation, Some(Table::new(out)));
            // Only readers of the changed coordinate need another evaluation.
            // Reclassify pending readers before taking any unanchored fallback.
            for r in readers
                .get(&relation)
                .into_iter()
                .flatten()
                .filter(|r| members.contains(r))
            {
                b.tick("completion descent reschedule")?;
                ready.remove(r);
                deferred.remove(r);
                if anchored(
                    producers.get(r).map(Vec::as_slice).unwrap_or(&[]),
                    tables,
                    domains,
                    b,
                )? {
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
