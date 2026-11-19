use super::*;

/// Preserve derived truth, not the truth of every alternative producer. Input
/// values outside the returned cube may vary; W is enforced independently.
pub(in super::super) fn certified(
    c: &Cone,
    values: &[bool],
    b: &mut Budget<'_>,
) -> Result<BTreeSet<usize>> {
    b.charge(c.fixed.len(), "SAT cube support")?;
    let mut producers = vec![None; c.fixed.len()];
    if !reduct(c, values, Some(&mut producers), b)?.is_empty() {
        return Err(CheckError::Internal("cube requires a stable model"));
    }
    let free_input = |a: usize| c.input[a] && c.fixed[a].is_none();
    let mut inputs = BTreeSet::new();
    for (a, producer) in producers.iter().enumerate() {
        b.tick("SAT cube support")?;
        if !values[a] || c.input[a] || c.fixed[a].is_some() {
            continue;
        }
        let r = &c.rules[producer.ok_or(CheckError::Internal("missing finite support"))?];
        b.charge(r.body.len(), "SAT cube support")?;
        inputs.extend(
            r.body
                .iter()
                .filter_map(|(i, _)| free_input(*i).then_some(*i)),
        );
    }
    for r in &c.rules {
        b.tick("SAT cube false producers")?;
        if values[r.head] {
            continue;
        }
        b.charge(r.body.len(), "SAT cube false producers")?;
        let blocker = r
            .body
            .iter()
            .filter(|(a, pos)| values[*a] != *pos)
            .min_by_key(|(a, _)| (free_input(*a) && !inputs.contains(a), *a))
            .ok_or(CheckError::Internal("false head has true producer"))?;
        if free_input(blocker.0) {
            inputs.insert(blocker.0);
        }
    }
    Ok(inputs)
}
