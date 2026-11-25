//! Existential projection of a reduced view, without changing semantic scope.
//!
//! Keep every cyclic SCC (including positive/self cycles), H and group targets,
//! and their upstream equations. Everything else is an acyclic function of these
//! atoms and the inputs, so every retained model has a unique extension. Rebuild
//! that extension before replaying the original, frozen-scope equations.
use super::*;
use std::collections::VecDeque;

pub(super) struct Slice {
    pub core: Cone,
    source: Cone,
    order: Vec<usize>,
    producers: Vec<Vec<usize>>,
}
impl Slice {
    pub fn new(view: &Cone, h: Option<usize>, b: &mut Budget<'_>) -> Result<Self> {
        let mut source = view.clone();
        source.fixed = encoding::fitting(view, b)?;
        let graph = consistency::analyse(&source, None, b)?;
        let n = source.fixed.len();
        b.charge(n + source.rules.len(), "completion existence slice")?;
        let mut producers = vec![vec![]; n];
        for (ri, r) in source.rules.iter().enumerate() {
            b.charge(r.body.len() + 1, "completion existence slice")?;
            if source.input[r.head]
                || source.fixed[r.head].is_some()
                || r.body
                    .iter()
                    .any(|(i, p)| source.fixed[*i].is_some_and(|v| v != *p))
            {
                continue;
            }
            producers[r.head].push(ri);
        }
        let mut pending: Vec<_> = graph
            .cyclic
            .iter()
            .enumerate()
            .filter_map(|(i, cyclic)| cyclic.then_some(i))
            .collect();
        pending.extend(h);
        for (_, group) in &source.groups {
            b.charge(group.len(), "completion existence slice")?;
            pending.extend(group);
        }
        let mut keep = vec![false; n];
        while let Some(i) = pending.pop() {
            b.tick("completion existence slice")?;
            if keep[i] {
                continue;
            }
            keep[i] = true;
            for ri in &producers[i] {
                b.charge(source.rules[*ri].body.len(), "completion existence slice")?;
                pending.extend(source.rules[*ri].body.iter().map(|(a, _)| *a));
            }
        }
        // Count duplicate dependencies consistently in both directions. Kahn's
        // order is deterministic and does not depend on recursion depth.
        let omitted = |i: usize| !keep[i] && !source.input[i] && source.fixed[i].is_none();
        let mut dependencies = vec![0usize; n];
        let mut readers = vec![vec![]; n];
        for (i, rs) in producers.iter().enumerate() {
            if !omitted(i) {
                continue;
            }
            for ri in rs {
                b.charge(
                    source.rules[*ri].body.len() + 1,
                    "completion existence extension order",
                )?;
                for (a, _) in &source.rules[*ri].body {
                    if omitted(*a) {
                        dependencies[i] += 1;
                        readers[*a].push(i);
                    }
                }
            }
        }
        let expected = (0..n).filter(|i| omitted(*i)).count();
        let mut ready: VecDeque<_> = (0..n)
            .filter(|i| omitted(*i) && dependencies[*i] == 0)
            .collect();
        let mut order = Vec::with_capacity(expected);
        while let Some(i) = ready.pop_front() {
            b.charge(readers[i].len() + 1, "completion existence extension order")?;
            order.push(i);
            for r in &readers[i] {
                dependencies[*r] -= 1;
                if dependencies[*r] == 0 {
                    ready.push_back(*r);
                }
            }
        }
        if order.len() != expected {
            return Err(CheckError::Internal("cyclic existential extension"));
        }
        let mut core = source.clone();
        core.rules = source
            .rules
            .iter()
            .filter(|r| keep[r.head])
            .cloned()
            .collect();
        Ok(Self {
            core,
            source,
            order,
            producers,
        })
    }
    pub fn extend(&self, values: &mut [bool], b: &mut Budget<'_>) -> Result<()> {
        for i in &self.order {
            let mut value = false;
            for ri in &self.producers[*i] {
                let r = &self.source.rules[*ri];
                b.charge(r.body.len() + 1, "completion existence extension")?;
                value |= r.body.iter().all(|(a, p)| values[*a] == *p);
            }
            values[*i] = value;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel};
    use denotate_ir::Corpus;

    fn models(c: &Cone, h: Option<usize>) -> BTreeSet<Vec<bool>> {
        (0..1usize << c.fixed.len())
            .filter_map(|bits| {
                let v: Vec<_> = (0..c.fixed.len()).map(|i| bits & (1 << i) != 0).collect();
                let equations = (0..v.len()).all(|i| {
                    if let Some(fixed) = c.fixed[i] {
                        v[i] == fixed
                    } else if c.input[i] {
                        true
                    } else {
                        v[i] == c
                            .rules
                            .iter()
                            .filter(|r| r.head == i)
                            .any(|r| r.body.iter().all(|(a, p)| v[*a] == *p))
                    }
                });
                (equations && h.is_none_or(|i| v[i])).then_some(v)
            })
            .collect()
    }
    #[test]
    fn cyclic_core_plus_topological_extension_preserves_every_tiny_model() {
        let mut corpus = Corpus::new();
        let atoms: Vec<_> = ["input", "p", "q", "output"]
            .into_iter()
            .enumerate()
            .map(|(i, n)| atom(rel(&mut corpus, n, i == 0)))
            .collect();
        let mut c = Cone {
            atoms: atoms.into(),
            input: vec![true, false, false, false].into(),
            fixed: vec![None; 4],
            rules: vec![].into(),
            target: vec![true; 4].into(),
            duplicated: vec![false; 4].into(),
            groups: vec![].into(),
            source_rules: 4,
        };
        let bodies = [
            vec![],
            vec![(0, true)],
            vec![(0, false)],
            vec![(1, true)],
            vec![(1, false)],
            vec![(2, true)],
            vec![(2, false)],
            vec![(0, true), (1, true)],
            vec![(0, false), (2, true)],
            vec![(1, true), (2, false)],
        ];
        let limits = Limits::default();
        for a in &bodies {
            for b in &bodies {
                for d in &bodies {
                    c.rules = [
                        (1, a.clone()),
                        (1, b.clone()),
                        (2, d.clone()),
                        (3, vec![(2, false)]),
                    ]
                    .into_iter()
                    .map(|(head, body)| crate::sat_probe::Rule {
                        head,
                        body,
                        ground: None,
                        source: None,
                    })
                    .collect();
                    for pin in [None, Some(false), Some(true)] {
                        c.fixed[0] = pin;
                        for h in [None, Some(1), Some(3)] {
                            let mut budget = Budget::new(&limits);
                            let view = search_free::reduce(&c, &mut budget).unwrap().cone;
                            let slice = Slice::new(&view, h, &mut budget).unwrap();
                            let extended: BTreeSet<_> = models(&slice.core, h)
                                .into_iter()
                                .map(|mut v| {
                                    slice.extend(&mut v, &mut budget).unwrap();
                                    queries::validate_assignment(&c, &v, None, &mut budget)
                                        .unwrap();
                                    v
                                })
                                .collect();
                            assert_eq!(models(&c, h), extended, "{a:?} {b:?} {d:?}; {pin:?} {h:?}");
                        }
                    }
                }
            }
        }
    }
}
