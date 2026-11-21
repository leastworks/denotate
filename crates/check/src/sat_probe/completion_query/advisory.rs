use super::*;

#[derive(Debug)]
pub enum Advisory {
    NotRequested,
    Checked {
        findings: Vec<CircularSupport>,
        incomplete: Option<Inconclusive>,
    },
}
#[derive(Debug)]
pub struct CircularSupport {
    /// Original positive ground component, independent of the chosen witness.
    pub component: BTreeSet<GroundAtom>,
    pub cycle: Vec<GroundRuleId>,
    pub model: Model,
}
impl Engine {
    #[cfg(test)]
    pub(super) fn circular_advisory(
        &self,
        models: &[Model],
        truncated: bool,
        options: &CheckOptions,
        keys: &SemanticKeys,
    ) -> Result<Advisory> {
        let mut limits = options.advisory_limits.clone();
        limits.cancellation = self.limits.cancellation.clone();
        let mut b = Budget::new(&limits);
        self.circular_advisory_using(models, truncated, options, keys, &mut b)
    }
    pub(super) fn circular_advisory_using(
        &self,
        models: &[Model],
        truncated: bool,
        options: &CheckOptions,
        keys: &SemanticKeys,
        mut b: &mut Budget<'_>,
    ) -> Result<Advisory> {
        let mut findings = Vec::new();
        let mut seen = BTreeSet::new();
        let result: Result<()> = (|| {
            let Some((cone, members, _)) = &self.classification else {
                return Ok(());
            };
            if models.is_empty() {
                return Ok(());
            }
            // Pruned dead producers must not change the advisory's identity.
            let mut components = BTreeMap::<GroundAtom, Arc<BTreeSet<GroundAtom>>>::new();
            let mut rule_ids = Vec::new();
            for r in &self.program.core.rules {
                b.tick("completion circular support")?;
                if members.contains(&r.head.atom) {
                    rule_ids.push(r.id);
                }
            }
            for model in models {
                let unfounded = least_unfounded(cone, &model.values, &mut b)?;
                let mut edges = vec![Vec::new(); cone.fixed.len()];
                for (i, r) in cone.rules.iter().enumerate() {
                    b.charge(r.body.len() + 1, "completion circular support")?;
                    if unfounded.contains(&r.head)
                        && r.body.iter().all(|(a, p)| model.values[*a] == *p)
                    {
                        for (a, p) in &r.body {
                            if *p && unfounded.contains(a) {
                                edges[r.head].push((*a, i));
                            }
                        }
                    }
                }
                // Iterative DFS: report only actual supported positive cycles.
                let mut color = vec![0u8; edges.len()];
                for root in &unfounded {
                    if color[*root] != 0 {
                        continue;
                    }
                    color[*root] = 1;
                    let mut stack = vec![(*root, 0usize, None::<usize>)];
                    while let Some((a, next, _)) = stack.last_mut() {
                        b.tick("completion circular support")?;
                        if *next == edges[*a].len() {
                            color[*a] = 2;
                            stack.pop();
                            continue;
                        }
                        let (to, rule) = edges[*a][*next];
                        *next += 1;
                        if color[to] == 0 {
                            color[to] = 1;
                            stack.push((to, 0, Some(rule)));
                        } else if color[to] == 1 {
                            let start = stack.iter().position(|(a, _, _)| *a == to).unwrap();
                            let root = &cone.atoms[to];
                            if !components.contains_key(root) {
                                let members = Arc::new(self.original.positive_component(root, b)?);
                                for atom in members.iter() {
                                    b.tick("completion circular support identity")?;
                                    components.insert(atom.clone(), members.clone());
                                }
                            }
                            let component = components[root].as_ref().clone();
                            let key = component
                                .iter()
                                .map(|a| AtomKey::from_atom(keys, a).map_err(CheckError::Keys))
                                .collect::<Result<BTreeSet<_>>>()?;
                            if !seen.insert(key) {
                                continue;
                            }
                            let indices = stack[start + 1..]
                                .iter()
                                .filter_map(|(_, _, r)| *r)
                                .chain([rule]);
                            b.room(
                                findings.len(),
                                options.max_examples,
                                "completion circular support",
                                "examples",
                            )?;
                            let cycle = indices.map(|i| rule_ids[i]).collect();
                            findings.push(CircularSupport {
                                component,
                                cycle,
                                model: model.clone(),
                            });
                        }
                    }
                }
            }
            Ok(())
        })();
        let incomplete = match result {
            Err(e) => Some(inconclusive(
                e.in_phase("completion circular support", None),
            )?),
            Ok(()) if truncated => Some(Inconclusive {
                phase: "completion circular support",
                resource: "examples",
                details: Default::default(),
            }),
            _ => None,
        };
        Ok(Advisory::Checked {
            findings,
            incomplete,
        })
    }
}
