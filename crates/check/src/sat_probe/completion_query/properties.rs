use super::*;
use denotate_ir::{ObligationId, Requirement};

#[derive(Debug, Clone)]
pub struct PropertyPart {
    pub component: Cardinality,
    pub group: Vec<ConstantId>,
    pub tuples: Vec<GroundAtom>,
    pub failed: bool,
    pub example: Option<Model>,
}
#[derive(Debug, Clone)]
pub struct ObligationResult {
    pub requirement: Requirement,
    pub parts: Vec<PropertyPart>,
    pub rejected: Option<Observation>,
    pub not_analysed: bool,
    pub vacuous: bool,
    pub finished: bool,
    pub no_groups: bool,
    pub inconclusive: Option<Inconclusive>,
    members: Option<Arc<BTreeSet<GroundAtom>>>,
}
impl ObligationResult {
    pub fn failed(&self) -> bool {
        self.rejected.is_some() || self.parts.iter().any(|p| p.failed)
    }
    pub fn complete(&self) -> bool {
        self.finished && !self.not_analysed && self.inconclusive.is_none()
    }
    pub(super) fn finish(&mut self, finished: bool, unknown: Option<Inconclusive>, vacuous: bool) {
        self.members = None;
        self.finished = finished;
        self.vacuous = vacuous;
        if self.inconclusive.is_none() {
            self.inconclusive = unknown;
        }
        if finished && vacuous {
            // No accepted observation needs a property query, even for a kind
            // whose non-vacuous solver path is unavailable in this increment.
            self.not_analysed = false;
            self.inconclusive = None;
        }
    }
    pub(super) fn rejection(
        requirement: Requirement,
        rejected: &Search<Observation>,
        unknown: Option<Inconclusive>,
    ) -> Self {
        Self {
            requirement,
            parts: vec![],
            rejected: if let Search::Exists(w) = rejected {
                Some(w.clone())
            } else {
                None
            },
            not_analysed: matches!(rejected, Search::NotAnalysed),
            vacuous: false,
            finished: rejected.complete(),
            no_groups: false,
            inconclusive: unknown.or_else(|| {
                if let Search::Inconclusive(c) = rejected {
                    Some(*c)
                } else {
                    None
                }
            }),
            members: None,
        }
    }
}
impl std::fmt::Debug for Cone {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Cone")
            .field("atoms", &self.atoms.len())
            .field("rules", &self.rules.len())
            .finish()
    }
}
impl Engine {
    pub(super) fn properties(
        &self,
        keys: &SemanticKeys,
        options: &CheckOptions,
    ) -> Result<BTreeMap<ObligationId, ObligationResult>> {
        let mut out = BTreeMap::new();
        for (id, requirement) in &self.selection {
            let Some(r) = requirement.cardinality() else {
                continue;
            };
            let mut result = ObligationResult {
                requirement: requirement.clone(),
                parts: vec![],
                rejected: None,
                not_analysed: false,
                vacuous: false,
                finished: false,
                no_groups: false,
                inconclusive: None,
                members: None,
            };
            let mut b = Budget::new(&self.limits);
            let built: Result<()> = (|| {
                let mut atoms = Vec::new();
                for a in &self.program.core.atoms {
                    b.tick("completion property preparation")?;
                    if a.relation == r.relation() {
                        atoms.push((
                            AtomKey::from_atom(keys, a).map_err(CheckError::Keys)?,
                            a.clone(),
                        ));
                    }
                }
                atoms.sort_by(|a, b| a.0.cmp(&b.0));
                let atoms: Vec<_> = atoms.into_iter().map(|(_, a)| a).collect();
                let original = self
                    .program
                    .dependency_cone_with_budget(atoms.clone(), &mut b)?;
                let fixed = original
                    .facts
                    .iter()
                    .all(|a| !self.program.inputs.contains(a))
                    && original
                        .components
                        .iter()
                        .all(|id| !self.program.components[id.index].recursive);
                let mut members = original.facts;
                if let Some((_, classification, _)) = &self.classification {
                    members.extend(classification.iter().cloned());
                }
                result.members = Some(Arc::new(members));
                let mut grouped = BTreeMap::<Vec<ConstantId>, Vec<GroundAtom>>::new();
                for a in atoms {
                    b.tick("completion property groups")?;
                    grouped
                        .entry(r.group_by().iter().map(|i| a.arguments[*i]).collect())
                        .or_default()
                        .push(a);
                }
                if r.kind().has_coverage() && !fixed {
                    result.not_analysed = true;
                }
                if r.kind().has_coverage() && fixed {
                    let signature = &self.program.signatures[&r.relation()];
                    let domains: Vec<_> = r
                        .group_by()
                        .iter()
                        .map(|i| &self.program.domains[&signature[*i]])
                        .collect();
                    if domains.iter().any(|d| d.is_empty()) {
                        result.no_groups = true;
                    } else {
                        let mut positions = vec![0; domains.len()];
                        loop {
                            b.room(
                                result.parts.len(),
                                options.max_tuples.min(self.limits.max_atoms),
                                "completion coverage",
                                "groups",
                            )?;
                            b.tick("completion coverage")?;
                            let group: Vec<_> =
                                domains.iter().zip(&positions).map(|(d, i)| d[*i]).collect();
                            result.parts.push(PropertyPart {
                                component: Cardinality::AtLeastOne,
                                tuples: grouped.get(&group).cloned().unwrap_or_default(),
                                group,
                                failed: false,
                                example: None,
                            });
                            let mut advanced = false;
                            for i in (0..positions.len()).rev() {
                                positions[i] += 1;
                                if positions[i] < domains[i].len() {
                                    advanced = true;
                                    break;
                                }
                                positions[i] = 0;
                            }
                            if !advanced {
                                break;
                            }
                        }
                    }
                }
                for (group, tuples) in grouped {
                    b.tick("completion property groups")?;
                    if r.kind() == Cardinality::Empty {
                        for tuple in tuples {
                            b.room(
                                result.parts.len(),
                                options.max_tuples,
                                "completion emptiness",
                                "tuples",
                            )?;
                            result.parts.push(PropertyPart {
                                component: Cardinality::Empty,
                                group: vec![],
                                tuples: vec![tuple],
                                failed: false,
                                example: None,
                            });
                        }
                    } else if r.kind().has_uniqueness() && tuples.len() > 1 {
                        b.room(
                            result.parts.len(),
                            options.max_tuples,
                            "completion uniqueness",
                            "groups",
                        )?;
                        result.parts.push(PropertyPart {
                            component: Cardinality::AtMostOne,
                            group,
                            tuples,
                            failed: false,
                            example: None,
                        });
                    }
                }
                Ok(())
            })();
            if let Err(e) = built {
                result.inconclusive = Some(inconclusive(e)?);
            }
            out.insert(*id, result);
        }
        Ok(out)
    }
    pub(super) fn check_property(
        &self,
        result: &mut ObligationResult,
        world: &Observation,
        classification: Option<&Model>,
        options: &CheckOptions,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        let Some(members) = &result.members else {
            return Ok(());
        };
        let mut cone = self.cone.clone();
        cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
        let mut retained = result.parts.iter().filter(|p| p.example.is_some()).count();
        for part in &mut result.parts {
            if part.failed {
                continue;
            }
            // A preparation cutoff can leave a useful prefix of candidates.
            let answer = queries::property(
                self,
                &cone,
                members.clone(),
                world,
                classification,
                part,
                budget,
            );
            match answer {
                Ok(Some(model)) => {
                    part.failed = true;
                    if retained < options.max_examples {
                        part.example = Some(model);
                        retained += 1;
                    }
                }
                Ok(None) => (),
                Err(e) => {
                    result.inconclusive =
                        Some(inconclusive(e.in_phase("completion property", None))?);
                    break;
                }
            }
        }
        Ok(())
    }
    pub(super) fn meaning_at(
        &self,
        world: &Observation,
        classification: Option<&Model>,
        budget: &mut Budget<'_>,
    ) -> Result<Interpretations> {
        let result: Result<Interpretations> = (|| {
            let mut run = queries::Run::new(self, budget)?;
            let pins = world
                .present
                .iter()
                .map(|a| run.input(a))
                .collect::<Result<Vec<_>>>()?;
            // Include absent inputs as well; observations are complete.
            let mut pins = pins;
            for a in &world.absent {
                pins.push(!run.input(a)?);
            }
            run.models(
                &self.cone,
                &pins,
                None,
                if classification.is_some() {
                    ModelScope::Processing
                } else {
                    ModelScope::WholeProgram
                },
                classification.map(|m| (self.classification.as_ref().unwrap().1.as_ref(), m)),
            )
        })();
        match result {
            Ok(r) => Ok(r),
            Err(e) => Ok(Interpretations::Inconclusive {
                cause: inconclusive(e.in_phase("completion processing", None))?,
                example: None,
            }),
        }
    }
}
