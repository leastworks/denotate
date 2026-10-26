use crate::Result;
use denotate_check::*;
use denotate_ir::*;
use serde_json::{Value, json};
use std::collections::BTreeSet;

/// Snapshot-local identity. Export comparisons translate these through the IR
/// structural correspondence; publication uses explicit semantic keys below.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Identity {
    Coverage(ObligationId),
    Group {
        obligation: ObligationId,
        tuple: Vec<ConstantId>,
    },
    Region(BTreeSet<GroundAtom>),
    Rewrite {
        rule: RuleId,
        literal: Option<OccurrenceId>,
    },
}
fn qualified(k: &QualifiedKey) -> Value {
    json!([k.namespace.as_ref(), k.name.as_ref()])
}
fn owner(k: &OwnerKey) -> Value {
    json!([k.namespace(), k.value()])
}
fn constant(k: &ConstantKey) -> Value {
    json!({"sort":qualified(&k.sort.0),"name":k.name.as_ref()})
}
fn relation(k: &RelationKey) -> Value {
    match k {
        RelationKey::Named(k) => json!({"named":qualified(k)}),
        RelationKey::Generated { owner: o, local } => {
            json!({"generated":{"owner":owner(o),"local":local}})
        }
    }
}
fn rule(k: &RuleKey) -> Value {
    match k {
        RuleKey::Library(k) => json!({"library":qualified(k)}),
        RuleKey::Installed { owner: o, local } => {
            json!({"installed":{"owner":owner(o),"local":local}})
        }
    }
}
fn occurrence(k: &OccurrenceKey) -> Value {
    match k {
        OccurrenceKey::Sort(k) => json!({"sort":qualified(&k.0)}),
        OccurrenceKey::Constant(k) => json!({"constant":constant(k)}),
        OccurrenceKey::Relation(k) => json!({"relation":relation(k)}),
        OccurrenceKey::Rule(k) => json!({"rule":rule(k)}),
        OccurrenceKey::Obligation(k) => json!({"obligation":qualified(&k.0)}),
        OccurrenceKey::Assumption(k) => json!({"assumption":qualified(&k.0)}),
        OccurrenceKey::Verification(k) => json!({"verification":qualified(&k.0)}),
        OccurrenceKey::Installed { owner: o, local } => {
            json!({"installed":{"owner":owner(o),"local":local}})
        }
        OccurrenceKey::Library {
            rule: r,
            atom,
            argument,
        } => json!({"library":{"rule":rule(r),"atom":atom,"argument":argument}}),
    }
}
pub fn atom_data(k: &AtomKey) -> Value {
    json!({"relation":relation(&k.relation),"arguments":k.arguments.iter().map(constant).collect::<Vec<_>>()})
}
impl Identity {
    /// A finding belongs to the selected verification as well as its group,
    /// region or rewrite. Null is reserved for low-level unnamed requests.
    pub fn data_in(
        &self,
        keys: &SemanticKeys,
        verification: Option<&VerificationKey>,
    ) -> Result<Value> {
        let mut data = self.data(keys)?;
        data["verification"] = verification.map(|v| qualified(&v.0)).unwrap_or(Value::Null);
        Ok(data)
    }

    /// Structured, arena-independent protocol data. Never Debug strings, rendered
    /// messages or ambiguous joined namespace/name strings.
    pub fn data(&self, keys: &SemanticKeys) -> Result<Value> {
        Ok(match self {
            Self::Coverage(id) => {
                json!({"obligation":qualified(&keys.obligation(*id)?.0), "component":"coverage"})
            }
            Self::Group { obligation, tuple } => {
                json!({"group":{"obligation":qualified(&keys.obligation(*obligation)?.0),"tuple":tuple.iter().map(|c| Ok(constant(keys.constant(*c)?))).collect::<Result<Vec<_>>>()?}})
            }
            Self::Region(atoms) => {
                json!({"region":atoms.iter().map(|a| AtomKey::from_atom(keys,a)).collect::<std::result::Result<BTreeSet<_>,_>>()?.iter().map(atom_data).collect::<Vec<_>>()})
            }
            Self::Rewrite { rule: r, literal } => {
                json!({"rewrite":{"rule":rule(keys.rule(*r)?),"literal":literal.map(|l| -> Result<Value> { Ok(occurrence(keys.bindings().key(l)?)) }).transpose()?}})
            }
        })
    }
}

/// Includes request backend/W even when checking exhausted before a report.
/// Proved groups remain status data, never diagnostic locations.
pub fn summary(results: &ScopedResults) -> Value {
    let kinds = |r: &ScopedResult| match r {
        ScopedResult::Proved => "proved",
        ScopedResult::Counterexample(..) => "counterexample",
        ScopedResult::Unsupported(_) => "unsupported",
        ScopedResult::Inconclusive(_) => "inconclusive",
    };
    let complete = results.unfinished.is_none()
        && results.incomplete.is_empty()
        && results.coverage.values().all(CoverageResult::proved)
        && results.regions.is_empty()
        && results
            .groups
            .values()
            .all(|r| matches!(r, ScopedResult::Proved));
    let mut summary = json!({
        "state":if complete { "proved" } else if results.coverage.values().any(|c| c.missing > 0) || results.groups.values().any(|r| matches!(r,ScopedResult::Counterexample(..))) || results.regions.values().any(|r| matches!(r.completion,RegionCompletion::NoMeaning{..})) { "findings" } else { "incomplete" },
        "backend":{"backend":results.context.backend.backend,"configuration":results.context.backend.configuration},
        "activeAssumptions":results.context.constraints.iter().map(|c| match c { InputConstraint::AtMostOne{relation:r,group_by} => json!({"kind":"at-most-one","relation":relation(r),"groupBy":group_by}) }).collect::<Vec<_>>(),
        "groups":results.groups.iter().map(|(k,v)|json!({"identity":{"obligation":qualified(&k.obligation.0),"tuple":k.tuple.iter().map(constant).collect::<Vec<_>>()} ,"outcome":kinds(v),"reason":result_reason(v)})).collect::<Vec<_>>(),
        "regions":results.regions.iter().map(|(k,v)|json!({"identity":k.0.iter().map(atom_data).collect::<Vec<_>>(),"outcome":kinds(&v.outcome),"reason":result_reason(&v.outcome),"completionReason":match &v.completion { RegionCompletion::Inconclusive(r)=>Some(json!({"phase":r.phase,"resource":r.resource})),_=>None },"completion":match v.completion { RegionCompletion::NoContradiction => "no-contradiction", RegionCompletion::NoMeaning{..} => "no-meaning",RegionCompletion::Deferred(_) => "deferred",RegionCompletion::Inconclusive(_) => "inconclusive" }})).collect::<Vec<_>>(),
        "unfinished":results.unfinished.as_ref().map(|r|json!({"phase":r.phase,"resource":r.resource})),
        "incomplete":results.incomplete.iter().map(|(k,r)|json!({"region":k.0.iter().map(atom_data).collect::<Vec<_>>(),"phase":r.phase,"resource":r.resource})).collect::<Vec<_>>()
    });
    if !results.coverage.is_empty() {
        summary["coverage"] = json!(results.coverage.iter().map(|(key,c)| json!({
            "identity":{"obligation":qualified(&key.0),"component":"coverage"},
            "outcome":if c.missing > 0 {"counterexample"} else if c.proved() {"proved"} else if c.inconclusive.is_some() {"inconclusive"} else {"unsupported"},
            "examinedGroups":c.examined,"missingGroups":{"count":c.missing,"exact":c.complete()},
            "complete":c.complete(),"noGroups":c.no_groups,"unsupportedGroups":c.unsupported,
            "reason":c.inconclusive.map(|r|json!({"phase":r.phase,"resource":r.resource}))
        })).collect::<Vec<_>>());
    }
    summary
}

/// Witnesses carry their own observation and producing occurrences. The world
/// used to refute consistency is explicitly different from a replayed conflict.
pub fn evidence_data(finding: &crate::Finding<'_>, keys: &SemanticKeys) -> Result<Value> {
    let observation = |o: &Observation| -> Result<Value> {
        let atoms = |atoms: &BTreeSet<GroundAtom>| -> Result<Vec<Value>> {
            Ok(atoms
                .iter()
                .map(|a| AtomKey::from_atom(keys, a))
                .collect::<std::result::Result<BTreeSet<_>, _>>()?
                .iter()
                .map(atom_data)
                .collect())
        };
        Ok(json!({"present":atoms(&o.present)?,"absent":atoms(&o.absent)?}))
    };
    let producers = finding
        .contributions
        .iter()
        .filter(|c| c.role == crate::Role::Producer)
        .map(|c| Ok(occurrence(keys.bindings().key(c.occurrence)?)))
        .collect::<Result<Vec<_>>>()?;
    if let Some(world) = &finding.unsupported_world {
        return Ok(
            json!({"kind":"unfounded-support-world","world":{"present":world.present.iter().map(atom_data).collect::<Vec<_>>(),"absent":world.absent.iter().map(atom_data).collect::<Vec<_>>()},"producers":producers}),
        );
    }
    Ok(match &finding.evidence {
        crate::Evidence::Coverage(c) => json!({
            "kind":if c.missing > 0 {"replayed-coverage-counterexamples"} else {"no-witness"},
            "component":"coverage", "missingGroups":{"count":c.missing,"exact":c.complete()},
            "complete":c.complete(), "unsupportedGroups":c.unsupported,
            "reason":c.inconclusive.map(|r|json!({"phase":r.phase,"resource":r.resource})),
            "examples":c.examples.iter().map(|e| Ok(json!({
                "group":e.group.iter().map(|id|Ok(constant(keys.constant(*id)?))).collect::<Result<Vec<_>>>()?,
                "observation":observation(&e.observation)?,
                "scope": match e.replay_scope { ReplayScope::WholeProgram=>"whole-program",ReplayScope::ConeOnly=>"cone-only" }
            }))).collect::<Result<Vec<_>>>()?
        }),
        crate::Evidence::Group(g) => match &g.outcome {
            VerifiedOutcome::Counterexample(c) => {
                json!({"kind":"replayed-counterexample","observation":observation(&c.observation)?,"tuples":c.tuples.iter().map(|a|Ok(atom_data(&AtomKey::from_atom(keys,a)?))).collect::<Result<Vec<_>>>()?,"scope":match c.replay_scope {ReplayScope::WholeProgram=>"whole-program",ReplayScope::ConeOnly=>"cone-only"},"producers":producers})
            }
            _ => json!({"kind":"no-witness","producers":producers}),
        },
        crate::Evidence::Region(r) => match &r.completion {
            CompletionOutcome::NoMeaning(n) => {
                json!({"kind":"no-meaning-observation","observation":observation(&n.observation)?,"producers":producers})
            }
            _ => json!({"kind":"no-witness","producers":producers}),
        },
    })
}

fn result_reason(result: &ScopedResult) -> Option<Value> {
    match result {
        ScopedResult::Inconclusive(r) => Some(json!({"phase":r.phase,"resource":r.resource})),
        ScopedResult::Unsupported(UnsupportedReason::UnfoundedSupport(_)) => {
            Some(json!({"kind":"unfounded-support"}))
        }
        ScopedResult::Unsupported(UnsupportedReason::UnsettledNegativeCycle) => {
            Some(json!({"kind":"unsettled-negative-cycle"}))
        }
        ScopedResult::Unsupported(UnsupportedReason::DependsOnUnsettled(regions)) => Some(
            json!({"kind":"unsettled-dependencies","regions":regions.iter().map(|r|r.0.iter().map(atom_data).collect::<Vec<_>>()).collect::<Vec<_>>()}),
        ),
        _ => None,
    }
}
