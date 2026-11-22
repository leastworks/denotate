//! Completion interpretations never masquerade as replayed finite derivations.
use crate::*;
use denotate_check::{AtomKey, GroundAtom, Inconclusive, Observation, completion_query::*};
use denotate_ir::*;
use serde_json::{Value, json};

pub struct CompletionFinding {
    pub finding: ContextFinding,
    pub evidence: Value,
}
fn cause_text(c: Inconclusive) -> String {
    if c.phase == "completion input contract" {
        "Universal results are incomplete because a selected assumption could not be determined on every input.".into()
    } else {
        exhaustion_text(c.phase, c.resource, c.details)
    }
}
fn reason(c: Inconclusive) -> Value {
    with_limit_details(
        json!({"phase":c.phase,"resource":c.resource,"message":cause_text(c)}),
        c.details,
    )
}
fn atom(a: &GroundAtom, keys: &SemanticKeys) -> Result<Value> {
    Ok(atom_data(&AtomKey::from_atom(keys, a)?))
}
fn observation(w: &Observation, keys: &SemanticKeys) -> Result<Value> {
    Ok(
        json!({"present":w.present.iter().map(|a|atom(a,keys)).collect::<Result<Vec<_>>>()?,"absent":w.absent.iter().map(|a|atom(a,keys)).collect::<Result<Vec<_>>>()?}),
    )
}
fn model(m: &Model, keys: &SemanticKeys, hypothesis: Option<RelationId>) -> Result<Value> {
    let mut values = m
        .interpretation()
        .map(|(a, v)| Ok((AtomKey::from_atom(keys, a)?, v)))
        .collect::<Result<Vec<_>>>()?;
    values.sort_by(|a, b| a.0.cmp(&b.0));
    let scope_atoms = m
        .scope_atoms()
        .map(|members| {
            let mut atoms = members
                .iter()
                .map(|a| AtomKey::from_atom(keys, a))
                .collect::<std::result::Result<Vec<_>, _>>()?;
            atoms.sort();
            Ok::<_, denotate_ir::KeyError>(atoms.iter().map(atom_data).collect::<Vec<_>>())
        })
        .transpose()?;
    Ok(
        json!({"kind":"completion-model","scope":match m.scope(){ModelScope::Classification=>"hypothesis-cone",ModelScope::ClassificationWithoutHypothesis=>"classification-without-hypothesis",ModelScope::Processing=>"accepted-processing",ModelScope::Property=>"property-cone",ModelScope::WholeProgram=>"whole-program",ModelScope::Assumption=>"assumption-cone",ModelScope::InputDomain=>"input-domain-cone"},
        "hypothesis":hypothesis.map(|h| atom(&GroundAtom::new(h,[]),keys)).transpose()?,
        "scopeAtoms":scope_atoms,"omittedInputRelations":m.omitted_input_relations().iter().map(|r|keys.relation(*r).map(crate::identity::relation)).collect::<std::result::Result<Vec<_>,_>>()?,"observation":observation(&m.observation(),keys)?,"interpretation":values.iter().map(|(a,v)|json!({"atom":atom_data(a),"value":v})).collect::<Vec<_>>(),"unlistedInScope":"false"}),
    )
}
fn rejection(m: &Model, keys: &SemanticKeys, h: Option<RelationId>) -> Result<Value> {
    Ok(
        json!({"kind":"rejected-observation", "scope":"hypothesis-cone",
        "observation":observation(&m.observation(),keys)?,
        "hypothesis":h.map(|h|atom(&GroundAtom::new(h,[]),keys)).transpose()?,
        "confirmedNoInterpretation":true,
        "withoutHypothesis":model(m,keys,None)?}),
    )
}
fn determinacy(r: &Report, keys: &SemanticKeys) -> Result<Value> {
    let relations = r
        .decisions
        .as_ref()
        .map(|rs| {
            let mut selected = rs
                .iter()
                .map(|id| keys.relation(*id))
                .collect::<std::result::Result<Vec<_>, _>>()?;
            selected.sort();
            Ok::<_, denotate_ir::KeyError>(
                selected
                    .into_iter()
                    .map(crate::identity::relation)
                    .collect::<Vec<_>>(),
            )
        })
        .transpose()?;
    Ok(
        json!({"kind":if relations.is_some(){"selected-relations"}else{"all-relations"},"relations":relations}),
    )
}
fn search<T>(s: &Search<T>, evidence: impl Fn(&T) -> Result<Value>) -> Result<Value> {
    Ok(match s {
        Search::None => json!({"state":"none"}),
        Search::NotAnalysed => json!({"state":"not-analysed"}),
        Search::Inconclusive(c) => json!({"state":"inconclusive","reason":reason(*c)}),
        Search::Exists(v) => json!({"state":"exists","evidence":evidence(v)?}),
    })
}
fn pair(p: &Pair, keys: &SemanticKeys, h: Option<RelationId>) -> Result<Value> {
    Ok(
        json!({"kind":"completion-ambiguity","first":model(&p.first,keys,h)?,"second":model(&p.second,keys,h)?}),
    )
}
fn kind(req: &Requirement) -> &'static str {
    match req {
        Requirement::NoRejections { .. } => "no-rejections",
        Requirement::Cardinality(r) => match r.kind() {
            Cardinality::Empty => "empty",
            Cardinality::AtMostOne => "at-most-one",
            Cardinality::AtLeastOne => "at-least-one",
            Cardinality::ExactlyOne => "exactly-one",
        },
    }
}
pub fn completion_summary(corpus: &Corpus, keys: &SemanticKeys, r: &Report) -> Result<Value> {
    let v = corpus.verification(r.verification).unwrap();
    let context = match r.context {
        Context::Permitted => json!({"state":"permitted"}),
        Context::EmptyUniverse => json!({"state":"empty-input-universe"}),
        Context::InconsistentAssumptions => json!({"state":"inconsistent-assumptions"}),
        Context::Inconclusive(c) => json!({"state":"inconclusive","reason":reason(c)}),
    };
    let classification = if let Some(c) = &r.classification {
        json!({"scope":"hypothesis-cone","state":if r.all_rejected(){"all-rejected"}else{"classified"},"accepted":search(&c.accepted,|m|model(m,keys,r.hypothesis))?,"rejected":search(&c.rejected,|m|rejection(m,keys,r.hypothesis))?,"noMeaning":search(&c.no_meaning,|w|Ok(json!({"kind":"completion-no-meaning","scope":"classification-without-hypothesis","observation":observation(w,keys)?})))?,"ambiguous":search(&c.ambiguous,|p|pair(p,keys,r.hypothesis))?})
    } else {
        json!({"state":"not-applicable"})
    };
    let meaning = if !r.meaning.applicable {
        json!({"state":"not-applicable","scope":"accepted-observations"})
    } else {
        let mut existence = search(&r.meaning.no_meaning, |w| {
            Ok(json!({"kind":"completion-no-meaning","observation":observation(w,keys)?}))
        })?;
        if existence["state"] == "none" {
            existence["state"] = json!("every-world");
        } else if existence["state"] == "exists" {
            existence["state"] = json!("no-meaning");
        }
        let mut uniqueness = search(&r.meaning.ambiguous, |p| pair(p, keys, r.hypothesis))?;
        if uniqueness["state"] == "none" {
            uniqueness["state"] = json!("at-most-one");
        } else if uniqueness["state"] == "exists" {
            uniqueness["state"] = json!("multiple");
        }
        json!({"scope":if r.hypothesis.is_some(){"accepted-observations"}else{"whole-program"},"existence":existence,"uniqueness":uniqueness})
    };
    let mut obligations = Vec::new();
    for (id, o) in &r.obligations {
        let state = if r.context != Context::Permitted {
            "not-analysed"
        } else if o.failed() {
            "counterexample"
        } else if o.not_analysed {
            "not-analysed"
        } else if !o.complete() {
            "inconclusive"
        } else if o.vacuous {
            "vacuous"
        } else {
            "proved"
        };
        let k = keys.obligation(*id)?;
        obligations.push(json!({"name":corpus.obligation(*id).unwrap().name,"identity":[k.0.namespace.as_ref(),k.0.name.as_ref()],"kind":kind(&o.requirement),"state":state,"complete":r.context==Context::Permitted&&o.complete(),"vacuous":o.vacuous&&r.context==Context::Permitted,
            "scope":if matches!(o.requirement,Requirement::NoRejections{..}){"permitted-observations"}else if r.hypothesis.is_some(){"accepted-observations-property-cone"}else{"property-cone"},"reasons":o.inconclusive.map(reason).into_iter().collect::<Vec<_>>(),"failures":o.parts.iter().filter(|p|p.failed).count()+usize::from(o.rejected.is_some())}));
    }
    let advisory = match &r.advisory {
        Advisory::NotRequested => json!({"state":"not-requested"}),
        Advisory::Checked {
            findings,
            incomplete,
        } => {
            json!({"state":if incomplete.is_some(){"incomplete"}else if findings.is_empty(){"none"}else{"findings"},"findings":findings.len(),"reason":incomplete.map(reason)})
        }
    };
    let dead = match &r.dead_producers {
        DeadProducerAdvisory::NotRequested => json!({"state":"not-requested"}),
        DeadProducerAdvisory::Checked {
            findings,
            incomplete,
        } => {
            json!({"state":if incomplete.is_some(){"incomplete"}else if findings.is_empty(){"none"}else{"findings"},"findings":findings.len(),"reason":incomplete.map(reason)})
        }
    };
    Ok(
        json!({"backend":{"backend":"sat","configuration":"original-completion-v1"},"semantics":"completion","determinacy":determinacy(r,keys)?,"hypothesis":r.hypothesis.map(|h| corpus.relation(h).unwrap().name.clone()),"hypothesisIdentity":r.hypothesis.map(|h|atom(&GroundAtom::new(h,[]),keys)).transpose()?,
        "verification":[keys.verification(v.id)?.0.namespace.as_ref(),keys.verification(v.id)?.0.name.as_ref()],"activeAssumptions":v.assumptions.iter().map(|id|corpus.assumption(*id).unwrap().name.clone()).collect::<Vec<_>>(),
        "state":if r.is_incomplete(){"incomplete"}else if r.has_failures(){"findings"}else if r.all_rejected(){"all-rejected"}else{"proved"},"hasFailures":r.has_failures(),"incomplete":r.is_incomplete(),"context":context,"classification":classification,"meaning":meaning,"obligations":obligations,
        "inputContract":{"complete":r.assumptions.iter().all(AssumptionAnalysis::certified),"assumptions":r.assumptions.iter().map(|a|assumption_data(a,keys)).collect::<Result<Vec<_>>>()?,"omittedInputDomains":r.ignored_input_domains.iter().map(|d|input_domain_data(d,keys)).collect::<Result<Vec<_>>>()?},
        "incompletePhases":r.incomplete.iter().map(|c|reason(*c)).collect::<Vec<_>>(),"notices":r.notices_not_analysed.iter().map(|id|json!({"name":corpus.notice(*id).unwrap().name,"state":"not-analysed"})).collect::<Vec<_>>(),"advisories":{"circularSupport":advisory,"deadProducers":dead}}),
    )
}

pub fn completion_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    r: &Report,
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<CompletionFinding>> {
    let mut out = assumption_findings(corpus, keys, r, names)?;
    let location = |id: OccurrenceId, role| Contribution {
        occurrence: id,
        role,
    };
    let mut base = vec![location(r.verification.into(), Role::Declaration)];
    if let Some(h) = r.hypothesis {
        base.push(location(h.into(), Role::Condition));
    }
    let add = |out: &mut Vec<CompletionFinding>,
               identity,
               kind,
               message: String,
               notes,
               contributions,
               evidence| {
        out.push(CompletionFinding {
            finding: ContextFinding {
                identity,
                kind,
                message,
                notes,
                contributions,
            },
            evidence,
        });
    };
    let obs_note = |w: &Observation| observation_note(corpus, names, w);
    if r.context == Context::InconsistentAssumptions || r.context == Context::EmptyUniverse {
        add(
            &mut out,
            Identity::InconsistentAssumptions,
            Kind::InconsistentAssumptions,
            "The selected input contract permits no observations.".into(),
            vec![],
            base.clone(),
            json!({"kind":"inconsistent-assumptions"}),
        );
        return Ok(out);
    }
    if r.all_rejected() {
        add(
            &mut out,
            Identity::AllRejected,
            Kind::AllRejected,
            "Every permitted input observation is rejected; processing is not applicable.".into(),
            vec![],
            base.clone(),
            json!({"kind":"all-rejected"}),
        );
    }
    if let Some(c) = &r.classification {
        if let Search::Exists(w) = &c.no_meaning {
            add(
                &mut out,
                Identity::CompletionMeaning("classification-no-meaning"),
                Kind::NoMeaning,
                "The classification equations have no interpretation even without the hypothesis."
                    .into(),
                vec![obs_note(w)?],
                base.clone(),
                json!({"kind":"completion-no-meaning","scope":"classification-without-hypothesis","observation":observation(w,keys)?}),
            );
        }
        if let Search::Exists(p) = &c.ambiguous {
            add(
                &mut out,
                Identity::CompletionMeaning("classification-ambiguity"),
                Kind::AmbiguousMeaning,
                "A permitted observation has several decision interpretations satisfying the hypothesis."
                    .into(),
                vec![obs_note(&p.first.observation())?],
                base.clone(),
                pair(p, keys, r.hypothesis)?,
            );
        }
    }
    if let Search::Exists(w) = &r.meaning.no_meaning {
        add(
            &mut out,
            Identity::CompletionMeaning("processing-no-meaning"),
            Kind::NoMeaning,
            "The processing equations have no interpretation for this observation.".into(),
            vec![obs_note(w)?],
            base.clone(),
            json!({"kind":"completion-no-meaning","observation":observation(w,keys)?}),
        );
    }
    if let Search::Exists(p) = &r.meaning.ambiguous {
        add(
            &mut out,
            Identity::CompletionMeaning("processing-ambiguity"),
            Kind::AmbiguousMeaning,
            "The processing equations have several decision interpretations for this observation."
                .into(),
            vec![obs_note(&p.first.observation())?],
            base.clone(),
            pair(p, keys, r.hypothesis)?,
        );
    }
    if r.is_incomplete() {
        let mut notes: Vec<_> = r.incomplete.iter().map(|c| cause_text(*c)).collect();
        let uncertain: Vec<_> = r.assumptions.iter().filter(|a| !a.certified()).collect();
        if !uncertain.is_empty() {
            notes.push(format!(
                "Unvalidated input contract: {}.",
                uncertain
                    .iter()
                    .map(|a| names(a.assumption.into()))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        add(
            &mut out,
            Identity::CompletionMeaning("incomplete"),
            Kind::Inconclusive,
            "Completion verification is incomplete.".into(),
            notes,
            base.clone(),
            json!({"kind":"incomplete","reasons":r.incomplete.iter().map(|c|reason(*c)).collect::<Vec<_>>(),"assumptions":uncertain.iter().map(|a|Identity::CompletionAssumption(a.assumption,"contract").data(keys)).collect::<Result<Vec<_>>>()?}),
        );
    }
    for (id, o) in &r.obligations {
        let mut contributions = vec![location((*id).into(), Role::Obligation)];
        if let Some(h) = r.hypothesis {
            contributions.push(location(h.into(), Role::Condition));
        }
        let declaration = corpus.obligation(*id).unwrap();
        let authored_message = if declaration.message_template.is_empty() {
            String::new()
        } else {
            format!(" {}", declaration.message_template)
        };
        if let Some(w) = &o.rejected {
            add(
                &mut out,
                Identity::Rejection(*id),
                Kind::Counterexample,
                format!(
                    "Obligation {} fails: a permitted input observation is rejected.{authored_message}",
                    declaration.name
                ),
                vec![obs_note(&w.observation())?],
                contributions.clone(),
                rejection(w, keys, r.hypothesis)?,
            );
        }
        for component in [
            Cardinality::Empty,
            Cardinality::AtLeastOne,
            Cardinality::AtMostOne,
        ] {
            let parts = o
                .parts
                .iter()
                .filter(|p| p.component == component && p.failed)
                .collect::<Vec<_>>();
            let batches = if component == Cardinality::AtMostOne {
                parts.iter().map(|p| vec![*p]).collect::<Vec<_>>()
            } else if parts.is_empty() {
                vec![]
            } else {
                vec![parts]
            };
            for parts in batches {
                let identity = match component {
                    Cardinality::Empty => Identity::Emptiness(*id),
                    Cardinality::AtLeastOne => Identity::Coverage(*id),
                    _ => {
                        if o.requirement.cardinality().unwrap().kind() == Cardinality::ExactlyOne {
                            Identity::Uniqueness {
                                obligation: *id,
                                tuple: parts[0].group.clone(),
                            }
                        } else {
                            Identity::Group {
                                obligation: *id,
                                tuple: parts[0].group.clone(),
                            }
                        }
                    }
                };
                let mut notes = Vec::new();
                let mut examples = Vec::new();
                for p in &parts {
                    if let Some(m) = &p.example {
                        let tuples = p
                            .tuples
                            .iter()
                            .filter(|a| m.value(a) == Some(true))
                            .map(|a| crate::evidence::atom_name(corpus, names, a))
                            .collect::<Result<Vec<_>>>()?;
                        notes.push(if component == Cardinality::AtLeastOne {
                            format!(
                                "Missing group: {}.",
                                p.group
                                    .iter()
                                    .map(|c| names((*c).into()))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        } else {
                            format!(
                                "Present tuple{}: {}{}.",
                                if tuples.len() == 1 { "" } else { "s" },
                                tuples
                                    .iter()
                                    .take(8)
                                    .cloned()
                                    .collect::<Vec<_>>()
                                    .join(", "),
                                if tuples.len() > 8 {
                                    format!("; +{} more", tuples.len() - 8)
                                } else {
                                    String::new()
                                }
                            )
                        });
                        notes.push(obs_note(&m.observation())?);
                        examples.push(json!({"model":model(m,keys,r.hypothesis)?,"group":p.group.iter().map(|c| keys.constant(*c).map(crate::identity::constant)).collect::<std::result::Result<Vec<_>,_>>()?,"presentTuples":p.tuples.iter().filter(|a|m.value(a)==Some(true)).map(|a|atom(a,keys)).collect::<Result<Vec<_>>>()?}));
                    }
                }
                let label = match component {
                    Cardinality::Empty => "a tuple is present",
                    Cardinality::AtLeastOne => "a group has no tuple",
                    _ => "several tuples overlap",
                };
                add(
                    &mut out,
                    identity,
                    Kind::Counterexample,
                    format!(
                        "Obligation {} fails: {label} in a completion interpretation.{authored_message}",
                        declaration.name
                    ),
                    notes,
                    contributions.clone(),
                    json!({"kind":"completion-model","scope":"property-cone","examples":examples,"count":parts.len(),"countKind":if o.complete(){"exact"}else{"at-least"},"omittedExamples":parts.iter().filter(|p|p.example.is_none()).count()}),
                );
            }
        }
        if o.no_groups {
            add(
                &mut out,
                Identity::Coverage(*id),
                Kind::EmptyGroupingDomain,
                format!(
                    "Obligation {} (coverage): no groups: the grouping domain is empty",
                    declaration.name
                ),
                vec![],
                contributions,
                json!({"kind":"empty-grouping-domain"}),
            );
        }
    }
    if let Advisory::Checked { findings, .. } = &r.advisory {
        for f in findings {
            let mut locations = base.clone();
            for id in f.cycle.iter().take(8) {
                locations.push(location(
                    r.program().original_rule(*id).unwrap().source.into(),
                    Role::Producer,
                ));
            }
            add(
                &mut out,
                Identity::CircularSupport(f.component.clone()),
                Kind::CircularSupport,
                "An accepted classification uses circular support.".into(),
                vec![obs_note(&f.model.observation())?],
                locations,
                model(&f.model, keys, r.hypothesis)?,
            );
        }
    }
    if let DeadProducerAdvisory::Checked { findings, .. } = &r.dead_producers {
        for f in findings {
            let outside = bounded_list(
                f.outside
                    .iter()
                    .map(|a| crate::evidence::atom_name(corpus, names, a))
                    .collect::<Result<Vec<_>>>()?,
            );
            add(&mut out,Identity::CompletionDeadProducer(f.rule),Kind::DeadProducer,
                "This producer instance never fires; its dependencies do not enter the classification scope.".into(),
                vec![format!("Positive premise {} has no possible support.",crate::evidence::atom_name(corpus,names,&f.missing)?),format!("For {}, this dead instance would link {outside} into the hypothesis cone.",crate::evidence::atom_name(corpus,names,&f.head)?)],
                vec![location(f.rule.into(),Role::Producer)],
                json!({"kind":"completion-dead-producer","head":atom(&f.head,keys)?,"missingPremise":atom(&f.missing,keys)?,"outside":f.outside.iter().map(|a|atom(a,keys)).collect::<Result<Vec<_>>>()?}));
        }
    }
    for finding in &mut out {
        if finding.evidence["kind"] == "completion-ambiguity" {
            finding.evidence["determinacy"] = determinacy(r, keys)?;
        }
    }
    Ok(out)
}

fn assumption_data(a: &AssumptionAnalysis, keys: &SemanticKeys) -> Result<Value> {
    Ok(
        json!({"identity":Identity::CompletionAssumption(a.assumption,"contract").data(keys)?,"complete":a.certified(),"ambiguous":search(&a.ambiguous,|v|Ok(json!({"kind":"completion-assumption-ambiguity","group":v.group.iter().map(|c|keys.constant(*c).map(crate::identity::constant)).collect::<std::result::Result<Vec<_>,_>>()?,"trueModel":model(&v.models.first,keys,None)?,"falseModel":model(&v.models.second,keys,None)?})))?,"noMeaning":search(&a.no_meaning,|w|Ok(json!({"kind":"completion-assumption-no-meaning","observation":observation(w,keys)?,"confirmedNoInterpretation":true})))?}),
    )
}
fn assumption_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    report: &Report,
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<CompletionFinding>> {
    let mut out = Vec::new();
    for a in &report.assumptions {
        let data = assumption_data(a, keys)?;
        for (phase, state) in [
            ("determinacy", &data["ambiguous"]),
            ("existence", &data["noMeaning"]),
        ] {
            let status = state["state"].as_str().unwrap();
            if status == "none" {
                continue;
            }
            let message = if status == "exists" {
                if phase == "determinacy" {
                    format!(
                        "Assumption {} has undetermined truth: its formula is true in one interpretation and false in another for the same input.",
                        names(a.assumption.into())
                    )
                } else {
                    format!(
                        "Assumption {} has no completion interpretation for an input observation.",
                        names(a.assumption.into())
                    )
                }
            } else {
                format!(
                    "Assumption {} could not be validated under completion: {}.",
                    names(a.assumption.into()),
                    state["reason"]["message"].as_str().unwrap_or("incomplete")
                )
            };
            let mut notes = vec![];
            if phase == "existence" {
                if let Search::Exists(w) = &a.no_meaning {
                    notes.push(observation_note(corpus, names, w)?);
                }
            }
            if phase == "determinacy" {
                if let Search::Exists(v) = &a.ambiguous {
                    notes.push(observation_note(
                        corpus,
                        names,
                        &v.models.first.observation(),
                    )?);
                    let group = v
                        .group
                        .iter()
                        .map(|c| names((*c).into()))
                        .collect::<Vec<_>>()
                        .join(", ");
                    notes.push(format!(
                        "A differing group is ({group}). Other helper values may differ."
                    ));
                    notes.push(format!(
                        "True formula: {}. False formula: {}.",
                        tuple_description(
                            corpus,
                            names,
                            &v.models.first,
                            corpus
                                .assumption(a.assumption)
                                .unwrap()
                                .restriction
                                .relation()
                        )?,
                        tuple_description(
                            corpus,
                            names,
                            &v.models.second,
                            corpus
                                .assumption(a.assumption)
                                .unwrap()
                                .restriction
                                .relation()
                        )?
                    ));
                }
            }
            out.push(CompletionFinding {
                finding: ContextFinding {
                    identity: Identity::CompletionAssumption(a.assumption, phase),
                    kind: if status == "exists" {
                        Kind::InvalidAssumption
                    } else {
                        Kind::UnvalidatedAssumption
                    },
                    message,
                    notes,
                    contributions: vec![Contribution {
                        occurrence: a.assumption.into(),
                        role: Role::Declaration,
                    }],
                },
                evidence: state[if status == "exists" {
                    "evidence"
                } else {
                    "reason"
                }]
                .clone(),
            });
        }
    }
    Ok(out)
}
fn tuple_description(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    m: &Model,
    relation: RelationId,
) -> Result<String> {
    let mut tuples = m
        .interpretation()
        .filter(|(a, v)| *v && a.relation == relation)
        .map(|(a, _)| crate::evidence::atom_name(corpus, names, a))
        .collect::<Result<Vec<_>>>()?;
    tuples.sort();
    Ok(bounded_list(tuples))
}
pub fn input_domain_data(d: &InputDomainIssue, keys: &SemanticKeys) -> Result<Value> {
    let failure = match &d.failure {
        InputDomainFailure::NotNeeded => json!({"state":"outside-verification-scope"}),
        InputDomainFailure::NoMeaning => {
            json!({"state":"no-meaning","confirmedNoInterpretation":true})
        }
        InputDomainFailure::Inconclusive(c) => json!({"state":"inconclusive","reason":reason(*c)}),
        InputDomainFailure::Ambiguous(p) => {
            let differing = p
                .first
                .interpretation()
                .find(|(a, v)| a.relation == d.provider && p.second.value(a) != Some(*v))
                .map(|(a, _)| atom(a, keys))
                .transpose()?;
            json!({"state":"ambiguous","differingTuple":differing,"first":model(&p.first,keys,None)?,"second":model(&p.second,keys,None)?})
        }
    };
    Ok(
        json!({"kind":"completion-input-domain","input":crate::identity::relation(keys.relation(d.input)?),"provider":crate::identity::relation(keys.relation(d.provider)?),"outcome":failure}),
    )
}
pub fn completion_input_domain_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    issues: &[InputDomainIssue],
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<CompletionFinding>> {
    issues
        .iter()
        .filter(|d| !matches!(d.failure, InputDomainFailure::NotNeeded))
        .map(|d| {
            let (kind, why) = match &d.failure {
                InputDomainFailure::Ambiguous(_) => (
                    Kind::InvalidInputDomain,
                    "has different tuple sets in two completion interpretations".into(),
                ),
                InputDomainFailure::NoMeaning => (
                    Kind::InvalidInputDomain,
                    "has no completion interpretation".into(),
                ),
                InputDomainFailure::Inconclusive(c) => (
                    Kind::Inconclusive,
                    exhaustion_text(c.phase, c.resource, c.details),
                ),
                InputDomainFailure::NotNeeded => unreachable!(),
            };
            let mut notes = vec![];
            if let InputDomainFailure::Ambiguous(p) = &d.failure {
                if let Some((a, _)) = p
                    .first
                    .interpretation()
                    .find(|(a, v)| a.relation == d.provider && p.second.value(a) != Some(*v))
                {
                    notes.push(format!(
                        "Differing tuple: {}.",
                        crate::evidence::atom_name(corpus, names, a)?
                    ));
                }
            }
            Ok(CompletionFinding {
                finding: ContextFinding {
                    identity: Identity::CompletionInputDomain(d.input),
                    kind,
                    message: format!(
                        "Domain provider {} for input {} {why}.",
                        names(d.provider.into()),
                        names(d.input.into())
                    ),
                    notes,
                    contributions: vec![
                        Contribution {
                            occurrence: d.input.into(),
                            role: Role::Declaration,
                        },
                        Contribution {
                            occurrence: d.provider.into(),
                            role: Role::Condition,
                        },
                    ],
                },
                evidence: input_domain_data(d, keys)?,
            })
        })
        .collect()
}

fn bounded_list(mut values: Vec<String>) -> String {
    if values.is_empty() {
        return "(none)".into();
    }
    values.sort();
    let count = values.len();
    values.truncate(8);
    if count > 8 {
        values.push(format!("… and {} more", count - 8));
    }
    values.join(", ")
}
fn observation_note(
    corpus: &Corpus,
    names: &dyn Fn(OccurrenceId) -> String,
    w: &Observation,
) -> Result<String> {
    let show = |items: &std::collections::BTreeSet<GroundAtom>| -> Result<String> {
        Ok(bounded_list(
            items
                .iter()
                .map(|a| crate::evidence::atom_name(corpus, names, a))
                .collect::<Result<Vec<_>>>()?,
        ))
    };
    Ok(format!(
        "Example input observation — present: {}; absent: {}.",
        show(&w.present)?,
        show(&w.absent)?
    ))
}

/// Bounded size report, separate from verdicts and evidence. Counts at an
/// unfinished descending round are observations, not lower bounds on its GFP.
pub fn completion_sizes(
    keys: &SemanticKeys,
    sizes: &denotate_check::CompletionSizeSnapshot,
) -> Result<Value> {
    let relation =
        |r: RelationId| -> Result<Value> { Ok(crate::identity::relation(keys.relation(r)?)) };
    let mut preparations = Vec::new();
    for p in &sizes.preparations {
        let mut rows = p.relations.iter().collect::<Vec<_>>();
        rows.sort_by(|(a, x), (b, y)| {
            y.observed
                .cmp(&x.observed)
                .then_with(|| keys.relation(**a).unwrap().cmp(keys.relation(**b).unwrap()))
        });
        let relations=rows.iter().take(32).map(|(id,r)| Ok(json!({"relation":relation(**id)?,"possibility":r.observed,"state":if r.fixed {"fixed-point"} else {"partial-round"},"round":r.round,"least":r.least,"leastCountKind":if p.least_complete {"exact"} else {"at-least"},"circularOnly":if r.fixed {r.circular} else {None},"observedOutsideLeast":r.circular,"example":r.example.as_ref().map(|a|atom(a,keys)).transpose()?}))).collect::<Result<Vec<_>>>()?;
        let mut components = Vec::new();
        for members in &p.components {
            let count = members
                .iter()
                .filter_map(|r| p.relations.get(r))
                .map(|r| r.observed)
                .sum::<usize>();
            let least = members
                .iter()
                .filter_map(|r| p.relations.get(r))
                .map(|r| r.least)
                .sum::<usize>();
            let fixed = members
                .iter()
                .all(|r| p.relations.get(r).is_some_and(|r| r.fixed));
            let circular = if fixed && p.least_complete {
                Some(count.saturating_sub(least))
            } else {
                None
            };
            let mut members = members.clone();
            members.sort_by_key(|r| keys.relation(*r).unwrap());
            let example = members
                .iter()
                .filter_map(|r| p.relations.get(r))
                .find_map(|r| r.example.as_ref());
            components.push((count,json!({"relations":members.iter().take(32).map(|r|relation(*r)).collect::<Result<Vec<_>>>()?,"omittedRelations":members.len().saturating_sub(32),"possibility":count,"least":least,"state":if fixed {"fixed-point"} else {"partial"},"circularOnly":circular,"example":example.map(|a|atom(a,keys)).transpose()?})));
        }
        components.sort_by(|a, b| {
            b.0.cmp(&a.0).then_with(|| {
                a.1["relations"]
                    .to_string()
                    .cmp(&b.1["relations"].to_string())
            })
        });
        preparations.push(json!({"scope":if p.static_provider {"static-provider"} else {"runtime"},"complete":p.complete,"atoms":p.atoms,"rules":p.rules,"possibilityObserved":p.relations.values().map(|r|r.observed).sum::<usize>(),"possibilityComplete":p.relations.values().all(|r|r.fixed),"countKind":if p.complete {"exact"} else {"at-least"},"leastComplete":p.least_complete,"leastError":p.least_error.as_ref().map(ToString::to_string),"relations":relations,"omittedRelations":rows.len().saturating_sub(32),"positiveRelationComponents":components.iter().take(32).map(|(_,v)|v).collect::<Vec<_>>(),"omittedComponents":components.len().saturating_sub(32)}));
    }
    Ok(
        json!({"preparations":preparations,"searches":sizes.searches.iter().map(|s|json!({"phase":s.phase,"variables":s.variables,"clauses":s.clauses,"literals":s.literals,"encodingsStarted":s.encodings})).collect::<Vec<_>>(),"omittedPreparations":sizes.omitted_preparations,"omittedSearches":sizes.omitted_searches}),
    )
}
