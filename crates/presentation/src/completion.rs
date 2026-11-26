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
    } else if c.resource == "work"
        && matches!(
            c.phase,
            "completion classification existence"
                | "completion processing existence"
                | "completion classification ambiguity"
                | "completion processing ambiguity"
                | "completion property"
                | "completion accepted observations"
                | "completion rejection"
        )
    {
        format!(
            "{} The work allowance is cumulative across this query; the subphase names the stopping operation, not where all work was spent.",
            exhaustion_text(c.phase, c.resource, c.details)
        )
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
mod evidence;
mod pruning;
pub use evidence::CompletionEvidenceOptions;
use evidence::Evidence;
fn observation(w: &Observation, keys: &SemanticKeys, evidence: &Evidence) -> Result<Value> {
    evidence.observation(w, keys)
}
fn model(
    m: &Model,
    keys: &SemanticKeys,
    h: Option<RelationId>,
    evidence: &Evidence,
) -> Result<Value> {
    evidence.model(m, keys, h, &[])
}
fn rejection(
    m: &Model,
    keys: &SemanticKeys,
    h: Option<RelationId>,
    evidence: &Evidence,
) -> Result<Value> {
    Ok(
        json!({"kind":"rejected-observation", "scope":"hypothesis-cone",
        "observation":observation(&evidence.relevant_observation(m),keys, evidence)?,
        "hypothesis":h.map(|h|atom(&GroundAtom::new(h,[]),keys)).transpose()?,
        "confirmedNoInterpretation":true,
        "withoutHypothesis":model(m,keys,None, evidence)?}),
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
fn pair(
    p: &Pair,
    keys: &SemanticKeys,
    h: Option<RelationId>,
    evidence: &Evidence,
) -> Result<Value> {
    let targets: Vec<_> = evidence.difference(p).into_iter().collect();
    Ok(
        json!({"kind":"completion-ambiguity","differingTuple":targets.first().map(|a|atom(a,keys)).transpose()?,"first":evidence.model(&p.first,keys,h,&targets)?,"second":evidence.model(&p.second,keys,h,&targets)?}),
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
fn summary_using(
    corpus: &Corpus,
    keys: &SemanticKeys,
    r: &Report,
    evidence: &Evidence,
) -> Result<Value> {
    let v = corpus.verification(r.verification).unwrap();
    let context = match r.context {
        Context::Permitted => json!({"state":"permitted"}),
        Context::EmptyUniverse => json!({"state":"empty-input-universe"}),
        Context::InconsistentAssumptions => json!({"state":"inconsistent-assumptions"}),
        Context::Inconclusive(c) => json!({"state":"inconclusive","reason":reason(c)}),
    };
    let classification = if let Some(c) = &r.classification {
        json!({"scope":"hypothesis-cone","state":if r.all_rejected(){"all-rejected"}else{"classified"},"accepted":search(&c.accepted,|m|model(m,keys,r.hypothesis, evidence))?,"rejected":search(&c.rejected,|m|rejection(m,keys,r.hypothesis, evidence))?,"noMeaning":search(&c.no_meaning,|w|Ok(json!({"kind":"completion-no-meaning","scope":"classification-without-hypothesis","observation":observation(w,keys, evidence)?})))?,"ambiguous":search(&c.ambiguous,|p|pair(p,keys,r.hypothesis, evidence))?})
    } else {
        json!({"state":"not-applicable"})
    };
    let meaning = if !r.meaning.applicable {
        json!({"state":"not-applicable","scope":"accepted-observations"})
    } else {
        let mut existence = search(&r.meaning.no_meaning, |w| {
            Ok(json!({"kind":"completion-no-meaning","observation":observation(w,keys, evidence)?}))
        })?;
        if existence["state"] == "none" {
            existence["state"] = json!("every-world");
        } else if existence["state"] == "exists" {
            existence["state"] = json!("no-meaning");
        }
        let mut uniqueness = search(&r.meaning.ambiguous, |p| {
            pair(p, keys, r.hypothesis, evidence)
        })?;
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
            "scope":if matches!(o.requirement,Requirement::NoRejections{..}){"permitted-observations"}else if r.hypothesis.is_some(){"accepted-observations-property-cone"}else{"property-cone"},"reasons":o.inconclusive.map(reason).into_iter().collect::<Vec<_>>(),"failureCountKind":if o.failures_truncated || !o.complete(){"at-least"}else{"exact"},"failureEnumerationComplete":o.complete() && !o.failures_truncated,"failures":o.parts.iter().filter(|p|p.failed).count()+usize::from(o.rejected.is_some())}));
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
    let mut summary = json!({"backend":{"backend":"sat","configuration":"original-completion-v1"},"semantics":"completion","determinacy":determinacy(r,keys)?,"hypothesis":r.hypothesis.map(|h| corpus.relation(h).unwrap().name.clone()),"hypothesisIdentity":r.hypothesis.map(|h|atom(&GroundAtom::new(h,[]),keys)).transpose()?,
        "verification":[keys.verification(v.id)?.0.namespace.as_ref(),keys.verification(v.id)?.0.name.as_ref()],"activeAssumptions":v.assumptions.iter().map(|id|corpus.assumption(*id).unwrap().name.clone()).collect::<Vec<_>>(),
        "state":if r.is_incomplete(){"incomplete"}else if r.has_failures(){"findings"}else if r.all_rejected(){"all-rejected"}else{"proved"},"hasFailures":r.has_failures(),"incomplete":r.is_incomplete(),"context":context,"classification":classification,"meaning":meaning,"obligations":obligations,
        "inputContract":{"complete":r.assumptions.iter().all(AssumptionAnalysis::certified),"assumptions":r.assumptions.iter().map(|a|assumption_data(a,keys, evidence)).collect::<Result<Vec<_>>>()?,"omittedInputDomains":r.ignored_input_domains.iter().map(|d|input_domain_using(d,keys,evidence)).collect::<Result<Vec<_>>>()?},
        "incompletePhases":r.incomplete.iter().map(|c|reason(*c)).collect::<Vec<_>>(),"notices":r.notices_not_analysed.iter().map(|id|json!({"name":corpus.notice(*id).unwrap().name,"state":"not-analysed"})).collect::<Vec<_>>(),"advisories":{"circularSupport":advisory,"deadProducers":dead}});
    if r.pruning.enabled {
        summary["simplifications"] = pruning::summary(r, keys)?;
    }
    if r.branches.enabled {
        summary["branches"] = json!({"splits":r.branches.splits,"leaves":r.branches.leaves,"pendingUnits":r.branches.pending_units,
            "records":r.branches.records.iter().map(|c|completion_branch_record(c,|a|atom(a,keys),|a|{let k=keys.assumption(a)?;Ok(json!([k.0.namespace.as_ref(),k.0.name.as_ref()]))})).collect::<Result<Vec<_>>>()?,
            "omittedRecords":r.branches.omitted_records});
    }
    Ok(summary)
}

fn findings_using(
    corpus: &Corpus,
    keys: &SemanticKeys,
    r: &Report,
    names: &dyn Fn(OccurrenceId) -> String,
    evidence: &Evidence,
) -> Result<Vec<CompletionFinding>> {
    let mut out = assumption_findings(corpus, keys, r, names, evidence)?;
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
                json!({"kind":"completion-no-meaning","scope":"classification-without-hypothesis","observation":observation(w,keys, evidence)?}),
            );
        }
        if let Search::Exists(p) = &c.ambiguous {
            add(
                &mut out,
                Identity::CompletionMeaning("classification-ambiguity"),
                Kind::AmbiguousMeaning,
                "A permitted observation has several decision interpretations satisfying the hypothesis."
                    .into(),
                vec![obs_note(&evidence.relevant_observation(&p.first))?],
                base.clone(),
                pair(p, keys, r.hypothesis, evidence)?,
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
            json!({"kind":"completion-no-meaning","observation":observation(w,keys, evidence)?}),
        );
    }
    if let Search::Exists(p) = &r.meaning.ambiguous {
        add(
            &mut out,
            Identity::CompletionMeaning("processing-ambiguity"),
            Kind::AmbiguousMeaning,
            "The processing equations have several decision interpretations for this observation."
                .into(),
            vec![obs_note(&evidence.relevant_observation(&p.first))?],
            base.clone(),
            pair(p, keys, r.hypothesis, evidence)?,
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
                rejection(w, keys, r.hypothesis, evidence)?,
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
                if o.failures_truncated {
                    notes.push("Stopped after the configured number of distinct failures for this obligation; more may exist.".into());
                }
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
                        notes.push(obs_note(&evidence.relevant_observation(m))?);
                        examples.push(json!({"model":evidence.model(m,keys,r.hypothesis,&p.tuples)?,"group":p.group.iter().map(|c| keys.constant(*c).map(crate::identity::constant)).collect::<std::result::Result<Vec<_>,_>>()?,"presentTuples":p.tuples.iter().filter(|a|m.value(a)==Some(true)).take(evidence.cap()).map(|a|atom(a,keys)).collect::<Result<Vec<_>>>()?,"omittedPresentTuples":p.tuples.iter().filter(|a|m.value(a)==Some(true)).count().saturating_sub(evidence.cap())}));
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
                    json!({"kind":"completion-model","scope":"property-cone","examples":examples,"count":parts.len(),"countKind":if o.complete() && !o.failures_truncated{"exact"}else{"at-least"},"omittedExamples":parts.iter().filter(|p|p.example.is_none()).count()}),
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
                vec![obs_note(&evidence.relevant_observation(&f.model))?],
                locations,
                model(&f.model, keys, r.hypothesis, evidence)?,
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
    if r.pruning.enabled {
        out.extend(pruning::findings(corpus, keys, r, names)?);
    }
    for finding in &mut out {
        if finding.evidence["kind"] == "completion-ambiguity" {
            finding.evidence["determinacy"] = determinacy(r, keys)?;
        }
    }
    Ok(out)
}

fn assumption_data(
    a: &AssumptionAnalysis,
    keys: &SemanticKeys,
    evidence: &Evidence,
) -> Result<Value> {
    Ok(
        json!({"identity":Identity::CompletionAssumption(a.assumption,"contract").data(keys)?,"complete":a.certified(),"ambiguous":search(&a.ambiguous,|v|Ok(json!({"kind":"completion-assumption-ambiguity","group":v.group.iter().map(|c|keys.constant(*c).map(crate::identity::constant)).collect::<std::result::Result<Vec<_>,_>>()?,"trueModel":model(&v.models.first,keys,None, evidence)?,"falseModel":model(&v.models.second,keys,None, evidence)?})))?,"noMeaning":search(&a.no_meaning,|w|Ok(json!({"kind":"completion-assumption-no-meaning","observation":observation(w,keys, evidence)?,"confirmedNoInterpretation":true})))?}),
    )
}
fn assumption_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    report: &Report,
    names: &dyn Fn(OccurrenceId) -> String,
    evidence: &Evidence,
) -> Result<Vec<CompletionFinding>> {
    let mut out = Vec::new();
    for a in &report.assumptions {
        let data = assumption_data(a, keys, evidence)?;
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
fn input_domain_using(
    d: &InputDomainIssue,
    keys: &SemanticKeys,
    evidence: &Evidence,
) -> Result<Value> {
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
            json!({"state":"ambiguous","differingTuple":differing,"first":model(&p.first,keys,None, evidence)?,"second":model(&p.second,keys,None, evidence)?})
        }
    };
    Ok(
        json!({"kind":"completion-input-domain","input":crate::identity::relation(keys.relation(d.input)?),"provider":crate::identity::relation(keys.relation(d.provider)?),"outcome":failure}),
    )
}
fn input_domain_findings_using(
    corpus: &Corpus,
    keys: &SemanticKeys,
    issues: &[InputDomainIssue],
    names: &dyn Fn(OccurrenceId) -> String,
    evidence: &Evidence,
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
                evidence: input_domain_using(d, keys, &evidence)?,
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
                .take(8)
                .map(|a| crate::evidence::atom_name(corpus, names, a))
                .collect::<Result<Vec<_>>>()?,
        ))
    };
    Ok(format!(
        "Example input observation — present: {}; absent: {}.",
        format!(
            "{}{}",
            show(&w.present)?,
            if w.present.len() > 8 {
                format!("; +{} more", w.present.len() - 8)
            } else {
                String::new()
            }
        ),
        format!(
            "{}{}",
            show(&w.absent)?,
            if w.absent.len() > 8 {
                format!("; +{} more", w.absent.len() - 8)
            } else {
                String::new()
            }
        )
    ))
}

/// Bounded size report, separate from verdicts and evidence. Counts at an
/// unfinished descending round are observations, not lower bounds on its GFP.
pub fn completion_sizes(
    keys: &SemanticKeys,
    sizes: &denotate_check::CompletionSizeSnapshot,
) -> Result<Value> {
    completion_sizes_with_explanations(keys, sizes, |o| {
        completion_odd_explanation(
            o,
            |a| atom(a, keys),
            |r| Ok(crate::identity::rule(keys.rule(r)?)),
            |r| Ok(crate::identity::relation(keys.relation(r)?)),
            |g| {
                Ok(
                    json!({"relation":crate::identity::relation(keys.relation(g.relation)?),
                "values":g.values.iter().map(|v| keys.constant(*v).map(crate::identity::constant)).collect::<std::result::Result<Vec<_>,_>>()?,
                "assumption":g.assumption.map(|a|keys.assumption(a).map(|k|json!([k.0.namespace.as_ref(),k.0.name.as_ref()]))).transpose()?,
                "declared":g.declared}),
                )
            },
        )
    })
}
pub fn completion_sizes_with_explanations(
    keys: &SemanticKeys,
    sizes: &denotate_check::CompletionSizeSnapshot,
    explanation: impl Fn(&denotate_check::CompletionOddExplanation) -> Result<Value>,
) -> Result<Value> {
    let relation =
        |r: RelationId| -> Result<Value> { Ok(crate::identity::relation(keys.relation(r)?)) };
    let preparation_work = sizes.preparation_work.as_ref().map(|w| -> Result<Value> {
        let mut rows = w.join_rules.iter().map(|((rule, stage), work)| Ok((keys.rule(*rule)?, *stage, *work))).collect::<Result<Vec<_>>>()?;
        rows.sort_by(|a,b| b.2.work.cmp(&a.2.work).then_with(||a.0.cmp(b.0)).then_with(||a.1.cmp(b.1)));
        Ok(json!({"work":w.work,"workByStage":w.by_stage,"workByPhase":w.by_phase,"elapsedMsByStage":w.time_by_stage.iter().map(|(k,v)|(*k,v.as_secs_f64()*1000.0)).collect::<std::collections::BTreeMap<_,_>>(),"rejectedWorkByPhase":w.rejected_by_phase,"lastStage":w.last_stage,"topJoinRules":rows.iter().take(32).map(|(rule,stage,work)|json!({"rule":crate::identity::rule(rule),"stage":stage,"work":work.work,"calls":work.calls})).collect::<Vec<_>>(),"omittedJoinRules":rows.len().saturating_sub(32)}))
    }).transpose()?;
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
        preparations.push(json!({"scope":if p.static_provider {"static-provider"} else {"runtime"},"provider":p.provider.map(relation).transpose()?,"work":p.work,"workByStage":p.work_by_stage,"error":p.error.as_ref().map(ToString::to_string),"complete":p.complete,"atoms":p.atoms,"rules":p.rules,"peakPossibilityAtoms":p.peak_possibility_atoms,"possibilityObserved":p.relations.values().map(|r|r.observed).sum::<usize>(),"possibilityComplete":p.relations.values().all(|r|r.fixed),"countKind":if p.complete {"exact"} else {"at-least"},"leastEnabled":p.least_enabled,"leastComplete":p.least_complete,"leastError":p.least_error.as_ref().map(ToString::to_string),"relations":relations,"omittedRelations":rows.len().saturating_sub(32),"positiveRelationComponents":components.iter().take(32).map(|(_,v)|v).collect::<Vec<_>>(),"omittedComponents":components.len().saturating_sub(32)}));
    }
    Ok(
        json!({"preparationWork":preparation_work,"preparations":preparations,"searches":sizes.searches.iter().map(|s| -> Result<Value> { Ok(json!({"phase":s.phase,"branchDepth":s.branch_depth,"solveMs":s.solve_time.as_secs_f64()*1000.0,"solveTimings":s.solve_timings.iter().map(|t|json!({"remainingMsAtStart":t.remaining_at_start.map(|d|d.as_secs_f64()*1000.0),"elapsedMs":t.elapsed.as_secs_f64()*1000.0,"overrunMs":t.overrun.as_secs_f64()*1000.0})).collect::<Vec<_>>(),"omittedSolveTimings":s.omitted_solve_timings,"elapsedMs":s.elapsed.as_secs_f64()*1000.0,"work":s.work,"workByPhase":s.work_by_phase,"variables":s.variables,"clauses":s.clauses,"literals":s.literals,"encodingsStarted":s.encodings,"encodingDetails":s.encoding_details.iter().map(|e|json!({"purpose":e.purpose,"complete":e.complete,"atoms":e.atoms,"inputAtoms":e.input_atoms,"foldedTrue":e.folded_true,"foldedFalse":e.folded_false,"variables":e.variables,"clauses":e.clauses})).collect::<Vec<_>>(),"existence":completion_existence_stats(&s.existence, relation, &explanation)?,"omittedEncodings":s.omitted_encodings})) }).collect::<Result<Vec<_>>>()?,"omittedPreparations":sizes.omitted_preparations,"omittedSearches":sizes.omitted_searches}),
    )
}

pub fn completion_summary(corpus: &Corpus, keys: &SemanticKeys, report: &Report) -> Result<Value> {
    summary_using(
        corpus,
        keys,
        report,
        &Evidence::new(Default::default(), report.decisions.as_ref(), false),
    )
}
pub fn completion_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    report: &Report,
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<CompletionFinding>> {
    findings_using(
        corpus,
        keys,
        report,
        names,
        &Evidence::new(Default::default(), report.decisions.as_ref(), false),
    )
}
/// One registry for summary and diagnostics. Model references are local to this
/// result; finding identities remain the authored verification/obligation keys.
pub fn completion_presentation(
    corpus: &Corpus,
    keys: &SemanticKeys,
    report: &Report,
    names: &dyn Fn(OccurrenceId) -> String,
    options: CompletionEvidenceOptions,
) -> Result<(Vec<CompletionFinding>, Value)> {
    let evidence = Evidence::new(options, report.decisions.as_ref(), true);
    let findings = findings_using(corpus, keys, report, names, &evidence)?;
    let mut summary = summary_using(corpus, keys, report, &evidence)?;
    summary["completionEvidence"] = evidence.finish(keys)?;
    Ok((findings, summary))
}
pub fn input_domain_data(d: &InputDomainIssue, keys: &SemanticKeys) -> Result<Value> {
    input_domain_using(d, keys, &Evidence::new(Default::default(), None, false))
}

/// Shared bounded provider-failure evidence, including preparation failures.
pub fn completion_input_domain_presentation(
    corpus: &Corpus,
    keys: &SemanticKeys,
    issues: &[InputDomainIssue],
    names: &dyn Fn(OccurrenceId) -> String,
    options: CompletionEvidenceOptions,
) -> Result<(Vec<CompletionFinding>, Vec<Value>, Value)> {
    let evidence = Evidence::new(options, None, true);
    let findings = input_domain_findings_using(corpus, keys, issues, names, &evidence)?;
    let data = issues
        .iter()
        .map(|i| input_domain_using(i, keys, &evidence))
        .collect::<Result<Vec<_>>>()?;
    Ok((findings, data, evidence.finish(keys)?))
}
pub fn completion_input_domain_findings(
    corpus: &Corpus,
    keys: &SemanticKeys,
    issues: &[InputDomainIssue],
    names: &dyn Fn(OccurrenceId) -> String,
) -> Result<Vec<CompletionFinding>> {
    input_domain_findings_using(
        corpus,
        keys,
        issues,
        names,
        &Evidence::new(Default::default(), None, false),
    )
}

/// Bounded component details are observations; oddComponents counts parity-
/// inconsistent SCCs, not all elementary cycles.
pub fn completion_existence_stats(
    s: &denotate_check::CompletionExistenceStats,
    relation: impl Fn(RelationId) -> Result<Value>,
    explanation: impl Fn(&denotate_check::CompletionOddExplanation) -> Result<Value>,
) -> Result<Value> {
    let detail = |c: &denotate_check::CompletionComponentStats| -> Result<Value> {
        Ok(
            json!({"scope":c.scope,"context":c.context,"view":c.view,"oddExplanation":c.odd_explanation.as_deref().map(&explanation).transpose()?,"index":c.index,"atoms":c.atoms,"rules":c.rules,"boundary":c.boundary,
            "relations":c.relations.iter().map(|r|relation(*r)).collect::<Result<Vec<_>>>()?,
            "omittedRelations":c.relation_count.saturating_sub(c.relations.len()),
            "query":if c.query.is_empty(){"existence"}else{c.query},"elapsedMs":c.elapsed.as_secs_f64()*1000.0,"variables":c.variables,"clauses":c.clauses,"duplicatedAtoms":c.duplicated_atoms,"oddComponents":((c.query.is_empty() || c.query == "hypothesis-model-coverage") && c.state != "analysing").then_some(c.odd_components),"oddAtoms":((c.query.is_empty() || c.query == "hypothesis-model-coverage") && c.state != "analysing").then_some(c.odd_atoms),"state":c.state}),
        )
    };
    Ok(
        json!({"coupledFallbackSkipped":s.coupled_fallback_skipped,"uniqueComponents":s.unique_components,"sharedAtoms":s.shared_atoms,"components":s.components,"totalComponents":s.total_components,"fallbackComponents":s.fallback_components,
        "rounds":s.rounds,"cubes":s.cubes,"pins":s.pins,"maxPins":s.max_pins,"validationWork":s.validation_work,
        "liftingAttempts":s.lifting_attempts,"liftedPins":s.lifted_pins,
        "currentComponent":s.current_component.as_ref().map(&detail).transpose()?,
        "componentDetails":s.component_details.iter().map(detail).collect::<Result<Vec<_>>>()?,"omittedComponents":s.omitted_components}),
    )
}

/// Format structural odd-cycle explanations without introducing source IO.
pub fn completion_odd_explanation(
    o: &denotate_check::CompletionOddExplanation,
    atom: impl Fn(&GroundAtom) -> Result<Value>,
    source: impl Fn(RuleId) -> Result<Value>,
    relation: impl Fn(RelationId) -> Result<Value>,
    group: impl Fn(&denotate_check::CompletionGuardGroup) -> Result<Value>,
) -> Result<Value> {
    let cycles = o.cycles.iter().map(|cycle| cycle.iter().map(|e| {
        let producers=e.producers.iter().map(|p| Ok(json!({
            "source":p.source.map(&source).transpose()?,
            "guards":p.guards.iter().map(|(a,negative)| Ok(json!({"atom":atom(a)?,"negative":negative}))).collect::<Result<Vec<_>>>()?,
            "omittedGuards":p.omitted_guards
        }))).collect::<Result<Vec<_>>>()?;
        Ok(json!({"from":atom(&e.from)?,"to":atom(&e.to)?,"negative":e.negative,
            "producers":producers,"producerCount":e.producer_count,"omittedProducers":e.producer_count-e.producers.len()}))
    }).collect::<Result<Vec<_>>>()).collect::<Result<Vec<_>>>()?;
    Ok(json!({
        "oddComponents":o.odd_components,"componentsWithCyclesFound":o.witnessed_components,"cycles":cycles,"distinctCyclesFound":o.found,"cycleCountKind":"lower-bound","cycleLimit":3,
        "omittedLongCycles":o.omitted_cycles,"searchIncomplete":o.incomplete,
        "negativeRelations":o.negative_relations.iter().map(|((a,b),n)|Ok(json!({"consumer":relation(*a)?,"provider":relation(*b)?,"occurrences":n}))).collect::<Result<Vec<_>>>()?,
        "inputGroups":o.input_groups.iter().map(|(g,n)|Ok(json!({"group":group(g)?,"edges":n}))).collect::<Result<Vec<_>>>()?,
        "histogramsComplete":o.histograms_complete,
        "omittedNegativeRelations":o.omitted_negative_relations,"omittedInputGroups":o.omitted_input_groups,
        "guardMeaning":"Other conjuncts of each producer; falsifying any disables that producer. Cutting an edge requires disabling every producer. Input groups are structural reachability candidates, not certified cuts."
    }))
}

pub fn completion_pruning_component(
    c: &PruningComponent,
    atom: impl Fn(&GroundAtom) -> Result<Value>,
) -> Result<Value> {
    Ok(json!({
        "kind":"completion-pruning","scope":c.scope,
        "context":match c.context {PruningContext::World=>"W",PruningContext::Hypothesis=>"W+H"},
        "representative":atom(&c.representative)?,"atoms":c.atoms,"rules":c.rules,"componentKind":c.kind,
        "discoveryComplete":c.discovery_complete,"candidateHeads":c.candidate_heads,"candidateProducers":c.candidate_producers,
        "candidateExamples":c.candidate_examples.iter().map(&atom).collect::<Result<Vec<_>>>()?,
        "omittedCandidateHeads":c.candidate_heads.saturating_sub(c.candidate_examples.len()),
        "considered":c.considered,"proved":c.proved,"removedInstances":c.removed,"removedBodyLiterals":c.removed_literals,
        "lastHead":c.last_head.as_ref().map(&atom).transpose()?,
        "cutoff":c.cutoff.map(reason),"elapsedMs":c.elapsed.as_secs_f64()*1000.0,
    }))
}

fn completion_pruned_producer(
    p: &denotate_check::completion_query::PrunedProducer,
    atom: &impl Fn(&GroundAtom) -> Result<Value>,
) -> Result<Value> {
    Ok(json!({"context":p.context,"head":atom(&p.head)?,
        "originalBody":p.original_body.iter().map(|(a,positive)| -> Result<Value> {Ok(json!({"atom":atom(a)?,"positive":positive}))}).collect::<Result<Vec<_>>>()?,
        "omittedBodyLiterals":p.omitted_body_literals}))
}

fn completion_forcing(
    records: &[denotate_check::completion_query::ForcingRecord],
    atom: &impl Fn(&GroundAtom) -> Result<Value>,
) -> Result<Vec<Value>> {
    records.iter().map(|r| Ok(json!({
        "context":r.context,"candidates":r.candidates,"attempted":r.attempted,
        "forced":r.forced,"forcedWitnesses":r.forced_witnesses,"noModel":r.no_model,
        "examples":r.examples.iter().map(|(a,v)|Ok(json!({"atom":atom(a)?,"value":v}))).collect::<Result<Vec<_>>>()?,
        "omitted":r.omitted,"cutoff":r.cutoff.map(reason),
        "shadowCache":{"queries":r.cache.queries,"modelHits":r.cache.model_hits,"coreHits":r.cache.core_hits,
            "checkedHits":r.cache.checked_hits,"mismatches":r.cache.mismatches,"models":r.cache.models,"cores":r.cache.cores,
            "skippedModels":r.cache.skipped_models,"skippedCores":r.cache.skipped_cores,
            "enforcedHits":r.cache.enforced_hits,"sampledHits":r.cache.sampled_hits}
    }))).collect()
}

fn completion_split_child(
    c: &denotate_check::completion_query::SplitChild,
    atom: &impl Fn(&GroundAtom) -> Result<Value>,
) -> Result<Value> {
    Ok(json!({
        "child":c.child,"context":c.context,"rest":c.rest,"forcing":completion_forcing(&c.forcing,atom)?,
        "pruningAttempts":c.pruning_attempts,"pruningProved":c.pruning_proved,
        "removedProducers":c.removed_producers,"removedLiterals":c.removed_literals,
        "removedProducerExamples":c.removed_producer_examples.iter().map(|p|completion_pruned_producer(p,atom)).collect::<Result<Vec<_>>>()?,
        "omittedProducerExamples":c.omitted_producer_examples,
        "prunedHeads":c.pruned_heads.iter().map(atom).collect::<Result<Vec<_>>>()?,
        "omittedPrunedHeads":c.omitted_pruned_heads,
        "targetAtoms":c.target_atoms,"settledTargetAtoms":c.settled_target_atoms,
        "disabledEdges":c.disabled_edges,"cyclesCut":c.cycles_cut,"complete":c.complete,"cutoff":c.cutoff.map(reason),
        "omittedDerivedGuards":c.omitted_derived_guards,"derivedGuardsComplete":c.derived_guards_complete
    }))
}

pub fn completion_branch_record(
    c: &denotate_check::completion_query::BranchRecord,
    atom: impl Fn(&GroundAtom) -> Result<Value>,
    assumption: impl Fn(denotate_ir::AssumptionId) -> Result<Value>,
) -> Result<Value> {
    Ok(
        json!({"kind":"completion-branch","id":c.id,"parent":c.parent,"closedChildren":c.closed_children,
        "forcing":completion_forcing(&c.forcing,&atom)?,
        "splitKind":c.split_kind,"assumption":c.assumption.map(&assumption).transpose()?,
        "runnerUp":c.runner_up.as_ref().map(|r| -> Result<Value> { Ok(json!({"split":atom(&r.split)?,"assumption":r.assumption.map(&assumption).transpose()?,"children":r.children,"guardedEdges":r.guarded_edges,"hasRest":r.has_rest})) }).transpose()?,
        "candidates":c.candidates.iter().map(|r| -> Result<Value> { Ok(json!({
            "split":atom(&r.split)?, "assumption":r.assumption.map(&assumption).transpose()?,
            "context":r.context,"state":r.state,"children":r.children,"guardedEdges":r.guarded_edges,
            "checkedChildren":r.checked_children,"disabledEdges":r.disabled_edges,
            "minimumDisabled":r.minimum_disabled,"cyclesCutEveryChild":r.cycles_cut_every_child,
            "selected":r.selected,"cutoff":r.cutoff.map(reason),
            "pruningAttempts":r.pruning_attempts,"pruningProved":r.pruning_proved,"formula":r.formula,
            "childTrials":r.child_trials.iter().map(|c| completion_split_child(c, &atom)).collect::<Result<Vec<_>>>()?,
            "derivedGuards":r.derived_guards.iter().map(|g|Ok(json!({"atom":atom(&g.atom)?,"child":g.child,"acyclicUpstream":g.acyclic_upstream}))).collect::<Result<Vec<_>>>()?,
            "omittedDerivedGuards":r.omitted_derived_guards,"derivedGuardsComplete":r.derived_guards_complete
        })) }).collect::<Result<Vec<_>>>()?,"omittedCandidates":c.omitted_candidates,
        "values":c.values.iter().map(&atom).collect::<Result<Vec<_>>>()?,"omittedValues":c.omitted_values,
        "mapping":c.mapping.iter().map(|(a,i)|Ok(json!({"member":atom(a)?,"input":atom(i)?}))).collect::<Result<Vec<_>>>()?,"omittedMapping":c.omitted_mapping,
        "hasRest":c.has_rest,"rest":c.rest,"preparationWork":c.preparation_work,"searchWork":c.search_work,
        "phase":c.phase,"depth":c.depth,"state":c.state,
        "pins":c.pins.iter().map(|(a,v)|Ok(json!({"atom":atom(a)?,"value":v}))).collect::<Result<Vec<_>>>()?,
        "omittedPins":c.omitted_pins,"split":c.split.as_ref().map(&atom).transpose()?,
        "children":c.children,"guardedEdges":c.guarded_edges,"work":c.work,
        "elapsedMs":c.elapsed.as_secs_f64()*1000.0,"cutoff":c.cutoff.map(reason),
        "rankingGap":c.ranking_gap.as_ref().map(|g| -> Result<Value> { Ok(json!({
            "reason":g.reason,"targets":g.targets,
            "witness":g.witness.iter().map(&atom).collect::<Result<Vec<_>>>()?,"omittedWitness":g.omitted_witness,
            "guardedEdges":g.guarded_edges,"inputs":g.inputs,"formulas":g.formulas})) }).transpose()?}),
    )
}
