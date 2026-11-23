//! Static eligibility is determined under completion before runtime inputs exist.
use super::*;
use denotate_ir::{Literal, Term};
use queries::{Run, checked_assignment};

#[derive(Debug, Clone)]
pub enum InputDomainFailure {
    Ambiguous(Pair),
    NoMeaning,
    Inconclusive(Inconclusive),
    NotNeeded,
}
#[derive(Debug, Clone)]
pub struct InputDomainIssue {
    pub input: RelationId,
    pub provider: RelationId,
    pub failure: InputDomainFailure,
}
pub(super) enum Inputs {
    Ready(GroundProgram, Vec<InputDomainIssue>),
    Invalid(Vec<InputDomainIssue>),
}

pub(super) fn prepare(
    corpus: &Corpus,
    domains: &crate::ground::CompletionDomains,
    original: &Arc<crate::ground::OriginalDependencies>,
    verification: VerificationId,
    limits: &Limits,
    config: &QueryLimits,
    planning_roots: &BTreeSet<RelationId>,
    b: &mut Budget<'_>,
) -> Result<Inputs> {
    b.completion_stage("input-scope");
    let mut needed = planning_roots.clone();
    let v = corpus.verification(verification).unwrap();
    needed.extend(
        v.assumptions
            .iter()
            .map(|id| corpus.assumption(*id).unwrap().restriction.relation()),
    );
    needed.extend(
        v.obligations
            .iter()
            .map(|id| corpus.obligation(*id).unwrap().requirement.relation()),
    );
    needed.extend(v.options.hypothesis);
    if let Some(ds) = &v.options.decisions {
        needed.extend(ds);
    }
    // A cheap conservative first pass. Invalid providers get a live-instance
    // reachability test below, so a dead producer alone cannot block preparation.
    for rule in corpus.rules() {
        let mut instantiated = true;
        for a in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
            for t in a.arguments() {
                b.tick("completion input scope")?;
                if let Term::Variable { sort, .. } = t.value() {
                    instantiated &= domains.values().get(sort).is_some_and(|d| !d.is_empty());
                }
            }
        }
        if instantiated {
            needed.extend(rule.body.iter().map(|l| l.atom().relation()));
        }
    }
    for r in corpus.relations() {
        if r.input_cardinality.is_some() || !v.notices.is_empty() {
            needed.insert(r.id);
        }
    }
    let mut eligibility = BTreeMap::new();
    let mut ignored = Vec::new();
    let mut issues = Vec::new();
    let mut dependencies: Option<BTreeMap<RelationId, BTreeSet<RelationId>>> = None;
    for r in corpus.relations().filter(|r| r.input_domain.is_some()) {
        b.completion_stage("provider-scope");
        b.tick("completion input domains")?;
        let provider = r.input_domain.unwrap();
        if !needed.contains(&r.id) {
            ignored.push(InputDomainIssue {
                input: r.id,
                provider,
                failure: InputDomainFailure::NotNeeded,
            });
            eligibility.insert(r.id, BTreeSet::new());
            continue;
        }
        let result: Result<_> = (|| {
            let started = b.used();
            let mut scope = BTreeSet::new();
            let mut pending = vec![provider];
            let scoped: Result<()> = (|| {
                // Lazy, shared by needed providers only. Reverse-declared chains
                // otherwise require one whole-corpus scan per dependency depth.
                if dependencies.is_none() {
                    let mut index = BTreeMap::<RelationId, BTreeSet<RelationId>>::new();
                    for rule in corpus.rules() {
                        b.charge(rule.body.len() + 1, "completion provider index")?;
                        index
                            .entry(rule.head.relation())
                            .or_default()
                            .extend(rule.body.iter().map(|l| l.atom().relation()));
                    }
                    dependencies = Some(index);
                }
                let dependencies = dependencies.as_ref().unwrap();
                while let Some(relation) = pending.pop() {
                    b.tick("completion provider relations")?;
                    if scope.insert(relation) {
                        for dependency in dependencies.get(&relation).into_iter().flatten() {
                            b.tick("completion provider relations")?;
                            pending.push(*dependency);
                        }
                    }
                }
                Ok(())
            })();
            let scope_work = b.used().saturating_sub(started);
            if let Err(error) = &scoped {
                if let Some(sink) = &limits.completion_sizes {
                    sink.preparation(crate::CompletionPreparationSize {
                        static_provider: true,
                        provider: Some(provider),
                        work: scope_work,
                        work_by_stage: BTreeMap::from([("provider-scope", scope_work)]),
                        error: Some(error.clone()),
                        ..Default::default()
                    });
                }
            }
            scoped?;
            b.completion_stage("provider-grounding");
            let p = GroundProgram::prepare_completion_with_inputs(
                corpus,
                domains,
                None,
                Some(crate::ground::StaticScope {
                    relations: &scope,
                    provider,
                    work: scope_work,
                }),
                b,
            )?;
            b.completion_stage("provider-query");
            // Only a reachability bound if the provider is invalid. Never used as
            // a verification's input universe or as a presented observation.
            eligibility.insert(
                r.id,
                p.rules()
                    .filter(|rule| rule.head.atom.relation == provider)
                    .map(|rule| GroundAtom::new(r.id, rule.head.atom.arguments.clone()))
                    .collect(),
            );
            let members = Arc::new(
                p.dependency_cone_with_budget(
                    p.atoms().filter(|a| a.relation == provider).cloned(),
                    b,
                )?
                .facts,
            );
            let mut e = Engine::skeleton(
                corpus,
                original.clone(),
                verification,
                p,
                limits,
                config.clone(),
                b,
            )?;
            let cone = Arc::make_mut(&mut e.cone);
            cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
            let mut run = Run::universe(&e, b)?;
            run.label("completion input provider");
            let encoded = encoding::encode_named(
                &e.cone,
                &mut run.cnf,
                run.truth,
                Some(&run.world.vars),
                run.budget,
                "input-domain",
            )?;
            if !run.solve(&[])? {
                return Ok(Err(InputDomainFailure::NoMeaning));
            }
            let first = checked_assignment(&e.cone, &encoded, &run.cnf, run.budget)?;
            let mut diff = Vec::new();
            let mut tuples = BTreeSet::new();
            for (i, a) in e.cone.atoms.iter().enumerate() {
                run.budget.tick("completion provider determinacy")?;
                if a.relation == provider {
                    diff.push(if first[i] {
                        !encoded.vars[i]
                    } else {
                        encoded.vars[i]
                    });
                    if first[i] {
                        tuples.insert(GroundAtom::new(r.id, a.arguments.clone()));
                    }
                }
            }
            run.cnf.clause(diff, run.budget)?;
            if run.solve(&[])? {
                let second = checked_assignment(&e.cone, &encoded, &run.cnf, run.budget)?;
                let mut first = e.model(first, ModelScope::InputDomain);
                first.members = Some(members.clone());
                let mut second = e.model(second, ModelScope::InputDomain);
                second.members = Some(members);
                return Ok(Err(InputDomainFailure::Ambiguous(Pair { first, second })));
            }
            Ok(Ok(tuples))
        })();
        match result {
            Ok(Ok(tuples)) => {
                eligibility.insert(r.id, tuples);
            }
            Ok(Err(failure)) => issues.push(InputDomainIssue {
                input: r.id,
                provider,
                failure,
            }),
            Err(error) => issues.push(InputDomainIssue {
                input: r.id,
                provider,
                failure: InputDomainFailure::Inconclusive(inconclusive(
                    error.in_phase("completion input domain", None),
                )?),
            }),
        }
    }
    if !issues.is_empty() {
        // Invalid providers have no eligible universe. A conservative possibility
        // graph can still prove that a dead producer cannot reach one: use the
        // provider's positive-support upper bound (or the declared domain if its
        // preparation was interrupted), only for this dependency test.
        b.completion_stage("provisional-grounding");
        let provisional = GroundProgram::prepare_completion_with_inputs(
            corpus,
            domains,
            Some(eligibility.clone()),
            None,
            b,
        )?;
        b.completion_stage("live-input-scope");
        let mut live_needed = planning_roots.clone();
        live_needed.extend(
            v.assumptions
                .iter()
                .map(|id| corpus.assumption(*id).unwrap().restriction.relation()),
        );
        live_needed.extend(
            v.obligations
                .iter()
                .map(|id| corpus.obligation(*id).unwrap().requirement.relation()),
        );
        live_needed.extend(v.options.hypothesis);
        if let Some(ds) = &v.options.decisions {
            live_needed.extend(ds);
        }
        for rule in provisional.rules() {
            b.tick("completion input scope")?;
            live_needed.extend(rule.body.iter().map(|l| l.term.atom.relation));
        }
        for r in corpus.relations() {
            if r.input_cardinality.is_some() || !v.notices.is_empty() {
                live_needed.insert(r.id);
            }
        }
        issues.retain(|issue| {
            if live_needed.contains(&issue.input) {
                true
            } else {
                eligibility.insert(issue.input, BTreeSet::new());
                ignored.push(InputDomainIssue {
                    input: issue.input,
                    provider: issue.provider,
                    failure: InputDomainFailure::NotNeeded,
                });
                false
            }
        });
        if !issues.is_empty() {
            return Ok(Inputs::Invalid(issues));
        }
    }
    b.completion_stage("runtime-grounding");
    Ok(Inputs::Ready(
        GroundProgram::prepare_completion_with_inputs(corpus, domains, Some(eligibility), None, b)?,
        ignored,
    ))
}
