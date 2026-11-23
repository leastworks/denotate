//! Completion equivalence using the common equations. The target head's
//! definition is disabled in every proof. Other equations are unchanged in both
//! programs. No scope is ever computed from these solver-instance rewrites.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PruningContext {
    World,
    Hypothesis,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PruningKind {
    Subsumption,
    Coverage,
}
#[derive(Debug, Clone)]
pub struct PruningRecord {
    pub context: PruningContext,
    pub kind: PruningKind,
    pub head: GroundAtom,
    pub rules: Vec<GroundRuleId>,
    pub removed: usize,
    pub scope_heads: usize,
    pub scope: &'static str,
}
#[derive(Debug, Clone, Default)]
pub struct PruningReport {
    pub enabled: bool,
    pub attempts: usize,
    pub removed: usize,
    pub covered: usize,
    pub records: Vec<PruningRecord>,
    pub omitted: usize,
    pub incomplete: Vec<Inconclusive>,
}
#[derive(Default)]
pub(super) struct Cache {
    views: BTreeMap<(Vec<usize>, PruningContext), Arc<Cone>>,
    pub report: PruningReport,
}
pub(super) enum View<'a> {
    Original(&'a Cone),
    Pruned(Arc<Cone>),
}
impl std::ops::Deref for View<'_> {
    type Target = Cone;
    fn deref(&self) -> &Cone {
        match self {
            Self::Original(c) => c,
            Self::Pruned(c) => c,
        }
    }
}

pub(super) fn view<'a>(
    engine: &Engine,
    cone: &'a Cone,
    hypothesis: bool,
    remaining: std::time::Duration,
) -> Result<View<'a>> {
    let Some(cache) = &engine.pruning else {
        return Ok(View::Original(cone));
    };
    // All callers supply a frozen scope with every original producer of its
    // heads. The program, domains and W are fixed for this invocation.
    let heads: Vec<_> = cone
        .rules
        .iter()
        .map(|r| r.head)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let context = if hypothesis && engine.classification.is_some() {
        PruningContext::Hypothesis
    } else {
        PruningContext::World
    };
    let key = (heads, context);
    if let Some(v) = cache.lock().unwrap().views.get(&key).cloned() {
        return Ok(View::Pruned(v));
    }
    let classification_heads = engine
        .classification
        .as_ref()
        .map(|(c, _, _)| c.rules.iter().map(|r| r.head).collect::<BTreeSet<_>>());
    let scope = if classification_heads
        .as_ref()
        .is_some_and(|h| h.iter().copied().eq(key.0.iter().copied()))
    {
        "classification"
    } else if engine
        .cone
        .rules
        .iter()
        .map(|r| r.head)
        .collect::<BTreeSet<_>>()
        .iter()
        .copied()
        .eq(key.0.iter().copied())
    {
        "processing"
    } else {
        "property"
    };
    let phase = match context {
        PruningContext::World => "completion pruning W",
        PruningContext::Hypothesis => "completion pruning W+H",
    };
    let _progress = engine.limits.progress.scope(phase, None, true);
    let mut limits = engine.shared_limits(engine.selection.len() + 6);
    limits.timeout = limits.timeout.min(remaining);
    let mut budget = Budget::new(&limits);
    let mut result = cone.clone();
    let mut report = PruningReport::default();
    let answer = simplify(
        engine,
        cone,
        &mut result,
        context,
        scope,
        key.0.len(),
        &mut report,
        &mut budget,
    );
    if let Err(error) = answer {
        // Optimization exhaustion cannot establish a proof or invalidate an
        // already installed proof. Cancellation still ends the invocation.
        limits.cancellation.check()?;
        report
            .incomplete
            .push(inconclusive(error.in_phase(phase, None))?);
    }
    let result = Arc::new(result);
    let mut cache = cache.lock().unwrap();
    cache.report.attempts += report.attempts;
    cache.report.removed += report.removed;
    cache.report.covered += report.covered;
    for record in report.records {
        if cache.report.records.len() < 64 {
            cache.report.records.push(record);
        } else {
            cache.report.omitted += 1;
        }
    }
    cache.report.omitted += report.omitted;
    let room = 64 - cache.report.incomplete.len().min(64);
    cache
        .report
        .incomplete
        .extend(report.incomplete.into_iter().take(room));
    cache.views.insert(key, result.clone());
    Ok(View::Pruned(result))
}

fn simplify(
    engine: &Engine,
    original: &Cone,
    result: &mut Cone,
    context: PruningContext,
    scope: &'static str,
    scope_heads: usize,
    report: &mut PruningReport,
    budget: &mut Budget<'_>,
) -> Result<()> {
    let n = original.fixed.len();
    budget.charge(n + original.rules.len(), "completion pruning index")?;
    let mut producers = vec![Vec::new(); n];
    for (i, r) in original.rules.iter().enumerate() {
        producers[r.head].push(i);
    }
    // One producer can be covered under H too. Skip facts and producer-less
    // heads; constants already have a completion-safe Fitting path.
    let settled = encoding::fitting(original, budget)?;
    let recursive: BTreeSet<_> = engine
        .program
        .components()
        .filter(|c| c.recursive)
        .flat_map(|c| c.atoms.iter().map(|a| engine.program.atom_index[a]))
        .collect();
    let mut candidates: Vec<_> = (0..original.atoms.len())
        .filter(|h| {
            !original.input[*h]
                && settled[*h].is_none()
                && !producers[*h].is_empty()
                && producers[*h]
                    .iter()
                    .all(|r| !original.rules[*r].body.is_empty())
        })
        .collect();
    candidates.sort_by_key(|h| (!recursive.contains(h), producers[*h].len() < 2, *h));
    if candidates.is_empty() {
        return Ok(());
    }
    // Fold only consequences independent of ALL candidate definitions. Those
    // constants remain valid whichever single equation the proof disables.
    let mut abstracted = original.clone();
    for h in &candidates {
        abstracted.input[*h] = true;
    }
    abstracted.rules.retain(|r| !abstracted.input[r.head]);
    let fixed = encoding::fitting(&abstracted, budget)?;
    let mut run = queries::Run::new(engine, budget)?;
    run.label(match context {
        PruningContext::World => "completion pruning W",
        PruningContext::Hypothesis => "completion pruning W+H",
    });
    let vars: Vec<_> = (0..n)
        .map(|i| match fixed[i] {
            Some(true) => Ok(run.truth),
            Some(false) => Ok(!run.truth),
            None if original.input[i] => Ok(run.world.vars[i]),
            _ => run.cnf.var(run.budget),
        })
        .collect::<Result<_>>()?;
    let mut logic = encoding::Booleans::new(run.truth);
    let mut bodies = Vec::with_capacity(original.rules.len());
    for r in &original.rules {
        let lits = r
            .body
            .iter()
            .map(|(i, p)| if *p { vars[*i] } else { !vars[*i] })
            .collect::<Vec<_>>();
        bodies.push(logic.and(&lits, &mut run.cnf, run.budget)?);
    }
    let mut gates = Vec::new();
    let mut live_gates = Vec::new();
    let mut current = vec![None; n];
    let mut enabled = vec![true; original.rules.len()];
    for h in 0..n {
        if original.input[h] || fixed[h].is_some() {
            continue;
        }
        let body = logic.or(
            &producers[h].iter().map(|r| bodies[*r]).collect::<Vec<_>>(),
            &mut run.cnf,
            run.budget,
        )?;
        let gate = run.cnf.var(run.budget)?;
        current[h] = Some(gates.len());
        gates.push(gate);
        live_gates.push(true);
        equation(&mut run, gate, vars[h], body)?;
    }
    // Original-cone producers preserve GroundProgram order. Scope filtering
    // never renumbers the source instances retained in reports.
    run.budget
        .charge(engine.cone.rules.len(), "completion pruning sources")?;
    let mut source = Vec::new();
    let mut cursor = 0;
    for r in &original.rules {
        while cursor < engine.cone.rules.len() && engine.cone.rules[cursor] != *r {
            cursor += 1;
        }
        if cursor == engine.cone.rules.len() {
            return Err(CheckError::Internal("pruning scope is not original"));
        }
        source.push(engine.program.core.rules[cursor].id);
        cursor += 1;
    }
    let outcome = (|| {
        for head in candidates {
            let _progress = engine.limits.progress.sampled(
                match context {
                    PruningContext::World => "completion pruning W head",
                    PruningContext::Hypothesis => "completion pruning W+H head",
                },
                true,
                || crate::CheckingTarget::Atom(original.atoms[head].clone()),
            );
            let mut remaining = producers[head].clone();
            let active = |current: &[Option<usize>], gates: &[Lit], live: &[bool]| {
                let mut pins: Vec<_> = gates
                    .iter()
                    .enumerate()
                    .map(|(i, g)| {
                        if live[i] && Some(i) != current[head] {
                            *g
                        } else {
                            !*g
                        }
                    })
                    .collect();
                if context == PruningContext::Hypothesis {
                    pins.push(vars[engine.classification.as_ref().unwrap().2]);
                }
                pins
            };
            report.attempts += 1;
            let union = logic.or(
                &remaining.iter().map(|r| bodies[*r]).collect::<Vec<_>>(),
                &mut run.cnf,
                run.budget,
            )?;
            let mut pins = active(&current, &gates, &live_gates);
            pins.push(!union);
            run.budget.charge(pins.len(), "completion pruning pins")?;
            if !run.raw_solve(&pins)? {
                let record = PruningRecord {
                    context,
                    kind: PruningKind::Coverage,
                    head: original.atoms[head].clone(),
                    rules: remaining.iter().take(32).map(|r| source[*r]).collect(),
                    removed: remaining.len(),
                    scope_heads,
                    scope,
                };
                for r in &remaining {
                    enabled[*r] = false;
                }
                result.fixed[head] = Some(true);

                report.covered += 1;
                report.removed += remaining.len();
                retain(report, record);
                let gate = run.cnf.var(run.budget)?;
                if let Some(old) = current[head] {
                    live_gates[old] = false;
                }
                current[head] = Some(gates.len());
                gates.push(gate);
                live_gates.push(true);
                let truth = run.truth;
                equation(&mut run, gate, vars[head], truth)?;
            } else {
                for candidate in producers[head].iter().copied() {
                    if remaining.len() < 2 {
                        break;
                    }
                    report.attempts += 1;
                    let other = logic.or(
                        &remaining
                            .iter()
                            .filter(|r| **r != candidate)
                            .map(|r| bodies[*r])
                            .collect::<Vec<_>>(),
                        &mut run.cnf,
                        run.budget,
                    )?;
                    let mut pins = active(&current, &gates, &live_gates);
                    pins.extend([bodies[candidate], !other]);
                    run.budget.charge(pins.len(), "completion pruning pins")?;
                    if run.raw_solve(&pins)? {
                        continue;
                    }
                    enabled[candidate] = false;
                    remaining.retain(|r| *r != candidate);

                    report.removed += 1;
                    retain(
                        report,
                        PruningRecord {
                            context,
                            kind: PruningKind::Subsumption,
                            head: original.atoms[head].clone(),
                            rules: vec![source[candidate]],
                            removed: 1,
                            scope_heads,
                            scope,
                        },
                    );
                    let gate = run.cnf.var(run.budget)?;
                    if let Some(old) = current[head] {
                        live_gates[old] = false;
                    }
                    current[head] = Some(gates.len());
                    gates.push(gate);
                    live_gates.push(true);
                    equation(&mut run, gate, vars[head], other)?;
                }
            }
        }
        Ok(())
    })();
    install_result(original, result, &enabled);
    outcome
}
fn retain(report: &mut PruningReport, record: PruningRecord) {
    if report.records.len() < 64 {
        report.records.push(record);
    } else {
        report.omitted += 1;
    }
}
fn install_result(original: &Cone, result: &mut Cone, enabled: &[bool]) {
    result.rules = original
        .rules
        .iter()
        .zip(enabled)
        .filter(|(_, on)| **on)
        .map(|(r, _)| r.clone())
        .collect();
}
fn equation(run: &mut queries::Run<'_, '_, '_>, gate: Lit, head: Lit, body: Lit) -> Result<()> {
    run.cnf.gate = Some(gate);
    run.cnf.clause(vec![!head, body], run.budget)?;
    run.cnf.clause(vec![head, !body], run.budget)?;
    run.cnf.gate = None;
    Ok(())
}
