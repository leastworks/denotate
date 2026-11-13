// Presentation of owner-thread progress snapshots; no estimates or proof status.
function busy(progress) {
  return progress && (progress.awaitingSnapshots || progress.counts.pending > 0 || progress.counts.checking > 0);
}
const phases = {
  loading: 'Loading', 'assumption-validation': 'Validating assumptions',
  'fixed-facts': 'Evaluating fixed facts', preparation: 'Preparing', admission: 'Admission', checking: 'Checking obligations and notices',
  presentation: 'Preparing diagnostics', publication: 'Preparing publication'
};
function phase(detail) { return phases[detail?.phase] ?? 'Starting check'; }
function text(progress, quietMs = 0) {
  if (progress.awaitingSnapshots) return '$(sync~spin) Denotate: Synchronizing sources';
  const detail = progress.active[0]?.detail;
  if (detail) return `$(sync~spin) Denotate: ${phase(detail)}` +
    (detail.admission ? ` · ${detail.admission.phase ? detail.admission.phase + ' · ' : ''}${detail.admission.stage === 'reused' ? 'reused' : `round ${detail.admission.round}`} · ${detail.admission.unresolvedComponents} unresolved components` : '') +
    (detail.checking ? ` · ${detail.checking.stage}` : '') +
    (detail.verificationIndex ? ` · verification ${detail.verificationIndex}/${detail.verificationTotal}` : '') +
    (quietMs >= 1000 ? ` · ${Math.floor(quietMs / 1000)}s since update` : '');
  return `$(sync~spin) Denotate: Checking ${progress.processed}/${progress.total} programs`;
}
function summary(progress) {
  const labels = {
    complete: 'checked', blocked: 'blocked', unconfigured: 'without verifications',
    deadline: 'deadline reached', failed: 'failed', cancelled: 'cancelled',
    checking: 'checking', pending: 'queued'
  };
  const states = Object.entries(labels).filter(([key]) => progress.counts[key] > 0)
    .map(([key, label]) => `${progress.counts[key]} ${label}`).join(', ');
  return `${progress.processed}/${progress.total} programs processed${states ? `; ${states}` : ''}`;
}
function activity(active) {
  const d = active.detail;
  return [`Checking: ${active.label} (run ${active.revision})`, ...(d ? [
    `${phase(d)}; reported ${Math.floor(d.elapsedMs / 1000)}s after check started`,
    ...(d.configuration ? [`Effective checker limits (per operation/query): timeoutMs=${d.configuration.timeoutMs}; ${Object.entries(d.configuration.limits).map(([k, v]) => `${k}=${v}`).join(', ')}`] : []),
    ...(d.files !== undefined ? [`${d.files} source files`] : []),
    ...(d.memory ? [`Process memory (bytes; peaks are lifetime): ${JSON.stringify(d.memory)}`] : []),
    ...(d.verification ? [`${d.verification} (${d.verificationIndex}/${d.verificationTotal}); ${d.assumptions} assumptions, ${d.obligations} obligations, ${d.notices} notices`] : []),
    ...(d.admission ? [admission(d.admission)] : []),
    ...(d.checking ? [checking(d.checking)] : []),
    ...(d.remainingComponent ? [remaining(d.remainingComponent)] : []),
    ...(d.ground ? [`Prepared size: ${d.ground.inputAtoms} inputs, ${d.ground.atoms} atoms, ${d.ground.ruleInstances} rule instances, ${d.ground.components} components (largest: ${d.ground.largestComponentAtoms} atoms)`] : []),
    ...(d.fold ? [`Fixed facts: ${d.fold.presentFacts} present, ${d.fold.absentFacts} absent; retained evidence: ${JSON.stringify(d.fold.retainedEvidence)}; residual graph: ${JSON.stringify(d.fold.residual)}`,
      ...(d.fold.retainedBytes !== undefined ? [`Retained keyed fold: ${d.fold.retainedBytes} accounted bytes`] : [])] : [])
  ] : [])].join('\n');
}
function admission(a) {
  const c = a.current, l = c?.location;
  return `Admission ${a.phase ? `(${a.phase}) ` : ''}round ${a.round} · ${a.stage}: ${a.unresolvedComponents} unresolved negation components; ${a.blockedAtoms} blocked atoms; ${a.removedRules} rules removed, ${a.dischargedNegations} negations discharged` +
    (a.skippedAttempts ? `; ${a.skippedAttempts} proof attempts skipped` : '') +
    (a.rule ? `; rule ${a.rule}/${a.rules}` : '') +
    (a.iteration != null ? `; iteration ${a.iteration}` : '') +
    (c ? `; component ${c.index} (${c.atoms} atoms, ${c.ruleInstances} rule instances), ${c.atom}` : '') +
    (l ? ` at ${l.uri}:${l.line}:${l.column}` : '') +
    (a.failure ? (a.skipped ? `; skipped ${a.skipped} for ${a.skipTarget?.head || 'current target'}: ${a.failure}; continuing admission` : `; stopped: ${a.failure}`) : '');
}
function checking(v) {
  const t = v.target, l = t?.location;
  let text = `Checking ${v.stage} · ${v.state}`;
  if (t?.kind === 'component') text += `: component ${t.index} (${t.atoms} atoms, ${t.ruleInstances} rule instances), ${t.atom}`;
  else if (t?.name) text += `: ${t.kind} ${t.name}`;
  if (l) text += ` at ${l.uri}:${l.line}:${l.column}`;
  if (v.failure) text += v.state === 'exhausted'
    ? `; ${v.failure}; ${v.continues ? 'current operation incomplete; continuing other checking work' : 'stopping this verification'}`
    : '; operation incomplete';
  return text;
}
function remaining(v) {
  const c = v.component;
  return `Unresolved component ${v.position}/${v.total}: component ${c.index} (${c.atoms} atoms, ${c.ruleInstances} rule instances), ${c.atom}` +
    (v.admissionFailure ? `; admission stopped: ${v.admissionFailure}` : '') +
    (v.admissionSkips || []).map(s => `; skipped ${s.attempt} for ${s.head}: ${s.reason}`).join('') +
    v.cycle.map(e => `\n  ${e.from} ${e.negative ? '-not->' : '->'} ${e.to}` + (e.location ? ` at ${e.location.uri}:${e.location.line}:${e.location.column}` : '')).join('') +
    (v.truncated ? `\n  ... ${v.cycleEdges} cycle edges in total` : '');
}
function details(progress, quietMs = 0) {
  return [summary(progress),
    ...progress.active.map(activity),
    ...(busy(progress) ? [`${Math.floor(quietMs / 1000)}s since the last server progress report; this is not a heartbeat.`] : []),
    ...(progress.awaitingSnapshots ? ['Waiting for current source snapshots.'] : []),
    'Processed includes blocked and unconfigured programs; it does not mean proved.',
    'Click to open Denotate output.'].join('\n');
}
function logProgress(output, previous, progress) {
  output.debug(`${summary(progress)}${progress.active.length ? `; active: ${progress.active.map(p => p.label).join(', ')}` : ''}`);
  for (const active of progress.active) {
    const old = previous?.active.find(p => p.program === active.program && p.revision === active.revision);
    if (!old || JSON.stringify(old.detail) !== JSON.stringify(active.detail)) {
      // Inner updates keep context without repeating every prepared-size field.
      const a = active.detail?.admission, c = active.detail?.checking, r = active.detail?.remainingComponent;
      const message = a || c || r ? `${active.label} (run ${active.revision}), ${active.detail.verification ?? 'program'}: ${a ? admission(a) : c ? checking(c) : remaining(r)}` : activity(active).replaceAll('\n', '; ');
      if (a?.failure || c?.state === 'exhausted') output.warn(message); else output.info(message);
    }
  }
  if (!busy(progress) && (!previous || busy(previous) || summary(previous) !== summary(progress))) {
    const message = `Checking finished: ${summary(progress)}.`;
    if (progress.counts.failed || progress.counts.deadline) output.warn(message);
    else output.info(message);
  }
}
module.exports = { busy, text, summary, details, logProgress };
