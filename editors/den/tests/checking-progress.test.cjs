const { test } = require('node:test');
const assert = require('node:assert/strict');
const view = require('../src/checking-progress.cjs');

function progress(overrides = {}, other = {}) {
  const counts = { pending: 0, checking: 0, complete: 0, blocked: 0, unconfigured: 0,
    deadline: 0, failed: 0, cancelled: 0, ...overrides };
  const total = Object.values(counts).reduce((a, b) => a + b, 0);
  return { total, processed: total - counts.pending - counts.checking, counts,
    active: [], awaitingSnapshots: false, ...other };
}
test('progress counts work processed and identifies the active program without claiming a proof', () => {
  const p = progress({ complete: 2, blocked: 1, checking: 1, pending: 4 },
    { active: [{ label: 'app/den.root' }] });
  assert.ok(view.busy(p));
  assert.match(view.text(p), /Checking 3\/8 programs/);
  assert.match(view.details(p), /Checking: app\/den.root/);
  assert.match(view.details(p), /1 blocked/);
  assert.match(view.details(p), /does not mean proved/);
});
test('terminal failures and unconfigured programs stop the spinner, awaiting sources keeps it', () => {
  for (const state of ['complete', 'blocked', 'unconfigured', 'deadline', 'failed', 'cancelled']) {
    assert.equal(view.busy(progress({ [state]: 1 })), false);
  }
  const waiting = progress({ blocked: 1 }, { awaitingSnapshots: true });
  assert.ok(view.busy(waiting));
  assert.match(view.text(waiting), /Synchronizing sources/);
  assert.equal(view.busy(progress()), false);
});
test('edits and program removal use current counts without fabricated monotonic percentages', () => {
  const done = progress({ complete: 4 });
  const edited = progress({ complete: 3, pending: 1 });
  const removed = progress({ complete: 2 });
  assert.equal(view.busy(done), false);
  assert.match(view.text(edited), /3\/4/);
  assert.match(view.summary(removed), /2\/2/);
});
test('routine updates use debug logs and completion is brief, with warnings for failed work', () => {
  const lines = [];
  const output = Object.fromEntries(['info', 'warn', 'debug'].map(level => [level, message => lines.push({ level, message })]));
  const running = progress({ checking: 1 });
  const done = progress({ complete: 1 });
  view.logProgress(output, undefined, running);
  assert.deepEqual(lines.map(l => l.level), ['debug']);
  view.logProgress(output, running, done);
  assert.equal(lines.at(-1).level, 'info');
  assert.match(lines.at(-1).message, /1 checked/);
  view.logProgress(output, done, done);
  assert.equal(lines.at(-1).level, 'debug');
  view.logProgress(output, running, progress({ deadline: 1 }));
  assert.equal(lines.at(-1).level, 'warn');
  assert.match(lines.at(-1).message, /deadline reached/);
});


test('one large program reports its phase, verification and prepared size', () => {
  const p = progress({ checking: 1 }, { active: [{ program: 'file:///app/den.root', label: 'app/den.root', revision: 12,
    detail: { phase: 'admission', elapsedMs: 5000, verification: 'library::checks', verificationIndex: 2, verificationTotal: 3,
      assumptions: 1, obligations: 7, notices: 4,
      memory: { rssBytes: 1024, peakRssBytes: 2048, footprintBytes: null, peakFootprintBytes: null },
      ground: { inputAtoms: 120, atoms: 300, ruleInstances: 200, components: 80, largestComponentAtoms: 15 },
      fold: { presentFacts: 30, absentFacts: 20, retainedBytes: 4096, retainedEvidence: { atoms: 50 }, residual: { atoms: 250 } } } }] });
  assert.match(view.text(p), /Admission · verification 2\/3/);
  assert.match(view.text(p, 9000), /9s since update/);
  assert.match(view.details(p), /120 inputs, 300 atoms, 200 rule instances, 80 components/);
  assert.match(view.details(p), /largest: 15 atoms/);
  assert.match(view.details(p), /30 present, 20 absent; retained evidence:.*50.*residual graph:.*250/);
  assert.match(view.details(p), /Retained keyed fold: 4096 accounted bytes/);
  assert.match(view.details(p), /Process memory \(bytes; peaks are lifetime\):.*"rssBytes":1024/);
  assert.match(view.details(p), /library::checks/);
  assert.match(view.details(p, 9000), /not a heartbeat/);
  const lines = [];
  const output = { debug() {}, warn() {}, info(message) { lines.push(message); } };
  view.logProgress(output, undefined, p);
  assert.match(lines[0], /run 12/);
  assert.match(lines[0], /Admission/);
  assert.match(lines[0], /Retained keyed fold: 4096 accounted bytes/);
  view.logProgress(output, p, p);
  assert.equal(lines.length, 1); // Don't repeat an unchanged phase.
  const restarted = structuredClone(p);
  restarted.active[0].revision = 13;
  view.logProgress(output, p, restarted);
  assert.match(lines[1], /run 13/);
  restarted.active[0].detail = { phase: 'publication', verificationTotal: 3, elapsedMs: 9000 };
  assert.doesNotMatch(view.text(restarted), /undefined/);
  restarted.active[0].detail = { phase: 'fixed-facts', elapsedMs: 0 };
  assert.match(view.text(restarted), /Evaluating fixed facts/);
});

test('Output names every effective limit without estimating unfinished work', () => {
  const limits = Object.fromEntries(Object.keys(require('../package.json').contributes.configuration.properties['denotate.limits'].properties).map((key, i) => [key, i]));
  const p = progress({ checking: 1 }, { active: [{ label: 'app', revision: 2,
    detail: { phase: 'loading', elapsedMs: 0, configuration: { timeoutMs: 42, limits } } }] });
  const lines = [];
  const output = Object.fromEntries(['info', 'warn', 'debug'].map(level => [level, value => lines.push(value)]));
  view.logProgress(output, undefined, p);
  assert.ok(lines.some(line => line.includes('timeoutMs=42')));
  for (const [key, value] of Object.entries(limits)) assert.ok(lines.some(line => line.includes(`${key}=${value}`)));
});

test('admission snapshots identify unresolved components, current work, reuse and exhaustion', () => {
  const a = { phase: 'relevant', round: 2, stage: 'upper-bounds', unresolvedComponents: 3, blockedAtoms: 12,
    removedRules: 1, dischargedNegations: 2, rule: 7, rules: 20, iteration: 4,
    current: { index: 6, atoms: 5, ruleInstances: 8, atom: "p('a')",
      location: { uri: 'file:///p.den', line: 3, column: 2 } } };
  const p = progress({ checking: 1 }, { active: [{ label: 'app', program: 'app', revision: 4,
    detail: { phase: 'admission', elapsedMs: 10, verification: '::v', verificationIndex: 1, verificationTotal: 1,
      assumptions: 0, obligations: 1, notices: 0, admission: a } }] });
  assert.match(view.text(p), /relevant · round 2 · 3 unresolved components/);
  assert.match(view.details(p), /Admission \(relevant\)/);
  a.phase = 'downstream';
  assert.match(view.text(p), /downstream · round 2/);
  assert.match(view.details(p), /Admission \(downstream\)/);
  assert.match(view.details(p), /upper-bounds.*12 blocked atoms.*component 6.*5 atoms.*p\('a'\).*file:\/\/\/p.den:3:2/);
  assert.match(view.details(p), /iteration 4/);
  const lines = [];
  const output = { debug() {}, info(s) { lines.push(['info', s]); }, warn(s) { lines.push(['warn', s]); } };
  view.logProgress(output, undefined, p);
  assert.match(lines[0][1], /app \(run 4\), ::v: Admission/);
  const failed = structuredClone(p);
  failed.active[0].detail.admission.failure = 'admission: BDD nodes limit reached';
  view.logProgress(output, p, failed);
  assert.equal(lines.at(-1)[0], 'warn');
  assert.match(lines.at(-1)[1], /stopped: admission: BDD nodes limit reached/);
  a.stage = 'reused'; a.round = 0; a.current = null; a.iteration = null;
  assert.match(view.text(p), /reused/);
  assert.doesNotMatch(view.details(p), /component 6|iteration 4|undefined/);
});

test('checking Output reports target, immediate exhaustion, recovery and remaining cycle locations', () => {
  const p = progress({ checking: 1 }, { active: [{ program: 'app', label: 'app', revision: 5,
    detail: { phase: 'checking', verification: '::v', elapsedMs: 50,
      checking: { stage: 'certification', state: 'exhausted', continues: true,
        target: { kind: 'obligation', name: '::o', location: { uri: 'file:///p.den', line: 4, column: 1 } },
        failure: 'certification: condition nodes limit 42' } } }] });
  assert.match(view.text(p), /certification/);
  const lines = [];
  const output = { debug() {}, info(s) { lines.push(['info', s]); }, warn(s) { lines.push(['warn', s]); } };
  view.logProgress(output, undefined, p);
  assert.equal(lines[0][0], 'warn');
  assert.match(lines[0][1], /::v: Checking certification.*obligation ::o.*file:\/\/\/p.den:4:1.*condition nodes limit 42.*continuing other checking work/);
  p.active[0].detail.checking.continues = false;
  p.active[0].detail.checking.failure = 'certification: deadline';
  assert.match(view.details(p), /deadline; stopping this verification/);
  p.active[0].detail = { phase: 'admission', verification: '::v', elapsedMs: 10,
    remainingComponent: { position: 1, total: 2, component: { index: 8, atoms: 3, ruleInstances: 5, atom: 'r()' },
      cycle: [{ from: 'r()', to: 's()', negative: true, location: { uri: 'file:///p.den', line: 9, column: 2 } }],
      truncated: true, cycleEdges: 20 } };
  view.logProgress(output, undefined, p);
  assert.match(lines.at(-1)[1], /Unresolved component 1\/2.*3 atoms, 5 rule instances/);
  assert.match(lines.at(-1)[1], /r\(\) -not-> s\(\) at file:\/\/\/p.den:9:2/);
  assert.match(lines.at(-1)[1], /20 cycle edges in total/);
});

test('admission proof skips continue and survive a reused completion count', () => {
  const a = { round: 2, stage: 'producer-removals', unresolvedComponents: 2, blockedAtoms: 12,
    removedRules: 1, dischargedNegations: 0, skippedAttempts: 3,
    skipped: 'producer-coverage', skipTarget: { head: 'wide()' }, failure: 'BDD preflight: BDD tasks limit 10' };
  const p = progress({ checking: 1 }, { active: [{ label: 'app', detail: { phase: 'admission', admission: a } }] });
  assert.match(view.details(p), /3 proof attempts skipped.*skipped producer-coverage for wide\(\).*continuing admission/);
  assert.doesNotMatch(view.details(p), /stopped:/);
  a.stage = 'reused'; a.skipped = null; a.failure = null;
  assert.match(view.details(p), /reused.*3 proof attempts skipped/);
  assert.doesNotMatch(view.details(p), /continuing admission|stopped:/);
});
