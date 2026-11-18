// Shape workloads and analysis. Execution uses the schema runner's persistent CLI runs.
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
export const families = ['knowledge-scc','repeated-field','fan-in-fixed','fan-in-input','negative-guarded','negative-unresolved','certification','removal-heavy','presentation','guarded-ring','guarded-fan-in','guarded-worlds','writer-ring','guarded-hub','component-chain','symbolic-exhaustion','schema-layered'];
export function source(family, n, {hubReader='split',hubRoutes=true,hubDecoys=0,hubDecoyShape='full',hubWriters=0,hubReaders=1,hubValues=1,hubVariant='pairs',hubTagValues=2,ringLanes=8,ringRelays=6,ringReaders=1}={}) {
  if (!['pairs','tagged'].includes(hubVariant)) throw Error('invalid hub variant');
  if (hubVariant==='pairs' && hubTagValues!==2) throw Error('tag values requires tagged hub variant');
  if (!families.includes(family) || !Number.isSafeInteger(n) || n < 1) throw Error('invalid family/positive size');
  let s = 'relation bad();\n';
  let assumptions = '';
  const add = x => { s += x + '\n'; };
  if (family.startsWith('fan-in')) {
    add('relation result();');
    for (let i=0;i<n;i++) {
      add(`${family==='fan-in-input'?'input':'relation'} source${i}();`);
      if (family==='fan-in-fixed') add(`source${i}();`);
      add(`result() :- source${i}();`);
    }
    add('bad() :- result();');
  } else if (family==='symbolic-exhaustion') {
    add('relation wide();');
    for(let i=0;i<n;i++) add(`input source${i}(); wide() :- source${i}();`);
    // Keep the wide provider in admission's cone; a separate guarded cycle
    // must still settle when computing that provider's exact condition fails.
    add('relation loop(); loop() :- wide(), !loop(); bad() :- !wide();');
    add('input flag(); relation a(); relation b(); a() :- flag(), !b(); b() :- !flag(), !a();');
    add('relation independent(); independent() :- a(), b(); obligation no_independent: empty(independent);');
  } else if (family.startsWith('negative') || family==='certification') {
    for (let i=0;i<n;i++) {
      add(`relation a${i}(); relation b${i}();`);
      if (family==='negative-guarded') {
        add(`input flag${i}(); a${i}() :- flag${i}(), !b${i}(); b${i}() :- !flag${i}(), !a${i}();`);
      } else add(`a${i}() :- !b${i}(); b${i}() :- !a${i}();`);
    }
    if (family==='certification') add(`bad() :- ${Array.from({length:n},(_,i)=>`a${i}()`).join(', ')};`);
  } else if (family === 'component-chain') {
    // Two small guarded components feed a wide removal component. The last
    // component's pending proofs can fill storage before guarded work starts.
    for (const [prefix, upstream] of [['up',null], ['mid','up']]) {
      add(`input ${prefix}_kind(); input ${prefix}_ready(); input ${prefix}_priority();`);
      for (const name of ['booked','fails','claim','inspected','held','cleared']) add(`relation ${prefix}_${name}();`);
      add(`${prefix}_booked() :- ${prefix}_kind(), ${prefix}_cleared();`);
      if(upstream) add(`${prefix}_booked() :- ${prefix}_kind(), ${upstream}_claim();`);
      add(`${prefix}_fails() :- ${prefix}_ready(), !${prefix}_booked();`);
      add(`${prefix}_claim() :- !${prefix}_kind(), !${prefix}_fails();`);
      add(`${prefix}_inspected() :- ${prefix}_kind(); ${prefix}_inspected() :- ${prefix}_claim();`);
      add(`${prefix}_held() :- ${prefix}_priority(), ${prefix}_inspected();`);
      add(`${prefix}_cleared() :- ${prefix}_ready(), !${prefix}_held();`);
    }
    add('input p(); input q(); relation guard(); guard():-p(); guard():-q();');
    add('relation wide(); wide():-p(); wide():-q(); wide():-mid_claim();');
    for(let i=0;i<n;i++) {
      add(`relation leaf${i}(); leaf${i}():-!wide(); leaf${i}():-q(); wide():-guard(),leaf${i}();`);
    }
  } else if (family === 'writer-ring') {
    if (![ringLanes,ringRelays,ringReaders].every(v=>Number.isSafeInteger(v)&&v>0)) throw Error('ring dimensions must be positive integers');
    if (ringRelays<2) throw Error('writer ring requires at least two relays');
    add(`sort Kind; const ${Array.from({length:ringRelays},(_,i)=>`t${i}`).join(', ')}: Kind; relation kinds(t: Kind);`);
    for(let i=0;i<ringRelays;i++)add(`kinds(t${i});`);
    add(`sort Lane; const ${Array.from({length:n},(_,w)=>Array.from({length:ringLanes},(_,j)=>`l${w}_${j}`)).flat().join(', ')}: Lane; relation lanes(l: Lane);`);
    for(let w=0;w<n;w++)for(let j=0;j<ringLanes;j++)add(`lanes(l${w}_${j});`);
    add('input route(l: Lane) within lanes at_most_one(group_by: ());');
    add('input received(t: Kind) within kinds at_most_one(group_by: ());');
    add('relation kind(t: Kind); relation written();');

    for(let w=0;w<n;w++) {
      add(`relation applies${w}(); input result${w}(t: Kind) within kinds exactly_one(group_by: ());`);
      add(`kind(T) :- applies${w}(), result${w}(T); written() :- applies${w}();`);
      for(let j=0;j<ringLanes;j++)add(`input fa${w}_${j}(); input fb${w}_${j}(); applies${w}() :- route(l${w}_${j}), fa${w}_${j}(), !fb${w}_${j}();`);
    }
    add('kind(T) :- received(T), !written();');
    for(let i=0;i<ringRelays;i++) {
      add(`relation context${i}(); relation relay${i}(); context${i}() :- kind(t${i}); relay${i}() :- context${i}(), !relay${(i+1)%ringRelays}();`);
      add(`bad() :- context${i}(), !relay${i}();`);
    }
    add('relation downstream();');
    for(let i=0;i<ringReaders;i++)add(`input w${i}(); relation down${i}(); down${i}() :- relay${i%ringRelays}(), w${i}(); downstream() :- down${i}();`);
    add('notice downstream_varies: varies(downstream);');
  } else if (family === 'guarded-ring') {
    // Grouped input names deliberately order priorities before readiness bits.
    // The positive ring is cut by ready_i; under !kind every booked_i is false.
    add('input kind();');
    for (let i = 0; i < n; i++) {
      add(`input priority${i}(); input ready${i}();`);
      for (const name of ['booked', 'fails', 'claim', 'inspected', 'held', 'cleared']) add(`relation ${name}${i}();`);
      add(`booked${i}() :- kind(), ready${i}(), priority${i}(), cleared${i}();`);
      add(`booked${i}() :- kind(), !ready${i}(), booked${(i + 1) % n}();`);
      add(`fails${i}() :- ready${i}(), !booked${i}();`);
      add(`claim${i}() :- !kind(), !fails${i}();`);
      add(`inspected${i}() :- kind(); inspected${i}() :- claim${i}();`);
      add(`held${i}() :- priority${i}(), inspected${i}();`);
      add(`cleared${i}() :- ready${i}(), !held${i}();`);
    }
  } else if (family === 'knowledge-scc') {
    // Two dual positive SCCs: knowledge travels against the initial rule order.
    // An input decides truth/falsehood; the cycle alone cannot invent knowledge.
    add(`sort Decision; const ${Array.from({length:n},(_,i)=>`d${i}`).join(', ')}: Decision;`);
    add('input seed(); relation known_true(d: Decision); relation known_false(d: Decision);');
    for(let i=0;i<n;i++) {
      add(`known_true(d${i}) :- known_true(d${(i+1)%n});`);
      add(`known_false(d${i}) :- known_false(d${(i+1)%n});`);
    }
    add(`known_true(d${n-1}) :- seed(); known_false(d${n-1}) :- !seed();`);
    add('bad() :- known_true(D), known_false(D);');
    add('relation selected(); selected() :- known_true(d0); notice selection_varies: varies(selected);');
  } else if (family === 'repeated-field') {
    // Constant appenders and tasks returning subsets of a repeated field.
    // Key order separates each guard from its output/presence bit.
    add('relation present(); relation absent(); absent() :- !present(); bad() :- present(), absent();');
    for (let i=0;i<n;i++) {
      add(`input appender${i}(); input guard${i}(); present() :- appender${i}(), guard${i}();`);
      add(`input applies${i}(); input output${i}(); present() :- applies${i}(), output${i}();`);
    }
    add('notice field_missing: varies(absent);');
  } else if (family === 'guarded-fan-in') {
    // One wide condition, rather than a large condition retained at every ring
    // head. Grouped variables make OR_i(priority_i AND ready_i) exponential.
    add('input kind(); input gate();');
    for (const name of ['booked', 'fails', 'claim', 'inspected', 'held', 'cleared']) add(`relation ${name}();`);
    for (let i = 0; i < n; i++) {
      add(`input priority${i}(); input ready${i}();`);
      add(`booked() :- kind(), priority${i}(), ready${i}(), cleared();`);
    }
    add('fails() :- gate(), !booked(); claim() :- !kind(), !fails();');
    add('inspected() :- kind(); inspected() :- claim();');
    // Once claim settles, held=inspected makes booked false. The expensive
    // upper approximation is not also an inherently expensive final meaning.
    add('held() :- inspected(); cleared() :- gate(), !held();');
  } else if (family === 'guarded-worlds') {
    // W is linear in n, but retaining W AND ready_i for each of n producers
    // makes cone preparation quadratic. There are only two atoms in the
    // claim's guard-live cone. Each input group stays adjacent in key order.
    add('sort Group; sort Choice; const left, right: Choice;');
    add(`const ${Array.from({length:2*n},(_,i)=>`g${i}`).join(', ')}: Group;`);
    add('input option(group: Group, choice: Choice) at_most_one(group_by: (group));');
    add('input kind(); input gate();');
    for (const name of ['booked', 'fails', 'claim', 'inspected', 'held', 'cleared']) add(`relation ${name}();`);
    add('booked() :- kind(), gate(), cleared();');
    for (let i = 0; i < n; i++) {
      // The two-input condition makes !kind the first guarded candidate without
      // duplicating expression leaves: each settled ready_i remains one atom.
      add(`input flag${i}(); relation ready${i}(); ready${i}() :- gate(), flag${i}();`);
      add(`fails() :- ready${i}(), !booked();`);
    }
    add('claim() :- !kind(), !fails();');
    add('inspected() :- kind(); inspected() :- claim();');
    add('held() :- inspected(); cleared() :- !held();');
  } else if (family==='guarded-hub' && hubVariant==='tagged') {
    if (hubReader!=='split' || !hubRoutes || hubDecoys || hubReaders!==1 || hubValues!==1) throw Error('tagged hub requires split reader, routes and no pair/decoy dimensions');
    if (![hubWriters,hubTagValues].every(Number.isSafeInteger) || hubWriters<1 || hubTagValues<1) throw Error('tagged hub requires positive writers and tag values');
    add('sort Class; const perishable, hazardous, general: Class;');
    add('relation classes(c: Class); classes(perishable); classes(hazardous); classes(general); input declared(c: Class) within classes at_most_one(group_by: ());');
    add('input docked(); input priority_call();');
    add(`sort Lane; const ${Array.from({length:n},(_,i)=>`l${i}`).join(', ')}: Lane; relation lanes(l: Lane);`);
    for(let i=0;i<n;i++)add(`lanes(l${i});`);
    add('input route(l: Lane) within lanes at_most_one(group_by: ());');
    for(let i=0;i<n;i++)add(`input fa${i}(); input fb${i}();`);
    add(`sort Tag; const ${Array.from({length:hubTagValues},(_,i)=>`t${i}`).join(', ')}: Tag; relation tags(t: Tag);`);
    for(let v=0;v<hubTagValues;v++)add(`tags(t${v});`);
    add('input received(t: Tag) within tags at_most_one(group_by: ()); input kept();');
    add('sort Check; const c0: Check; relation checks(c: Check); checks(c0); input satisfies(c: Check) within checks at_most_one(group_by: ());');

    for(let w=0;w<hubWriters;w++) {
      add(`input result${w}(t: Tag) within tags exactly_one(group_by: ());`);
    }
    add('relation tagged(t: Tag); tagged(T) :- received(T), kept();');
    for(let w=0;w<hubWriters;w++)add(`relation applies${w}(); relation triggered${w}(); tagged(T) :- applies${w}(), result${w}(T); applies${w}() :- triggered${w}();`);
    for(let i=0;i<n;i++)add(`relation use${i}(); relation when${i}(); triggered${i%hubWriters}() :- use${i}(); use${i}() :- when${i}(); when${i}() :- route(l${i}), fa${i}(), !fb${i}(), declared(perishable), cleared();`);
    add('relation tag_present(); tag_present() :- tagged(_);');
    for(const name of ['checked','claim_fails_ok','hc_type_ok','hc_unsat','claim_fails_unsat','hc_read_ok','claim_fails','hazard_claim','inspected_ok','inspected_unsat','inspected','held_ok','held_unsat','held','cleared_ok','cleared_unsat','cleared'])add(`relation ${name}();`);
    add('checked() :- tag_present(), satisfies(c0); claim_fails_ok() :- docked(), !checked();');
    add('hc_type_ok() :- declared(hazardous); hc_unsat() :- !hc_type_ok(); claim_fails_unsat() :- !claim_fails_ok(); hc_read_ok() :- !claim_fails(); hc_unsat() :- !hc_read_ok(); claim_fails() :- !claim_fails_unsat(); hazard_claim() :- !hc_unsat();');
    add('inspected_ok() :- declared(perishable); inspected_ok() :- hazard_claim(); inspected_unsat() :- !inspected_ok(); inspected() :- !inspected_unsat();');
    add('held_ok() :- priority_call(), inspected(); held_unsat() :- !held_ok(); held() :- !held_unsat();');
    add('cleared_ok() :- docked(), !held(); cleared_unsat() :- !cleared_ok(); cleared() :- !cleared_unsat();');
    add('notice hazard_condition: varies(cleared);');
  } else if (family==='guarded-hub') {
    if(!['split','merged'].includes(hubReader))throw Error('hub reader must be split or merged');
    if(!Number.isSafeInteger(hubDecoys)||hubDecoys<0||!['full','near-full'].includes(hubDecoyShape))throw Error('invalid hub decoys');
    if (![hubWriters,hubReaders,hubValues].every(Number.isSafeInteger) || hubWriters<0 || hubReaders<1 || hubValues<1) throw Error('invalid hub chain dimensions');
    if (hubDecoys && (hubWriters || hubReaders!==1 || hubValues!==1)) throw Error('chain dimensions and decoys are separate workloads');
    add(`sort Class; const perishable, hazardous${Array.from({length:hubReaders-1},(_,j)=>`, reader${j+1}`).join('')}: Class; input declared(kind: Class) at_most_one(group_by: ());`);
    add('sort Lane;');
    add(`const ${Array.from({length:n},(_,i)=>`l${i}`).join(', ')}: Lane; input route(lane: Lane);`);
    if(hubRoutes)s=s.replace('input route(lane: Lane);', 'input route(lane: Lane) at_most_one(group_by: ());');
    add('input docked(); input priority_call();');
    for(const name of ['tagged','claim_fails','hazard_claim','inspected','held','cleared'])add(`relation ${name}();`);
    if (hubWriters) {
      for(let w=0;w<hubWriters;w++) {
        add(`relation triggered${w}(); relation applies${w}(); applies${w}() :- triggered${w}(); tagged() :- applies${w}();`);
      }
      for(let i=0;i<n;i++) {
        add(`relation lane_when${i}(); relation lane_use${i}(); lane_when${i}() :- declared(perishable), cleared(); lane_use${i}() :- lane_when${i}();`);
        for(let v=0;v<hubValues;v++)add(`input fa${i}_${v}(); input fb${i}_${v}(); triggered${i%hubWriters}() :- route(l${i}), fa${i}_${v}(), !fb${i}_${v}(), lane_use${i}();`);
      }
    } else {
      if(hubValues!==1)throw Error('hub values requires writer chains');
      for(let i=0;i<n;i++)add(`input fa${i}(); input fb${i}(); tagged() :- route(l${i}), fa${i}(), !fb${i}(), declared(perishable), cleared();`);
    }
    add('claim_fails() :- docked(), !tagged();');
    if(hubReader==='split') {
      add('relation hc_type_ok(); relation hc_read_ok(); relation hc_unsat();');
      add('hc_type_ok() :- declared(hazardous); hc_read_ok() :- !claim_fails();');
      add('hc_unsat() :- !hc_type_ok(); hc_unsat() :- !hc_read_ok(); hazard_claim() :- !hc_unsat();');
    } else add('hazard_claim() :- declared(hazardous), !claim_fails();');
    for(let j=1;j<hubReaders;j++) {
      add(`relation hc_type_ok${j}(); relation hc_read_ok${j}(); relation hc_unsat${j}(); relation hazard_claim${j}();`);
      add(`hc_type_ok${j}() :- declared(reader${j}); hc_read_ok${j}() :- !claim_fails(); hc_unsat${j}() :- !hc_type_ok${j}(); hc_unsat${j}() :- !hc_read_ok${j}(); hazard_claim${j}() :- !hc_unsat${j}(); inspected() :- hazard_claim${j}();`);
    }
    add('inspected() :- declared(perishable); inspected() :- hazard_claim();');
    add('held() :- priority_call(), inspected(); cleared() :- docked(), !held();');
    if(hubDecoys) {
      // The class bit makes the two class tests complementary even without a
      // selected assumption. Final meanings stay small without route exclusivity.
      s=s.replace('input declared(kind: Class) at_most_one(group_by: ());', 'relation declared(kind: Class); input class_bit(); declared(perishable) :- class_bit(); declared(hazardous) :- !class_bit();');
      s=s.replace('cleared() :- docked(), !held();', '').replace('priority_call(), inspected()', 'inspected()');
      let decoys='';
      for(let i=0;i<hubDecoys;i++) {
        // Split readers infer docked, which leaves the wide tagged fan-in live.
        decoys+=`relation decoy_held${i}(); relation decoy_unsat${i}(); decoy_held${i}() :- inspected(); decoy_unsat${i}() :- !docked(); decoy_unsat${i}() :- decoy_held${i}(); cleared() :- !decoy_unsat${i}();\n`;
      }
      if(hubDecoyShape==='near-full') {
        decoys+='relation decoy_side(); decoy_side() :- !cleared();\n';
        for(let i=0;i<hubDecoys;i++)decoys+=`decoy_held${i}() :- !docked(), decoy_side();\n`;
      }
      // Source order deliberately puts decoys before the useful shared reader.
      s=decoys+s;
    }
    add('notice hazard_condition: varies(hazard_claim);');
  } else if (family==='removal-heavy') {
    add('input flag(); relation a(); relation b(); a() :- !b(); b() :- !a();');
    for(let i=0;i<n;i++) add(`relation output${i}(); output${i}() :- flag(); output${i}() :- flag(), a(); bad() :- output${i}();`);
  } else if (family==='presentation') {
    add('relation seed(); seed(); relation a(); relation b(); a() :- !b(); b() :- !a();');
    for(let i=0;i<n;i++) add(`relation support${i}(); support${i}() :- ${i?`support${i-1}`:'seed'}(); relation result${i}(); result${i}() :- support${i}(); result${i}() :- a();`);
  } else throw Error('schema-layered uses the schema generator');
  return s+`obligation no_bad: empty(bad); verification checks { assumptions: [${assumptions}]; obligations: [no_bad${family==='symbolic-exhaustion'?', no_independent':''}]; ${family==='guarded-hub'?'notices: [hazard_condition];':family==='writer-ring'?'notices: [downstream_varies];':family==='repeated-field'?'notices: [field_missing];':family==='knowledge-scc'?'notices: [selection_varies];':''} }\n`;
}
export function fit(points, threshold = 1.3) {
  const usable = points.filter(([x, y]) => Number.isFinite(x) && x > 0 && Number.isFinite(y) && y > 0);
  if (new Set(usable.map(([x]) => x)).size < 3) {
    return { state: 'insufficient data', points: usable.length };
  }
  const xs = usable.map(([x]) => Math.log(x));
  const ys = usable.map(([, y]) => Math.log(y));
  const mean = values => values.reduce((a, b) => a + b, 0) / values.length;
  const mx = mean(xs), my = mean(ys);
  const slope = xs.reduce((sum, x, i) => sum + (x - mx) * (ys[i] - my), 0)
    / xs.reduce((sum, x) => sum + (x - mx) ** 2, 0);
  return { state: 'fitted', points: usable.length, slope, flag: slope > threshold };
}

export function stats(values, requested) {
  const sorted = values.filter(Number.isFinite).sort((a, b) => a - b);
  return {
    completed: sorted.length, requested,
    median: sorted.length ? (sorted[Math.floor((sorted.length - 1) / 2)] + sorted[Math.floor(sorted.length / 2)]) / 2 : null,
    min: sorted[0] ?? null, max: sorted.at(-1) ?? null,
  };
}

const stages = ['loading', 'assumption-validation', 'fixed-facts', 'preparation', 'admission', 'checking', 'presentation'];
// Phase boundaries are non-overlapping; nested spans are deliberately not fitted.
export function measurements(records, outcomes) {
  const complete=[], open=new Map(), failed=new Set(), successors=new Set();
  let current=null;
  for(const r of records) {
    if(r.type==='profile' && r.event==='start' && [...stages,'publication'].includes(r.stage)) {
      for(const prior of complete) {
        const expected={preparation:['admission'],admission:['checking'],checking:['presentation'],presentation:['publication','preparation']}[prior.stage];
        if(!expected || expected.includes(r.stage)) successors.add(prior.span);
      }
    }
    if(r.type==='profile' && stages.includes(r.stage)) {
      if(r.event==='start') {current=r.stage;open.set(r.span,r.stage);}
      else {open.delete(r.span);complete.push(r);}
    }
    if(r.type==='progress') {
      const d=r.detail;
      // A recoverable attempt skip can precede successful admission. Final
      // unresolved reasons below still mark genuinely incomplete admission.
      if(d?.admission?.failure && !d.admission.skipped) failed.add('admission');
      if(d?.checking?.failure) failed.add('checking');
    }
    if(r.type==='run-end' && r.error && current) failed.add(current);
  }
  // Failure progress is emitted without throttling. Status reasons are a fallback
  // for preparation failures and saved/partial streams. Do not discard completed
  // admission merely because a later obligation exhausted its own budget.
  const inspect = (value, context = null) => {
    if (!value || typeof value !== 'object') return;
    // An unresolved emptiness target also says inconclusive, without exhaustion.
    if (value.resource != null) {
      const phase = String(value.phase ?? value.reason?.phase ?? '');
      let affected = context;
      if (/admission|rewrite|discharge|removal/.test(phase)) affected = 'admission';
      else if (/coverage|emptiness|uniqueness|completion|evidence|notice|checking|certification/.test(phase)) affected = 'checking';
      else if (/assumption|ground|prepar|fixed/.test(phase)) {
        affected = complete.some(r => r.stage === 'preparation') ? 'preparation'
          : complete.some(r => r.stage === 'fixed-facts') ? 'fixed-facts' : 'assumption-validation';
      }
      if (affected) failed.add(affected);
      else if (!failed.has('admission') && !failed.has('checking')) {
        // Without enough evidence, exclude the latest substantive phase only.
        failed.add(complete.some(r => r.stage === 'checking') ? 'checking'
          : complete.some(r => r.stage === 'admission') ? 'admission' : 'preparation');
      }
    }
    for (const [key, child] of Object.entries(value)) {
      const childContext = ['downstreamIncomplete', 'admissionSkips'].includes(key) ? 'admission'
        : ['emptiness', 'coverage', 'groups', 'notices'].includes(key) ? 'checking' : context;
      inspect(child, childContext);
    }
  };
  outcomes.forEach(outcome => inspect(outcome));
  for(const stage of open.values()) failed.add(stage);
  const result={};
  for(const stage of stages) {
    const rows=complete.filter(r=>r.stage===stage);
    if(!rows.length || rows.some(r=>!successors.has(r.span)) || failed.has(stage)) {result[stage]={complete:false};continue;}
    const peak=key=>rows.every(r=>Number.isFinite(r.sampledPeak?.[key]))?Math.max(...rows.map(r=>r.sampledPeak[key])):null;
    result[stage]={complete:true,ms:rows.reduce((s,r)=>s+r.elapsedMs,0),rss:peak('rssBytes'),footprint:peak('footprintBytes'),bddResultNodes:rows.every(r=>Number.isFinite(r.bddResultNodes))?rows.reduce((s,r)=>s+r.bddResultNodes,0):null,peakAccountedConditionNodes:rows.every(r=>Number.isFinite(r.peakAccountedConditionNodes))?Math.max(...rows.map(r=>r.peakAccountedConditionNodes)):null};
  }
  return result;
}
export function attemptTable(runs) {
  return runs.flatMap(run => (run.attemptSummaries ?? []).flatMap(round =>
    (round.attempts ?? []).map(counts => ({
      size: run.size, rep: run.rep, verification: round.verification,
      phase: round.phase, round: round.round, complete: round.complete, ...counts,
    }))));
}

export function aggregate(runs, sizes, repeat, threshold) {
  const phases = {};
  for (const phase of stages) {
    const rows = sizes.map(size => {
      const completed = runs.filter(r => r.size === size && r.phases[phase]?.complete);
      const measured = phase === 'loading' ? 'sourceBytes' : phase === 'presentation' ? 'findings' : 'ruleInstances';
      return {
        size, measuredAxis: measured,
        measured: stats(completed.map(r => r.sizes[measured]), repeat),
        completed: completed.length, requested: repeat,
        ms: stats(completed.map(r => r.phases[phase].ms), repeat),
        rss: stats(completed.map(r => r.phases[phase].rss), repeat),
        footprint: stats(completed.map(r => r.phases[phase].footprint), repeat),
        bddResultNodes: stats(completed.map(r => r.phases[phase].bddResultNodes), repeat),
        peakAccountedConditionNodes: stats(completed.map(r => r.phases[phase].peakAccountedConditionNodes), repeat),
      };
    });
    const fits = {};
    for (const metric of ['ms', 'rss', 'footprint']) {
      const knob = fit(rows.map(r => [r.size, r[metric].median]), threshold);
      const measured = fit(rows.map(r => [r.measured.median, r[metric].median]), threshold);
      fits[metric] = {
        knob, measured,
        label: knob.flag && measured.state === 'fitted' && !measured.flag ? 'superlinear in knob only'
          : knob.flag || measured.flag ? 'triage' : 'no signal',
      };
    }
    phases[phase] = { rows, fits };
  }
  return phases;
}

function readRun(dir, size, rep) {
  const report = JSON.parse(fs.readFileSync(path.join(dir, 'report.json')));
  const profile = path.join(dir, 'memory.jsonl');
  const records = (fs.existsSync(profile) ? fs.readFileSync(profile, 'utf8') : '')
    .split('\n').flatMap(line => { try { return [JSON.parse(line)]; } catch { return []; } });
  const ground = report.beforeAdmission?.ground ?? {};
  const rounds = report.admissionRounds ?? [];
  return {
    size, rep, dir, inputOrder: report.inputOrderDetails, checkerFinished: report.checkerFinished,
    exit: report.checkerExitCode, outcomes: report.outcomes,
    sizes: {
      sourceBytes: fs.statSync(path.join(dir, 'program/schema.den')).size, ...ground,
      removalProofs: Math.max(0, ...rounds.map(r => r.removedRules ?? 0)),
      dischargeProofs: Math.max(0, ...rounds.map(r => r.dischargedNegations ?? 0)),
      findings: report.outcomes.reduce((sum, outcome) => sum + (outcome.findings?.length ?? 0), 0),
    },
    before: report.beforeAdmission, after: report.afterAdmission,
    guardedAttempts: report.guardedAttempts ?? [],
    satProbes: report.satProbes ?? [],
    candidateProbes: report.candidateProbes ?? [],
    attemptSummaries: report.admissionAttemptSummaries ?? [],
    attemptSamples: report.admissionAttemptSamples ?? [],
    phases: measurements(records, report.outcomes),
  };
}

// Rebuild the aggregate, including a partially completed child, from saved files.
export function summarize(out) {
  const config = JSON.parse(fs.readFileSync(path.join(out, 'sweep.json')));
  const { family, sizes, repeat, threshold, binary } = config;
  const report = { threshold, repeat, sizes, inputOrder: config.inputOrder ?? 'key', hubReader: config.hubReader ?? 'split', hubRoutes: config.hubRoutes ?? true, hubDecoys: config.hubDecoys ?? 0, hubDecoyShape: config.hubDecoyShape ?? 'full', hubWriters: config.hubWriters ?? 0, hubReaders: config.hubReaders ?? 1, hubValues: config.hubValues ?? 1, hubVariant: config.hubVariant ?? 'pairs', hubTagValues: config.hubTagValues ?? 2, ringLanes: config.ringLanes ?? 8, ringRelays: config.ringRelays ?? 6, ringReaders: config.ringReaders ?? 1, satProbe: config.satProbe ?? false, satProbeCandidates: config.satProbeCandidates ?? false, families: {} };
  for (const name of family) {
    const runs = [];
    for (const size of sizes) for (let rep = 0; rep < repeat; rep++) {
      const dir = path.resolve(out, `${name}-${size}-${rep}`);
      if (!fs.existsSync(path.join(dir, 'run.json'))) continue;
      const proc = spawnSync(binary, ['--summarize', dir], { encoding: 'utf8' });
      if (proc.error || proc.status !== 0) throw Error(proc.error?.message || proc.stderr);
      runs.push(readRun(dir, size, rep));
    }
    report.families[name] = { runs, attempts: attemptTable(runs), phases: aggregate(runs, sizes, repeat, threshold) };
  }
  fs.writeFileSync(path.join(out, 'zoo.json'), JSON.stringify(report, null, 2));
  return report;
}

export function run({out,family= families,sizes=[8,16,32],repeat=3,threshold=1.3,binary='target/profiling/examples/bench_schema',samply=false,limits=[],inputOrder='key',hubReader='split',hubRoutes=true,hubDecoys=0,hubDecoyShape='full',hubWriters=0,hubReaders=1,hubValues=1,hubVariant='pairs',hubTagValues=2,ringLanes=8,ringRelays=6,ringReaders=1,satProbe=false,satProbeCandidates=false}) {
  if (!['split','merged'].includes(hubReader)) throw Error('hub reader must be split or merged');
  if (!['key','reverse-key','structural'].includes(inputOrder)) throw Error('invalid input order');
  fs.mkdirSync(path.dirname(out),{recursive:true});
  fs.mkdirSync(out,{recursive:false});
  fs.writeFileSync(path.join(out, 'sweep.json'), JSON.stringify({family, sizes, repeat, threshold, inputOrder, hubReader, hubRoutes, hubDecoys, hubDecoyShape, hubWriters, hubReaders, hubValues, hubVariant, hubTagValues, ringLanes, ringRelays, ringReaders, satProbe, satProbeCandidates, binary: path.resolve(binary)}, null, 2));
  const report={threshold,repeat,sizes,inputOrder,hubReader,hubRoutes,hubDecoys,hubDecoyShape,hubWriters,hubReaders,hubValues,hubVariant,hubTagValues,ringLanes,ringRelays,ringReaders,satProbe,satProbeCandidates,families:{}};
  for(const name of family) {
    const runs=[];
    for(const size of sizes) for(let rep=0;rep<repeat;rep++) {
      const dir=path.resolve(out,`${name}-${size}-${rep}`);
      let args=['--out',dir,'--input-order',inputOrder];
      if(name==='schema-layered') args.push('--topology','layered','--fields',String(size+2),'--reads',String(size),'--depth','2','--encoding','assumed');
      else {const input=path.resolve(out,`${name}-${size}.den`);fs.writeFileSync(input,source(name,size,{hubReader,hubRoutes,hubDecoys,hubDecoyShape,hubWriters,hubReaders,hubValues,hubVariant,hubTagValues,ringLanes,ringRelays,ringReaders}));args.push('--source',input);}
      if(samply) args.push('--samply');
      if(satProbe) args.push('--sat-probe');
      if(satProbeCandidates) args.push('--sat-probe-candidates');
      if(limits.length) args.push('--',...limits);
      const proc=spawnSync(binary,args,{stdio:'pipe',encoding:'utf8'});
      if(proc.error || proc.status!==0) throw Error(proc.error?.message||proc.stderr);
      runs.push(readRun(dir, size, rep));
      report.families[name]={runs,attempts:attemptTable(runs),phases:aggregate(runs,sizes,repeat,threshold)};
      fs.writeFileSync(path.join(out,'zoo.json'),JSON.stringify(report,null,2));
    }
    const flags=Object.entries(report.families[name].phases).filter(([,p])=>Object.values(p.fits).some(f=>f.knob.flag||f.measured.flag)).map(([p])=>p);
    console.log(`${name}: ${runs.length} runs; triage: ${flags.join(', ')||'none'}; report ${path.join(out,'zoo.json')}`);
  }
  return report;
}
if(!process.execArgv.some(a=>a==='-e'||a==='--eval') && process.argv[1] && path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  try {
    if (process.argv[2] === '--summarize' && process.argv.length === 4) {
      summarize(process.argv[3]);
      console.log(`Recovered ${path.join(process.argv[3], 'zoo.json')}`);
      process.exit(0);
    }
    const opts={out:`target/bench-den-zoo-${Date.now()}`}; const args=process.argv.slice(2);
    for(let i=0;i<args.length;i++) {
      const key=args[i];if(key==='--'){opts.limits=args.slice(i+1);break;}
      if(key==='--hub-no-routes'){opts.hubRoutes=false;continue;}
      if(key==='--samply'){opts.samply=true;continue;}
      if(key==='--sat-probe-candidates'){opts.satProbeCandidates=true;continue;}
      if(key==='--sat-probe'){opts.satProbe=true;continue;}
      if(key==='--help'){console.log('just bench-den-zoo [--family NAME,...] [--sizes 8,16,32] [--repeat 3] [--threshold 1.3] [--out DIR] [--samply] [--input-order key|reverse-key|structural] [--hub-reader split|merged] [--hub-no-routes] [--sat-probe] [--sat-probe-candidates] [--hub-variant pairs|tagged] [--hub-tag-values V] [--hub-writers N] [--hub-readers N] [--hub-values N] [--hub-decoys N] [--hub-decoy-shape full|near-full] [--ring-lanes N] [--ring-relays N] [--ring-readers N] [-- CHECK LIMITS]; --summarize DIR recovers a sweep');process.exit(0);}
      const val=args[++i];
      if(key==='--family')opts.family=val.split(',');else if(key==='--sizes')opts.sizes=val.split(',').map(Number);
      else if(key==='--input-order')opts.inputOrder=val;
      else if(key==='--ring-lanes')opts.ringLanes=Number(val);
      else if(key==='--ring-relays')opts.ringRelays=Number(val);
      else if(key==='--ring-readers')opts.ringReaders=Number(val);
      else if(key==='--hub-reader')opts.hubReader=val;
      else if(key==='--hub-variant')opts.hubVariant=val;
      else if(key==='--hub-tag-values')opts.hubTagValues=Number(val);
      else if(key==='--hub-writers')opts.hubWriters=Number(val);
      else if(key==='--hub-readers')opts.hubReaders=Number(val);
      else if(key==='--hub-values')opts.hubValues=Number(val);
      else if(key==='--hub-decoys')opts.hubDecoys=Number(val);
      else if(key==='--hub-decoy-shape')opts.hubDecoyShape=val;
      else if(key==='--repeat')opts.repeat=Number(val);else if(key==='--threshold')opts.threshold=Number(val);else if(key==='--out')opts.out=val;
      else throw Error(`unknown option ${key}`);
    }
    if(opts.family?.some(f=>!families.includes(f))||opts.sizes?.some(n=>!Number.isSafeInteger(n)||n<=0)||!Number.isSafeInteger(opts.repeat??3)||(opts.repeat??3)<1||!Number.isFinite(opts.threshold??1.3))throw Error('invalid sweep options');
    run(opts);
  } catch(e){console.error(e.message);process.exitCode=1;}
}
