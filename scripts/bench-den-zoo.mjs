// Shape workloads and analysis. Execution uses the schema runner's persistent CLI runs.
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
export const families = ['fan-in-fixed','fan-in-input','negative-guarded','negative-unresolved','certification','removal-heavy','presentation','guarded-ring','guarded-fan-in','guarded-worlds','guarded-hub','schema-layered'];
export function source(family, n, {hubReader='split',hubRoutes=true,hubDecoys=0,hubDecoyShape='full'}={}) {
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
  } else if (family.startsWith('negative') || family==='certification') {
    for (let i=0;i<n;i++) {
      add(`relation a${i}(); relation b${i}();`);
      if (family==='negative-guarded') {
        add(`input flag${i}(); a${i}() :- flag${i}(), !b${i}(); b${i}() :- !flag${i}(), !a${i}();`);
      } else add(`a${i}() :- !b${i}(); b${i}() :- !a${i}();`);
    }
    if (family==='certification') add(`bad() :- ${Array.from({length:n},(_,i)=>`a${i}()`).join(', ')};`);
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
    add('input option(group: Group, choice: Choice);');
    add('assumption exclusive: at_most_one(option, group_by: (group));');
    assumptions = 'exclusive';
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
  } else if (family==='guarded-hub') {
    if(!['split','merged'].includes(hubReader))throw Error('hub reader must be split or merged');
    if(!Number.isSafeInteger(hubDecoys)||hubDecoys<0||!['full','near-full'].includes(hubDecoyShape))throw Error('invalid hub decoys');
    add('sort Class; const perishable, hazardous: Class; input declared(kind: Class);');
    add('sort Lane;');
    add(`const ${Array.from({length:n},(_,i)=>`l${i}`).join(', ')}: Lane; input route(lane: Lane);`);
    add('assumption one_class: at_most_one(declared, group_by: ());');
    if(hubRoutes)add('assumption one_route: at_most_one(route, group_by: ());');
    assumptions=hubRoutes?'one_class, one_route':'one_class';
    add('input docked(); input priority_call();');
    for(const name of ['tagged','claim_fails','hazard_claim','inspected','held','cleared'])add(`relation ${name}();`);
    for(let i=0;i<n;i++)add(`input fa${i}(); input fb${i}(); tagged() :- route(l${i}), fa${i}(), !fb${i}(), declared(perishable), cleared();`);
    add('claim_fails() :- docked(), !tagged();');
    if(hubReader==='split') {
      add('relation hc_type_ok(); relation hc_read_ok(); relation hc_unsat();');
      add('hc_type_ok() :- declared(hazardous); hc_read_ok() :- !claim_fails();');
      add('hc_unsat() :- !hc_type_ok(); hc_unsat() :- !hc_read_ok(); hazard_claim() :- !hc_unsat();');
    } else add('hazard_claim() :- declared(hazardous), !claim_fails();');
    add('inspected() :- declared(perishable); inspected() :- hazard_claim();');
    add('held() :- priority_call(), inspected(); cleared() :- docked(), !held();');
    if(hubDecoys) {
      // The class bit makes the two class tests complementary even without a
      // selected assumption. Final meanings stay small without route exclusivity.
      s=s.replace('input declared(kind: Class);', 'relation declared(kind: Class); input class_bit(); declared(perishable) :- class_bit(); declared(hazardous) :- !class_bit();');
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
  return s+`obligation no_bad: empty(bad); verification checks { assumptions: [${assumptions}]; obligations: [no_bad]; ${family==='guarded-hub'?'notices: [hazard_condition];':''} }\n`;
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
    attemptSummaries: report.admissionAttemptSummaries ?? [],
    attemptSamples: report.admissionAttemptSamples ?? [],
    phases: measurements(records, report.outcomes),
  };
}

// Rebuild the aggregate, including a partially completed child, from saved files.
export function summarize(out) {
  const config = JSON.parse(fs.readFileSync(path.join(out, 'sweep.json')));
  const { family, sizes, repeat, threshold, binary } = config;
  const report = { threshold, repeat, sizes, inputOrder: config.inputOrder ?? 'key', hubReader: config.hubReader ?? 'split', hubRoutes: config.hubRoutes ?? true, hubDecoys: config.hubDecoys ?? 0, hubDecoyShape: config.hubDecoyShape ?? 'full', satProbe: config.satProbe ?? false, families: {} };
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

export function run({out,family= families,sizes=[8,16,32],repeat=3,threshold=1.3,binary='target/profiling/examples/bench_schema',samply=false,limits=[],inputOrder='key',hubReader='split',hubRoutes=true,hubDecoys=0,hubDecoyShape='full',satProbe=false}) {
  if (!['split','merged'].includes(hubReader)) throw Error('hub reader must be split or merged');
  if (!['key','reverse-key','structural'].includes(inputOrder)) throw Error('invalid input order');
  fs.mkdirSync(path.dirname(out),{recursive:true});
  fs.mkdirSync(out,{recursive:false});
  fs.writeFileSync(path.join(out, 'sweep.json'), JSON.stringify({family, sizes, repeat, threshold, inputOrder, hubReader, hubRoutes, hubDecoys, hubDecoyShape, satProbe, binary: path.resolve(binary)}, null, 2));
  const report={threshold,repeat,sizes,inputOrder,hubReader,hubRoutes,hubDecoys,hubDecoyShape,satProbe,families:{}};
  for(const name of family) {
    const runs=[];
    for(const size of sizes) for(let rep=0;rep<repeat;rep++) {
      const dir=path.resolve(out,`${name}-${size}-${rep}`);
      let args=['--out',dir,'--input-order',inputOrder];
      if(name==='schema-layered') args.push('--topology','layered','--fields',String(size+2),'--reads',String(size),'--depth','2','--encoding','assumed');
      else {const input=path.resolve(out,`${name}-${size}.den`);fs.writeFileSync(input,source(name,size,{hubReader,hubRoutes,hubDecoys,hubDecoyShape}));args.push('--source',input);}
      if(samply) args.push('--samply');
      if(satProbe) args.push('--sat-probe');
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
      if(key==='--sat-probe'){opts.satProbe=true;continue;}
      if(key==='--help'){console.log('just bench-den-zoo [--family NAME,...] [--sizes 8,16,32] [--repeat 3] [--threshold 1.3] [--out DIR] [--samply] [--input-order key|reverse-key|structural] [--hub-reader split|merged] [--hub-no-routes] [--sat-probe] [--hub-decoys N] [--hub-decoy-shape full|near-full] [-- CHECK LIMITS]; --summarize DIR recovers a sweep');process.exit(0);}
      const val=args[++i];
      if(key==='--family')opts.family=val.split(',');else if(key==='--sizes')opts.sizes=val.split(',').map(Number);
      else if(key==='--input-order')opts.inputOrder=val;
      else if(key==='--hub-reader')opts.hubReader=val;
      else if(key==='--hub-decoys')opts.hubDecoys=Number(val);
      else if(key==='--hub-decoy-shape')opts.hubDecoyShape=val;
      else if(key==='--repeat')opts.repeat=Number(val);else if(key==='--threshold')opts.threshold=Number(val);else if(key==='--out')opts.out=val;
      else throw Error(`unknown option ${key}`);
    }
    if(opts.family?.some(f=>!families.includes(f))||opts.sizes?.some(n=>!Number.isSafeInteger(n)||n<=0)||!Number.isSafeInteger(opts.repeat??3)||(opts.repeat??3)<1||!Number.isFinite(opts.threshold??1.3))throw Error('invalid sweep options');
    run(opts);
  } catch(e){console.error(e.message);process.exitCode=1;}
}
