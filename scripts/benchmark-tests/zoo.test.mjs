import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {fit,stats,aggregate,measurements,run,summarize,families,source} from '../bench-den-zoo.mjs';
// Whole-component certificates can now finish before candidate-relative probes,
// bounds or ranking. Recovery must preserve whichever actual path completed.
const joint = r => r.attemptSummaries.some(s => s.attempts.some(a => a.kind==='structural-split' && a.completed>0));
test('fits distinguish linear quadratic mixed and insufficient observations',()=>{
  assert.ok(Math.abs(fit([[1,2],[2,4],[4,8]]).slope-1)<1e-10);
  assert.ok(fit([[1,1],[2,4],[4,16]]).flag);
  for(const p of [[],[[1,1],[2,2]],[[1,1],[1,2],[1,3]],[[0,2],[1,0],[2,null],[3,3]]])assert.equal(fit(p).state,'insufficient data');
  const runs=[1,2,4].map(size=>({size,sizes:{ruleInstances:size*size},phases:{admission:{complete:true,ms:size*size,rss:null,footprint:null}}}));
  assert.equal(aggregate(runs,[1,2,4],1,1.3).admission.fits.ms.label,'superlinear in knob only');
});
test('surviving medians preserve counts and unavailable memory',()=>{
  const runs=[{size:1,sizes:{ruleInstances:3},phases:{admission:{complete:true,ms:4,rss:7,footprint:null}}}, {size:1,phases:{admission:{complete:false}}}];
  const a=aggregate(runs,[1],3,1.3).admission.rows[0];assert.equal(a.completed,1);assert.equal(a.requested,3);assert.equal(a.ms.median,4);assert.equal(a.footprint.median,null);
  assert.deepEqual(stats([2,4,6],3),{completed:3,requested:3,median:4,min:2,max:6});
});
test('end alone does not certify completion; exhaustion excludes only affected phases',()=>{
  const start=(span,stage)=>({type:'profile',span,stage,event:'start'});
  const end=(span,stage)=>({type:'profile',span,stage,event:'end',elapsedMs:1,sampledPeak:{rssBytes:10,footprintBytes:null}});
  const records=[start(1,'preparation'),end(1,'preparation'),start(2,'admission'),{type:'progress',detail:{admission:{failure:{resource:'work'}}}},end(2,'admission'),start(3,'checking')];
  const m=measurements(records,[]);assert.equal(m.preparation.complete,true);assert.equal(m.admission.complete,false);assert.equal(m.checking.complete,false);
  assert.equal(measurements([start(1,'checking'),end(1,'checking')],[]).checking.complete,false);
  const laterFailure=measurements([start(1,'admission'),end(1,'admission'),start(2,'checking'),end(2,'checking'),start(3,'presentation')],[{emptiness:[{outcome:'inconclusive',reason:{phase:'emptiness',resource:'work'}}]}]);
  assert.equal(laterFailure.admission.complete,true);assert.equal(laterFailure.checking.complete,false);
  const rounds=measurements([start(1,'admission'),end(1,'admission'),start(2,'checking'),end(2,'checking'),start(3,'presentation'),end(3,'presentation'),start(4,'admission'),end(4,'admission'),start(5,'checking')],[]);
  assert.equal(rounds.admission.ms,2);assert.equal(rounds.admission.rss,10);assert.equal(rounds.checking.complete,false);
  assert.equal(measurements([start(1,'preparation'),end(1,'preparation'),start(2,'publication')],[{unfinished:{phase:'assumptions',resource:'BDD tasks'}}]).preparation.complete,false);
  assert.equal(measurements([start(1,'checking'),end(1,'checking'),start(2,'presentation')],[{state:'incomplete',regions:[{outcome:'unsupported'}],emptiness:[{outcome:'inconclusive',reason:null,unresolved:true}]}]).checking.complete,true);
});
test('each family reaches its semantic and structural path; two-size smoke has no fit',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-zoo-'));
  try {
    for(const f of families.filter(f=>f!=='schema-layered'))assert.equal(source(f,2),source(f,2));
    const r=run({out:path.join(root,'tiny'),binary:'target/debug/examples/bench_schema',family:families,sizes:[2],repeat:1,threshold:1.3,ringLanes:1,ringRelays:2,schema:{depth:1,fanout:2}});
    for(const [name,{runs}] of Object.entries(r.families)) {
      const r=runs[0];assert.ok(r.checkerFinished,name);assert.ok(r.sizes.atoms>0,name);
      if(name==='negative-guarded') {assert.equal(r.after.admitted,true);assert.ok(r.sizes.dischargeProofs>0||joint(r));}
      if(['negative-unresolved','certification','removal-heavy','presentation'].includes(name))assert.equal(r.after.admitted,false,name);
      if(name==='certification') {assert.ok(r.outcomes[0].emptiness.some(e=>e.outcome!=='proved'));assert.equal(r.phases.checking.complete,true);}
      if(name==='removal-heavy') {assert.ok(r.sizes.removalProofs>=2);assert.equal(r.sizes.dischargeProofs,0);assert.ok(r.outcomes[0].emptiness.some(e=>e.outcome==='counterexample'));}
      if(name==='presentation')assert.ok(r.sizes.findings>=2);
      if(name.startsWith('fan-in'))assert.ok(r.outcomes[0].emptiness.some(e=>e.outcome==='counterexample'));
      if(name==='guarded-ring'||name==='guarded-fan-in'||name==='guarded-worlds') {assert.equal(r.before.ground.largestComponentAtoms,name==='guarded-ring'?12:6);assert.equal(r.after.admitted,true);assert.ok(r.outcomes[0].findings.some(f=>f.kind==='guarded-settlement'));assert.ok(joint(r)||r.attemptSummaries.some(a=>a.complete&&a.attempts.some(c=>c.kind==='guarded-bounds')));}
      if(name.startsWith('guarded-')&&name!=='guarded-schema') {assert.ok(joint(r)||r.guardedAttempts.some(g=>g.attempt.state==='completed'&&g.attempt.restricted&&g.attempt.coneAtoms>0));assert.ok(r.guardedAttempts.every(g=>Number.isFinite(g.attempt.preprocessingMs)&&Number.isFinite(g.attempt.iterationMs)));}
      if(name==='guarded-hub') {assert.equal(r.after.admitted,true);assert.equal(r.exit,0);assert.ok(r.outcomes[0].findings.some(f=>f.kind==='guarded-settlement'));assert.equal(r.outcomes[0].notices[0].result.state,'varying');}
      if(name==='writer-ring') {assert.equal(r.after.admitted,true);assert.equal(r.outcomes[0].emptiness[0].outcome,'proved');assert.equal(r.outcomes[0].notices[0].result.state,'varying');}
      if(name==='declared-groups') {assert.equal(r.exit,0);assert.equal(r.outcomes[0].emptiness[0].outcome,'proved');}
      if(name==='knowledge-scc') {assert.equal(r.exit,0);assert.equal(r.after.admitted,true);assert.equal(r.before.ground.largestComponentAtoms,2);assert.equal(r.outcomes[0].emptiness[0].outcome,'proved');assert.equal(r.outcomes[0].notices[0].result.state,'varying');}
      if(name==='schema-layered')assert.equal(r.after.admitted,true);
      if(name==='component-chain') {
        assert.equal(r.after.admitted,true);
        const starts=fs.readFileSync(path.join(root,'tiny','component-chain-2-0','memory.jsonl'),'utf8').trim().split('\n').map(JSON.parse).filter(r=>r.detail?.admission?.stage==='starting');
        assert.equal(starts[0].detail.admission.unresolvedComponents,3);
        assert.ok(r.outcomes[0].findings.some(f=>f.kind==='guarded-settlement'));
      }
    }
    assert.ok(r.families['guarded-ring'].attempts.some(a=>['guarded-bounds','structural-split'].includes(a.kind)));
    const smoke=run({out:path.join(root,'smoke'),binary:'target/debug/examples/bench_schema',family:['fan-in-input','negative-unresolved'],sizes:[1,2],repeat:1,threshold:1.3,inputOrder:'structural'});
    assert.equal(smoke.inputOrder,'structural');
    for(const f of Object.values(smoke.families))for(const r of f.runs) {assert.equal(r.inputOrder.requested,'structural');assert.equal(r.inputOrder.effective,'structural');assert.ok(Number.isFinite(r.phases.admission.bddResultNodes));assert.ok(Number.isFinite(r.phases.admission.peakAccountedConditionNodes));}
    assert.deepEqual(summarize(path.join(root,'smoke')),smoke);
    for(const hubReader of ['split','merged'])for(const hubRoutes of [true,false]) {
      const variant=run({out:path.join(root,`hub-${hubReader}-${hubRoutes}`),binary:'target/debug/examples/bench_schema',family:['guarded-hub'],sizes:[1],repeat:1,hubReader,hubRoutes});
      assert.equal(variant.hubReader,hubReader);assert.equal(variant.hubRoutes,hubRoutes);
      const checked=variant.families['guarded-hub'].runs[0];assert.equal(checked.exit,0);assert.equal(checked.after.admitted,true);assert.equal(checked.outcomes[0].notices[0].result.state,'varying');
      assert.deepEqual(summarize(path.join(root,`hub-${hubReader}-${hubRoutes}`)),variant);
    }
    const interrupted=path.join(root,'smoke','fan-in-input-2-0');
    const profile=fs.readFileSync(path.join(interrupted,'memory.jsonl'),'utf8').split('\n');
    const stop=profile.findIndex(l=>{try {const r=JSON.parse(l);return r.type==='profile'&&r.event==='start'&&r.stage==='checking';}catch{return false;}});
    assert.ok(stop>=0);
    fs.writeFileSync(path.join(interrupted,'memory.jsonl'),profile.slice(0,stop+1).join('\n')+'\n{"type":');
    fs.writeFileSync(path.join(interrupted,'stdout.txt'),'');
    const recovered=summarize(path.join(root,'smoke')).families['fan-in-input'];
    assert.equal(recovered.runs[1].checkerFinished,false);
    assert.equal(recovered.runs[1].phases.admission.complete,true);
    assert.equal(recovered.phases.checking.rows[1].completed,0);
    assert.equal(recovered.phases.checking.rows[1].requested,1);
    for(const f of Object.values(smoke.families))for(const p of Object.values(f.phases))assert.equal(p.fits.ms.knob.state,'insufficient data');
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('BDD work sums while accepted condition storage takes a peak',()=>{
  const records=[1,2].flatMap(span=>[{type:'profile',span,stage:'admission',event:'start'}, {type:'profile',span,stage:'admission',event:'end',elapsedMs:1,bddResultNodes:span*7,peakAccountedConditionNodes:span*3}, {type:'profile',span:10+span,stage:'checking',event:'start'}]);
  const measured=measurements(records,[]).admission;
  assert.equal(measured.bddResultNodes,21);
  assert.equal(measured.peakAccountedConditionNodes,6);
  for(const r of records)delete r.peakAccountedConditionNodes;
  assert.equal(measurements(records,[]).admission.peakAccountedConditionNodes,null);
});

test('symbolic exhaustion preserves independent admission and names the unknown atom',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-zoo-unknown-'));
  try {
    const out=path.join(root,'run');
    const result=run({out,binary:'target/debug/examples/bench_schema',family:['symbolic-exhaustion'],sizes:[8],repeat:1,limits:['--max-bdd-nodes','5']});
    const r=result.families['symbolic-exhaustion'].runs[0];
    assert.equal(r.checkerFinished,true);
    const outcome=r.outcomes[0];
    const obligation=e=>e.identity.obligation.at(-1);
    assert.equal(outcome.emptiness.find(e=>obligation(e)==='no_independent').outcome,'proved');
    assert.equal(outcome.emptiness.find(e=>obligation(e)==='no_bad').outcome,'inconclusive');
    assert.ok(outcome.unknownAtoms.some(u=>u.causeAtom.relation.named.at(-1)==='wide' && u.reason.resource==='BDD nodes'));
    const events=fs.readFileSync(path.join(out,'symbolic-exhaustion-8-0','memory.jsonl'),'utf8').trim().split('\n').map(JSON.parse);
    assert.ok(events.some(e=>e.detail?.admission?.unknownAtom?.atom?.endsWith('wide()')));
    assert.ok(events.some(e=>e.detail?.admission?.stage==='committed'||e.detail?.admission?.stage==='structural-committed'));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('SAT probes preserve checker outcomes and survive report recovery',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-sat-probe-'));
  try {
    const config={binary:'target/debug/examples/bench_schema',family:['negative-unresolved','guarded-ring'],sizes:[2],repeat:1};
    const normal=run({...config,out:path.join(root,'normal')});
    const probed=run({...config,out:path.join(root,'probed'),satProbe:true,satProbeCandidates:true});
    assert.equal(probed.satProbe,true);
    assert.equal(probed.satProbeCandidates,true);
    for(const name of config.family) {
      const a=normal.families[name].runs[0], b=probed.families[name].runs[0];
      // Each runner owns a different temporary root; compare every status field
      // except that root URI. CLI parity on the same root is tested separately.
      const statuses=r=>r.outcomes.map(({program,...status})=>status);
      assert.equal(a.exit,b.exit);assert.deepEqual(statuses(a),statuses(b));
      assert.equal(a.candidateProbes.length,0);assert.ok(b.candidateProbes.length>0);
      const counts=b.candidateProbes.at(-1).probe.counts;
      assert.equal(counts.candidates,counts.ruledOut+counts.notRuledOut+counts.unknown+counts.unexamined);
      assert.equal(a.satProbes.length,0);assert.ok(b.satProbes.length>0);
      for(const {probe:p} of b.satProbes) {
        assert.equal(p.state,name==='guarded-ring'?'unsat':'sat');
        assert.equal(p.verifiedStablePair,name!=='guarded-ring');
        if(name==='guarded-ring') assert.equal(p.existence.state,'every-world');
        else assert.equal(p.existence,null);
        assert.ok(p.variables>0);assert.ok(p.clauses>0);assert.ok(Number.isFinite(p.solveMs));
      }
    }
    assert.deepEqual(summarize(path.join(root,'probed')),probed);
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});


test('a recoverable admission skip does not discard a later completed result',()=>{
  const records=[{type:'profile',span:1,stage:'admission',event:'start'},
    {type:'progress',detail:{admission:{failure:'BDD tasks',skipped:'guaranteed-bounds'}}},
    {type:'profile',span:1,stage:'admission',event:'end',elapsedMs:3,sampledPeak:{rssBytes:7,footprintBytes:null}},
    {type:'profile',span:2,stage:'checking',event:'start'}];
  assert.equal(measurements(records,[{state:'proved'}]).admission.complete,true);
  assert.equal(measurements(records,[{state:'incomplete',admissionSkips:[{reason:{phase:'BDD operation',resource:'BDD tasks'}}]}]).admission.complete,false);
});

test('decoy options and the successful admission path survive saved reports',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-cone-order-'));
  try {
    for(const hubDecoyShape of ['full','near-full']) {
      const out=path.join(root,hubDecoyShape);
      const report=run({out,binary:'target/debug/examples/bench_schema',family:['guarded-hub'],sizes:[53],repeat:1,hubRoutes:false,hubDecoys:12,hubDecoyShape});
      assert.equal(report.hubDecoys,12);assert.equal(report.hubDecoyShape,hubDecoyShape);
      const r=report.families['guarded-hub'].runs[0];
      assert.equal(r.after.admitted,true);
      const attempts=r.guardedAttempts.filter(a=>a.phase==='relevant').map(a=>a.attempt);
      if (!joint(r)) {
      assert.ok(attempts.some(a=>a.pruning==='complete'&&a.coneAtoms<a.beforePruningAtoms));
      const first=attempts.filter(a=>a.position!==null).sort((a,b)=>a.position-b.position)[0];
      assert.equal(first.deferred,false);
      assert.ok(first.liveAtoms*10<first.componentAtoms*9);
      }
      assert.deepEqual(summarize(out),report);
    }
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('writer chains prune, admit and preserve dimensions and progress on recovery',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-chain-pruning-'));
  try {
    for(const hubValues of [1,2]) {
      const out=path.join(root,`values-${hubValues}`);
      const report=run({out,binary:'target/debug/examples/bench_schema',family:['guarded-hub'],sizes:[2],repeat:1,hubRoutes:false,hubWriters:2,hubReaders:2,hubValues,satProbeCandidates:true});
      assert.equal(report.hubWriters,2);assert.equal(report.hubReaders,2);assert.equal(report.hubValues,hubValues);
      const r=report.families['guarded-hub'].runs[0];
      assert.equal(r.after.admitted,true);
      assert.equal(r.exit,0);
      assert.ok(joint(r)||r.guardedAttempts.some(({attempt:a})=>a.pruning==='complete'&&a.coneAtoms<a.beforePruningAtoms&&a.coneRules<a.beforePruningRules));
      assert.ok(r.outcomes[0].findings.some(f=>f.kind==='guarded-settlement'));
      assert.deepEqual(summarize(out),report);
    }
    assert.throws(()=>source('guarded-hub',2,{hubWriters:-1}));
    assert.throws(()=>source('guarded-hub',2,{hubReaders:0}));
    assert.throws(()=>source('guarded-hub',2,{hubValues:2}));
    assert.throws(()=>source('guarded-hub',2,{hubWriters:2,hubDecoys:1}));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('schema runner keeps local component dumps and recovery retains their path', async()=>{
  const {spawnSync}=await import('node:child_process');
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-component-dump-'));
  try {
    const input=path.join(root,'source.den');
    fs.writeFileSync(input,source('negative-unresolved',1));
    const out=path.join(root,'run');
    const result=spawnSync('target/debug/examples/bench_schema',['--out',out,'--source',input,'--dump-component','component.jsonl'],{encoding:'utf8'});
    assert.equal(result.status,0,result.stderr);
    const report=JSON.parse(fs.readFileSync(path.join(out,'report.json')));
    assert.equal(report.componentDump,fs.realpathSync(path.join(out,'component.jsonl')));
    const data=fs.readFileSync(report.componentDump,'utf8');
    assert.ok(data.trim().split('\n').map(JSON.parse).some(r=>r.record==='graph-end' && r.complete));
    const recovery=spawnSync('target/debug/examples/bench_schema',['--summarize',out],{encoding:'utf8'});
    assert.equal(recovery.status,0,recovery.stderr);
    assert.equal(JSON.parse(fs.readFileSync(path.join(out,'report.json'))).componentDump,report.componentDump);
    assert.equal(fs.readFileSync(report.componentDump,'utf8'),data);
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});


test('tagged hub is a separate value domain, with persistent configuration',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-tagged-hub-'));
  try {
    const options={hubVariant:'tagged',hubWriters:2,hubTagValues:3};
    const text=source('guarded-hub',2,options);
    assert.equal(text,source('guarded-hub',2,options));
    assert.match(text,/tagged\(T\) :- applies0\(\), result0\(T\)/);
    assert.match(text,/input result0\(t: Tag\) within tags exactly_one\(group_by: \(\)\)/);
    assert.match(text,/input declared\(c: Class\) within classes at_most_one\(group_by: \(\)\)/);
    assert.match(text,/t2: Tag/);
    assert.doesNotMatch(text,/fa0_1/);
    const out=path.join(root,'run');
    const report=run({...options,out,binary:'target/debug/examples/bench_schema',family:['guarded-hub'],sizes:[2],repeat:1});
    assert.equal(report.hubVariant,'tagged');assert.equal(report.hubTagValues,3);
    const r=report.families['guarded-hub'].runs[0];
    assert.equal(r.after.admitted,true);assert.equal(r.exit,0);
    assert.equal(r.outcomes[0].notices[0].result.state,'varying');
    assert.ok(r.guardedAttempts.every(({attempt:g})=>Number.isFinite(g.lookaheadWork)&&Number.isFinite(g.lookaheadLimit)));
    assert.ok(r.attemptSummaries.every(a=>Number.isFinite(a.lookaheadWork)&&Number.isFinite(a.lookaheadLimit)));
    assert.deepEqual(summarize(out),report);
    for(const bad of [{hubVariant:'unknown'},{hubVariant:'tagged'},{...options,hubTagValues:0},{...options,hubValues:2},{...options,hubDecoys:1},{...options,hubReader:'merged'},{...options,hubRoutes:false},{hubTagValues:3}])assert.throws(()=>source('guarded-hub',2,bad));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});


test('writer ring dimensions and all input orders survive report recovery',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-writer-ring-'));
  try {
    const options={ringLanes:1,ringRelays:2,ringReaders:2};
    for(const inputOrder of ['key','reverse-key','structural']) {
      const out=path.join(root,inputOrder);
      const report=run({...options,out,inputOrder,binary:'target/debug/examples/bench_schema',family:['writer-ring'],sizes:[2],repeat:1});
      for(const [key,value] of Object.entries(options))assert.equal(report[key],value);
      const r=report.families['writer-ring'].runs[0];
      assert.equal(r.inputOrder.requested,inputOrder);assert.equal(r.inputOrder.effective,inputOrder);assert.equal(r.inputOrder.fallback,null);
      assert.equal(r.after.admitted,true);assert.equal(r.outcomes[0].emptiness[0].outcome,'proved');
      assert.equal(r.outcomes[0].notices[0].result.state,'varying');
      assert.deepEqual(summarize(out),report);
    }
    for(const bad of [{ringLanes:0},{ringRelays:1},{ringReaders:-1},{ringLanes:1.5}])assert.throws(()=>source('writer-ring',2,bad));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('writer ring completes the verification with co-read inputs outside uniqueness groups',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-writer-ring-storage-'));
  try {
    // Eight lanes per writer now exposes the declared-block trade-off and belongs
    // in measured runs. Keep a conclusive co-read control in the correctness gate.
    const report=run({out:path.join(root,'run'),binary:'target/debug/examples/bench_schema',family:['writer-ring'],sizes:[4],repeat:1,ringLanes:2,inputOrder:'structural',
      limits:['--timeout-ms','30000','--max-work','2000000000','--max-bdd-nodes','1000000','--max-bdd-tasks','10000000','--max-condition-nodes','100000000']});
    const r=report.families['writer-ring'].runs[0];
    assert.equal(r.inputOrder.effective,'structural');assert.equal(r.inputOrder.fallback,null);
    assert.equal(r.after.admitted,true);assert.equal(r.outcomes[0].state,'proved');
    assert.equal(r.outcomes[0].emptiness[0].outcome,'proved');
    assert.equal(r.outcomes[0].notices[0].result.state,'varying');
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('repeated field has independent appender and task-output paths and an absence reader',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-repeated-field-'));
  try {
    for(const inputOrder of ['key','structural']) {
      const report=run({out:path.join(root,inputOrder),binary:'target/debug/examples/bench_schema',family:['repeated-field'],sizes:[3],repeat:1,inputOrder});
      const r=report.families['repeated-field'].runs[0];
      assert.equal(r.exit,0);
      assert.equal(r.after.admitted,true);
      assert.equal(r.outcomes[0].notices[0].result.state,'varying');
    }
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('guarded schema is reproducible, scales facts independently and fixes blocks across depth',async()=>{
  const {guardedSchema}=await import('../guarded-schema.mjs');
  const base={sets:3,blocks:12,depth:2};
  assert.equal(guardedSchema(base).source,guardedSchema(base).source);
  const rows=guardedSchema({...base,stmts:4}), fewer=guardedSchema({...base,stmts:2});
  assert.equal(rows.shape.statementRows,2*fewer.shape.statementRows);
  assert.equal(rows.shape.totalBlocks,fewer.shape.totalBlocks);
  for(const depth of [1,3,6]) {
    const a=guardedSchema({...base,depth});
    assert.equal(a.shape.totalBlocks,guardedSchema(base).shape.totalBlocks);
    assert.equal(a.shape.statementRows,guardedSchema(base).shape.statementRows);
    assert.equal(a.shape.conditionSites,36);
  }
  const corpus=guardedSchema({sets:275,depth:2,fanout:5,stmts:3,triggers:1});
  assert.equal(corpus.shape.nestedBlocks,8250);assert.equal(corpus.shape.statementRows,24750);
  assert.doesNotMatch(corpus.source,/message_set|\bgiven\b|\bkept\b|\bmti\b|\bSTIP\b/i);
  assert.match(guardedSchema({...base,impossible:1}).source,/relation control_present\(\);/);
  assert.match(guardedSchema({...base,wide:1}).source,/decisions:\[format_recognized,accepted_field,written_value,violated,task_active\]/);
  for(const cfg of [{wide:2},{depth:0},{self:101},{blocks:2,depth:3},{impossible:2}])assert.throws(()=>guardedSchema(cfg));
});

test('guarded schema completion reports recover stages and control semantics',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-guarded-schema-'));
  try {
    for(const impossible of [0,1]) {
      const out=path.join(root,`case-${impossible}`);
      const report=run({out,binary:'target/debug/examples/bench_schema',family:['guarded-schema'],sizes:[1,2],repeat:1,schema:{sets:2,blocks:4,impossible},schemaAxis:'depth',limits:impossible?[]:['--sat-max-worlds','0']});
      const family=report.families['guarded-schema'];
      for(const r of family.runs) {
        assert.equal(r.checkerFinished,true);
        assert.equal(r.phases.preparation.complete,true);
        assert.ok(r.completion.preparationWork.workByStage['runtime-grounding']>0);
        assert.equal(r.shape.nestedBlocks,8);
        assert.equal(r.completion.preparations.find(p=>p.scope==='runtime').leastEnabled,false);
        if(impossible) assert.equal(r.outcomes[0].classification.accepted.state,'none');
      }
      assert.equal(family.completion['runtime-grounding'].work.state,'insufficient data');
      assert.deepEqual(summarize(out),report);
    }
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('guarded schema double-giving retains the profile and adds a guarded splice',async()=>{
  const {guardedSchema}=await import('../guarded-schema.mjs');
  const plain=guardedSchema({sets:3,self:100});
  const doubled=guardedSchema({sets:3,self:100,double:1});
  assert.equal(doubled.source,guardedSchema({sets:3,self:100,double:1}).source);
  for(let f=0;f<3;f++) {
    assert.ok(!plain.source.includes(`accepted_field(element_${f}) :- type_matches(format_${f});`));
    assert.ok(doubled.source.includes(`accepted_field(element_${f}) :- type_matches(format_${f});`));
  }
  assert.equal(doubled.shape.statementRows,plain.shape.statementRows);
  assert.throws(()=>guardedSchema({double:2}));
});

test('guarded schema double-giving exercises scoped completion pruning',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-double-giving-'));
  try {
    const out=path.join(root,'run');
    const report=run({out,binary:'target/debug/examples/bench_schema',family:['guarded-schema'],sizes:[2],repeat:1,schema:{depth:1,fanout:1,stmts:1,outs:1,values:1,self:100,double:1,wide:1},limits:['--completion-prune']});
    const family=report.families['guarded-schema'];
    const runReport=JSON.parse(fs.readFileSync(path.join(out,'guarded-schema-2-0','report.json'),'utf8'));
    assert.equal(runReport.checkerFinished,true);
    assert.ok(runReport.outcomes.some(o=>o.simplifications?.removedInstances>0));
    const components=runReport.outcomes.flatMap(o=>o.simplifications?.components??[]);
    assert.ok(components.some(c=>c.considered>0 && c.proved>0 && c.candidateHeads>0));
    assert.ok(components.filter(c=>c.considered>0).every(c=>['odd','non-unique'].includes(c.componentKind)));
    assert.ok(family);
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('guarded schema identifies its known odd edge, rule location and disabling guard',async()=>{
  const {guardedSchema}=await import('../guarded-schema.mjs');
  const {spawnSync}=await import('node:child_process');
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-odd-explanation-'));
  try {
    const source=guardedSchema({sets:1,depth:1,fanout:1,stmts:1,triggers:0,outs:1,values:1,self:100,odd:1}).source;
    const file=path.join(root,'program.den');
    fs.writeFileSync(file,source);
    fs.writeFileSync(path.join(root,'den.root'),'{}');
    const marker='accepted_field(element_0) :- type_matches(format_0), !accepted_field(element_0);';
    const line=source.split('\n').indexOf(marker)+1;
    assert.ok(line>0);
    const profile=path.join(root,'profile.jsonl');
    const args=[root,'--engine','sat','--json','--profile-memory',profile];
    const r=spawnSync('target/debug/examples/check',args,{encoding:'utf8',maxBuffer:16*1024*1024});
    assert.ok([0,1,2].includes(r.status),r.stderr);
    const records=fs.readFileSync(profile,'utf8').trim().split('\n').map(JSON.parse);
    const searches=records.filter(r=>r.type==='completion-sizes').flatMap(r=>r.sizes.searches);
    const details=searches.flatMap(s=>s.existence.componentDetails);
    assert.ok(details.length>0);
    assert.ok(details.every(c=>['classification','processing','whole-program'].includes(c.scope) &&
      ['W','W + H'].includes(c.context) && c.view==='unpruned'));
    const witnesses=details.flatMap(c=>c.oddExplanation?.cycles??[]);
    const cycle=witnesses.find(c=>c.length===1 && c[0].from==='accepted_field(element_0)');
    assert.ok(cycle,JSON.stringify(details));
    assert.equal(cycle[0].negative,true);
    assert.equal(cycle[0].to,cycle[0].from);
    const producer=cycle[0].producers.find(p=>p.source.location.line===line);
    assert.ok(producer);
    assert.ok(producer.guards.some(g=>g.atom==='type_matches(format_0)' && g.negative===false));
    assert.match(r.stderr,/odd cycle 1:/);
    assert.ok(r.stderr.includes(file+':'+line+':'),r.stderr);
    const human=spawnSync('target/debug/examples/check',[root,'--engine','sat','--verbose','--no-progress'],{encoding:'utf8',maxBuffer:16*1024*1024});
    assert.equal(human.status,r.status);
    assert.match(human.stdout,/odd cycles: at least/);
    assert.ok(human.stdout.includes(file+':'+line+':'));
    assert.throws(()=>guardedSchema({odd:2}));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('guarded schema type-field preserves verdicts and ordinary first attempts',async()=>{
  const {guardedSchema}=await import('../guarded-schema.mjs');
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-type-cut-'));
  try {
    const schema={depth:1,fanout:1,stmts:1,triggers:0,outs:1,values:1,self:0,typecut:1};
    const outcomes=[];
    for(const enabled of [false,true]) {
      const out=path.join(root,enabled?'on':'off');
      run({out,binary:'target/debug/examples/bench_schema',family:['guarded-schema'],sizes:[2],repeat:1,schema,
        limits:enabled?['--completion-split-depth','2','--completion-split-branches','16']:[]});
      const r=JSON.parse(fs.readFileSync(path.join(out,'guarded-schema-2-0','report.json'),'utf8'));
      assert.equal(r.checkerFinished,true);
      outcomes.push(r);
    }
    const [before,after]=outcomes;
    assert.equal(after.checkerExitCode,before.checkerExitCode);
    const [a,b]=outcomes.map(r=>r.outcomes[0]);
    assert.equal(b.state,a.state);assert.equal(b.hasFailures,a.hasFailures);
    assert.ok(b.branches.records.some(r=>r.state==='unsplit-proved'));
    assert.equal(b.branches.splits,0);
    assert.ok(b.branches.records.filter(r=>r.state.startsWith('unsplit-')).every(r=>r.phase!=='completion classification existence'));
    assert.ok(b.branches.records.filter(r=>r.state==='split').every(r=>r.children===2));
    assert.throws(()=>guardedSchema({typecut:2}));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});


test('guarded schema field-value checking preserves results and exploration probes skip structural work',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-field-cut-'));
  try {
    const rows=[];
    for(const mode of ['off','split','explore']){
      const out=path.join(root,mode);
      run({out,binary:'target/debug/examples/bench_schema',family:['guarded-schema'],sizes:[2],repeat:1,
        schema:{depth:1,fanout:1,stmts:1,triggers:0,outs:1,values:1,self:0,fieldcut:1},
        limits:mode==='off'?[]:['--completion-split-depth','3',...(mode==='explore'?['--completion-explore','--completion-force','--completion-prune']:[])]});
      rows.push(JSON.parse(fs.readFileSync(path.join(out,'guarded-schema-2-0','report.json'),'utf8')));
    }
    const a=rows[0].outcomes[0];
    for(const row of rows.slice(1)) {
    assert.equal(rows[0].checkerExitCode,row.checkerExitCode);
    const b=row.outcomes[0];assert.equal(a.state,b.state);assert.equal(a.hasFailures,b.hasFailures);
    for (const question of ['accepted','rejected','noMeaning','ambiguous'])
      assert.equal(b.classification[question].state,a.classification[question].state,question);
    for (const question of ['existence','uniqueness'])
      assert.equal(b.meaning[question].state,a.meaning[question].state,question);
    assert.deepEqual(b.obligations.map(o=>[o.name,o.state]),a.obligations.map(o=>[o.name,o.state]));
    }
    const ordinary=rows[1].outcomes[0];
    assert.ok(ordinary.branches.records.every(r=>!['completion rejection','completion accepted observations'].includes(r.phase)));
    assert.ok(ordinary.branches.records.some(r=>r.state==='unsplit-proved' && r.phase.includes('ambiguity')));
    const explored=rows[2].outcomes[0].branches.records;
    const probes=explored.flatMap((r,i)=>r.phase==='completion unsplit probe' && r.state==='completed'?[i]:[]);
    assert.ok(probes.length>0);
    for(const i of probes){
      const question=explored[i+1];
      assert.ok(['proved','counterexample'].includes(question.state));
      assert.equal(question.candidates.length,0);
      assert.equal(question.forcing.length,0);
    }
  }finally{fs.rmSync(root,{recursive:true,force:true});}
});


test('guarded schema catch-all control stays conditional through its cyclic guard',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-decoy-cut-'));
  try {
    const rows=[];
    for(const enabled of [false,true]) {
      const out=path.join(root,enabled?'on':'off');
      run({out,binary:'target/debug/examples/bench_schema',family:['guarded-schema'],sizes:[2],repeat:1,
        schema:{depth:1,fanout:1,stmts:1,triggers:0,outs:1,values:1,self:0,fieldcut:1,decoycut:1},
        limits:enabled?['--completion-prune','--completion-split-depth','3']:[]});
      rows.push(JSON.parse(fs.readFileSync(path.join(out,'guarded-schema-2-0','report.json'),'utf8')));
    }
    assert.equal(rows[0].checkerExitCode,rows[1].checkerExitCode);
    const [a,b]=rows.map(r=>r.outcomes[0]);
    for(const question of ['accepted','rejected','noMeaning','ambiguous'])
      assert.equal(a.classification[question].state,b.classification[question].state,question);
    for(const question of ['existence','uniqueness'])assert.equal(a.meaning[question].state,b.meaning[question].state,question);
    assert.deepEqual(a.obligations.map(o=>[o.name,o.state]),b.obligations.map(o=>[o.name,o.state]));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});


test('guarded schema implied presence removes a body edge without changing verdicts',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-implied-presence-'));
  try {
    const rows=[];
    for(const enabled of [false,true]) {
      const out=path.join(root,enabled?'on':'off');
      run({out,binary:'target/debug/examples/bench_schema',family:['guarded-schema'],sizes:[2],repeat:1,
        schema:{depth:1,fanout:1,stmts:1,triggers:0,outs:1,values:1,self:0,presence:1},
        limits:enabled?['--completion-prune']:[]});
      rows.push(JSON.parse(fs.readFileSync(path.join(out,'guarded-schema-2-0','report.json'),'utf8')));
    }
    const [a,b]=rows.map(r=>r.outcomes[0]);
    assert.equal(a.state,b.state); assert.equal(a.hasFailures,b.hasFailures);
    for(const key of ['accepted','rejected','noMeaning','ambiguous']) assert.equal(a.classification[key].state,b.classification[key].state,key);
    for(const key of ['existence','uniqueness']) assert.equal(a.meaning[key].state,b.meaning[key].state,key);
    assert.deepEqual(a.obligations.map(o=>[o.name,o.state]),b.obligations.map(o=>[o.name,o.state]));
    const proofs=b.simplifications.records.filter(r=>r.kind==='implied-body-literal' && r.head.relation.named?.[1]==='presence_ready');
    assert.ok(proofs.length>0); assert.ok(proofs.every(r=>r.proof==='structural' && r.removedInstances===0 && r.removedBodyLiterals===1));
    assert.ok(b.simplifications.removedBodyLiterals>0);
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('guarded schema formula partition cuts both children and preserves outcomes',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'den-formula-splits-'));
  try {
    const rows=[];
    for(const enabled of [false,true]) {
      const out=path.join(root,enabled?'on':'off');
      run({out,binary:'target/debug/examples/bench_schema',family:['guarded-schema'],sizes:[2],repeat:1,
        schema:{depth:1,fanout:1,stmts:1,triggers:0,outs:1,values:1,self:0,formulacut:1},
        limits:enabled?['--completion-split-depth','2']:[]});
      rows.push(JSON.parse(fs.readFileSync(path.join(out,'guarded-schema-2-0','report.json'),'utf8')));
    }
    const [a,b]=rows.map(r=>r.outcomes[0]);
    assert.equal(a.state,b.state); assert.equal(a.hasFailures,b.hasFailures);
    for(const key of ['accepted','rejected','noMeaning','ambiguous']) assert.equal(a.classification[key].state,b.classification[key].state,key);
    for(const key of ['existence','uniqueness']) assert.equal(a.meaning[key].state,b.meaning[key].state,key);
    assert.deepEqual(a.obligations.map(o=>[o.name,o.state]),b.obligations.map(o=>[o.name,o.state]));
    const candidates=b.branches.records.flatMap(r=>r.candidates);
    const selected=candidates.filter(r=>r.selected && r.formula && r.split.relation.named?.[1]==='formula_term');
    assert.ok(selected.length>0);
    assert.ok(selected.every(r=>r.childTrials.length===2 && r.childTrials.every(c=>c.complete && c.disabledEdges>0 && ['W','W+H'].includes(c.context))));
    assert.ok(selected.every(r=>r.derivedGuards.length<=32));
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});
