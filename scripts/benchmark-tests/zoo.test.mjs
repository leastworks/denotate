import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {fit,stats,aggregate,measurements,run,summarize,families,source} from '../bench-den-zoo.mjs';
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
    const r=run({out:path.join(root,'tiny'),binary:'target/debug/examples/bench_schema',family:families,sizes:[2],repeat:1,threshold:1.3});
    for(const [name,{runs}] of Object.entries(r.families)) {
      const r=runs[0];assert.ok(r.checkerFinished,name);assert.ok(r.sizes.atoms>0,name);
      if(name==='negative-guarded') {assert.equal(r.after.admitted,true);assert.ok(r.sizes.dischargeProofs>0);}
      if(['negative-unresolved','certification','removal-heavy','presentation'].includes(name))assert.equal(r.after.admitted,false,name);
      if(name==='certification') {assert.ok(r.outcomes[0].emptiness.some(e=>e.outcome!=='proved'));assert.equal(r.phases.checking.complete,true);}
      if(name==='removal-heavy') {assert.ok(r.sizes.removalProofs>=2);assert.equal(r.sizes.dischargeProofs,0);assert.ok(r.outcomes[0].emptiness.some(e=>e.outcome==='counterexample'));}
      if(name==='presentation')assert.ok(r.sizes.findings>=2);
      if(name.startsWith('fan-in'))assert.ok(r.outcomes[0].emptiness.some(e=>e.outcome==='counterexample'));
      if(name==='schema-layered')assert.equal(r.after.admitted,true);
    }
    const smoke=run({out:path.join(root,'smoke'),binary:'target/debug/examples/bench_schema',family:['fan-in-input','negative-unresolved'],sizes:[1,2],repeat:1,threshold:1.3});
    assert.deepEqual(summarize(path.join(root,'smoke')),smoke);
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
