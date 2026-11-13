import test from 'node:test';
import assert from 'node:assert/strict';
import { hasGameSource } from '../model/game-source.mjs';
import { createPolicyRuntime, createPolicySession, decidePolicy, replayPolicyTrace, censorPolicyAction, ADAPTER_SOURCE_FILES, ADAPTER_SOURCE_HASHES, EXECUTION_RUNTIME, STRATEGY_REVIEW, FIXED_HERALDS } from '../model/policy-runtime.mjs';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync, mkdtempSync, mkdirSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
const engineTest = (name, fn) => test(name, { skip: !hasGameSource() && 'Pinned Steam game source required' }, fn);

test('policy sessions enforce the selected fixed-herald environment before starting a game', () => {
  const assumptions = JSON.parse(readFileSync(new URL('../model/mathematical-assumptions.json', import.meta.url)));
  assert.equal(assumptions.externalData.heralds.mode, 'fixed');
  assert.equal(assumptions.externalData.heralds.value, FIXED_HERALDS);
  for (const heralds of [0, 99, 101, null, '100', NaN, Infinity]) {
    assert.throws(() => createPolicySession({heralds}), /fixed herald count of 100/);
  }
});

engineTest('Policy capability exposes observations/actions only and replay audit data is separate', () => {
  const session = createPolicySession({ randomSeed: 9 }); const policy = session.policy;
  assert.deepEqual(Object.keys(policy).sort(), ['act','actions','observe']);
  for (const key of ['Game','evaluate','context','clock','timers','consumedRandom','events','environment','source','randomSeed']) assert.equal(policy[key], undefined);
  const observation = policy.observe(); assert.equal(Object.isFrozen(observation), true);
  assert.throws(() => { observation.shop.buildings[0].price = 0; }, TypeError);
  policy.act({ type: 'wait', milliseconds: 1000 }); policy.act({ type: 'click' });
  const trace = session.exportTrace(); assert.equal(Object.isFrozen(trace.randomTape), true);
  assert.equal(trace.environment.heralds, FIXED_HERALDS);
  assert.deepEqual(trace.strategyReview, STRATEGY_REVIEW);
  assert.equal(trace.strategyReview.strategyAdmissibilityCertified, false);
  assert.equal(trace.strategyReview.seededTimingAudit, 'decision-rule-review-required');
  assert.deepEqual(replayPolicyTrace(trace).policy.observe(), policy.observe());
  const altered = structuredClone(trace); altered.sourceHashes['main.js'] = '0'.repeat(64);
  assert.throws(() => replayPolicyTrace(altered), /hash mismatch/);
  assert.throws(() => createPolicyRuntime({ diagnosticMode: true }), /normal initialized/);
});

engineTest('replays require exact adapter sources and execution-runtime pins independently of game identities', () => {
  const session=createPolicySession();const trace=session.exportTrace();
  assert.equal(Object.keys(trace.sourceHashes).length,8);
  assert.deepEqual(trace.adapterSourceHashes,ADAPTER_SOURCE_HASHES);assert.deepEqual(trace.executionRuntime,EXECUTION_RUNTIME);
  assert.deepEqual(Object.keys(ADAPTER_SOURCE_HASHES),['model/runtime.mjs','model/maintenance-schedule.mjs','model/policy-runtime.mjs','model/evaluate-policy.mjs',
    'model/game-source.mjs','model/completion.mjs','model/catalogue.json','model/completion-profile.json','model/completion-requirements.json',
    'model/mathematical-assumptions.json']);
  assert.deepEqual(Object.keys(ADAPTER_SOURCE_HASHES),ADAPTER_SOURCE_FILES.map(name=>`model/${name}`));
  for(const [path,hash] of Object.entries(ADAPTER_SOURCE_HASHES))assert.equal(hash,createHash('sha256').update(readFileSync(new URL(`../${path}`,import.meta.url))).digest('hex'));
  for(const name of Object.keys(ADAPTER_SOURCE_HASHES)) {
    const altered=structuredClone(trace);altered.adapterSourceHashes[name]='0'.repeat(64);
    assert.throws(()=>replayPolicyTrace(altered),/adapter source hash mismatch/);
  }
  assert.throws(()=>replayPolicyTrace({...trace,adapterSourceHashes:undefined}),/older archives/);
  const oldPins=Object.fromEntries(Object.entries(trace.adapterSourceHashes).slice(0,3));
  assert.throws(()=>replayPolicyTrace({...trace,adapterSourceHashes:oldPins}),/older archives/);
  assert.throws(()=>replayPolicyTrace({...trace,executionRuntime:undefined}),/execution runtime mismatch/);
  for(const key of Object.keys(EXECUTION_RUNTIME))assert.throws(()=>replayPolicyTrace({...trace,executionRuntime:{...trace.executionRuntime,[key]:'different'}}),/execution runtime mismatch/);
});

engineTest('a changed completion implementation or profile file is rejected before replay in a fresh process', () => {
  const directory=mkdtempSync(join(tmpdir(),'cookie-dependency-pins-'));
  try {
    mkdirSync(join(directory,'model'));
    const originals=new Map();
    for(const name of ADAPTER_SOURCE_FILES) {
      const bytes=readFileSync(new URL(`../model/${name}`,import.meta.url));
      originals.set(name,bytes);writeFileSync(join(directory,'model',name),bytes);
    }
    const session=createPolicySession();session.policy.act({type:'wait',milliseconds:100});
    writeFileSync(join(directory,'trace.json'),JSON.stringify(session.exportTrace()));
    const script=`
      import {readFileSync} from 'node:fs';
      import {replayPolicyTrace} from './model/policy-runtime.mjs';
      try { replayPolicyTrace(JSON.parse(readFileSync('./trace.json')));process.exitCode=2; }
      catch(error) { if(!/adapter source hash mismatch/.test(error.message))throw error;console.log(error.message); }
    `;
    for(const name of ['completion.mjs','completion-profile.json','mathematical-assumptions.json']) {
      const bytes=originals.get(name);
      const changed=name.endsWith('.mjs') ? `${bytes}\n// Different completion implementation revision.\n`
        : `${JSON.stringify({...JSON.parse(bytes),version:'changed-profile'},null,2)}\n`;
      writeFileSync(join(directory,'model',name),changed);
      const child=spawnSync(process.execPath,['--input-type=module','-e',script],{cwd:directory,encoding:'utf8',timeout:10000});
      assert.equal(child.status,0,`${name}: ${child.stderr}`);
      assert.match(child.stdout,/adapter source hash mismatch/);
      writeFileSync(join(directory,'model',name),bytes);
    }
  } finally { rmSync(directory,{recursive:true,force:true}); }
});

test('Policy VM receives JSON data without host handles, RNG, real clock or dynamic code generation', () => {
  assert.deepEqual(decidePolicy('(o, actions) => actions[0]', { cookies: 1 }, [{ type: 'click' }]), { type: 'click' });
  assert.deepEqual(decidePolicy('() => [typeof process, typeof require, typeof Date, typeof Promise]', {}, []), ['undefined','undefined','undefined','undefined']);
  assert.deepEqual(decidePolicy('() => [typeof Intl, typeof WeakRef, typeof FinalizationRegistry]', {}, []), ['undefined','undefined','undefined']);
  assert.throws(() => decidePolicy('() => new Intl.DateTimeFormat().format()', {}, []), /undefined/);
  assert.throws(() => decidePolicy('() => Math.random()', {}, []), /RNG access/);
  assert.throws(() => decidePolicy('() => Function("return globalThis")()', {}, []), /Code generation/);
  assert.throws(() => decidePolicy('(o) => { o.cookies=99; return o; }', { cookies: 0 }, []), /read only/);
  assert.throws(() => decidePolicy('() => { while (true) {} }', {}, [], null, { timeoutMs: 10 }), /timed out/);
});

engineTest('A rejected action ends the policy session and remains explicit in the audit trace', () => {
  const session = createPolicySession();
  session.policy.act({ type: 'wait', milliseconds: 1000 });
  assert.throws(() => session.policy.act({ type: 'grant-cookies', amount: 1e100 }), /unknown action/);
  assert.throws(() => session.policy.observe(), /stopped after a failed action/);
  assert.throws(() => session.policy.act({ type: 'click' }), /stopped after a failed action/);
  const trace = session.exportTrace();
  assert.equal(trace.actions.length, 1); assert.equal(trace.failure.action.type, 'grant-cookies');
  assert.throws(() => replayPolicyTrace(trace), /failed action/);
});

engineTest('summary sessions retain failure and successful-prefix counts but cannot masquerade as full replays', () => {
  const session=createPolicySession({randomSeed:13,recordAudit:false});
  assert.throws(()=>session.policy.act({type:'sequence',actions:[{type:'wait',milliseconds:100},{type:'tiny-cookie'},{type:'grant-cookies'}]}),/unknown action/);
  assert.throws(()=>session.policy.observe(),/stopped after a failed action/);
  const summary=session.exportSummary({includeObservation:true});
  assert.equal(summary.recordingMode,'summary-only');assert.equal(summary.actionCount,2);
  assert.equal(summary.observation.elapsedMs,100);assert.equal(summary.observation.achievements['Tiny cookie'],true);
  assert.equal(summary.failure.action.type,'sequence');assert.match(summary.failure.message,/unknown action/);
  assert.equal(summary.actions,undefined);assert.equal(summary.randomTape,undefined);
  assert.throws(()=>session.exportTrace(),/no full replay history/);
  assert.throws(()=>replayPolicyTrace(summary),/summary-only data cannot be replayed/);
  const missing=createPolicySession().exportTrace();
  assert.throws(()=>replayPolicyTrace({...missing,randomTape:undefined}),/requires full recorded/);
});

engineTest('precommitted input sequences are exactly expanded native actions and replay without duplicate execution', () => {
  const a=createPolicySession({randomSeed:31});const b=createPolicySession({randomSeed:31});
  const actions=[{type:'wait',milliseconds:100},{type:'click'},{type:'wait',milliseconds:20},{type:'click'}];
  a.policy.act({type:'sequence',actions});
  for(const action of actions)b.policy.act(action);
  assert.deepEqual(a.policy.observe(),b.policy.observe());
  assert.deepEqual(a.exportTrace().actions,actions);
  assert.deepEqual(replayPolicyTrace(a.exportTrace()).policy.observe(),a.policy.observe());
  assert.throws(()=>createPolicySession().policy.act({type:'sequence',actions:[{type:'sequence',actions}]}),/flat native/);
});

test('sequence censoring retains actions scheduled at the horizon and excludes later inputs', () => {
  const action={type:'sequence',actions:[{type:'wait',milliseconds:100},{type:'click'},{type:'wait',milliseconds:20},{type:'click'}]};
  assert.deepEqual(censorPolicyAction(action,110).actions,[...action.actions.slice(0,2),{type:'wait',milliseconds:10}]);
  assert.deepEqual(censorPolicyAction(action,100).actions,[...action.actions.slice(0,2),{type:'wait',milliseconds:0}]);
  assert.deepEqual(censorPolicyAction(action,120),action);
});
