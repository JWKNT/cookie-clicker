import test from 'node:test';
import assert from 'node:assert/strict';
import { evaluatePolicy, summarizeExperiments } from '../model/evaluate-policy.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { baselinePolicySource } from '../model/baseline-policy.mjs';
import { createPolicySession, ADAPTER_SOURCE_FILES } from '../model/policy-runtime.mjs';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
const idle = '() => ({type:"wait", milliseconds:5000})';

test('full-engine evaluation censors unfinished play without a free terminal reward', { skip }, () => {
  const result = evaluatePolicy(idle, { horizonMs: 1000, recordObservations: true });
  assert.equal(result.status, 'censored');
  assert.equal(result.firstCompletionMs, null);
  assert.equal(result.observedUntilMs, 1000);
  assert.equal(result.decisions, 1);
  assert(result.checkpointCount > 30);
  assert.equal(result.checkpointTrace.records[0].kind, 'initial');
  assert.equal(result.checkpointTrace.records.at(-1).elapsedMs, 1000);
  assert.equal(result.completion.complete, false);
  assert.equal(result.strategyReview.strategyAdmissibilityCertified, false);
  assert.equal(result.strategyReview.seededTimingRule, 'forbidden');
  assert.deepEqual(result.audit.strategyReview, result.strategyReview);
  assert.deepEqual(result.replay.strategyReview, result.strategyReview);
  assert.deepEqual(summarizeExperiments([result]).strategyReview, result.strategyReview);
  assert.deepEqual(summarizeExperiments([result]).empiricalRestrictedMeanMilliseconds, { numerator: '1000', denominator: '1' });
});

test('zero-time loops and policy errors are unscored, not fast completion', { skip }, () => {
  const loop = evaluatePolicy('() => ({type:"wait", milliseconds:0})', { horizonMs: 1000, maxSameTimeActions: 3 });
  assert.equal(loop.status, 'decision-limit');
  assert.equal(loop.firstCompletionMs, null);
  assert.throws(() => summarizeExperiments([loop]), /cannot be scored/);
  const invalid = evaluatePolicy('() => ({type:"grant-cookies",amount:1e100})', { horizonMs: 1000 });
  assert.equal(invalid.status, 'policy-error');
  assert.equal(invalid.decisionFailure, null); // This is an action failure, not a failed decision.
  assert.equal(invalid.firstCompletionMs, null);
  assert.throws(() => summarizeExperiments([invalid]), /cannot be scored/);
});

test('decision timeout validation accepts only the positive uint32 Node timeout range', () => {
  for (const decisionTimeoutMs of [0, -1, 1.5, NaN, Infinity, 0x100000000, '1000', null]) {
    assert.throws(() => evaluatePolicy(idle, { decisionTimeoutMs }), /positive uint32/);
  }
  for (const maxSameTimeActions of [0, -1, 1.5, NaN, Infinity, Number.MAX_SAFE_INTEGER + 1]) {
    assert.throws(() => evaluatePolicy(idle, { maxSameTimeActions }), /positive decision budgets/);
  }
});

test('a timed-out decision exports its exact public inputs after memory updates without another native action', { skip }, () => {
  const source = `(o,a,m) => {
    if (!m) return {action:{type:'wait',milliseconds:20},memory:{phase:1,history:['wait']}};
    if (m.phase === 1) return {action:{type:'name-bakery',name:'Decision diagnostic'},
      memory:{phase:2,history:[...m.history,'name'],lastTime:o.elapsedMs}};
    while (true) {}
  }`;
  // Allow the two finite decisions to finish under parallel test/build load.
  // The third decision still contains an actual nonterminating loop.
  const options = { horizonMs: 1000, maxDecisions: 9, maxSameTimeActions: 3, decisionTimeoutMs: 1000 };
  const prefix = [{ type: 'wait', milliseconds: 20 }, { type: 'name-bakery', name: 'Decision diagnostic' }];
  const expected = createPolicySession();
  for (const action of prefix) expected.policy.act(action);
  const publicInputs = JSON.parse(JSON.stringify({ observation: expected.policy.observe(), actions: expected.policy.actions(),
    memory: { phase: 2, history: ['wait', 'name'], lastTime: 20 } }));
  const full = evaluatePolicy(source, options);
  const summary = evaluatePolicy(source, { ...options, recordAudit: false });
  for (const result of [full, summary]) {
    assert.equal(result.status, 'policy-error');
    assert.match(result.error, /Script execution timed out after 1000ms/);
    assert.equal(result.decisions, 2);
    assert.equal(result.observedUntilMs, 20);
    assert.equal(result.audit.actionCount, 2);
    assert.equal(result.audit.failure, null);
    assert.deepEqual(result.observation, publicInputs.observation);
    assert.deepEqual(result.decisionFailure.inputs, publicInputs);
    assert.equal(result.decisionFailure.policySha256, createHash('sha256').update(source).digest('hex'));
    assert.equal(result.decisionFailure.decisionIndex, 2);
    assert.equal(result.decisionFailure.sameTimeActions, 1);
    assert.equal(result.decisionFailure.message, result.error);
    assert.deepEqual(result.decisionFailure.experimentBudgets, options);
    assert.deepEqual(result.experimentBudgets, options);
    // Allowlist the standalone diagnostic. All three input values are checked
    // against the observation-only interface above, not a private engine dump.
    assert.deepEqual(Object.keys(result.decisionFailure).sort(),
      ['schemaVersion', 'kind', 'policySha256', 'decisionIndex', 'sameTimeActions', 'experimentBudgets', 'message', 'inputs'].sort());
    assert.throws(() => summarizeExperiments([result]), /cannot be scored/);
  }
  assert.deepEqual(full.replay.actions, prefix);
  assert.equal(summary.replay, null);
  assert.deepEqual(full.decisionFailure, summary.decisionFailure);
});

test('execution budgets are recorded separately from semantic environment identity', { skip }, () => {
  const first = evaluatePolicy(idle, { horizonMs: 10, maxDecisions: 7, maxSameTimeActions: 3, decisionTimeoutMs: 1000 });
  const second = evaluatePolicy(idle, { horizonMs: 10, maxDecisions: 11, maxSameTimeActions: 5, decisionTimeoutMs: 0xffffffff });
  assert.equal(first.status, 'censored', first.error);
  assert.equal(second.status, 'censored', second.error);
  assert.notDeepEqual(first.experimentBudgets, second.experimentBudgets);
  assert.equal(first.environmentSha256, second.environmentSha256);
  for (const name of Object.keys(first.experimentBudgets)) assert.equal(Object.hasOwn(first.audit.environment, name), false);
  assert.equal(summarizeExperiments([first, second]).samples, 2);
});

test('policy observations do not expose the experiment seed or future tape', { skip }, () => {
  const source = `(observation) => {
    if ('randomTape' in observation || 'seed' in observation || typeof process !== 'undefined' || typeof Date !== 'undefined') throw Error('leaked capability');
    return {type:'wait',milliseconds:100};
  }`;
  const result = evaluatePolicy(source, { randomSeed: 49, horizonMs: 100 });
  assert.equal(result.status, 'censored');
  const random = evaluatePolicy('() => ({type:"wait", milliseconds:Math.random()})', { horizonMs: 100 });
  assert.equal(random.status, 'policy-error');
});

test('restricted sample means retain censored costs and reject mismatched experiments', () => {
  const base = { requestedHorizonMs: 1000, policySha256: 'fixed', profileId: 'full' };
  const complete = { ...base, status: 'complete', firstCompletionMs: 200, observedUntilMs: 200 };
  const censored = { ...base, status: 'censored', firstCompletionMs: null, observedUntilMs: 1000 };
  const summary = summarizeExperiments([complete, censored]);
  assert.deepEqual(summary.empiricalRestrictedMeanMilliseconds, { numerator: '1200', denominator: '2' });
  assert.equal(summary.unrestrictedExpectedCompletionTime, null);
  assert.equal(summary.optimalityCertified, false);
  assert.throws(() => summarizeExperiments([{ ...censored, observedUntilMs: 500 }]), /full horizon/);
  assert.throws(() => summarizeExperiments([complete, { ...censored, policySha256: 'other' }]), /must share/);
  assert.throws(() => summarizeExperiments([complete, { ...censored, environmentSha256: 'different-calendar-or-heralds' }]), /must share/);
});

test('experiment summaries hold the environment fixed while allowing different sample seeds', { skip }, () => {
  const first = evaluatePolicy(idle, { randomSeed: 1, horizonMs: 10 });
  const second = evaluatePolicy(idle, { randomSeed: 2, horizonMs: 10 });
  assert.equal(first.environmentSha256, second.environmentSha256);
  assert.equal(summarizeExperiments([first, second]).samples, 2);
  assert.throws(() => evaluatePolicy(idle, { randomSeed: 1, heralds: 0, horizonMs: 10 }), /fixed herald count of 100/);
  const changed = evaluatePolicy(idle, { randomSeed: 1, epochMs: Date.UTC(2026, 9, 30, 12), horizonMs: 10 });
  assert.throws(() => summarizeExperiments([first, changed]), /must share/);
});

test('the baseline grows through native actions while remaining incomplete under the full goal', { skip }, () => {
  const result = evaluatePolicy(baselinePolicySource(), { horizonMs: 2000 });
  assert.equal(result.status, 'censored', result.error);
  assert(result.observation.cookiesEarned >= 15);
  assert(result.observation.progression.buildingAmounts.Cursor >= 1);
  assert.equal(result.completion.complete, false);
});

test('atomic and batched schedules include the same native click at the exact censoring horizon', { skip }, () => {
  const schedule = [
    { type: 'wait', milliseconds: 100 }, { type: 'click' },
    { type: 'wait', milliseconds: 20 }, { type: 'click' },
    { type: 'wait', milliseconds: 20 }, { type: 'click' },
    { type: 'wait', milliseconds: 20 }, { type: 'click' },
  ];
  const atomic = `(o,a,m) => { const inputs=${JSON.stringify(schedule)}; const i=m?.i || 0;
    return {action:inputs[i] || {type:'wait',milliseconds:1000},memory:{i:i+1}}; }`;
  const batched = `() => ({type:'sequence',actions:${JSON.stringify(schedule)}})`;
  const options = { horizonMs: 140, randomSeed: 31, recordObservations: true };
  const a = evaluatePolicy(atomic, options);
  const b = evaluatePolicy(batched, options);
  assert.equal(a.status, 'censored', a.error);
  assert.equal(b.status, 'censored', b.error);
  assert.equal(a.observation.cookieClicks, 3);
  assert.equal(a.observedUntilMs, 140);
  assert.equal(a.decisions, 7);
  assert.equal(b.decisions, 1);
  assert.deepEqual(a.replay.actions, [...schedule.slice(0, 6), { type: 'wait', milliseconds: 0 }]);
  assert.deepEqual(b.replay.actions, a.replay.actions);
  assert.deepEqual(b.observation, a.observation);
  assert.deepEqual(b.checkpointTrace.records, a.checkpointTrace.records);
});

test('a horizon inside a positive wait ends that prefix without another policy decision', { skip }, () => {
  const source = `(o) => o.elapsedMs === 0
    ? {type:'sequence',actions:[{type:'wait',milliseconds:100},{type:'tiny-cookie'}]}
    : {type:'tiny-cookie'}`;
  const result = evaluatePolicy(source, { horizonMs: 50, maxSameTimeActions: 3 });
  assert.equal(result.status, 'censored', result.error);
  assert.equal(result.decisions, 1);
  assert.equal(result.observedUntilMs, 50);
  assert.equal(result.observation.achievements['Tiny cookie'], false);
  assert.deepEqual(result.replay.actions, [{ type: 'wait', milliseconds: 50 }]);
});

test('zero-time inputs are included even at a zero horizon and retain intermediate checkpoints', { skip }, () => {
  const schedule = [{ type: 'tiny-cookie' }, { type: 'name-bakery', name: 'Sequence fixture' }, { type: 'wait', milliseconds: 1 }];
  const source = `() => ({type:'sequence',actions:${JSON.stringify(schedule)}})`;
  const result = evaluatePolicy(source, { horizonMs: 0, recordObservations: true });
  assert.equal(result.status, 'censored', result.error);
  assert.equal(result.observedUntilMs, 0);
  assert.equal(result.observation.achievements['Tiny cookie'], true);
  assert.equal(result.observation.achievements["What's in a name"], true);
  const actionRecords = result.checkpointTrace.records.filter(record => record.kind === 'action');
  assert.equal(actionRecords.length, 3);
  assert.equal(actionRecords[0].elapsedMs, 0);
  assert.equal(actionRecords[0].observation.achievements['Tiny cookie'], true);
  assert.equal(actionRecords[0].observation.achievements["What's in a name"], false);
  assert.equal(actionRecords[1].observation.achievements["What's in a name"], true);
  assert.equal(result.firstCompletionMs, null); // A subsystem achievement is not the full terminal target.
});

test('atomic and batched zero-time loops at the horizon exhaust their budget instead of scoring censorship', { skip }, () => {
  for (const zeroTime of [{ type: 'wait', milliseconds: 0 },
    { type: 'sequence', actions: [{ type: 'wait', milliseconds: 0 }, { type: 'click' }] }]) {
    const source = `(o) => o.elapsedMs < 20 ? {type:'wait',milliseconds:20} : ${JSON.stringify(zeroTime)}`;
    const result = evaluatePolicy(source, { horizonMs: 20, maxSameTimeActions: 3 });
    assert.equal(result.status, 'decision-limit');
    assert.equal(result.observedUntilMs, 20);
    assert.equal(result.decisions, 4);
    assert.equal(result.firstCompletionMs, null);
    assert.throws(() => summarizeExperiments([result]), /cannot be scored/);
  }
});

test('early baseline click batching preserves native growth at a purchase boundary', { skip }, () => {
  const atomic = evaluatePolicy(baselinePolicySource(), { horizonMs: 300, randomSeed: 31 });
  const batched = evaluatePolicy(baselinePolicySource({ inputBatchMilliseconds: 300 }), { horizonMs: 300, randomSeed: 31 });
  assert.equal(atomic.status, 'censored', atomic.error);
  assert.equal(batched.status, 'censored', batched.error);
  assert.equal(atomic.observation.cookieClicks, 5);
  assert.equal(batched.observation.cookieClicks, atomic.observation.cookieClicks);
  assert.deepEqual(batched.observation, atomic.observation);
});

test('full and summary experiments have identical observations, checkpoints, progress and counts', {skip},()=>{
  const source=baselinePolicySource({inputBatchMilliseconds:300});const fullProgress=[];const summaryProgress=[];
  const options={horizonMs:2000,randomSeed:71,recordObservations:true,progressEveryMs:100};
  const full=evaluatePolicy(source,{...options,onProgress:p=>fullProgress.push(p)});
  const summary=evaluatePolicy(source,{...options,recordAudit:false,onProgress:p=>summaryProgress.push(p)});
  for(const key of ['status','error','firstCompletionMs','observedUntilMs','decisions','checkpointCount','environmentSha256','policySha256','completion','observation','checkpointTrace'])assert.deepEqual(summary[key],full[key],key);
  assert.deepEqual(summaryProgress,fullProgress);assert.equal(summary.replay,null);
  assert.equal(summary.audit.actionCount,full.replay.actions.length);assert.equal(summary.audit.randomDrawCount,full.replay.randomTape.length);
  assert.deepEqual(summary.audit.sourceHashes,full.audit.sourceHashes);assert.deepEqual(summary.audit.environment,full.audit.environment);
  assert.deepEqual(summary.audit.adapterSourceHashes,full.audit.adapterSourceHashes);assert.deepEqual(summary.audit.executionRuntime,full.audit.executionRuntime);
  const {randomSeed,...environment}=summary.audit.environment;
  const hash=(adapterSourceHashes,executionRuntime)=>createHash('sha256').update(JSON.stringify({environment,adapterSourceHashes,executionRuntime})).digest('hex');
  assert.equal(summary.environmentSha256,hash(summary.audit.adapterSourceHashes,summary.audit.executionRuntime));
  assert.notEqual(summary.environmentSha256,hash({...summary.audit.adapterSourceHashes,'model/runtime.mjs':'0'.repeat(64)},summary.audit.executionRuntime));
  for(const name of ['model/completion.mjs','model/completion-profile.json','model/catalogue.json','model/completion-requirements.json']) {
    assert.match(summary.audit.adapterSourceHashes[name],/^[a-f0-9]{64}$/);
    assert.notEqual(summary.environmentSha256,hash({...summary.audit.adapterSourceHashes,[name]:'0'.repeat(64)},summary.audit.executionRuntime));
  }
  assert.notEqual(summary.environmentSha256,hash(summary.audit.adapterSourceHashes,{...summary.audit.executionRuntime,v8:'different'}));
  assert.equal(summary.audit.actions,undefined);assert.equal(summary.audit.randomTape,undefined);
  assert.equal(summarizeExperiments([full,summary]).samples,2);
});

test('summary experiment failures report the actual completed prefix rather than a stale observation', {skip},()=>{
  const source=()=>({type:'sequence',actions:[{type:'wait',milliseconds:100},{type:'tiny-cookie'},{type:'grant-cookies'}]});
  const full=evaluatePolicy(source.toString(),{horizonMs:1000});
  const summary=evaluatePolicy(source.toString(),{horizonMs:1000,recordAudit:false});
  assert.equal(summary.status,'policy-error');assert.match(summary.error,/unknown action/);
  assert.equal(summary.observedUntilMs,100);assert.equal(summary.observation.achievements['Tiny cookie'],true);
  assert.equal(summary.audit.actionCount,2);assert.deepEqual(summary.observation,full.observation);
  assert.deepEqual(summary.audit.failure,full.audit.failure);assert.throws(()=>summarizeExperiments([summary]),/cannot be scored/);
});

test('summary CLI writes compact experiment metadata and emits progress without a replay tape', {skip},()=>{
  const directory=mkdtempSync(join(tmpdir(),'cookie-summary-'));const output=join(directory,'result.json');
  try {
    const child=spawnSync(process.execPath,['tools/evaluate-policy.mjs','--policy','growth','--seconds','0.2','--summary-only','--progress','--progress-seconds','0.1','--decision-timeout-ms','1234','--max-same-time-actions','17','--max-decisions','42','--output',output],{cwd:new URL('..',import.meta.url),encoding:'utf8',timeout:10000});
    assert.equal(child.status,0,child.stderr);
    const data=JSON.parse(readFileSync(output,'utf8'));const result=data.results[0];
    assert.equal(result.replay,null);assert.equal(result.audit.recordingMode,'summary-only');assert.equal(result.audit.environment.randomSeed,1);
    assert.equal(Object.keys(result.audit.sourceHashes).length,8);assert.match(result.policySha256,/^[a-f0-9]{64}$/);
    assert.equal(Object.keys(result.audit.adapterSourceHashes).length,ADAPTER_SOURCE_FILES.length);assert.equal(result.audit.executionRuntime.node,process.version);
    assert.deepEqual(result.experimentBudgets,{horizonMs:200,maxDecisions:42,maxSameTimeActions:17,decisionTimeoutMs:1234});
    const progress=child.stderr.trim().split('\n').map(line=>JSON.parse(line)).filter(row=>'checkpointCount' in row);
    assert(progress.length>0);assert(progress.every(row=>row.actionCount>0&&row.randomDrawCount>0&&row.rssBytes>0));
  } finally {rmSync(directory,{recursive:true,force:true});}
});

test('CLI rejects an invalid VM timeout before starting an experiment',()=>{
  const child=spawnSync(process.execPath,['tools/evaluate-policy.mjs','--seconds','0','--decision-timeout-ms','0'],
    {cwd:new URL('..',import.meta.url),encoding:'utf8',timeout:10000});
  assert.notEqual(child.status,0);
  assert.match(child.stderr,/Decision timeout must be a positive uint32/);
  assert.equal(child.stdout,'');
});
