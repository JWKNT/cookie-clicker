/** Regression tests for the verified first-completion function on event observations. */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { r, terminal } from './completion-fixtures.mjs';
import { assessCompletion } from '../model/completion.mjs';

const root = fileURLToPath(new URL('./', import.meta.url));
const incomplete = structuredClone(terminal);
incomplete.achievements['Wake and bake'] = false;
const lost = structuredClone(terminal);
lost.progression.onAscend = true;
const point = (kind, elapsedMs, observation) => ({ kind, elapsedMs, observation });
const requirementsSha256 = createHash('sha256').update(readFileSync(new URL('../model/completion-requirements.json', import.meta.url))).digest('hex');
const trace = records => ({ schemaVersion: 1, requirementsSha256,
  checkpointSemantics: 'native-action-and-timer-boundaries-v1', profileId: r.profileId, records });
const cases = [];
const add = (name, value, first, valid = true) => cases.push({ name, value, first, valid });
add('no complete checkpoint', trace([point('initial', 0, incomplete), point('timer', 30, incomplete)]), null);
add('first hit survives later loss at same time', trace([
  point('initial', 0, incomplete), point('timer', 100, terminal), point('action', 100, lost),
]), 100);
add('first hit wins over later hit', trace([
  point('initial', 0, incomplete), point('action', 20, terminal), point('timer', 30, terminal),
]), 20);
add('censored prefix can complete later', trace([
  point('initial', 0, incomplete), point('timer', 30, incomplete), point('action', 31, terminal),
]), 31);
add('zero-time hit at later atomic boundary', trace([
  point('initial', 0, incomplete), point('action', 0, terminal),
]), 0);
add('backwards clock rejected', trace([
  point('initial', 0, incomplete), point('timer', 30, incomplete), point('action', 20, terminal),
]), null, false);
add('missing initial checkpoint rejected', trace([point('action', 0, incomplete)]), null, false);
add('fractional clock rejected', trace([point('initial', 0, incomplete), point('timer', 1.5, terminal)]), null, false);
add('empty trace rejected', trace([]), null, false);
const wrongProfile = trace([point('initial', 0, incomplete)]);
wrongProfile.profileId = 'another-profile';
add('wrong profile rejected', wrongProfile, null, false);
if (process.argv.includes('--engine')) {
  const { createRuntime } = await import('../model/runtime.mjs');
  const records = [];
  const runtime = createRuntime({ onTransition: record => records.push(record) });
  runtime.act({ type: 'click' });
  runtime.advance(100);
  runtime.act({ type: 'click' });
  assert.ok(records.length > 1, 'The runtime must emit initial and timer checkpoints');
  assert.equal(records[0].kind, 'initial');
  assert.ok(records.some(x => x.kind === 'timer'));
  assert.ok(records.some(x => x.kind === 'action'));
  assert.ok(records.every(Object.isFrozen));
  const first = records.find(x => assessCompletion(x.observation, r).complete)?.elapsedMs ?? null;
  add('actual source initial and timer checkpoints', trace(records), first);
  const { evaluatePolicy } = await import('../model/evaluate-policy.mjs');
  const evaluated = evaluatePolicy('() => ({type:"wait",milliseconds:5000})', { horizonMs: 1000, recordObservations: true });
  assert.equal(evaluated.status, 'censored');
  assert.equal(evaluated.checkpointTrace.requirementsSha256, requirementsSha256);
  add('actual evaluator full-horizon recorded trace', evaluated.checkpointTrace, evaluated.firstCompletionMs);
  const clicked = evaluatePolicy('(observation, actions, memory) => ({ action: memory ? {type:"wait",milliseconds:100} : {type:"click"}, memory:true })',
    { horizonMs: 200, recordObservations: true });
  assert.equal(clicked.status, 'censored');
  assert.equal(clicked.replay.actions[0].type, 'click');
  assert.ok(clicked.checkpointTrace.records.some(record => record.kind === 'action')); 
  add('actual evaluator mixed action and timer trace', clicked.checkpointTrace, clicked.firstCompletionMs);
}
const result = spawnSync(`${root}.lake/build/bin/tracecheck`, [], {
  input: JSON.stringify(cases.map(x => x.value)), encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
  timeout: 120000,
});
assert.equal(result.status, 0, result.stderr || result.error?.message);
const actual = JSON.parse(result.stdout);
assert.equal(actual.length, cases.length);
for (let i = 0; i < cases.length; i++) {
  assert.equal(actual[i].valid, cases[i].valid, cases[i].name);
  if (cases[i].valid) assert.equal(actual[i].firstCompletion?.elapsedMs ?? null, cases[i].first, cases[i].name);
}
console.log(`Lean first-completion trace checks passed for ${cases.length} traces.`);
