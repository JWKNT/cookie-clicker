import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { buildCompletionContract, assessCompletion, captureCompletionSnapshot } from '../model/completion.mjs';

const read = name => JSON.parse(readFileSync(new URL(`../model/${name}`, import.meta.url), 'utf8'));
const contract = buildCompletionContract(read('catalogue.json'), read('completion-profile.json'));
const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';

test('Actual new-save observations satisfy the completion input contract', { skip }, () => {
  const r = createRuntime();
  const live = assessCompletion(r.snapshot(), contract);
  assert.equal(live.valid, true, live.issues.join('; '));
  assert.equal(live.complete, false);
  assert.equal(live.missing.filter(x => x.category === 'achievement').length, 598);
  const captured = captureCompletionSnapshot(r.Game, {}, { edition: 'steam' });
  assert.deepEqual(assessCompletion(captured, contract), live);
});

test('A legal engine purchase changes only the corresponding completion observations', { skip }, () => {
  const r = createRuntime();
  r.act({ type: 'wait', milliseconds: 1000 });
  for (let i = 0; i < 20; i++) {
    r.act({ type: 'click' });
    r.act({ type: 'wait', milliseconds: 50 });
  }
  r.act({ type: 'buy-building', id: 0 });
  r.act({ type: 'wait', milliseconds: 1000 });
  const observation = r.snapshot();
  const captured = captureCompletionSnapshot(r.Game, observation.history, { edition: 'steam' });
  assert.deepEqual(assessCompletion(captured, contract), assessCompletion(observation, contract));
  assert.equal(assessCompletion(observation, contract).complete, false);
  assert.equal(observation.progression.buildingAmounts.Cursor, 1);
});
