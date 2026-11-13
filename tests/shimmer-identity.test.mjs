import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { decideSeasonAction } from '../model/season-policy.mjs';

const skip = !hasGameSource();

test('distinct native shimmer controls remain selectable when their numeric counter saturates', { skip }, () => {
  const r = createRuntime({ diagnosticMode: true });
  const G = r.Game;
  // This is an exact native saturation implication, not a reached new-save
  // trajectory. The constructor, DOM handlers and reward callbacks are real.
  G.shimmersN = 2 ** 53;
  G.season = 'christmas';
  const golden = new G.shimmer('golden', { type: 'cookie storm drop' }, true);
  const reindeer = new G.shimmer('reindeer');
  assert.equal(golden.id, reindeer.id);
  assert.equal(G.shimmersN, 2 ** 53);
  assert.notEqual(golden.l, reindeer.l);
  const seen = r.snapshot().shimmers;
  assert.equal(seen.length, 2);
  assert.equal(new Set(seen.map(s => s.id)).size, 2);
  assert(seen.every(s => typeof s.id === 'string' && /^shimmer-node:\d+$/.test(s.id)));
  const target = seen.find(s => s.type === 'reindeer');
  assert.deepEqual(r.snapshot().shimmers.map(s => s.id), seen.map(s => s.id));
  assert(r.actions().some(a => a.type === 'click-shimmer' && a.id === target.id));
  const decision = decideSeasonAction(r.snapshot(), {}, { eldeer: false, preserveChallengeAchievements: false });
  assert.deepEqual(decision.action, { type: 'click-shimmer', id: target.id });
  const bankBefore = G.cookies;
  r.act(decision.action);
  assert(G.cookies > bankBefore);
  assert.equal(G.shimmers.length, 1);
  assert.equal(G.shimmers[0], golden);
  const replacement = new G.shimmer('reindeer');
  assert.equal(replacement.id, reindeer.id);
  assert.throws(() => r.act({ type: 'click-shimmer', id: target.id }), /shimmer is absent/);
  const replacementId = r.snapshot().shimmers.find(s => s.type === 'reindeer').id;
  assert.notEqual(replacementId, target.id);
  r.act({ type: 'click-shimmer', id: seen.find(s => s.type === 'golden').id });
  assert.equal(G.shimmers.length, 1);
  assert.equal(G.shimmers[0], replacement);
});

test('safe native shimmer IDs remain compatible with existing actions', { skip }, () => {
  const r = createRuntime({ diagnosticMode: true });
  const shimmer = new r.Game.shimmer('golden', { type: 'cookie storm drop' }, true);
  assert(Number.isSafeInteger(shimmer.id));
  assert.equal(r.snapshot().shimmers[0].id, shimmer.id);
  r.act({ type: 'click-shimmer', id: shimmer.id });
  assert.equal(r.Game.shimmers.length, 0);
});
