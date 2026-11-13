import assert from 'node:assert/strict';
import test from 'node:test';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'Pinned Steam source is unavailable';
const fixture = (draw = 0.5) => createRuntime({ diagnosticMode: true, randomTape: Array(100000).fill(draw) });

test('untimed constructor forms do not increment the golden-cookie counter', { skip }, () => {
  const runtime = fixture(), G = runtime.Game;
  // These are source-path fixtures, not a new-save trajectory. The forms cover
  // Orbs, Fortune/FtHoF, wrath FtHoF, and storm drops, respectively.
  for (const [label, forceObj, noCount] of [
    ['unforced', undefined, undefined], ['noWrath', { noWrath: true }, undefined],
    ['wrath', { wrath: true }, undefined], ['storm', { type: 'cookie storm drop' }, 1],
  ]) {
    const shimmer = new G.shimmer('golden', forceObj, noCount);
    assert.equal(Object.hasOwn(shimmer, 'spawnLead'), false, label);
    shimmer.force = 'blab';
    runtime.act({ type: 'click-shimmer', id: shimmer.id });
    assert.equal(G.goldenClicks, 0, label);
    assert.equal(G.goldenClicksLocal, 0, label);
    assert.throws(() => runtime.act({ type: 'click-shimmer', id: shimmer.id }), /shimmer is absent/);
  }
});

test('Distilled essence creates one counted leader and one uncounted extra cookie', { skip }, () => {
  const runtime = fixture(0.005), G = runtime.Game, golden = G.shimmerTypes.golden;
  G.Upgrades['Distilled essence of redoubled luck'].bought = 1;
  golden.minTime = 1; golden.maxTime = 1; golden.time = 1;
  G.updateShimmers();
  const shimmers = [...G.shimmers].filter(shimmer => shimmer.type === 'golden');
  assert.equal(shimmers.length, 2);
  assert.deepEqual(shimmers.map(shimmer => !!shimmer.spawnLead), [true, false]);
  for (const shimmer of shimmers) {
    shimmer.force = 'blab';
    runtime.act({ type: 'click-shimmer', id: shimmer.id });
  }
  assert.equal(G.goldenClicks, 1);
  assert.equal(G.goldenClicksLocal, 1);
});

test('a continuing chain produces a counted leader after exactly 91 shimmer updates', { skip }, () => {
  const runtime = fixture(), G = runtime.Game, golden = G.shimmerTypes.golden;
  G.cookies = 1e12; G.cookiesEarned = 1e12; G.cookiesPs = 1e9;
  golden.minTime = 90; golden.maxTime = 90; golden.time = 90;
  G.updateShimmers();
  const leader = G.shimmers.find(shimmer => shimmer.spawnLead);
  assert(leader);
  leader.force = 'chain cookie';
  runtime.act({ type: 'click-shimmer', id: leader.id });
  assert.equal(G.goldenClicks, 1);
  assert(golden.chain > 0);
  assert.equal(golden.time, 0);
  assert.equal(golden.minTime, 90);
  assert.equal(golden.maxTime, 90);
  for (let index = 0; index < 90; index++) G.updateShimmers();
  assert.equal(G.shimmers.filter(shimmer => shimmer.spawnLead).length, 0);
  G.updateShimmers();
  const next = G.shimmers.find(shimmer => shimmer.spawnLead);
  assert(next);
  runtime.act({ type: 'click-shimmer', id: next.id });
  assert.equal(G.goldenClicks, 2);
  // Calling updateShimmers directly counts native updates only. This diagnostic
  // does not claim that a policy may run those updates without elapsed time.
});
