import test from 'node:test';
import assert from 'node:assert/strict';
import { HAND_PICKED_BOUND, handPickedMatureMilliseconds, conditionalHandPickedTailMilliseconds } from '../model/hand-picked-bound.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
const minimum = HAND_PICKED_BOUND.minimumFirstAttemptClockMilliseconds;

// Synthetic late-game fixtures isolate native handlers. They are not complete
// legal trajectories from a new save, and never touch an installed game save.
function fastestFixture({ random = 0.75 } = {}) {
  const runtime = createRuntime({ randomTape: Array(5000).fill(random) });
  const G = runtime.Game;
  G.lumps = 0; G.lumpsTotal = 0;
  G.Upgrades['Diabetica Daemonicus'].bought = 1;
  G.Upgrades['Ichor syrup'].bought = 1;
  G.dragonLevel = 27;
  G.dragonAura = G.dragonAurasBN["Dragon's Curve"].id;
  G.dragonAura2 = G.dragonAurasBN['Reality Bending'].id;
  G.computeLumpTimes();
  return runtime;
}

test('the exact minimum and binary64 threshold imply the same integer clock boundary', () => {
  const fraction = HAND_PICKED_BOUND.exactMinimumMatureMilliseconds;
  assert.equal(Math.ceil(fraction.numerator / fraction.denominator), minimum);
  assert.equal(Math.ceil(HAND_PICKED_BOUND.binary64MinimumMatureMilliseconds), minimum);
  const values = [];
  for (const diabetica of [false, true]) for (const ichor of [false, true]) {
    for (const curveMultiplier of [0, 0.1, 1, 1.1]) values.push(handPickedMatureMilliseconds({ diabetica, ichor, curveMultiplier }));
  }
  assert.equal(Math.min(...values), HAND_PICKED_BOUND.binary64MinimumMatureMilliseconds);
  assert.throws(() => handPickedMatureMilliseconds({ curveMultiplier: 2 }), /Invalid vanilla/);
});

test('conditional geometric calculations remain explicitly separate from a game guarantee', () => {
  assert.equal(conditionalHandPickedTailMilliseconds(0), 0);
  assert.equal(conditionalHandPickedTailMilliseconds(1), minimum);
  assert.equal(conditionalHandPickedTailMilliseconds(2), minimum * 1.5);
  assert.equal(conditionalHandPickedTailMilliseconds(3), minimum * 1.75);
  assert.equal(conditionalHandPickedTailMilliseconds(3, 0), minimum * 3);
  assert.equal(conditionalHandPickedTailMilliseconds(3, 1), minimum);
  assert.match(HAND_PICKED_BOUND.expectedBoundStatus, /No unconditional/);
});

test('native aura multipliers never exceed 1.1, including duplicate-slot fixture values', { skip }, () => {
  const { Game: G } = createRuntime();
  G.dragonLevel = G.dragonLevels.length - 1;
  let max = 0;
  for (const first of Object.keys(G.dragonAuras)) for (const second of Object.keys(G.dragonAuras)) {
    G.dragonAura = Number(first); G.dragonAura2 = Number(second);
    const multiplier = G.auraMult("Dragon's Curve");
    assert(multiplier <= 1.1);
    max = Math.max(max, multiplier);
  }
  assert.equal(max, 1.1);
});

test('native maturity formula agrees for every upgrade and aura combination', { skip }, () => {
  const { Game: G } = createRuntime();
  G.dragonLevel = 27;
  const curve = G.dragonAurasBN["Dragon's Curve"].id;
  const reality = G.dragonAurasBN['Reality Bending'].id;
  for (const diabetica of [false, true]) for (const ichor of [false, true]) {
    G.Upgrades['Diabetica Daemonicus'].bought = Number(diabetica);
    G.Upgrades['Ichor syrup'].bought = Number(ichor);
    for (const [first, second, curveMultiplier] of [[0, 0, 0], [reality, 0, 0.1], [curve, 0, 1], [curve, reality, 1.1]]) {
      G.dragonAura = first; G.dragonAura2 = second; G.computeLumpTimes();
      assert.equal(G.lumpMatureAge, handPickedMatureMilliseconds({ diabetica, ichor, curveMultiplier }));
    }
  }
});

test('native harvest cannot succeed one millisecond before the threshold but can at the threshold', { skip }, () => {
  const runtime = fastestFixture();
  const G = runtime.Game;
  const start = G.lumpT;
  runtime.clock.now = start + minimum - 1;
  G.clickLump();
  assert.equal(G.lumpT, start);
  assert.equal(G.Achievements['Hand-picked'].won, 0);
  runtime.clock.now = start + minimum;
  G.clickLump();
  assert.equal(G.Achievements['Hand-picked'].won, 1);
  assert.equal(G.lumpT, start + minimum);
});

test('a failed native unripe harvest resets the timer and immediate retries make no random draw', { skip }, () => {
  const runtime = fastestFixture({ random: 0.25 });
  const G = runtime.Game;
  runtime.clock.now = G.lumpT + minimum;
  G.clickLump();
  const failedAt = runtime.clock.now;
  assert.equal(G.Achievements['Hand-picked'].won, 0);
  assert.equal(G.lumpT, failedAt);
  const consumed = runtime.consumedRandom.length;
  G.clickLump();
  runtime.clock.now = failedAt + minimum - 1;
  G.clickLump();
  assert.equal(G.lumpT, failedAt);
  assert.equal(runtime.consumedRandom.length, consumed);
});

test('native offline processing advances the prior timer and cannot backdate it before the run', { skip }, () => {
  const runtime = fastestFixture();
  const G = runtime.Game;
  const start = G.lumpT;
  runtime.clock.now = start + 2 * G.lumpOverripeAge + 1234;
  G.loadLumps();
  assert(G.lumpT >= start);
  assert(G.lumpT <= runtime.clock.now);
  assert(Math.abs((Math.floor(runtime.clock.now) - G.lumpT) - 1234) < 1);
  assert.equal(G.Achievements['Hand-picked'].won, 0);
});

test('native clone hover and scheduled frames determine Hand-picked success without a random-value probe in a prepared diagnostic fixture', { skip }, () => {
  const runtime = createRuntime({ diagnosticMode: true });
  runtime.advance(100);
  const G = runtime.Game;
  // Fix the synthetic state's seed, independently of startup draw order.
  // This preparation is not a policy action or a claim of legal reachability.
  // The following native input schedule neither reads nor probes the generator.
  G.seed = 'sbjuo';
  G.Objects.You.amount = 1; G.Objects.You.bought = 1;
  G.lumpsTotal = 0; G.lumps = 0; G.computeLumpTimes();
  G.lumpT = Math.floor(runtime.clock.now) - G.lumpMatureAge;
  runtime.act({ type: 'building-hover', id: 19, x: 32, y: 32 });
  runtime.act({ type: 'wait', milliseconds: 100 });
  runtime.act({ type: 'building-hover', id: 19, x: 32, y: 32, leave: true });
  runtime.act({ type: 'harvest-lump' });
  assert.equal(G.Achievements['Hand-picked'].won, 1);
  assert.equal(G.lumps, 1);
  // The action trace contains native input and elapsed time, no RNG inspection.
  assert.deepEqual(runtime.events.map(x => x.type), ['wait', 'building-hover', 'wait', 'building-hover', 'harvest-lump']);
});

test('clone rendering leaves a repeatable seeded generator; leaving and redrawing restores fresh randomness', { skip }, () => {
  const runtime = createRuntime({ diagnosticMode: true });
  const you = runtime.Game.Objects.You;
  you.amount = 1; you.mouseOn = true; you.mousePos = [32, 32];
  you.draw();
  const count = runtime.consumedRandom.length;
  const first = runtime.evaluate('Math.random()');
  assert.equal(runtime.consumedRandom.length, count);
  you.draw();
  assert.equal(runtime.evaluate('Math.random()'), first);
  assert.equal(runtime.consumedRandom.length, count);
  you.mouseOn = false; you.draw();
  runtime.evaluate('Math.random()');
  assert.equal(runtime.consumedRandom.length, count + 1);
});
