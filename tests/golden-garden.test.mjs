import test from 'node:test';
import assert from 'node:assert/strict';
import { planGoldenGarden } from '../model/golden-garden.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

// Independent cell-by-cell integer objective; no transfer states or row weights.
function score(plot) {
  let total = 0n;
  for (let y = 0; y < plot.length; y++) {
    for (let x = 0; x < plot[y].length; x++) {
      if (plot[y][x] !== 'goldenClover') continue;
      let neighbors = 0n;
      for (let yy = y - 1; yy <= y + 1; yy++) {
        for (let xx = x - 1; xx <= x + 1; xx++) {
          if (plot[yy]?.[xx] === 'nursetulip') neighbors++;
        }
      }
      total += 5n ** neighbors * 4n ** (8n - neighbors);
    }
  }
  return total;
}

test('row dynamic program equals exhaustive layouts through 4 by 4, including exterior edges', () => {
  for (const [width, height] of [[1,1], [1,6], [6,1], [2,3], [3,2], [3,4], [4,3], [4,4]]) {
    let best = -1n;
    for (let mask = 0; mask < 2 ** (width * height); mask++) {
      const plot = Array.from({ length: height }, (_, y) => Array.from({ length: width }, (_, x) =>
        mask & (1 << (y * width + x)) ? 'nursetulip' : 'goldenClover'));
      const value = score(plot);
      if (value > best) best = value;
    }
    const plan = planGoldenGarden(width, height);
    assert.equal(BigInt(plan.powerSum.numerator), best, `${width} by ${height}`);
    assert.equal(score(plan.plot), best, 'reconstructed witness');
  }
});

test('full-plot planner returns the exact alternating-row frequency witness', () => {
  const plan = planGoldenGarden();
  assert.deepEqual(plan.rowMasks, [0,63,0,63,0,63]);
  assert.equal(score(plan.plot), 3356800n);
  assert.deepEqual(plan.frequency, { numerator: 15313280, denominator: 5242880 });
  assert.equal(plan.frequency.numerator / plan.frequency.denominator, 2.9207763671875);
  assert.equal(plan.policyOptimalityCertified, false);
  for (const dimensions of [[0,6], [7,6], [6,0], [6,7], [2.5,3], [3,NaN]]) {
    assert.throws(() => planGoldenGarden(...dimensions), /dimensions/);
  }
});

test('native mature clay effects match the planned gain and retain the tulip production cost', {
  skip: !hasGameSource() && 'Pinned Steam source is unavailable',
}, () => {
  const runtime = createRuntime();
  runtime.evaluate(runtime.source.sources['minigameGarden.js'], 'minigameGarden.js');
  const farm = runtime.Game.Objects.Farm;
  farm.level = 9; farm.amount = 300; farm.highest = 300;
  farm.minigame.launch(); farm.minigameLoaded = true;
  const garden = farm.minigame;
  garden.soil = garden.soils.clay.id;
  const plan = planGoldenGarden();
  const fill = plot => {
    garden.plot = plot.map(row => row.map(key => [garden.plants[key].id + 1, garden.plants[key].mature]));
    garden.computeBoostPlot(); garden.computeEffs();
    return { ...garden.effs };
  };
  const planned = fill(plan.plot);
  assert.ok(Math.abs(planned.goldenCookieFreq - plan.frequency.numerator / plan.frequency.denominator) < 1e-12);
  assert.equal(planned.wrathCookieFreq, 1);
  assert.ok(planned.cps < 1, 'Nursetulips have a real production penalty');
  const allClovers = fill(Array.from({ length: 6 }, () => Array(6).fill('goldenClover')));
  assert.ok(Math.abs(allClovers.goldenCookieFreq - 2.35) < 1e-12);
  assert.ok(planned.goldenCookieFreq > allClovers.goldenCookieFreq);
  garden.freeze = true; garden.computeEffs();
  assert.equal(garden.effs.goldenCookieFreq, 1, 'freezing removes the frequency effect');
});
