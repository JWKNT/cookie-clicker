import assert from 'node:assert/strict';
import test from 'node:test';
import {
  PLOT_LIMITS, achievementValue, bankThreshold, checkerboard, exchangeIndex, godzamokBuff, goldenInterval,
  luckyPayout, marginalValueMultiplier, optimalRunMultiplier, orderTimes, roundTripCost, stageIncomes, wrinklerFactor,
} from '../assets/cookie-math.mjs';

const close = (actual, expected, tolerance, message) => assert.ok(Math.abs(actual - expected) <= tolerance, `${message}: ${actual} vs ${expected}`);

test('golden cookie interval matches the paper (447 s at base, 121 s with both upgrades)', () => {
  close(goldenInterval().mean, 446.6, 0.2, 'base');
  close(goldenInterval().share, 0.244, 0.001, 'base share');
  close(goldenInterval({ luckyDay: true, serendipity: true }).mean, 121.2, 0.1, 'both upgrades');
  close(goldenInterval({ luckyDay: true, serendipity: true }).share, 0.308, 0.001, 'share with both');
});

test('the Lucky! payout caps at 15 minutes of CpS and a banked cookie pays back in about 1,900 s', () => {
  assert.equal(luckyPayout(3000, 1), 450 + 13);
  assert.equal(luckyPayout(6000, 1), 900 + 13);
  assert.equal(luckyPayout(60000, 1), 900 + 13);
  close(bankThreshold(goldenInterval({ luckyDay: true, serendipity: true }).mean), 1862, 2, 'theta');
  close(bankThreshold(121.2, { lucky: 0.2447, chain: 0.0553, ruin: 0.2442 }), 3331, 2, 'stage 3');
});

test('the exchange index orders the example and agrees with the direct times', () => {
  const a = { price: 1000, gain: 10 };
  const b = { price: 5000, gain: 80 };
  assert.equal(exchangeIndex(a.price, a.gain, 100), 110);
  assert.equal(exchangeIndex(b.price, b.gain, 100), 112.5);
  const times = orderTimes(a, b, 100);
  assert.ok(times.ab < times.ba);
  close(times.ab, 55.45, 0.01, 'A then B');
  close(times.ba, 55.56, 0.01, 'B then A');
  // The index decides exactly: random pairs agree with the direct comparison
  for (let i = 0; i < 500; i++) {
    const x = { price: 10 ** (Math.random() * 6), gain: 10 ** (Math.random() * 3) };
    const y = { price: 10 ** (Math.random() * 6), gain: 10 ** (Math.random() * 3) };
    const c = 10 ** (Math.random() * 3);
    const t = orderTimes(x, y, c);
    if (Math.abs(t.ab - t.ba) > 1e-9 * t.ab) assert.equal(exchangeIndex(x.price, x.gain, c) < exchangeIndex(y.price, y.gain, c), t.ab < t.ba);
  }
});

test('the run multiplier reproduces the paper table, and the marginal value theorem errs', () => {
  const table = [[1.5, 4.24, 2.40], [2, 7.87, 4.92], [2.5, 12.03, 9.31], [3, 16.80, 16.80], [4, 28.39, 50.44], [6, 60.91, 397.38]];
  for (const [beta, v, naive] of table) {
    close(optimalRunMultiplier(beta), v, 0.01, `v at beta ${beta}`);
    close(marginalValueMultiplier(beta), naive, 0.01 * naive, `naive v at beta ${beta}`);
  }
});

test('achievements, wrinklers and the calm-or-wrath threshold', () => {
  close(achievementValue(8, 9.52, 1.1), 0.0214, 0.0003, 'achievement');
  assert.equal(achievementValue(0, 9.52), 0);
  close(wrinklerFactor(10), 6, 1e-12, 'W(10)');
  close(wrinklerFactor(12), 8.32, 1e-12, 'W(12)');
  assert.equal(wrinklerFactor(0), 1);
  const crossover = (62.8 - 8.7) / (11.8 - 8.5);
  close(crossover, 16.4, 0.1, 'threshold');
  assert.ok(stageIncomes(crossover - 0.1).wrath > stageIncomes(crossover - 0.1).calm);
  assert.ok(stageIncomes(crossover + 0.1).calm > stageIncomes(crossover + 0.1).wrath);
});

test('Godzamok round trips cost 71.25% of the buy-back and the buff averages 1 + 150 bU', () => {
  const { rebuy, net } = roundTripCost(1e6, 300);
  close(net / rebuy, 0.7125, 1e-12, 'net share');
  close(rebuy, (1e6 * (1 - 1.15 ** -300)) / 0.15, 1e-3, 'rebuy');
  const buff = godzamokBuff(0.01, 2200);
  assert.equal(buff.series.length, 300);
  close(buff.series[299], 6601, 1e-9, 'peak');
  close(buff.average, 3312, 1e-9, 'average');
  close(buff.series.reduce((s, m) => s + m, 0) / 300, buff.average, 1e-9, 'series mean');
});

test('the checkerboard layout lets every empty tile touch both parents on every plot', () => {
  for (let level = 1; level <= PLOT_LIMITS.length; level++) {
    const layout = checkerboard(level);
    assert.ok(layout.touchesBoth, `level ${level}`);
    assert.equal(layout.empty + layout.parents, layout.width * layout.height);
  }
  assert.deepEqual(checkerboard(1).rows, [['A', ''], ['', 'B']]);
  assert.equal(checkerboard(9).empty, 18);
});
