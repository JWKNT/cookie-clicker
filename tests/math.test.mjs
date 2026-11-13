import assert from 'node:assert/strict';
import test from 'node:test';
import {
  GODZAMOK_BONUS, LUCKY_SHARE, PLOT_LIMITS, STAGE_THRESHOLD, THREE_ITEMS, achievementValue, bankThreshold,
  checkerboard, chipOrderTime, chipRatio, completionTimeSaved, effectShares, exchangeIndex, expectedIncome,
  fastestSchedule, fraction, fractionText, fractionValue, godzamokBuff, goldenInterval, horizonForPause,
  indexRuleOrder, marginalValueMultiplier, marketReturn, optimalRunMultiplier, orderTimes, permutations,
  refillSeconds, roundTripCost, runCost, scheduleTime, stageIncomes, wrinklerFactor,
} from '../assets/cookie-math.mjs';

const close = (actual, expected, tolerance, label) => assert.ok(Math.abs(actual - expected) <= tolerance, `${label}: ${actual} is not within ${tolerance} of ${expected}`);
// A fixed seed makes the generated cases reproducible.
const generator = (seed) => () => {
  seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
  return seed / 2 ** 32;
};
const names = (order) => order.map((at) => THREE_ITEMS[at].name).join('');
const timeOf = (order, items = THREE_ITEMS) => scheduleTime(order.map((at) => items[at]));

test('the difference of the two orders is the difference of the indices times a positive factor', () => {
  const a = { price: 1000, gain: 10 };
  const b = { price: 5000, gain: 80 };
  close(exchangeIndex(a.price, a.gain, 100), 110, 1e-9, 'E_A');
  close(exchangeIndex(b.price, b.gain, 100), 112.5, 1e-9, 'E_B');
  const times = orderTimes(a, b, 100);
  close(times.ab, 55.45, 0.01, 'A then B');
  close(times.ba, 55.56, 0.01, 'B then A');
  const random = generator(20261029);
  for (let i = 0; i < 500; i++) {
    const x = { price: 10 ** (random() * 6), gain: 10 ** (random() * 3) };
    const y = { price: 10 ** (random() * 6), gain: 10 ** (random() * 3) };
    const c = 10 ** (random() * 3);
    const t = orderTimes(x, y, c);
    const factor = (x.gain * y.gain) / ((c + x.gain) * (c + y.gain));
    const difference = factor * (exchangeIndex(x.price, x.gain, c) - exchangeIndex(y.price, y.gain, c));
    close(t.ab - t.ba, difference, 1e-9 * (t.ab + t.ba), 'Theorem 2.1');
  }
});

test('with three items the index rule loses 3/110 of a second', () => {
  assert.equal(names(indexRuleOrder(THREE_ITEMS)), 'ABC');
  const times = Object.fromEntries(permutations(3).map((order) => [names(order), fractionText(timeOf(order))]));
  assert.deepEqual(times, { ABC: '13/2', ACB: '53/8', BAC: '33/5', BCA: '356/55', CAB: '395/56', CBA: '538/77' });
  const fastest = fastestSchedule(THREE_ITEMS);
  assert.equal(names(fastest.order), 'BCA');
  assert.equal(fractionText(fastest.time), '356/55');
  const gap = fractionValue(timeOf(indexRuleOrder(THREE_ITEMS))) - fractionValue(fastest.time);
  close(gap, 3 / 110, 1e-12, 'gap');
  close(gap / 6.5, 0.004, 0.0003, 'the loss of 0.4%');
  // From a bank that holds all prices, the purchases need no time.
  assert.equal(fractionText(fastestSchedule(THREE_ITEMS, 1, 14).time), '0');
  assert.deepEqual(fraction(6, -4), { n: -3n, d: 2n });
});

test('the recursion over the sets of bought items gives the least time of all orders', () => {
  const random = generator(20261113);
  for (let round = 0; round < 120; round++) {
    const count = 2 + Math.floor(random() * 4);
    const items = Array.from({ length: count }, () => ({ price: 1 + Math.floor(random() * 40), gain: Math.floor(random() * 9) }));
    const income = 1 + Math.floor(random() * 5);
    const bank = Math.floor(random() * 30);
    const best = fastestSchedule(items, income, bank);
    let least = Infinity;
    for (const order of permutations(count)) least = Math.min(least, fractionValue(scheduleTime(order.map((at) => items[at]), income, bank)));
    close(fractionValue(best.time), least, 1e-12, `list ${round}`);
    close(fractionValue(scheduleTime(best.order.map((at) => items[at]), income, bank)), least, 1e-12, `order ${round}`);
  }
});

test('the wait for a golden cookie: exact means, the upper limit and the share of Lucky', () => {
  const base = goldenInterval();
  const one = goldenInterval({ luckyDay: true });
  const both = goldenInterval({ luckyDay: true, serendipity: true });
  assert.deepEqual([base.window, one.window, both.window], [18000, 9000, 4500]);
  close(base.frames, 4396.85, 0.005, 'frames, no upgrade');
  close(one.frames, 2467.53, 0.005, 'frames, one upgrade');
  close(both.frames, 1384.74, 0.005, 'frames, two upgrades');
  close(base.mean, 446.56, 0.005, 'seconds, no upgrade');
  close(one.mean, 232.25, 0.005, 'seconds, one upgrade');
  close(both.mean, 121.16, 0.005, 'seconds, two upgrades');
  for (const wait of [base, one, both]) {
    assert.ok(wait.frames <= wait.limit, 'the limit of Lemma 3.2');
    assert.ok(wait.limit - wait.frames < 2, 'the limit is less than two frames above the mean');
  }
  close(base.limit, 4398.13, 0.005, 'limit, no upgrade');
  const shares = effectShares();
  close(Object.values(shares).reduce((sum, share) => sum + share, 0), 1, 1e-12, 'shares');
  close(shares.lucky, shares.frenzy, 1e-12, 'Frenzy and Lucky have the same share');
  close(shares.lucky, 0.4217, 0.00005, 'share of Lucky');
  close(shares.building, 0.1, 0.0005, 'share of the building effects');
  close(shares.click, 0.04, 0.0005, 'share of Click frenzy');
  close(shares.chain, 0.0084, 0.0001, 'share of Cookie chain');
  assert.equal(LUCKY_SHARE, 0.4217);
  close(bankThreshold(base.mean), 7060, 0.5, 'theta, no upgrade');
  close(bankThreshold(one.mean), 3672, 0.5, 'theta, one upgrade');
  close(bankThreshold(both.mean), 1915, 0.5, 'theta, two upgrades');
});

test('a purchase changes the expected income as Theorem 3.1 says', () => {
  const rate = LUCKY_SHARE / 121.16;
  const theta = 1 / (0.15 * rate);
  const change = (bank, income, price, gain) => expectedIncome(bank - price, income + gain, rate) - expectedIncome(bank, income, rate);
  // (a) below the cap: gain - 0.15 lambda price, positive exactly when the payback time is less than theta
  for (const [price, gain] of [[1000, 1], [1000, 0.6], [1000, 0.5], [400, 0.2]]) {
    close(change(5000, 1, price, gain), gain - 0.15 * rate * price, 1e-12, 'case (a)');
    assert.equal(change(5000, 1, price, gain) > 0, price / gain < theta, `payback ${price / gain}`);
  }
  // (b) above the cap before and after: (1 + 900 lambda) gain
  close(change(20000, 1, 1000, 1), (1 + 900 * rate) * 1, 1e-12, 'case (b)');
});

test('the ratio rule gives the fastest order of upgrades when each chip costs the same effort', () => {
  const x = { price: 10, factor: 1.05 };
  const y = { price: 100, factor: 3 };
  close(chipRatio(x.price, x.factor), 0.0048, 0.00005, 'ratio of X');
  close(chipRatio(y.price, y.factor), 0.0067, 0.00005, 'ratio of Y');
  close(chipOrderTime([y, x]), 103.3, 0.05, 'Y first');
  close(chipOrderTime([x, y]), 105.2, 0.05, 'X first');
  const random = generator(4);
  for (let round = 0; round < 200; round++) {
    const upgrades = Array.from({ length: 4 }, () => ({ price: 1 + Math.floor(random() * 500), factor: 1.01 + random() * 3 }));
    const sorted = [...upgrades].sort((a, b) => chipRatio(b.price, b.factor) - chipRatio(a.price, a.factor));
    let least = Infinity;
    for (const order of permutations(4)) least = Math.min(least, chipOrderTime(order.map((at) => upgrades[at])));
    close(chipOrderTime(sorted), least, 1e-9 * least, `upgrades ${round}`);
  }
  // Example 4.2: the chip number B takes B seconds at speed 1. X: 1 chip, factor 2. Y: 2 chips, factor 100.
  const effort = (from, to) => (to * to - from * from) / 2;
  assert.ok(chipRatio(1, 2) > chipRatio(2, 100));
  assert.equal(effort(0, 1) + effort(1, 3) / 2, 5 / 2);
  assert.equal(effort(0, 2) + effort(2, 3) / 100, 81 / 40);
});

test('the factor of a run is the one minimum point of the time for each unit of progress', () => {
  const table = { 1.5: [4.24, 1.62, 2.40], 2: [7.87, 1.99, 4.92], 2.5: [12.03, 2.29, 9.31], 3: [16.80, 2.56, 16.80], 4: [28.39, 3.05, 50.44], 6: [60.91, 3.93, 397.38] };
  for (const [beta, [factor, prestige, known]] of Object.entries(table)) {
    const v = optimalRunMultiplier(Number(beta));
    close(v, factor, 0.005, `v* at ${beta}`);
    close(Math.cbrt(v), prestige, 0.005, `prestige at ${beta}`);
    close(marginalValueMultiplier(Number(beta)), known, 0.005, `known rule at ${beta}`);
    // rho decreases before v* and increases after it
    let best = Infinity;
    let at = 0;
    let turns = 0;
    let last = Infinity;
    let falling = true;
    for (let x = 1.02; x < 4000; x *= 1.001) {
      const cost = runCost(x, Number(beta));
      if (cost < best) [best, at] = [cost, x];
      if (falling && cost > last) [falling, turns] = [false, turns + 1];
      else if (!falling && cost < last) turns += 1;
      last = cost;
    }
    close(at, v, 0.002 * v, `minimum point at ${beta}`);
    assert.equal(turns, 1, `one turn at ${beta}`);
  }
  // At beta = 3/2 the factor of the prestige is the golden ratio.
  close(Math.cbrt(optimalRunMultiplier(1.5)), (1 + Math.sqrt(5)) / 2, 1e-9, 'golden ratio');
  close(optimalRunMultiplier(3), marginalValueMultiplier(3), 1e-6, 'the two rules agree at beta = 3');
});

test('a pause for a permanent gain: the limit H x / (1 + x)', () => {
  assert.equal(completionTimeSaved(1, 100), 50);
  assert.equal(completionTimeSaved(0, 100), 0);
  const first = achievementValue(8, 9.52, 1.1);
  const second = achievementValue(8, 9.56, 1.1);
  const combined = achievementValue(8, 9.52, 1.1, 2);
  close(1 + first, 1.0214, 0.00005, 'one achievement');
  close(1 + combined, (1 + first) * (1 + second), 1e-12, 'two achievements, one after the other');
  close(completionTimeSaved(first, 77), 1.61, 0.005, 'pause for one achievement');
  close(completionTimeSaved(combined, 77), 3.19, 0.005, 'pause for two achievements');
  assert.ok(completionTimeSaved(combined, 77) < combined * 77);
  const horizon = horizonForPause(combined, 4);
  assert.ok(horizon > 96 && horizon < 97, `a run of 4 hours repays from ${horizon} hours`);
  close(completionTimeSaved(combined, horizon), 4, 1e-9, 'the two functions agree');
});

test('Godzamok: the cost of a round trip and the mean of the buff', () => {
  const trip = roundTripCost(1000, 100);
  close(trip.rebuy, 1000 * (1 - 1.15 ** -100) / 0.15, 1e-9, 'cost to buy back');
  close(trip.net / trip.rebuy, 0.7125, 1e-12, 'share that the round trip costs');
  const buff = godzamokBuff(GODZAMOK_BONUS[0], 2200);
  assert.equal(buff.series.length, 300);
  close(buff.series.at(-1), 6601, 1e-9, 'end of the buff');
  close(buff.average, 3312, 1e-9, 'mean of the buff');
  close(buff.series.reduce((sum, value) => sum + value, 0) / 300, buff.average, 1e-9, 'mean of the series');
  close(3 * buff.average, 9900, 50, 'clicks with the buff, in units of production');
  assert.deepEqual(GODZAMOK_BONUS, [0.01, 0.005, 0.0025]);
});

test('wrinklers and the estimate for a pledge', () => {
  assert.equal(wrinklerFactor(0), 1);
  close(wrinklerFactor(4), 1.68, 1e-9, 'W(4)');
  close(wrinklerFactor(8), 4.12, 1e-9, 'W(8)');
  close(wrinklerFactor(10), 6, 1e-9, 'W(10)');
  close(wrinklerFactor(12), 8.32, 1e-9, 'W(12)');
  close(STAGE_THRESHOLD, 16.4, 0.05, 'click income at which the pledge earns more');
  const below = stageIncomes(16);
  const above = stageIncomes(17);
  assert.ok(below.wrath > below.calm && above.calm > above.wrath);
});

test('Grimoire, Garden and Stock Market', () => {
  close(refillSeconds(19, 72) / 60, 23, 0.5, 'a cast at full magic');
  close(refillSeconds(0, 53) / 60, 40, 0.5, 'a cast from empty magic');
  assert.ok(refillSeconds(10, 63) < refillSeconds(0, 53));
  assert.equal(PLOT_LIMITS.length, 9);
  for (let level = 1; level <= 9; level++) {
    const plot = checkerboard(level);
    assert.ok(plot.touchesBoth, `farm level ${level}`);
    assert.equal(plot.empty + plot.parents, plot.width * plot.height);
  }
  assert.deepEqual(checkerboard(1).rows, [['A', ''], ['', 'B']]);
  assert.equal(checkerboard(9).empty, 18);
  // On the full plot, parent A is in the columns 1, 3, 5 and parent B in the columns 2, 4, 6.
  for (const row of checkerboard(9).rows) row.forEach((tile, column) => assert.ok(tile === '' || tile === (column % 2 === 0 ? 'A' : 'B')));
  close(marketReturn(), 7 / 18, 1e-12, 'least return of one trade');
});
