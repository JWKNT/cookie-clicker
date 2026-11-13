import assert from 'node:assert/strict';
import test from 'node:test';
import { Q, completionTime, optimalCompletion } from '../tools/completion-model.mjs';

const permutations = (xs) => xs.length === 0 ? [[]]
  : xs.flatMap((x, i) => permutations(xs.filter((_, j) => i !== j)).map((tail) => [x, ...tail]));

test('strict counterexample: greedy completion is slower in its own model', () => {
  const offers = [{ price: 3, gain: 1 }, { price: 5, gain: 4 }, { price: 6, gain: 6 }];
  assert.equal(completionTime(offers, [0, 1, 2]).toString(), '13/2');
  const optimum = optimalCompletion(offers);
  assert.deepEqual(optimum.order, [1, 2, 0]);
  assert.equal(optimum.time.toString(), '356/55');
  assert.equal(completionTime(offers, [0, 1, 2]).sub(optimum.time).toString(), '3/110');
});

test('subset recurrence agrees with all permutations, including partial affordability and zero gains', () => {
  for (let seed = 0; seed < 32; seed++) {
    const offers = Array.from({ length: 5 }, (_, i) => ({
      price: (seed * 7 + i * 11) % 19,
      gain: (seed * 3 + i * 7) % 9,
    }));
    const bank = seed % 13;
    const income = seed % 5 + 1;
    const all = permutations([0, 1, 2, 3, 4]).map((order) => completionTime(offers, order, bank, income));
    const expected = all.reduce((a, b) => a.lt(b) ? a : b);
    const actual = optimalCompletion(offers, { bank, income });
    assert.equal(actual.time.toString(), expected.toString());
    assert.equal(completionTime(offers, actual.order, bank, income).toString(), expected.toString());
    assert.ok(actual.states <= 2 ** offers.length);
  }
});

test('completion handles a finished state, full bank, fractions, and invalid inputs', () => {
  assert.equal(optimalCompletion([]).time.toString(), '0');
  assert.equal(optimalCompletion([{ price: 4, gain: 0 }], { bank: 4 }).time.toString(), '0');
  assert.equal(optimalCompletion([{ price: '3/2', gain: 0 }], { income: '2/3' }).time.toString(), '9/4');
  assert.throws(() => optimalCompletion([{ price: -1, gain: 1 }]), RangeError);
  assert.throws(() => optimalCompletion([], { income: 0 }), RangeError);
  assert.throws(() => Q.of(0.1), RangeError);
  assert.throws(() => new Q(1, 0), RangeError);
});
