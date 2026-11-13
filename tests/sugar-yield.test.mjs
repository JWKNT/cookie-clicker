import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { IID53_SIZE, SUGAR_YIELD_TABLES, nativeYieldIndex, projectedYieldIndex,
  sugarYieldBuckets, sugarYieldDistribution, sugarYieldExpectation } from '../model/sugar-yield-kernel.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';

test('golden lump buckets retain the native multiplication rounding', () => {
  assert.equal(nativeYieldIndex('golden', 6004799503160661n), 4);
  assert.equal(Number(6004799503160661n * 6n / IID53_SIZE), 3);
  assert.equal(nativeYieldIndex('golden', 7505999378950826n), 5);
  assert.equal(Number(7505999378950826n * 6n / IID53_SIZE), 4);
});

test('meaty lump buckets retain the native multiplication rounding', () => {
  assert.equal(nativeYieldIndex('meaty', 5404319552844595n), 3);
  assert.equal(Number(5404319552844595n * 5n / IID53_SIZE), 2);
});

test('all bucket endpoints and adjacent draws match native Number operations', () => {
  for (const [kind, table] of Object.entries(SUGAR_YIELD_TABLES)) {
    for (const boundary of table.boundaries) {
      for (let delta = -2n; delta <= 2n; delta++) {
        const index = boundary + delta;
        if (index >= 0n && index < IID53_SIZE)
          assert.equal(projectedYieldIndex(kind, index), nativeYieldIndex(kind, index));
      }
    }
    assert.equal(sugarYieldBuckets(kind).reduce((sum, row) => sum + row.count, 0n), IID53_SIZE);
  }
});

test('exact yield probabilities are nonuniform across indices but preserve their expectations', () => {
  assert.deepEqual(sugarYieldDistribution('meaty').map(row => row.numerator),
    [3602879701896397n, 1801439850948198n, 3602879701896397n]);
  assert.deepEqual(sugarYieldExpectation('golden'), { numerator: 9n, denominator: 2n });
  assert.deepEqual(sugarYieldExpectation('meaty'), { numerator: 1n, denominator: 1n });
});

test('the sugar kernel rejects indices outside the declared random law', () => {
  for (const index of [-1n, IID53_SIZE, 0, 0.5])
    assert.throws(() => nativeYieldIndex('golden', index), RangeError);
  assert.throws(() => sugarYieldDistribution('unknown'), RangeError);
});

test('the sugar yield artifact matches the intact native choice and pinned harvest arrays', { skip }, () => {
  execFileSync(process.execPath, ['tools/audit-sugar-yield.mjs', '--check'],
    { cwd: new URL('../', import.meta.url), stdio: 'pipe' });
});
