import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { hasGameSource } from '../model/game-source.mjs';
import { INCOME_LADDER, nextPositiveFloat, probeFundedIncomeLadder } from '../model/income-route.mjs';

test('positive binary64 neighbors include the lower spacing at powers of two', () => {
  for (const exponent of [0, 53, 88, 90, 140, 190, 220, 240, 270, 280, 286]) {
    const value = 2 ** exponent;
    assert.equal(nextPositiveFloat(value) - value, 2 ** (exponent - 52));
    assert.equal(value - nextPositiveFloat(value, -1), 2 ** (exponent - 53));
    assert.equal(nextPositiveFloat(nextPositiveFloat(value), -1), value);
  }
  for (const value of [0, -1, Infinity, NaN]) assert.throws(() => nextPositiveFloat(value));
});

test('funded native ladder clears click and production ULP barriers with native-derived prestige',
  { skip: !hasGameSource() && 'Pinned Steam source is unavailable' }, () => {
    const result = probeFundedIncomeLadder();
    assert.equal(result.scope, 'funded-native-implications-only');
    assert(result.doesNotProve.includes('new-save reachability'));
    assert(result.doesNotProve.includes('funding or rebuild income'));
    assert.equal(result.rows.length, INCOME_LADDER.length);
    for (const row of result.rows) {
      assert(row.clickProbe.accepted, `click ${row.bankExponent}`);
      assert(row.clickProbe.amountOverTargetUlp > 1, `click ULP margin ${row.bankExponent}`);
      for (const counter of Object.values(row.clickProbe.counters)) assert(counter.crossed);
      assert(row.purchases.every(purchase => purchase.bankBefore >= purchase.price && purchase.bankAfter >= 0));
      assert(row.remainingBank >= 2 ** 88);
      if (row.ascension) {
        assert.equal(row.ascension.prestige, row.ascension.expectedNativePrestige);
        assert.equal(row.ascension.bankAfterReincarnate, 0);
        assert.equal(row.heavenlyPower, 1);
      }
    }
    for (const premise of result.premises.filter(premise => premise.kind === 'macro-endpoint'))
      assert.equal(premise.bankBeforeCycle, premise.bankAfterCycle);
    const final = result.rows.at(-1);
    assert(final.rawCps > result.maxRawCpsGoal);
    assert(final.production.every(building => building.incrementOverUlp > 1));
    assert.equal(result.productionProbe.nativeTicks, 1);
    assert(result.productionProbe.counters.every(counter => counter.crossed));
  });

test('archived funded witness identifies its premises and generating module', () => {
  const witness = JSON.parse(readFileSync(new URL('../model/income-route-witness.json', import.meta.url)));
  const module = readFileSync(new URL('../model/income-route.mjs', import.meta.url));
  assert.equal(witness.moduleSha256, createHash('sha256').update(module).digest('hex'));
  assert.equal(witness.scope, 'funded-native-implications-only');
  assert(witness.premises.some(premise => premise.reason.includes('independent premise')));
  assert(witness.rows.every(row => row.everyPurchaseAffordable && row.purchasesSha256.length === 64));
  assert(witness.productionProbe.counters.every(counter => counter.crossed));
});
