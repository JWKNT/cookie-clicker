/** Native/rational forcing-step comparison; this is not a binary64 refinement proof. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { MARKET_RECURRENCE as bounds } from '../model/market-recurrence.mjs';

assert.equal(bounds.fallingBlockTicks, 801);
assert.equal(bounds.risingBlockTicks, 231);
assert.equal(bounds.maximumDrawsPerForcedTick, 327);
assert.equal((801 + 231) * 327, 337464);
if (!process.argv.includes('--engine')) {
  console.log('Market forcing-block constants match; native comparison requires --engine.');
  process.exit(0);
}
const { createRuntime } = await import('../model/runtime.mjs');
const runtime = createRuntime();
const G = runtime.Game, bank = G.Objects.Bank;
bank.level = 1; bank.amount = bank.highest = 700;
runtime.evaluate(runtime.source.sources['minigameMarket.js'], 'minigameMarket.js');
const M = bank.minigame;
M.launch(); bank.minigameLoaded = true; G.dragonLevel = 27;
const aura = name => Object.values(G.dragonAuras).find(x => x.name === name).id;
const top = 1 - 2 ** -53;
const cases = [], actual = [];
for (const boostTenths of [0, 1, 10, 11]) for (const velocity of [-300, 300])
  for (const highPrice of [false, true]) for (const rising of [false, true]) {
    G.dragonAura = boostTenths >= 10 ? aura('Supreme Intellect') : 0;
    G.dragonAura2 = boostTenths % 10 ? aura('Reality Bending') : 0;
    const boost = G.auraMult('Supreme Intellect');
    assert.equal(boost, boostTenths / 10);
    M.goodsById.forEach((good, index) => {
      good.mode = index % 6; good.dur = 699; good.d = velocity;
      const resting = M.getRestingVal(index);
      good.val = highPrice ? resting + 250000 : 1;
      cases.push({ direction: rising ? 'rise' : 'fall', mode: good.mode, price: good.val, velocity, resting, boostTenths });
    });
    const tape = [0.5, 0, 0.5 + 2 ** -53];
    for (const good of M.goodsById) {
      tape.push(top);
      if (good.mode === 3 || good.mode === 4) tape.push(top);
      tape.push(0, 0, 0, 0, rising ? top : 0, rising ? top : 0, 0.5, 0.5, 0.5);
      if (good.mode === 5) tape.push(0.5, 0.5);
      if (good.mode === 3) tape.push(0.5, 0.5);
      if (good.mode === 4) tape.push(0.5);
      tape.push(0, top);
      if (top < boost) tape.push(top);
      tape.push(top, rising ? 11 / 16 : 13 / 16);
    }
    assert(tape.length <= 327);
    for (const atom of tape) assert(Number.isSafeInteger(atom * 2 ** 53));
    const original = runtime.context.Math.random;
    let used = 0;
    try {
      runtime.context.Math.random = () => { assert(used < tape.length); return tape[used++]; };
      M.tick();
      assert.equal(used, tape.length);
    } finally { runtime.context.Math.random = original; }
    for (const good of M.goodsById) {
      assert.equal(good.mode, rising ? 3 : 4);
      assert(good.val >= 1 && good.val <= M.getRestingVal(good.id) + 250000);
      assert(Math.abs(good.d) <= 300);
      actual.push({ price: good.val, velocity: good.d });
    }
  }
const root = fileURLToPath(new URL('./', import.meta.url));
const result = spawnSync(`${root}.lake/build/bin/marketcheck`, [], {
  input: JSON.stringify(cases), encoding: 'utf8', maxBuffer: 16 * 1024 * 1024, timeout: 120000,
});
assert.equal(result.status, 0, result.stderr || result.error?.message);
const projected = JSON.parse(result.stdout);
assert.equal(projected.length, actual.length);
const number = value => Number(value.numerator) / Number(value.denominator);
let priceError = 0, velocityError = 0;
for (let index = 0; index < actual.length; index++) {
  const dp = Math.abs(number(projected[index].price) - actual[index].price);
  const dd = Math.abs(number(projected[index].velocity) - actual[index].velocity);
  assert(dp < 1e-8, `Price mismatch at ${index}: ${dp}`);
  assert(dd < 1e-10, `Velocity mismatch at ${index}: ${dd}`);
  priceError = Math.max(priceError, dp); velocityError = Math.max(velocityError, dd);
}
console.log(`Native market comparison passed for ${actual.length} boundary transitions; observed price error ${priceError}, velocity error ${velocityError}. This is a finite probe, not a general rounding bound.`);
