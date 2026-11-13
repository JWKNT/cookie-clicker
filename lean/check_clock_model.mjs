/** Clock-model diagnostics. These states are not admissible gameplay routes. */
import assert from 'node:assert/strict';

const maximumDate = 8_640_000_000_000_000;
const epoch = Date.UTC(2026, 9, 29, 12);
const spacing = 64_436_019;
assert.equal(new Date(maximumDate).toISOString(), '+275760-09-13T00:00:00.000Z');
assert(Number.isNaN(new Date(maximumDate + 1).getTime()));
assert.equal(Math.floor((maximumDate - epoch) / spacing), 134_058_665);
assert.equal((BigInt(maximumDate) - BigInt(epoch)) / BigInt(spacing), 134_058_665n);

if (process.argv.includes('--engine')) {
  const { createRuntime } = await import('../model/runtime.mjs');
  const runtime = createRuntime({ epochMs: maximumDate + 1, recordAudit: false });
  // The adapter is not Date.now's standard bounded time-value semantics.
  // This diagnostic prevents applying the Date range as its global time cap.
  assert.equal(runtime.evaluate('Date.now()'), maximumDate + 1);
  assert.equal(runtime.evaluate('Number.isNaN(new Date().getTime())'), true);
  assert.equal(runtime.evaluate('Date.now() > 8640000000000000'), true);
  console.log('Clock-model checks passed: Date range, exact conditional attempt cap, and adapter/calendar divergence.');
} else {
  console.log('Clock-model arithmetic checks passed; adapter diagnostic requires --engine.');
}
