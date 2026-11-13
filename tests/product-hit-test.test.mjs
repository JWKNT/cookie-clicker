import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource, defaultGameSourceDirectory } from '../model/game-source.mjs';
import { join } from 'node:path';

const engineTest = (name, fn) => test(name, { skip: !hasGameSource() && 'Pinned Steam source is required' }, fn);

test('Pinned browser distinguishes visible locked rows from hidden later rows', () => {
  const witness = JSON.parse(readFileSync(new URL('../model/product-hit-test-witness.json', import.meta.url)));
  assert.equal(witness.versions.chrome, '87.0.4280.141');
  assert.equal(witness.gameEntryPointExecuted, false);
  for (const example of witness.result.cases) for (const row of example.results) {
    assert.equal(row.hitInsideProduct, example.expectedHitIds.includes(row.id));
    assert.equal(row.bubbledClicks, example.expectedHitIds.includes(row.id) ? 1 : 0);
  }
  const fresh = witness.result.cases[0].results;
  assert.equal(fresh[0].className.includes('locked'), true);
  assert.equal(fresh[0].display, 'block');
  assert.equal(fresh.at(-1).display, 'none');
  assert.ok(witness.result.cases[1].results.at(-1).scrollTop > 0);
  if (hasGameSource()) assert.equal(createHash('sha256').update(readFileSync(join(defaultGameSourceDirectory(), 'style.css'))).digest('hex'), witness.sourceHashes['style.css']);
});

engineTest('A visible mystery row can be bought before the next native store draw', () => {
  for (const type of ['buy-building', 'click-product']) {
    const runtime = createRuntime();
    const cursor = runtime.Game.Objects.Cursor;
    runtime.Game.cookies = cursor.getPrice(); // Diagnostic affordability fixture.
    assert.equal(cursor.locked, 1);
    assert.equal(cursor.l.classList.contains('toggledOff'), false);
    runtime.act({ type, id: cursor.id, amount: 1 });
    assert.equal(cursor.amount, 1);
    assert.equal(runtime.Game.cookies, 0);
  }
});

engineTest('Hidden later rows remain unavailable until a native store draw reveals them', () => {
  const runtime = createRuntime();
  const farm = runtime.Game.Objects.Farm;
  runtime.Game.cookies = runtime.Game.cookiesEarned = farm.getPrice();
  assert.equal(farm.l.classList.contains('toggledOff'), true);
  for (const type of ['buy-building', 'click-product'])
    assert.throws(() => runtime.act({ type, id: farm.id, amount: 1 }), /hidden/);
  runtime.advance(200);
  assert.equal(farm.l.classList.contains('toggledOff'), false);
  runtime.act({ type: 'click-product', id: farm.id });
  assert.equal(farm.amount, 1);
});
