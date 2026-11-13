import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { gunzipSync } from 'node:zlib';
import { gardenCollectionCylinder, probeGardenRecovery } from '../model/garden-cylinders.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const witness = JSON.parse(readFileSync(new URL('../model/garden-cylinders-witness.json', import.meta.url)));
const compressed = readFileSync(new URL('../model/certificates/garden-collection-cylinder.bin.gz', import.meta.url));
const tape = gunzipSync(compressed);
const hash = bytes => createHash('sha256').update(bytes).digest('hex');

test('Garden certificate has explicit finite draw mass, source hashes and remaining obligations', () => {
  assert.equal(hash(compressed), witness.certificate.compressedSha256);
  assert.equal(hash(tape), witness.tapeSha256);
  assert.equal(hash(readFileSync(new URL('../model/garden-cylinders.mjs', import.meta.url))), witness.moduleSha256);
  assert(tape.every(bit => bit === 0 || bit === 1));
  assert.equal(tape.length, witness.iidEvent.drawCount);
  assert.equal(witness.iidEvent.probability, `2^(-${53 * tape.length})`);
  assert.equal(witness.rows.length, 66);
  assert(witness.open.length >= 3);
});

test('Unmodified Garden callbacks replay both full seed logs, sacrifice, seven drops and1000 harvests',
  { skip: !hasGameSource() && 'Pinned Steam source is required' }, () => {
    const { tape: usedTape, ...result } = gardenCollectionCylinder({ replayTape: tape });
    assert.equal(result.seedCount, 34);
    assert(result.seedless && result.fullPlot);
    assert(result.gardenDrops.every(drop => drop.bought));
    assert(result.harvestsTotal >= 1000);
    assert.equal(result.actionsSha256, witness.actionsSha256);
    assert.equal(result.tapeSha256, witness.tapeSha256);
    assert.deepEqual(result.rows, witness.rows);
    assert.equal(result.gardenTicks, witness.gardenTicks);
    assert.equal(usedTape.length, tape.length);
  });

test('Native two-pass clearing handles36 replacements on either meddleweed branch',
  { skip: !hasGameSource() && 'Pinned Steam source is required' }, () => {
    const result = probeGardenRecovery();
    assert.deepEqual(result.replacingPlants, ['meddleweed']);
    assert(result.childCallbacksAbsent);
    for (const example of result.result) {
      assert.equal(example.harvestCalls, 72);
      assert.equal(example.remainingPlants, 0);
    }
  });
