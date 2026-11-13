import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { probeBootstrapRoute } from '../model/bootstrap-route.mjs';
import { hasGameSource } from '../model/game-source.mjs';

test('native bootstrap prefix and boundary checks preserve explicit premises',
  { skip: !hasGameSource() && 'Pinned Steam source is required' }, () => {
    const result = probeBootstrapRoute();
    assert.equal(result.freshPrefix.clicks, 15);
    assert.equal(result.freshPrefix.cursorAmount, 1);
    assert.equal(result.freshPrefix.upgrades, 0);
    assert.equal(result.freshPrefix.rawCps, 0.1);
    assert.equal(result.freshPrefix.frameIncrement, 0.1 / 30);
    assert.equal(result.ladder.length, 7);
    assert.deepEqual(result.ladder.map(x => x.afterCps), [1.1,9.1,56.1,316.1,1716.1,9516.1,53516.1]);
    for (const stage of result.ladder) {
      assert.equal(stage.amount,1); assert.equal(stage.clicks,15); assert.equal(stage.upgrades,0);
      assert.equal(stage.elderWrath,0); assert(stage.normalOrZeroBank); assert(stage.before>=stage.price);
    }
    assert.equal(result.entry.templeAmount,1);
    assert(result.challengeBoundary.hardcore && result.challengeBoundary.neverclick);
    assert.equal(result.challengeBoundary.elderWrath, 0);
    assert.notEqual(result.challengeBoundary.lumpType, 3);
    assert(result.ripeHarvest.lumps >= 1);
    assert.equal(result.entry.templeLevel, 1);
    assert.equal(result.entry.godSlot, 1);
    assert(result.entry.mouseCps >= 64);
    assert(result.burst.before - result.burst.afterCycles <= 16 * result.burst.cycles);
    assert.equal(result.burst.acceptedClicks, 400);
    assert(result.burst.remainingBuffFrames > 0);
    assert(result.burst.after - result.burst.before >= result.burst.claimedMinimumGain);
    assert(result.premises.some(p => p.kind === 'challenge-boundary'));
    assert(result.premises.some(p => p.kind === 'ripe-boundary'));
  });

test('bootstrap witness names its source, premises and open refinement obligations', () => {
  const witness = JSON.parse(readFileSync(new URL('../model/bootstrap-route-witness.json', import.meta.url)));
  const module = readFileSync(new URL('../model/bootstrap-route.mjs', import.meta.url));
  assert.equal(witness.moduleSha256, createHash('sha256').update(module).digest('hex'));
  assert.equal(witness.scope, 'native-prefix-and-boundary-diagnostics-not-long-route-execution');
  assert(witness.route.open.length >= 4);
  assert.equal(witness.route.bounds.proposedTotalFramesUpper, '2^40');
});
