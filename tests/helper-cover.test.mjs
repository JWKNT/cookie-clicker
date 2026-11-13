import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';
import test from 'node:test';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { HELPER_GRANDMAS, HELPER_ART_EXCLUSIONS, helperSweepPoint, helperSweepActions } from '../model/helper-cover.mjs';
import { shortAsciiSeededRandom, STARTUP_SEED_COUNT } from '../model/seed-inference.mjs';

const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const witness = JSON.parse(readFileSync(new URL('../model/helper-seeds-witness.json', import.meta.url)));

test('archived exhaustive helper certificate covers every startup seed', () => {
  const compressed = readFileSync(new URL('../model/certificates/helper-first-index.bin.gz', import.meta.url));
  const certificate = gunzipSync(compressed);
  assert.equal(certificate.length, STARTUP_SEED_COUNT);
  assert.equal(sha256(compressed), witness.certificate.compressedSha256);
  assert.equal(sha256(certificate), witness.certificate.sha256);
  assert.equal(sha256(readFileSync(new URL('../tools/check-helper-seeds.cpp', import.meta.url))), witness.cppSourceSha256);
  assert.equal(sha256(readFileSync(new URL('../model/helper-cover.mjs', import.meta.url))), witness.helperSweepModuleSha256);
  const histogram = Array(HELPER_GRANDMAS).fill(0);
  for (const index of certificate) { assert(index < HELPER_GRANDMAS); histogram[index]++; }
  assert.deepEqual(histogram, witness.histogram);
  assert.equal(witness.maximumFirstHelperIndex, 23);
  assert.equal(witness.sufficientBytePredicateVerification.allChosenThirdLeadingBytesAtLeast128, true);
  assert.equal(witness.scope, 'native-exhaustive-enumeration-not-Lean-proof');
});

test('fixed helper grid points hit every allowed native jittered rectangle', () => {
  for (let index = 0; index < HELPER_GRANDMAS; index++) {
    const point = helperSweepPoint(index);
    assert(point.x >= 0 && point.x < 278 && point.y >= 0 && point.y < 89);
    for (let jitterX = -4; jitterX <= 3; jitterX++) for (let jitterY = -4; jitterY <= 3; jitterY++) {
      const x = Math.floor(32 * Math.floor(index / 3) + 32 * (index % 3) / 3 + jitterX);
      const y = 24 + 16 * (index % 3) + jitterY;
      assert(point.x >= x + 18 && point.x < x + 46);
      assert(point.y >= y + 10 && point.y < y + 54);
    }
  }
  assert.equal(helperSweepActions().filter(action => action.type === 'wait').reduce((sum, action) => sum + action.milliseconds, 0), 3350);
});

test('unique worst startup seed has its first helper at index 23', () => {
  for (let index = 0; index < 24; index++) {
    const random = shortAsciiSeededRandom(`${witness.firstMaximumSeed} 1 ${index}`);
    random(); random();
    assert.equal(random() >= 0.5, index === 23);
  }
});

test('fixed public sweep wins in native source for the worst seed without sprite-guided inputs',
  { skip: !hasGameSource() && 'Pinned Steam source is unavailable' }, () => {
    const runtime = createRuntime({ diagnosticMode: true, recordAudit: false }), G = runtime.Game;
    // A bounded native fixture, not a new-save reachability claim.
    G.seed = witness.firstMaximumSeed; G.cookies = G.cookiesEarned = 1e6;
    G.season = 'christmas'; G.seasonT = G.fps * 86400;
    runtime.advance(5100);
    assert(HELPER_ART_EXCLUSIONS.every(name => !G.Has(name)));
    runtime.act({ type: 'buy-building', id: 1, amount: 24 }, { observe: false });
    for (const action of helperSweepActions()) runtime.act(action, { observe: false });
    assert(G.HasAchiev("Baby it's old outside"));
  });
