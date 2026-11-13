/** Native Garden transition probes for the explicitly conditional Lean invariant.
 * All prepared states are synthetic fixtures. They are not new-save policies.
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { r as requirements } from './completion-fixtures.mjs';

if (!process.argv.includes('--engine')) {
  console.log('Native Garden probes require --engine; no source check was claimed.');
  process.exit(0);
}
const { createRuntime } = await import('../model/runtime.mjs');
const root = fileURLToPath(new URL('./', import.meta.url));
const digest = createHash('sha256').update(readFileSync(new URL('../model/completion-requirements.json', import.meta.url))).digest('hex');
function fixture(options = {}) {
  const runtime = createRuntime(options);
  runtime.evaluate(runtime.source.sources['minigameGarden.js'], 'minigameGarden.js');
  const farm = runtime.Game.Objects.Farm;
  farm.level = 9; farm.amount = 300; farm.highest = 300;
  farm.minigame.launch(); farm.minigameLoaded = true;
  runtime.Game.cookies = 1e100; runtime.Game.cookiesEarned = 1e100;
  runtime.Game.cookiesPs = 0; runtime.Game.lumps = 0;
  return runtime;
}
const runtime = fixture();
const M = runtime.Game.Objects.Farm.minigame;
assert.equal(M.plants.queenbeetLump.plantable, false);
assert.throws(() => runtime.act({ type: 'garden-plant', seed: 'queenbeetLump', x: 1, y: 1 }), /cannot be planted/);
// Test the native guard with each of the 34 possible missing seeds.
for (const missing of requirements.seeds) {
  for (const plant of Object.values(M.plants)) M.unlockSeed(plant);
  M.lockSeed(M.plants[missing.key]);
  assert.equal(M.plantsUnlockedN, 33);
  assert.equal(M.convert(), false);
  assert.equal(runtime.Game.Achievements['Seedless to nay'].won, 0);
}
for (const plant of Object.values(M.plants)) M.unlockSeed(plant);
M.lockSeed(M.plants.queenbeetLump);
const records = [{ kind: 'initial', elapsedMs: 0, observation: runtime.snapshot() }];
const capture = () => records.push({ kind: 'action', elapsedMs: 0, observation: runtime.snapshot() });
// An immature harvest cannot unlock JQB. A mature native harvest can.
M.plot[1][1] = [M.plants.queenbeetLump.id + 1, Math.ceil(M.plants.queenbeetLump.mature) - 1];
runtime.act({ type: 'garden-harvest', x: 1, y: 1 });
assert.equal(M.plants.queenbeetLump.unlocked, 0);
capture();
M.plot[1][1] = [M.plants.queenbeetLump.id + 1, Math.ceil(M.plants.queenbeetLump.mature)];
runtime.act({ type: 'garden-harvest', x: 1, y: 1 });
assert.equal(M.plantsUnlockedN, 34);
capture();
runtime.act({ type: 'garden-sacrifice' });
capture();
runtime.act({ type: 'prompt', option: 0 });
assert.equal(runtime.Game.Achievements['Seedless to nay'].won, 1);
assert.deepEqual(runtime.snapshot().progression.gardenSeeds, ['bakerWheat']);
capture();
M.plot[1][1] = [M.plants.queenbeetLump.id + 1, Math.ceil(M.plants.queenbeetLump.mature)];
runtime.act({ type: 'garden-harvest', x: 1, y: 1 });
assert.equal(M.plants.queenbeetLump.unlocked, 1);
capture();
// Pebbles can unlock the seed on old-age death; manual harvest is not necessary.
const death = fixture({ randomTape: Array(100000).fill(0) });
const D = death.Game.Objects.Farm.minigame;
D.soil = D.soils.pebbles.id;
D.plot[1][1] = [D.plants.queenbeetLump.id + 1, 100];
D.nextStep = 0;
assert.equal(D.plants.queenbeetLump.unlocked, 0);
D.logic();
assert.equal(D.plot[1][1][0], 0);
assert.equal(D.plants.queenbeetLump.unlocked, 1);
const trace = { schemaVersion: 1, profileId: requirements.profileId, requirementsSha256: digest,
  checkpointSemantics: 'native-action-and-timer-boundaries-v1', records,
  provenance: 'Synthetic preconditions; only the recorded native Garden operations are under test.' };
const result = spawnSync(`${root}.lake/build/bin/tracecheck`, [], {
  input: JSON.stringify([trace]), encoding: 'utf8', maxBuffer: 8 * 1024 * 1024,
});
assert.equal(result.status, 0, result.stderr || result.error?.message);
const checked = JSON.parse(result.stdout)[0];
assert.equal(checked.valid, true);
assert.equal(checked.garden.contractValid, true);
assert.equal(checked.garden.initialJuicyKnown, false);
assert.equal(checked.garden.initialSeedlessWon, false);
assert.equal(checked.garden.juicyAcquisitions, 2);
assert.equal(checked.firstCompletion, null, 'A synthetic Garden probe is not a full-game completing policy');
console.log('Native Garden probes passed: 34 sacrifice guards, reset, two acquisition paths, and Lean trace budget.');
