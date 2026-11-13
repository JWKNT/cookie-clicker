import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { buildGoalCoverage } from '../model/goal-coverage.mjs';

const read = file => JSON.parse(readFileSync(new URL(file, import.meta.url)));
const coverage = read('../model/goal-coverage.json');
const requirements = read('../model/completion-requirements.json');
test('every required achievement, owned upgrade, and access item has exactly one trigger mapping', () => {
  for (const [section, required] of [['achievements','requiredAchievements'], ['upgrades','ownedUpgrades'], ['access','accessUpgrades']]) {
    assert.deepEqual(coverage[section].map(x=>[x.id,x.name]), requirements[required].map(x=>[x.id,x.name]));
    assert.equal(new Set(coverage[section].map(x=>x.id)).size, coverage[section].length);
  }
  assert.deepEqual(coverage.unmapped, []);
  assert.equal(coverage.achievements.length, 598);
  assert.equal(coverage.upgrades.length, 845);
  assert.equal(coverage.access.length, 17);
  assert.equal(coverage.finiteUnlocks.sufficientBuildingTargets.find(x=>x.name==='Cursor').amount,1000);
  assert.equal(coverage.finiteUnlocks.deterministicMilkFallback.additionalLumpsFromLevel9,10);
});
test('the saved goal mapping reproduces from the hash-pinned native registrations', {
  skip: !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory',
}, () => {
  assert.deepEqual(buildGoalCoverage(createRuntime(),requirements),coverage);
});
