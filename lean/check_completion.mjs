/** Compare the compiled Lean predicate with JavaScript on normalized observations.
 * This is regression evidence, not a proof of JavaScript/Lean semantic equivalence.
 */
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { assessCompletion } from '../model/completion.mjs';

const root = fileURLToPath(new URL('./', import.meta.url));
import { r, terminal } from './completion-fixtures.mjs';
const cases = [{ name: 'synthetic terminal witness', snapshot: terminal }];
const change = (name, edit, options = {}) => {
  const snapshot = structuredClone(terminal);
  edit(snapshot);
  cases.push({ name, snapshot, ...options });
};
assert.equal(assessCompletion(terminal, r).complete, true);
change('first required achievement', s => { s.achievements[r.requiredAchievements[0].name] = false; });
change('last required achievement', s => { s.achievements[r.requiredAchievements.at(-1).name] = false; });
change('first owned upgrade', s => { s.upgrades[r.ownedUpgrades[0].name].bought = false; });
change('last owned upgrade', s => { s.upgrades[r.ownedUpgrades.at(-1).name].bought = false; });
for (const x of r.accessUpgrades.slice(0, 2)) {
  change(`no access to ${x.name}`, s => { s.upgrades[x.name] = { bought: false, unlocked: false }; });
  change(`historical access to ${x.name}`, s => {
    s.upgrades[x.name] = { bought: false, unlocked: false };
    s.history.accessedUpgrades = [x.name];
  });
}
for (const x of r.minigames) change(`minigame ${x.name}`, s => { s.progression.minigames[x.building] = false; });
for (const x of r.buildingLevels) change(`building level ${x.building}`, s => { s.progression.buildingLevels[x.building] = x.level - 1; });
change('missing seed', s => { s.progression.gardenSeeds.pop(); });
change('soil current amount', s => { s.progression.buildingAmounts.Farm--; });
for (const x of r.marketGoods.slice(0, 2)) change(`market good ${x.id}`, s => { s.progression.buildingHighest[x.building] = 0; });
change('missing spell', s => { s.progression.grimoireSpells.pop(); });
change('missing god', s => { s.progression.pantheonGods.pop(); });
for (const key of ['dragonLevel', 'santaLevel', 'stockOfficeLevel']) change(`progression ${key}`, s => { s.progression[key]--; });
for (const key of ['ascensionMode', 'ascendTimer', 'reincarnateTimer']) change(`transition ${key}`, s => { s.progression[key] = 1; });
change('on ascension screen', s => { s.progression.onAscend = true; });
change('wrong game version', s => { s.gameVersion = '2.052'; });
change('wrong edition', s => { s.edition = 'web'; });
change('wrong history version', s => { s.history.gameVersion = '2.052'; });
change('wrong history edition', s => { s.history.edition = 'web'; });
change('shadow does not matter', s => { s.achievements['Cheated cookies taste awful'] = true; });
change('sugar individual exclusion with adequate total', s => { s.achievements[r.excludedAchievements[0].name] = false; });
for (const count of [0, 1, 2]) change(`required achievements plus ${count} sugar exceptions`, s => {
  s.achievements = Object.fromEntries(r.requiredAchievements.map(x => [x.name, true]));
  for (const x of r.excludedAchievements.slice(0, count)) s.achievements[x.name] = true;
});
change('won flags complete but native milk counter stale', s => { s.progression.achievementsOwned = 599; }, { mustDecode: true });
change('native milk count at threshold', s => { s.progression.achievementsOwned = 600; }, { mustDecode: true });
change('native milk count does not replace flags', s => {
  s.progression.achievementsOwned = 622;
  s.achievements = Object.fromEntries(r.requiredAchievements.map(x => [x.name, true]));
});
for (const value of [null, -1, 599.5, '600']) change(`invalid native count ${value}`, s => { s.progression.achievementsOwned = value; }, { mustNotDecode: true });
change('missing native milk counter', s => { delete s.progression.achievementsOwned; }, { mustNotDecode: true });
change('negative required number' , s => { s.progression.dragonLevel = -1; });
change('fractional required number', s => { s.progression.dragonLevel = 27.5; });
for (const value of [2 ** 53, 2 ** 53 + 2, 2 ** 90, 2 ** 1000, Number.MAX_VALUE]) {
  change('large represented native count '+value, s => { s.progression.achievementsOwned = value; }, { mustDecode: true });
  change('large represented building counts '+value, s => {
    s.progression.buildingLevels.Farm = value;
    s.progression.buildingAmounts.Farm = value;
    s.progression.buildingHighest.Mine = value;
  }, { mustDecode: true });
}
change('missing zero-threshold field', s => { delete s.progression.buildingAmounts.Farm; });
change('duplicate seed observation', s => { s.progression.gardenSeeds.push(s.progression.gardenSeeds[0]); });
change('missing required section', s => { delete s.history; });
if (process.argv.includes('--engine')) {
  const { createRuntime } = await import('../model/runtime.mjs');
  const runtime = createRuntime();
  const snapshot = runtime.snapshot();
  assert.equal(snapshot.achievements['Wake and bake'], false);
  cases.push({ name: 'actual pinned engine new-save snapshot', snapshot, mustDecode: true });
}
const result = spawnSync(`${root}.lake/build/bin/completion`, [], {
  input: JSON.stringify(cases.map(x => x.snapshot)), encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
});
assert.equal(result.status, 0, result.stderr || result.error?.message);
const actual = JSON.parse(result.stdout);
assert.equal(actual.length, cases.length);
for (let i = 0; i < cases.length; i++) {
  const expected = assessCompletion(cases[i].snapshot, r).complete;
  assert.equal(actual[i].complete, expected, cases[i].name);
  if (i === 0 || cases[i].mustDecode) assert.equal(actual[i].decoded, true, cases[i].name);
  if (cases[i].mustNotDecode) assert.equal(actual[i].decoded, false, cases[i].name);
}
console.log(`Lean/JavaScript normalized completion checks passed for ${cases.length} observations.`);
