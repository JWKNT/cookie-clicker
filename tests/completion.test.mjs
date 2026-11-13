import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { buildCompletionContract, assessCompletion, captureCompletionSnapshot } from '../model/completion.mjs';

const json = path => JSON.parse(readFileSync(new URL(path, import.meta.url), 'utf8'));
const catalogue = json('../model/catalogue.json');
const profile = json('../model/completion-profile.json');
const contract = buildCompletionContract(catalogue, profile);
const assess = state => assessCompletion(state, contract);

// A terminal-condition fixture, not a claim that this state has a legal trace.
function terminalFixture() {
  return {
    schemaVersion: 1, gameVersion: contract.gameVersion, edition: contract.edition,
    achievements: Object.fromEntries(contract.normalAchievements.map(x => [x.name, true])),
    upgrades: Object.fromEntries([...contract.ownedUpgrades.map(x => [x.name, { bought: true, unlocked: true }]),
      ...contract.accessUpgrades.map(x => [x.name, { bought: false, unlocked: false }])]),
    history: { gameVersion: contract.gameVersion, edition: contract.edition, accessedUpgrades: contract.accessUpgrades.map(x => x.name) },
    progression: {
      achievementsOwned: contract.normalAchievements.length,
      dragonLevel: contract.dragonLevel, santaLevel: contract.santaLevel, stockOfficeLevel: contract.officeLevel,
      ascensionMode: 0, onAscend: false, ascendTimer: 0, reincarnateTimer: 0,
      buildingLevels: Object.fromEntries(contract.buildingLevels.map(x => [x.building, x.level])),
      buildingAmounts: { Farm: 300 },
      buildingHighest: Object.fromEntries(contract.marketGoods.map(x => [x.building, x.highest])),
      minigames: Object.fromEntries(contract.minigames.map(x => [x.building, true])),
      gardenSeeds: contract.seeds.map(x => x.key),
      grimoireSpells: contract.spells.map(x => x.key), pantheonGods: contract.gods.map(x => x.key),
    },
  };
}

test('the canonical contract includes every normal identity and the exact sugar exceptions', () => {
  assert.equal(contract.requiredAchievements.length, 598);
  assert.equal(contract.excludedAchievements.length, 24);
  assert.equal(contract.ownedUpgrades.length, 845);
  assert.equal(contract.accessUpgrades.length, 17);
  assert.equal(contract.seeds.length, 34);
  assert.equal(contract.marketGoods.length, 18);
  assert.equal(contract.dragonLevel, 27);
  assert.equal(contract.santaLevel, 14);
  assert.equal(contract.officeLevel, 5);
  assert.equal(contract.gardenLevel, 9);
  assert.equal(contract.minimumNormalAchievements, 600);
  const selected = new Set([...contract.requiredAchievements, ...contract.excludedAchievements].map(x => x.id));
  assert.deepEqual(selected, new Set(catalogue.achievements.filter(x => x.normal).map(x => x.id)));
  assert(contract.ownedUpgrades.some(x => x.name === 'Steamed cookies'));
  assert(!contract.ownedUpgrades.some(x => x.name === 'Web cookies'));
});

test('generated requirements exactly match the executable classifier', () => {
  assert.deepEqual(json('../model/completion-requirements.json'), contract);
});

test('a terminal fixture passes and a fresh state fails with concrete missing categories', () => {
  assert.equal(assess(terminalFixture()).complete, true);
  const fresh = terminalFixture();
  fresh.achievements = {};
  fresh.upgrades = {};
  fresh.history.accessedUpgrades = [];
  fresh.progression.gardenSeeds = ['bakerWheat'];
  fresh.progression.dragonLevel = 0;
  const report = assess(fresh);
  assert.equal(report.complete, false);
  assert(report.missing.some(x => x.category === 'achievement' && x.key === 'Wake and bake'));
  assert(report.missing.some(x => x.category === 'ownedUpgrade'));
  assert(report.missing.some(x => x.category === 'gardenSeed'));
  assert(report.missing.some(x => x.key === 'dragonLevel'));
});

test('current ordinary ownership cannot be replaced by achievement or access history', () => {
  const state = terminalFixture();
  state.upgrades['Chocolate egg'].bought = false;
  state.history.accessedUpgrades.push('Chocolate egg');
  const report = assess(state);
  assert.equal(report.complete, false);
  assert.deepEqual(report.missing.map(x => [x.category, x.key]), [['ownedUpgrade', 'Chocolate egg']]);
});

test('zero-production and cosmetic heavenly upgrades remain required', () => {
  for (const name of ['Classic dairy selection', 'Sound test', 'Label printer', 'Sugar baking']) {
    const state = terminalFixture();
    assert(state.upgrades[name], `${name} is required`);
    state.upgrades[name].bought = false;
    assert(assess(state).missing.some(x => x.category === 'ownedUpgrade' && x.key === name));
  }
});

test('opposed switches require access and do not require simultaneous ownership', () => {
  const state = terminalFixture();
  const names = ['Golden switch [off]', 'Golden switch [on]', 'Shimmering veil [off]', 'Shimmering veil [on]'];
  for (const name of names) assert.equal(state.upgrades[name].bought, false);
  assert.equal(assess(state).complete, true);
  state.history.accessedUpgrades = state.history.accessedUpgrades.filter(name => name !== 'Golden switch [on]');
  assert(assess(state).missing.some(x => x.category === 'accessUpgrade' && x.key === 'Golden switch [on]'));
  state.upgrades['Golden switch [on]'].unlocked = true;
  assert.equal(assess(state).complete, true);
  state.history.gameVersion = '2.052';
  assert.equal(assess(state).valid, false);
});

test('shadow achievements cannot change completion; sugar exceptions retain the aggregate milk threshold', () => {
  const state = terminalFixture();
  for (const x of catalogue.achievements.filter(x => !x.normal)) state.achievements[x.name] = false;
  assert.equal(assess(state).complete, true);
  for (const x of catalogue.achievements.filter(x => !x.normal)) state.achievements[x.name] = true;
  assert.equal(assess(state).complete, true);
  for (const x of contract.excludedAchievements) state.achievements[x.name] = false;
  let report = assess(state);
  assert.deepEqual(report.missing.map(x => [x.category, x.key]), [['cosmeticUnlock', 'milkChoices']]);
  state.achievements['Freaky jazz hands'] = true;
  assert.equal(assess(state).complete, false);
  state.achievements['Huge tracts of land'] = true;
  assert.equal(assess(state).complete, true);
  state.achievements['Huge tracts of land'] = false;
  state.achievements['Sugar sugar'] = true;
  assert.equal(assess(state).complete, true);
  state.progression.buildingLevels.Cursor = 11;
  assert(assess(state).missing.some(x => x.category === 'buildingLevel' && x.key === 'Cursor'));
});

test('native milk access requires the actual counter as well as won flags', () => {
  const state = terminalFixture();
  state.progression.achievementsOwned = 599;
  assert.equal(assess(state).valid, true);
  assert.deepEqual(assess(state).missing.map(x => [x.category, x.key]), [['progression', 'achievementsOwned']]);
  state.progression.achievementsOwned = 600;
  assert.equal(assess(state).complete, true);
  state.achievements = Object.fromEntries(contract.requiredAchievements.map(x => [x.name, true]));
  assert.equal(assess(state).complete, false, 'native counter does not replace missing won flags');
  for (const value of [undefined, null, NaN, Infinity, -1, 599.5, '600']) {
    const malformed = terminalFixture();
    malformed.progression.achievementsOwned = value;
    assert.equal(assess(malformed).valid, false, String(value));
    assert.equal(assess(malformed).complete, false, String(value));
  }
  delete state.progression.achievementsOwned;
  assert.equal(assess(state).valid, false);
});

test('normal waiting and sugar prerequisites remain required' , () => {
  for (const name of ['No time like the present', 'Dude, sweet', 'Sugar rush', 'Hand-picked', 'Seedless to nay', 'Pyramid scheme']) {
    const state = terminalFixture();
    assert(state.achievements[name], `${name} is required`);
    state.achievements[name] = false;
    assert.equal(assess(state).complete, false);
  }
});

test('Garden sacrifice achievement does not replace rebuilding the current seed log', () => {
  const state = terminalFixture();
  assert.equal(state.achievements['Seedless to nay'], true);
  state.progression.gardenSeeds = ['bakerWheat'];
  const report = assess(state);
  assert.equal(report.missing.filter(x => x.category === 'gardenSeed').length, 33);
  assert(report.missing.some(x => x.key === 'queenbeetLump'));
});

test('soil access uses current farms, stock access uses the run maximum', () => {
  const state = terminalFixture();
  state.progression.buildingAmounts.Mine = 0;
  state.progression.buildingHighest.Mine = 1;
  assert.equal(assess(state).complete, true);
  state.progression.buildingAmounts.Farm = 299;
  assert.deepEqual(assess(state).missing.map(x => [x.category, x.key]), [['gardenSoil', 'woodchips']]);
  state.progression.buildingAmounts.Farm = 300;
  state.progression.buildingHighest.Mine = 0;
  assert(assess(state).missing.some(x => x.category === 'marketGood'));
});

test('minigame definitions and finite unlocks are separate completion conditions', () => {
  const state = terminalFixture();
  state.progression.minigames['Wizard tower'] = false;
  state.progression.grimoireSpells = [];
  state.progression.pantheonGods = [];
  state.progression.stockOfficeLevel = 4;
  const report = assess(state);
  assert(report.missing.some(x => x.category === 'minigame' && x.key === 'Grimoire'));
  assert.equal(report.missing.filter(x => x.category === 'grimoireSpell').length, 9);
  assert.equal(report.missing.filter(x => x.category === 'pantheonGod').length, 11);
  assert(report.missing.some(x => x.category === 'marketLoan' && x.key === '3'));
});

test('ascension transitions and a reset run are not terminal even with persistent achievements', () => {
  for (const [key, value] of [['onAscend', true], ['ascendTimer', 1], ['reincarnateTimer', 1], ['ascensionMode', 1]]) {
    const state = terminalFixture();
    state.progression[key] = value;
    assert.equal(assess(state).complete, false, key);
  }
  const state = terminalFixture();
  for (const upgrade of catalogue.upgrades.filter(x => x.pool !== 'prestige')) if (state.upgrades[upgrade.name]) state.upgrades[upgrade.name].bought = false;
  state.progression.dragonLevel = 0;
  state.progression.santaLevel = 0;
  state.progression.stockOfficeLevel = 0;
  const report = assess(state);
  assert.equal(report.complete, false);
  assert.equal(report.missing.filter(x => x.category === 'achievement').length, 0);
  assert(report.missing.some(x => x.category === 'ownedUpgrade'));
});

test('mismatched edition, missing metadata, malformed counts, and unknown pools fail closed', () => {
  for (const value of [Infinity, NaN, '12', -1, 11.5]) {
    const state = terminalFixture();
    state.progression.buildingLevels.Cursor = value;
    assert.equal(assess(state).valid, false);
    assert.equal(assess(state).complete, false);
  }
  const state = terminalFixture();
  state.edition = 'web';
  assert.equal(assess(state).valid, false);
  delete state.schemaVersion;
  assert.equal(assess(state).complete, false);
  const changed = structuredClone(catalogue);
  changed.upgrades[0].pool = 'new-unknown-pool';
  assert.throws(() => buildCompletionContract(changed, profile), /Unclassified/);
  const badProfile = structuredClone(profile);
  badProfile.sugarAchievementExclusions[0].name = 'Cheated cookies taste awful';
  assert.throws(() => buildCompletionContract(catalogue, badProfile), /not a vanilla normal achievement/);
});

test('read-only capture preserves game data, collects access history, and tests minigame readiness', () => {
  const game = {
    version: 2.053, dragonLevel: 0, santaLevel: 0, ascensionMode: 0, OnAscend: 0, AscendTimer: 0, ReincarnateTimer: 0,
    AchievementsOwned: 0,
    Achievements: { first: { name: 'Wake and bake', won: 1 } },
    Upgrades: { toggle: { name: 'Golden switch [off]', id: 331, bought: 0, unlocked: 1 } },
    Objects: {
      Farm: { name: 'Farm', level: 1, amount: 300, highest: 400, minigameUrl: 'garden.js', minigameLoaded: true,
        minigame: { plants: { bakerWheat: { unlocked: 1 }, queenbeetLump: { unlocked: 0 } } } },
      Bank: { name: 'Bank', level: 0, amount: 1, highest: 1, minigameUrl: 'market.js', minigameLoaded: true, minigame: { officeLevel: 0 } },
    },
  };
  const history = { gameVersion: '2.053', edition: 'steam', accessedUpgrades: ['Golden switch [on]'] };
  const before = structuredClone(game);
  const snapshot = captureCompletionSnapshot(game, history, { edition: 'steam' });
  assert.deepEqual(game, before);
  assert.deepEqual(history.accessedUpgrades, ['Golden switch [on]']);
  assert.deepEqual(snapshot.history.accessedUpgrades, ['Golden switch [off]', 'Golden switch [on]']);
  assert.equal(snapshot.progression.minigames.Farm, true);
  assert.equal(snapshot.progression.minigames.Bank, false);
  assert.deepEqual(snapshot.progression.gardenSeeds, ['bakerWheat']);
  assert.equal(snapshot.achievements['Wake and bake'], true);
  assert.equal(snapshot.progression.achievementsOwned, 0, 'capture does not infer native count from won flags');
  const wrongHistory = captureCompletionSnapshot(game, { ...history, edition: 'web' }, { edition: 'steam' });
  assert.deepEqual(wrongHistory.history.accessedUpgrades, ['Golden switch [off]']);
});

// These isolated source fixtures show native field dependence and exception order.
// They do not establish reachability of the synthetic terminal fixture.
test('pinned milk selector and interrupted Win use the actual native counter', async t => {
  const { hasGameSource } = await import('../model/game-source.mjs');
  if (!hasGameSource()) { t.skip('Pinned game source is not installed'); return; }
  const { createRuntime } = await import('../model/runtime.mjs');
  const { Game } = createRuntime();
  const highestMilk = Game.AllMilks.findIndex(x => x.rank === 24);
  assert(highestMilk >= 0);
  const selector = Game.Upgrades['Milk selector'];
  Game.milkType = 0;
  Game.AchievementsOwned = 599;
  assert.equal(selector.choicesFunction()[highestMilk], 0);
  Game.AchievementsOwned = 600;
  assert.equal(selector.choicesFunction()[highestMilk].milk.rank, 24);

  const target = Game.Achievements['Wake and bake'];
  target.won = 0;
  Game.AchievementsOwned = 599;
  const failure = new Error('isolated notification failure');
  Game.Notify = () => { throw failure; };
  assert.throws(() => Game.Win('Wake and bake'), error => error === failure);
  assert.equal(target.won, 1);
  assert.equal(Game.AchievementsOwned, 599, 'Win increments after notification');
  assert.equal(selector.choicesFunction()[highestMilk], 0);
  const captured = captureCompletionSnapshot(Game, {}, { edition: 'steam' });
  assert.equal(captured.progression.achievementsOwned, 599);
  assert.equal(captured.achievements['Wake and bake'], true);
  const terminal = terminalFixture();
  terminal.progression.achievementsOwned = captured.progression.achievementsOwned;
  assert.equal(assess(terminal).complete, false);
});


test('finite represented counts above the safe-integer range retain their unlocks', () => {
  for (const value of [2 ** 53, 2 ** 53 + 2, 2 ** 90, 2 ** 1000, Number.MAX_VALUE]) {
    const state = terminalFixture();
    state.progression.achievementsOwned = value;
    state.progression.buildingLevels.Farm = value;
    state.progression.buildingAmounts.Farm = value;
    state.progression.buildingHighest.Mine = value;
    assert.equal(assess(state).valid, true, String(value));
    assert.equal(assess(state).complete, true, String(value));
    assert.equal(assess(JSON.parse(JSON.stringify(state))).complete, true, 'native JSON round trip');
    state.progression.ascendTimer = value;
    assert.equal(assess(state).complete, false, 'a large transition timer is not zero');
  }
});
