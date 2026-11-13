import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { completionPolicySource } from '../model/completion-policy.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { assessCompletion, captureCompletionSnapshot } from '../model/completion.mjs';

const skip = !hasGameSource() && 'Pinned Steam source is unavailable';
const requirements = JSON.parse(readFileSync(new URL('../model/completion-requirements.json', import.meta.url)));

/** Supplied late-game boundary, not evidence of a new-save completing path. */
function finalFixture({ milkFallback = false } = {}) {
  const runtime = createRuntime();
  const G = runtime.Game;
  const requiredAchievements = new Set(requirements.requiredAchievements.map(a => a.name));
  for (const a of Object.values(G.Achievements)) {
    a.won = Number(!milkFallback || requiredAchievements.has(a.name) || a.name === 'Freaky jazz hands');
  }
  G.AchievementsOwned = milkFallback ? 599 : 622;
  Object.assign(G, { resets: 100, pledges: 10, santaLevel: 14, dragonLevel: 27,
    cookies: 1e200, cookiesEarned: 1e200, handmadeCookies: 1e40, lumps: 10, lumpsTotal: 136 });
  for (const item of requirements.ownedUpgrades) Object.assign(G.Upgrades[item.name], { bought: 1, unlocked: 1 });
  for (const item of requirements.accessUpgrades) G.Upgrades[item.name].unlocked = 1;
  for (const b of Object.values(G.Objects)) {
    b.amount = b.highest = b.id === 0 ? 1000 : 700;
    b.level = b.id === 0 ? 12 : b.id === 2 ? (milkFallback ? 9 : 10) : 1;
  }
  G.LoadMinigames();
  runtime.snapshot(); // Keep the supplied access history through native selector locks.
  runtime.advance(1000);
  const garden = G.Objects.Farm.minigame;
  for (const p of Object.values(garden.plants)) p.unlocked = 1;
  garden.convertTimes = 1;
  garden.harvestsTotal = 1000;
  G.Objects.Bank.minigame.officeLevel = 5;
  return runtime;
}

test('a second native Garden sacrifice can pass through completion before it clears the seed log', { skip }, () => {
  // Conditional late-game fixture, not a reachable new-save route. The intact
  // convert/harvest/Win bodies run in the isolated source adapter. This rejects
  // an unconditional claim that every internal completion persists to return.
  const runtime = finalFixture();
  const G = runtime.Game;
  const M = G.Objects.Farm.minigame;
  G.Achievements['Green, aching thumb'].won = 0;
  G.AchievementsOwned--;
  M.harvestsTotal = 999;
  M.getUnlockedN();
  M.plot[0][0] = [M.plants.bakerWheat.id + 1, 100];
  const before = runtime.snapshot();
  assert.deepEqual(assessCompletion(before, requirements).missing.map(x => [x.category, x.key]),
    [['achievement', 'Green, aching thumb']]);
  let during = null;
  const nativeWin = G.Win;
  G.Win = function (name) {
    const result = nativeWin.apply(this, arguments);
    if (name === 'Green, aching thumb') {
      during = assessCompletion(captureCompletionSnapshot(G, before.history, { edition: 'steam' }), requirements);
    }
    return result;
  };
  try { M.convert(); } finally { G.Win = nativeWin; }
  assert.equal(during?.complete, true);
  const after = runtime.snapshot();
  const result = assessCompletion(after, requirements);
  assert.equal(result.complete, false);
  assert.equal(result.missing.length, 33);
  assert(result.missing.every(x => x.category === 'gardenSeed'));
  assert.equal(after.elapsedMs, before.elapsedMs);
});

test('harvesting without the second sacrifice retains completion in the same conditional fixture', { skip }, () => {
  const runtime = finalFixture();
  const G = runtime.Game;
  const M = G.Objects.Farm.minigame;
  G.Achievements['Green, aching thumb'].won = 0;
  G.AchievementsOwned--;
  M.harvestsTotal = 999;
  M.getUnlockedN();
  M.plot[0][0] = [M.plants.bakerWheat.id + 1, 100];
  const before = runtime.snapshot();
  assert.equal(assessCompletion(before, requirements).complete, false);
  M.harvestAll();
  const after = runtime.snapshot();
  assert.equal(assessCompletion(after, requirements).complete, true);
  assert.equal(after.elapsedMs, before.elapsedMs);
});

test('every required ordinary upgrade has a composed native purchase path from a supplied final boundary', { skip }, () => {
  const runtime = finalFixture();
  const source = completionPolicySource({ inputBatchMilliseconds: 0 });
  const upgrades = requirements.ownedUpgrades.filter(item => runtime.Game.Upgrades[item.name].pool !== 'prestige');
  assert.equal(upgrades.length, 716);
  // Remove one ownership flag at a time. All prices, canBuy checks, native
  // purchase effects, and the One mind confirmation workflow remain real.
  for (const item of upgrades) {
    const upgrade = runtime.Game.Upgrades[item.name];
    upgrade.bought = 0;
    runtime.Game.RebuildUpgrades();
    // This supplied final boundary includes the controller's completed fixed
    // preparation. It is not a fresh controller at the start of that phase.
    let memory = { restoreViewport: true, finalPreparationComplete: true,
      finalCollectionStarted: true };
    for (let step = 0; step < 3 && !upgrade.bought; step++) {
      const decision = decidePolicy(source, runtime.snapshot(), [], memory);
      memory = decision.memory;
      if (step === 0) assert.deepEqual(decision.action, { type: 'buy-upgrade', id: item.id }, item.name);
      else assert.deepEqual(decision.action, { type: 'prompt', option: 0 }, item.name);
      runtime.act(decision.action);
    }
    assert.equal(upgrade.bought, 1, item.name);
    assert.equal(runtime.Game.promptOn, 0, item.name);
  }
  assert.equal(assessCompletion(runtime.snapshot(), requirements).complete, true);
});

test('the native Farm-level fallback closes the sole 599-achievement milk gap in a supplied final state', { skip }, () => {
  const runtime = finalFixture({ milkFallback: true });
  const before = assessCompletion(runtime.snapshot(), requirements);
  assert.equal(before.valid, true);
  assert.deepEqual(before.missing.map(x => [x.category, x.key]), [
    ['cosmeticUnlock', 'milkChoices'], ['progression', 'achievementsOwned'],
  ]);
  assert.equal(runtime.Game.AchievementsOwned, 599);
  const source = completionPolicySource({ inputBatchMilliseconds: 0 });
  const decision = decidePolicy(source, runtime.snapshot(), [], { restoreViewport: true });
  assert.equal(decision.stage, 'milk-unlock');
  assert.deepEqual(decision.action, { type: 'level-building', id: 2 });
  runtime.act(decision.action);
  assert.equal(runtime.Game.HasAchiev('Huge tracts of land'), 1);
  assert.equal(runtime.Game.Objects.Farm.level, 10);
  assert.equal(runtime.Game.AchievementsOwned, 600, 'actual native award increments the milk selector counter');
  assert.equal(assessCompletion(runtime.snapshot(), requirements).complete, true);
});

test('native bulk purchases debit each rounded unit and may stop below the displayed full-batch quote', { skip }, () => {
  const runtime = createRuntime();
  const G = runtime.Game;
  G.cookies = G.cookiesEarned = 305;
  runtime.advance(1000);
  const cursor = G.Objects.Cursor;
  assert.equal(cursor.getSumPrice(10), 305);
  runtime.act({ type: 'buy-building', id: 0, amount: 10 });
  assert.equal(cursor.amount, 9);
  assert.equal(G.cookies, 50);
  assert.equal(cursor.getPrice(), 53);
  // The next public observation reports the actual partial purchase; the
  // adapter does not fabricate ten owned copies from its quote precondition.
  assert.equal(runtime.snapshot().shop.buildings[0].amount, 9);
  G.cookies += 3; // Supplied affordability boundary; no claim about earning this gift.
  runtime.act({ type: 'buy-building', id: 0, amount: 1 });
  assert.equal(cursor.amount, 10);
  assert.equal(G.cookies, 0);
});

test('native store controls expose buy100 and sellAll, with no buyMax alias', { skip }, () => {
  const runtime = createRuntime();
  const G = runtime.Game;
  G.cookies = G.cookiesEarned = 1e12;
  runtime.advance(1000);
  runtime.act({ type: 'store-bulk', id: 5 });
  assert.equal(G.buyMode, 1);
  assert.equal(G.buyBulk, 100);
  runtime.act({ type: 'click-product', id: 0 });
  assert.equal(G.Objects.Cursor.amount, 100);
  runtime.act({ type: 'store-bulk', id: 1 });
  runtime.act({ type: 'store-bulk', id: 5 });
  assert.equal(G.buyBulk, -1);
  runtime.act({ type: 'click-product', id: 0 });
  assert.equal(G.Objects.Cursor.amount, 0);
});
