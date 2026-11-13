import test from 'node:test';
import assert from 'node:assert/strict';
import { nextPrestigeWithSevens, decideAscensionAction, ascensionPolicySource } from '../model/ascension-policy.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
const sevens = x => (String(x).match(/7/g) || []).length;
const permit = { allowReset: true };
function challenges(runtime) { runtime.Game.Win('Hardcore'); runtime.Game.Win('Neverclick'); }
function fundPrestige(runtime, prestige) {
  // Synthetic milestone fixture, not a demonstrated new-save production trace.
  runtime.Game.cookiesEarned = (prestige + 0.25) ** 3 * 1e12 - runtime.Game.cookiesReset;
  runtime.Game.cookies = runtime.Game.cookiesEarned;
}
function cycle(runtime, memory = {}, options = permit) {
  const oldResets = runtime.Game.resets;
  const actions = [];
  for (let i = 0; i < 500; i++) {
    const state = runtime.snapshot();
    if (actions.length && runtime.Game.resets > oldResets && !state.progression.onAscend
      && !state.progression.reincarnateTimer && !state.progression.ascendTimer) return { memory, actions };
    const d = decideAscensionAction(state, memory, options); memory = d.memory;
    assert(d.action, `${d.status}: ${d.reason}`);
    actions.push(d.action); runtime.act(d.action);
  }
  assert.fail('Ascension cycle exceeded its test decision budget');
}

test('the decimal planner finds the earliest safe integer with seven occurrences anywhere', () => {
  for (let n = 0; n < 10000; n += 37) for (const count of [1, 2, 4]) {
    const answer = nextPrestigeWithSevens(n, count);
    assert(answer >= n && sevens(answer) >= count);
    for (let earlier = n; earlier < answer; earlier++) assert(sevens(earlier) < count);
  }
  assert.equal(nextPrestigeWithSevens(7000, 1), 7000);
  assert.equal(nextPrestigeWithSevens(7700, 2), 7700);
  assert.equal(nextPrestigeWithSevens(77770000, 4), 77770000);
  assert(nextPrestigeWithSevens(Number.MAX_SAFE_INTEGER, 4) > Number.MAX_SAFE_INTEGER);
});

test('the source builder works with frozen observations and no helper closure', { skip }, () => {
  const r = createRuntime();
  const state = r.snapshot();
  assert.deepEqual(decidePolicy(ascensionPolicySource(), state, [], null), decideAscensionAction(state));
});

test('first-run achievements and explicit scheduler permission protect a funded run', { skip }, () => {
  const r = createRuntime(); fundPrestige(r, 100077777);
  assert.equal(decideAscensionAction(r.snapshot(), {}, permit).status, 'needs-achievement');
  challenges(r);
  const d = decideAscensionAction(r.snapshot());
  assert.equal(d.status, 'deferred'); assert.equal(d.action, null);
  assert.equal(d.gatePlan.ready, true);
  assert.equal(r.Game.OnAscend, 0);
});

test('heavenly growth precedes grinding counted resets unless the scheduler opts into early counts', { skip }, () => {
  const r = createRuntime(); challenges(r);
  for (const u of Object.values(r.Game.Upgrades)) if (u.pool === 'prestige' && u.getPrice() <= 1) u.earn();
  r.Game.cookiesReset = 1000.25 ** 3 * 1e12;
  r.Game.prestige = Math.floor(r.Game.HowMuchPrestige(r.Game.cookiesReset));
  fundPrestige(r, r.Game.prestige + 1);
  let d = decideAscensionAction(r.snapshot(), {}, permit);
  assert.equal(r.snapshot().ascension.gainedIfAscend, 1);
  assert.notEqual(d.action?.type, 'ascend');
  d = decideAscensionAction(r.snapshot(), {}, { ...permit, earlyCountResets: true });
  assert.equal(d.action.type, 'ascend'); assert.equal(d.goal, 'Reincarnation');
  fundPrestige(r, r.Game.prestige * 4);
  d = decideAscensionAction(r.snapshot(), {}, permit);
  assert.equal(d.action.type, 'ascend'); assert.equal(d.goal, 'Heavenly growth');
});

test('native sevens gates are not suffix gates, and large-number targets survive native numeric rounding', { skip }, () => {
  const r = createRuntime(); challenges(r);
  for (const [name, prestige] of [['Lucky digit', 7000], ['Lucky number', 7700], ['Lucky payout', 77770000]]) {
    r.Game.prestige = prestige;
    assert.equal(r.Game.Upgrades[name].showIf(), true, name);
  }
  r.Game.cookiesReset = 1e78; r.Game.cookiesEarned = 0;
  r.Game.prestige = Math.floor(r.Game.HowMuchPrestige(r.Game.cookiesReset));
  const d = decideAscensionAction(r.snapshot(), {}, permit);
  assert.equal(d.status, 'needs-prestige'); assert.equal(d.action, null);
  assert(d.gatePlan.targetPrestige > r.Game.prestige);
  const nativeTarget = Math.floor(r.Game.HowMuchPrestige(d.gatePlan.targetLifetimeCookies));
  assert(sevens(nativeTarget) >= d.gatePlan.sevens);
  for (const count of [1,2,4]) for (const start of [1e16,1e22,1e40,1e80]) {
    const target = nextPrestigeWithSevens(start, count);
    assert(target >= start && sevens(target) >= count);
    assert(sevens(Math.floor(r.Game.HowMuchPrestige(target ** 3 * 1e12))) >= count);
  }
  r.Game.cookiesEarned = d.gatePlan.targetLifetimeCookies - r.Game.cookiesReset;
  r.Game.cookies = r.Game.cookiesEarned;
  cycle(r);
  for (const name of ['Lucky digit', 'Lucky number', 'Lucky payout']) assert.equal(r.Game.Upgrades[name].bought, 1, name);
});

test('a native ascent buys gated ancestors first, handles slot prompts, and returns to normal mode', { skip }, () => {
  const r = createRuntime(); challenges(r); fundPrestige(r, 100077777);
  r.Game.Upgrades['Reinforced index finger'].earn();
  const { actions } = cycle(r);
  for (const name of ['Lucky digit', 'Lucky number', 'Lucky payout']) assert.equal(r.Game.Upgrades[name].bought, 1, name);
  assert(actions.some(a => a.type === 'key' && a.code === 27 && a.down === false));
  assert(actions.some(a => a.type === 'permanent-slot'));
  assert.equal(r.Game.permanentUpgrades[0], r.Game.Upgrades['Reinforced index finger'].id);
  assert.equal(r.Game.promptOn, 0); assert.equal(r.Game.OnAscend, 0);
  assert.equal(r.Game.ascensionMode, 0); assert.equal(r.Game.resets, 1);
});

test('a sufficiently funded native ascent purchases all129 legal heavenly upgrades', { skip }, () => {
  const r = createRuntime(); challenges(r);
  fundPrestige(r, 7777777777777777000);
  const initial = r.snapshot();
  assert(sevens(initial.ascension.prestigeIfAscend) >= 4);
  assert(initial.ascension.heavenlyUpgrades.reduce((total, u) => total + u.price, 0) < initial.ascension.gainedIfAscend);
  const { actions } = cycle(r);
  assert.equal(r.snapshot().ascension.heavenlyUpgrades.filter(u => u.bought).length, 129);
  assert.equal(r.Game.Achievements['All the stars in heaven'].won, 1);
  assert.equal(r.Game.promptOn, 0);
  assert(actions.filter(a => a.type === 'close-prompt').length >= 5);
});

test('multiple native cycles count only positive prestige gains and resolve empty slot prompts', { skip }, () => {
  const r = createRuntime(); challenges(r);
  let memory = {};
  for (const target of [7, 77, 777]) {
    fundPrestige(r, target);
    const outcome = cycle(r, memory); memory = outcome.memory;
  }
  assert.equal(r.Game.resets, 3);
  assert.equal(r.Game.promptOn, 0);
  const d = decideAscensionAction(r.snapshot(), memory, permit);
  assert.notEqual(d.action?.type, 'ascend');
  assert.equal(r.snapshot().ascension.gainedIfAscend, 0);
});

test('the native100th counted reset awards the high-cookie, stars and active-loan goals', { skip }, () => {
  const r = createRuntime(); challenges(r);
  r.Game.resets = 99;
  for (const u of Object.values(r.Game.Upgrades)) if (u.pool === 'prestige') { u.bought = 1; u.unlocked = 1; }
  r.evaluate(r.source.sources['minigameMarket.js'], 'minigameMarket.js');
  const bank = r.Game.Objects.Bank;
  bank.level = 1; bank.amount = 1; bank.highest = 1;
  bank.minigame.launch(); bank.minigameLoaded = true; bank.minigame.officeLevel = 2;
  r.Game.cookies = 1e57; r.Game.cookiesEarned = 1e57;
  const { memory, actions } = cycle(r);
  assert(actions.some(a => a.type === 'market-loan'));
  assert.equal(r.Game.resets, 100);
  for (const name of ['No more room in hell', 'All the stars in heaven', 'Debt evasion', 'Reincarnation']) assert.equal(r.Game.Achievements[name].won, 1, name);
  assert.equal(bank.minigame.officeLevel, 0);
  assert.equal(decideAscensionAction(r.snapshot(), memory, permit).goal, 'Final run growth');
  fundPrestige(r, r.Game.prestige * 4 + 10);
  assert.equal(decideAscensionAction(r.snapshot(), memory, permit).goal, 'Heavenly growth');
  assert.equal(decideAscensionAction(r.snapshot(), memory, { ...permit, continueGrowthAfterMilestones: false }).status, 'complete');
  r.Game.cookiesEarned = 1e72;
  r.Game.Win('And a little extra'); r.Game.Win("What's not clicking");
  assert.notEqual(decideAscensionAction(r.snapshot(), memory, permit).status, 'complete');
  r.Game.Win("Speed's the name of the game (no it's not it's called Cookie Clicker)");
  const d = decideAscensionAction(r.snapshot(), memory, permit);
  assert.equal(d.status, 'complete'); assert.equal(d.action, null);
  assert.equal(r.Game.ascensionMode, 0);
  r.Game.cookiesEarned = 0;
  assert.equal(decideAscensionAction(r.snapshot(), memory, permit).status, 'complete');
  assert.notEqual(decideAscensionAction(r.snapshot(), memory, { ...permit, finalRunCookies: 1e73 }).status, 'complete');
});
