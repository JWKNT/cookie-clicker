import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { decideSeasonAction, seasonPolicySource } from '../model/season-policy.mjs';
import { decideGardenAction } from '../model/garden-policy.mjs';
import { decideMarketAction } from '../model/market-policy.mjs';
import { decideRecoveryTail, recoveryTailPolicySource, NATURAL_TAIL_OPTIONS, NATURAL_TAIL_MAINTENANCE } from '../model/recovery-tail-policy.mjs';
const skip = !hasGameSource() && 'Pinned source unavailable';
const contract = JSON.parse(readFileSync(new URL('../model/completion-requirements.json', import.meta.url)));
const source = recoveryTailPolicySource();

// This snapshot is an explicit conditional entry fixture, not a new-save path.
function entry() {
  const r = createRuntime({ recordAudit: false }); r.advance(200);
  const G = r.Game;
  G.cookies = G.cookiesEarned = 2 ** 500; G.resets = 100; G.dragonLevel = 27; G.santaLevel = 14; G.pledges = 10;
  for (const a of Object.values(G.Achievements)) a.won = 1;
  G.AchievementsOwned = Object.values(G.Achievements).filter(a => a.pool !== 'shadow').length;
  for (const u of Object.values(G.Upgrades)) { u.unlocked = 1; u.bought = Number(!['debug','unused','dungeon','shadow','toggle'].includes(u.pool)); }
  // Native mutually exclusive toggles are not all active in the fixture.
  for (const name of ['Golden switch [off]', 'Elder Covenant', 'Shimmering veil [off]', 'Sugar frenzy']) G.Upgrades[name].bought = 0;
  G.dragonAura = G.dragonAura2 = 0; G.seasonT = 0;
  for (const b of Object.values(G.Objects)) { b.amount = b.highest = 1000; b.level = 1; }
  G.Objects.Farm.level = 10; G.Objects.Cursor.level = 12;
  for (const [name, file] of [['Farm','minigameGarden.js'],['Bank','minigameMarket.js'],['Temple','minigamePantheon.js'],['Wizard tower','minigameGrimoire.js']]) {
    const b = G.Objects[name]; if (!b.minigame) r.evaluate(r.source.sources[file], file);
    b.minigame.launch(); b.minigameLoaded = true; b.switchMinigame(true);
  }
  const M = G.Objects.Bank.minigame; M.officeLevel = 4; M.brokers = 50;
  const garden = G.Objects.Farm.minigame; garden.soil = 0; garden.convertTimes = 1; garden.harvestsTotal = 1000;
  for (const p of Object.values(garden.plants)) p.unlocked = 1;
  G.recalculateGains = 1; r.advance(200);
  const o = r.snapshot();
  o.seasonal.remainingMs = 0;
  return { r, o };
}
function active(o) { return { released: true, entry: { ascensions: o.ascensions, seasonUses: o.seasonal.uses } }; }
const seasonOnly = { preserveChallengeAchievements: false, naturalSeasons: true, popGoldenCookies: false,
  research: false, fortunes: false, dragonDrops: false, wrinklers: false, helperGrandma: false, eldeer: false, reindeerTarget: 0 };

test('the separate recovery tail has an explicit handoff and a fixed daily maintenance contract', { skip }, () => {
  const { o } = entry();
  assert.deepEqual(NATURAL_TAIL_MAINTENANCE, { firstMs: 86400000, everyMs: 86400000 });
  assert.equal(decideRecoveryTail(o).status, 'deferred');
  o.achievements['Thick-skinned'] = false;
  const d = decideRecoveryTail(o, { released: true });
  assert.equal(d.status, 'needs-entry'); assert(d.missing.includes('Thick-skinned'));
});

test('a complete conditional entry uses the actual full terminal predicate and agrees in the restricted VM', { skip }, () => {
  const { o } = entry();
  const d = decideRecoveryTail(o, { released: true });
  assert.notEqual(d.status, 'needs-entry', JSON.stringify(d));
  assert.deepEqual(decidePolicy(source, o, [], { released: true }), d);
  o.market.officeLevel = o.progression.stockOfficeLevel = 5;
  const done = decideRecoveryTail(o, d.memory);
  assert.equal(done.status, 'complete', JSON.stringify(done));
});

test('natural windows do not buy paid switches, reset at the old use cap, or ignore active Christmas', { skip }, () => {
  const { r, o } = entry();
  const heart = o.seasonal.groups.valentines[0]; o.upgrades[heart] = { ...o.upgrades[heart], bought: false, unlocked: false };
  o.seasonal.season = ''; o.seasonal.uses = 1000000;
  let d = decideSeasonAction(o, {}, { ...seasonOnly, seasons: ['valentines','christmas'] });
  assert.equal(d.status, 'waiting'); assert.equal(d.goal, 'Natural season window'); assert.equal(d.action.type, 'wait');
  assert.deepEqual(decidePolicy(seasonPolicySource({ ...seasonOnly, seasons: ['valentines','christmas'] }), o, [], {}), d);
  o.seasonal.season = 'christmas'; o.santa.level = 0; o.santa.canUpgrade = true;
  d = decideSeasonAction(o, {}, { ...seasonOnly, seasons: ['valentines','christmas'] });
  assert.equal(d.action.type, 'upgrade-santa');
  // Native control execution is separate from this public snapshot test.
  r.Game.season = 'christmas'; r.Game.santaLevel = 0; r.Game.Upgrades['A festive hat'].bought = 1;
  const before = r.Game.seasonUses; r.act(d.action); assert.equal(r.Game.santaLevel, 1); assert.equal(r.Game.seasonUses, before);
});

test('golden cookies are left untouched, including when seasonal rewards remain', { skip }, () => {
  const { o } = entry(); o.shimmers = [{ id: 77, type: 'golden', life: 20, lifeSeconds: 1 }];
  const d = decideSeasonAction(o, {}, { ...seasonOnly, seasons: [] });
  assert.notEqual(d.action?.type, 'click-shimmer');
  const all = decideRecoveryTail(o, active(o));
  assert.notEqual(all.action?.type, 'click-shimmer');
});

test('the dirt option overrides recipe and novel-growth soil changes and honors cooldowns', { skip }, () => {
  const { r, o } = entry(); const G = o.garden;
  G.plants.thumbcorn.unlocked = false; G.soil = 'fertilizer'; G.nextSoilMs = 100;
  let d = decideGardenAction(o, {}, NATURAL_TAIL_OPTIONS.garden);
  assert.equal(d.action.type, 'wait');
  G.nextSoilMs = 0; d = decideGardenAction(o, {}, NATURAL_TAIL_OPTIONS.garden);
  assert.deepEqual(d.action, { type: 'garden-soil', soil: 'dirt' });
  const M = r.Game.Objects.Farm.minigame; M.soil = 1; M.nextSoil = 0;
  r.act(d.action); assert.equal(M.soil, 0);
  G.soil = 'dirt'; G.plot[2][2] = ['thumbcorn', 0];
  d = decideGardenAction(o, {}, NATURAL_TAIL_OPTIONS.garden);
  assert.notEqual(d.action?.type, 'garden-soil');
});

test('market preparation defers office 5 and caps holdings and both transaction directions', { skip }, () => {
  const { r, o } = entry(); o.achievements['Pyramid scheme'] = false;
  let d = decideMarketAction(o, {}, NATURAL_TAIL_OPTIONS.market);
  assert.equal(d.status, 'prepared'); assert.equal(d.action, null);
  o.achievements['Liquid assets'] = false;
  for (const g of o.market.goods) { g.stock = 0; g.canBuy = true; g.price = 1; g.buyCookiePrice = 1; g.maxStock = 2000; }
  d = decideMarketAction(o, {}, NATURAL_TAIL_OPTIONS.market);
  assert.equal(d.action.type, 'market-buy'); assert.equal(d.action.amount, 1000);
  const good = o.market.goods.find(g => g.id === d.action.id); good.stock = 999;
  d = decideMarketAction(o, {}, NATURAL_TAIL_OPTIONS.market);
  assert.equal(d.action.amount, 1);
  good.stock = 1000; good.price = 1000; good.canSell = true;
  d = decideMarketAction(o, {}, NATURAL_TAIL_OPTIONS.market);
  assert.equal(d.action.type, 'market-sell'); assert.equal(d.action.amount, 1000);
  // Native quantity and cash conversion remain in the intact market callback.
  const M = r.Game.Objects.Bank.minigame; const native = M.goodsById[good.id]; native.stock = 1000; native.last = 0;
  r.act(d.action); assert.equal(native.stock, 0);
});

test('the final office waits for Garden and Hand-picked, then uses the native office callback', { skip }, () => {
  const { r, o } = entry();
  o.achievements['Pyramid scheme'] = false; o.achievements['Hand-picked'] = false;
  let d = decideRecoveryTail(o, active(o));
  assert.equal(d.memory.market.config.maximumOffice, 4); assert.notEqual(d.action?.type, 'market-office');
  o.achievements['Hand-picked'] = true;
  d = decideRecoveryTail(o, d.memory);
  assert.equal(d.memory.market.config.maximumOffice, 5); assert.equal(d.action.type, 'market-office');
  const M = r.Game.Objects.Bank.minigame; r.Game.Objects.Cursor.amount = 1000; r.Game.Objects.Cursor.level = 12;
  r.advance(400); assert.equal(r.snapshot().market.officeUpgradeVisible, true);
  r.act(d.action); assert.equal(M.officeLevel, 5);
});

test('prefix buffs drain, Sugar blessing does not block the tail, and missing reload fields preserve phase memory', { skip }, () => {
  const { o } = entry(); const m = active(o); m.garden = { target: 'queenbeetLump' };
  o.buffs = { Frenzy: { time: 20, multCpS: 7 }, 'Sugar blessing': { time: 9999 } };
  let d = decideRecoveryTail(o, m); assert.equal(d.stage, 'drain-prefix-buffs');
  delete o.buffs.Frenzy; d = decideRecoveryTail(o, m); assert.notEqual(d.stage, 'drain-prefix-buffs');
  o.ascensions = 0; o.controls.promptOn = true; o.garden = null;
  d = decideRecoveryTail(o, m); assert.equal(d.stage, 'maintenance-restoration');
  assert.equal(d.memory.garden.target, 'queenbeetLump'); assert.equal(d.action.type, 'wait');
});

test('a paid season change or a resource-envelope violation is explicit, never silently repaired with a reset', { skip }, () => {
  const { o } = entry(); const m = active(o);
  o.seasonal.uses++; let d = decideRecoveryTail(o, m); assert.equal(d.stage, 'tail-invariant'); assert.equal(d.action, null);
  o.seasonal.uses--; o.shop.buildings[0].amount = 2001;
  d = decideRecoveryTail(o, m); assert.equal(d.stage, 'tail-envelope'); assert.equal(d.action, null);
});

test('prefix controller options cannot turn paid switching or non-dirt soil back on', { skip }, () => {
  const { o } = entry();
  const heart = o.seasonal.groups.valentines[0]; o.upgrades[heart].bought = false; o.upgrades[heart].unlocked = false;
  o.seasonal.season = ''; o.shimmers = [{ id: 79, type: 'golden', life: 20, lifeSeconds: 1 }];
  const memory = { ...active(o), season: { config: { naturalSeasons: false, popGoldenCookies: true } },
    garden: { config: { fixedSoil: null, naturalCookieFarm: true } } };
  const d = decideRecoveryTail(o, memory);
  assert.equal(d.memory.season.config.naturalSeasons, true); assert.equal(d.memory.season.config.popGoldenCookies, false);
  assert.equal(d.memory.garden.config.fixedSoil, 'dirt'); assert.equal(d.memory.garden.config.naturalCookieFarm, false);
  assert.deepEqual(decidePolicy(source, o, [], memory), d);
});

test('natural Halloween and Easter use positive wrinkler payouts and leave golden drops alone', { skip }, () => {
  const { o } = entry();
  for (const season of ['halloween','easter']) {
    const name = o.seasonal.groups[season][0]; o.upgrades[name] = { ...o.upgrades[name], bought: false, unlocked: false };
    o.seasonal.season = season; o.seasonal.elderWrath = 3;
    o.shimmers = [{ id: 77, type: 'golden', life: 20, lifeSeconds: 1 }];
    o.controls.wrinklers = [{ id: 0, phase: 2, selected: true, sucked: 100, hp: 3 }];
    const d = decideSeasonAction(o, {}, { ...seasonOnly, seasons: ['valentines','christmas','halloween','easter'], wrinklers: true });
    assert.equal(d.action.type, 'wrinkler-poke');
  }
});

test('a bounded native Santa-to-office tail can reach the full predicate from its stated conditional entry', { skip }, () => {
  const { r, o } = entry(); const G = r.Game;
  G.santaLevel = 13; G.season = 'christmas'; G.Achievements['Pyramid scheme'].won = 0;
  // All prior goals and entry resources are premises; only this suffix is run.
  let memory = { released: true }; const actions = [];
  for (let step = 0; step < 20; step++) {
    const observation = r.snapshot();
    const d = decideRecoveryTail(observation, memory); memory = d.memory;
    if (d.status === 'complete') break;
    assert(d.action, JSON.stringify(d)); actions.push(d.action); r.act(d.action);
  }
  const observation = r.snapshot();
  assert.equal(decideRecoveryTail(observation, memory).status, 'complete');
  assert(actions.some(a => a.type === 'upgrade-santa')); assert(actions.some(a => a.type === 'market-office'));
  assert.equal(G.seasonUses, 0); assert.equal(actions.some(a => ['ascend','reincarnate','click-shimmer'].includes(a.type)), false);
});

test('a maintenance language prompt does not inherit Garden or research confirmation ownership', { skip }, () => {
  const { o } = entry(); o.controls.promptOn = true; o.controls.menu = 'prefs';
  const m = { ...active(o), garden: { confirmSacrifice: true },
    prompt: { owner: 'garden', elapsedMs: o.elapsedMs, menu: '' } };
  const d = decideRecoveryTail(o, m);
  assert.equal(d.stage, 'unowned-prompt'); assert.equal(d.action.type, 'wait');
  assert.equal(d.memory.garden.confirmSacrifice, undefined); assert.equal(d.memory.prompt, undefined);
  o.controls.promptOn = false;
  const restored = decideRecoveryTail(o, d.memory);
  assert.deepEqual(restored.action, { type: 'open-menu', menu: '' });
});

test('an owned native Garden confirmation completes before returning to the seed-rebuild phase', { skip }, () => {
  const { r } = entry(); const G = r.Game; const garden = G.Objects.Farm.minigame;
  garden.convertTimes = 0; G.Achievements['Seedless to nay'].won = 0;
  garden.plantsUnlockedN = garden.plantsN;
  let d = decideRecoveryTail(r.snapshot(), { released: true });
  assert.equal(d.action.type, 'garden-sacrifice'); r.act(d.action);
  assert.equal(G.promptOn, 1);
  d = decideRecoveryTail(r.snapshot(), d.memory);
  assert.deepEqual(d.action, { type: 'prompt', option: 0 }); r.act(d.action);
  assert.equal(garden.convertTimes, 1); assert.equal(!!G.HasAchiev('Seedless to nay'), true);
  assert.equal(d.memory.prompt, undefined);
  const next = decideRecoveryTail(r.snapshot(), d.memory);
  assert(next.memory.garden); assert.equal(r.snapshot().progression.gardenSeeds.length, 1);
  assert.notEqual(next.action?.type, 'prompt'); assert.notEqual(next.status, 'blocked');
});

test('native 699-to-700 ownership is collected in the tail instead of required at entry', { skip }, () => {
  const { r } = entry(); const G = r.Game;
  // Coherent conditional ownership fixture; every subsequent purchase and award
  // is the intact native callback. This is not a fresh-save route.
  const owned = Object.values(G.Upgrades).filter(u => u.bought && G.CountsAsUpgradeOwned(u.pool));
  const removed = owned.filter(u => u.id < 100).slice(0, owned.length - 699);
  assert.equal(owned.length - removed.length, 699);
  for (const u of removed) u.bought = 0;
  G.UpgradesOwned = Object.values(G.Upgrades).filter(u => u.bought && G.CountsAsUpgradeOwned(u.pool)).length;
  G.Achievements["Oft we mar what's well"].won = 0; G.AchievementsOwned--;
  G.upgradesToRebuild = 1; G.recalculateGains = 1; r.advance(1200);
  assert.equal(G.UpgradesOwned, 699); assert.equal(G.HasAchiev("Oft we mar what's well"), 0);
  let memory = { released: true }; let bought = false;
  for (let n = 0; n < 20; n++) {
    const d = decideRecoveryTail(r.snapshot(), memory); memory = d.memory;
    assert.notEqual(d.status, 'needs-entry', JSON.stringify(d));
    assert(d.action, JSON.stringify(d)); r.act(d.action);
    if (G.UpgradesOwned === 700) { bought = true; break; }
  }
  assert(bought); r.advance(5100); assert.equal(G.HasAchiev("Oft we mar what's well"), 1);
});
