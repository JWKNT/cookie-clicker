import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { GARDEN_RECIPES, GARDEN_DROP_CROPS, decideGardenAction, gardenPolicySource } from '../model/garden-policy.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const catalogue = JSON.parse(readFileSync(new URL('../model/catalogue.json', import.meta.url)));
const seeds = catalogue.garden.seeds;
const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
const seedOnly = { farmDrops: false, harvestTarget: 0, requireFullPlot: false };

function observation({ known = ['bakerWheat'], level = 9, seedless = false } = {}) {
  return {
    cookies: 1e100, progression: { onAscend: false, ascensionMode: 0 }, controls: { promptOn: false },
    achievements: {}, upgrades: {},
    garden: { ready: true, level, farmAmount: 300, freeze: false, soil: 'fertilizer', nextStepMs: 180000, nextSoilMs: 0,
      stepSeconds: 180, plot: Array.from({ length: 6 }, () => Array.from({ length: 6 }, () => [null, 0])),
      plants: Object.fromEntries(seeds.map(p => [p.key, { ...p, cost: 10, unlocked: known.includes(p.key) }])),
      harvestsTotal: 0, convertTimes: Number(seedless), seedless,
    },
  };
}

function nativeGarden() {
  const runtime = createRuntime();
  runtime.evaluate(runtime.source.sources['minigameGarden.js'], 'minigameGarden.js');
  const farm = runtime.Game.Objects.Farm;
  farm.level = 9; farm.amount = 300; farm.highest = 300;
  farm.minigame.launch(); farm.minigameLoaded = true;
  runtime.Game.cookies = 1e100; runtime.Game.cookiesPs = 0;
  return runtime;
}

// The long kernel fixture needs only the Garden's public observation. Avoid
// quoting thousands of unrelated building purchases at every growth tick.
// The fixture checks this projection against the complete adapter periodically.
function gardenKernelObservation(runtime) {
  const { Game, clock } = runtime;
  const farm = Game.Objects.Farm;
  const garden = farm.minigame;
  return {
    cookies: Game.cookies,
    progression: { onAscend: !!Game.OnAscend, ascensionMode: Game.ascensionMode },
    controls: { promptOn: !!Game.promptOn },
    achievements: Object.fromEntries(Object.values(Game.Achievements).map(a => [a.name, !!a.won])),
    upgrades: Object.fromEntries(Object.values(Game.Upgrades).map(u => [u.name, { id: u.id, bought: !!u.bought, unlocked: !!u.unlocked }])),
    garden: { ready: !!Game.isMinigameReady(farm), level: farm.level, farmAmount: farm.amount,
      freeze: !!garden.freeze, frozen: !!garden.freeze, soil: garden.soilsById[garden.soil]?.key ?? garden.soil,
      nextStepMs: Math.max(0, garden.nextStep - clock.now), nextSoilMs: Math.max(0, garden.nextSoil - clock.now), stepSeconds: garden.stepT,
      plot: Array.from(garden.plot, row => Array.from(row, tile => [tile[0] > 0 ? garden.plantsById[tile[0] - 1].key : null, tile[1]])),
      plants: Object.fromEntries(Object.entries(garden.plants).map(([key, p]) => [key, {
        id: p.id, name: p.name, unlocked: !!p.unlocked, mature: p.mature, immortal: !!p.immortal,
        plantable: p.plantable !== false, cost: garden.getCost(p), ageTick: p.ageTick, ageTickR: p.ageTickR,
      }])),
      harvestsTotal: garden.harvestsTotal, convertTimes: garden.convertTimes, seedless: !!Game.HasAchiev('Seedless to nay'),
    },
  };
}

function projectGardenObservation(snapshot) {
  return { cookies: snapshot.cookies, progression: { onAscend: snapshot.progression.onAscend, ascensionMode: snapshot.progression.ascensionMode },
    controls: { promptOn: snapshot.controls.promptOn }, achievements: snapshot.achievements,
    upgrades: snapshot.upgrades, garden: snapshot.garden };
}

test('the constructive recipe dependency order covers every canonical seed', () => {
  const reached = new Set(['bakerWheat']);
  for (const recipe of GARDEN_RECIPES) {
    assert(Object.keys(recipe.parents).every(parent => reached.has(parent)), recipe.target);
    reached.add(recipe.target);
  }
  assert.deepEqual(reached, new Set(seeds.map(x => x.key)));
  assert.equal(GARDEN_DROP_CROPS.length, 7);
});

test('every stated cross-breeding recipe is accepted by the unmodified native mutation function', { skip }, () => {
  const runtime = nativeGarden();
  const M = runtime.Game.Objects.Farm.minigame;
  for (const recipe of GARDEN_RECIPES.filter(x => !x.kind)) {
    const all = Object.fromEntries(seeds.map(x => [x.key, 0]));
    const mature = { ...all };
    for (const [key, count] of Object.entries(recipe.parents)) {
      all[key] = count;
      mature[key] = recipe.immatureParents?.includes(key) ? 0 : count;
    }
    const candidates = M.getMuts(all, mature);
    assert(candidates.some(([key, p]) => key === recipe.target && p === recipe.candidateProbability), recipe.target);
  }
});

test('the source builder runs in the restricted evaluator with no helper closure', () => {
  const state = observation();
  assert.deepEqual(decidePolicy(gardenPolicySource(seedOnly), state, [], null), decideGardenAction(state, {}, seedOnly));
});

test('new mature seeds are harvested and immature rare plants are preserved', () => {
  const state = observation({ known: ['bakerWheat', 'queenbeet'] });
  state.garden.plot[1][1] = ['queenbeetLump', 84];
  state.garden.plot[0][0] = ['queenbeet', 80];
  let decision = decideGardenAction(state, {}, seedOnly);
  assert.deepEqual(decision.action, { type: 'garden-harvest', x: 0, y: 0 });
  state.garden.plot[0][0] = [null, 0];
  decision = decideGardenAction(state, {}, seedOnly);
  assert.equal(decision.status, 'waiting');
  state.garden.plot[1][1][1] = 85;
  decision = decideGardenAction(state, {}, seedOnly);
  assert.deepEqual(decision.action, { type: 'garden-harvest', x: 1, y: 1 });
});

test('novel growth retains helpful elderwort and buys only affordable support for slow plants', () => {
  const state = observation({ known: ['bakerWheat', 'elderwort', 'nursetulip', 'queenbeet'] });
  state.garden.plot[1][1] = ['queenbeetLump', 0];
  state.garden.plot[0][0] = ['elderwort', 90];
  state.garden.plot[0][1] = ['nursetulip', 60];
  let decision = decideGardenAction(state, {}, seedOnly);
  assert.deepEqual(decision.action, { type: 'garden-harvest', x: 1, y: 0 });
  state.garden.plot[0][1] = [null, 0];
  decision = decideGardenAction(state, {}, seedOnly);
  assert.equal(decision.action.type, 'garden-plant');
  assert.equal(decision.action.seed, 'elderwort');
  assert.notDeepEqual([decision.action.x, decision.action.y], [0, 0]);
  state.cookies = 999; // The optional 10-cookie support exceeds 1% of bank.
  decision = decideGardenAction(state, {}, seedOnly);
  assert.equal(decision.status, 'waiting');
  assert.equal(decision.requiredCookies, undefined);
  state.cookies = 1e100;
  state.garden.plot[1][1][1] = 84; // Do not buy support when maturation is close.
  assert.equal(decideGardenAction(state, {}, seedOnly).status, 'waiting');
  decision = decideGardenAction(state, {}, { ...seedOnly, boostNovelGrowth: false });
  assert.deepEqual(decision.action, { type: 'garden-harvest', x: 0, y: 0 });
  state.garden.plot[1][1][1] = 0;
  state.garden.plot[1][0] = ['glovemorel', 79];
  decision = decideGardenAction(state, {}, seedOnly);
  assert.deepEqual(decision.action, { type: 'garden-harvest', x: 0, y: 0 });
  state.garden.plot[0][0] = [null, 0];
  decision = decideGardenAction(state, {}, seedOnly);
  if (decision.action.type === 'garden-plant') assert(decision.action.x > 1);
});

test('native elderwort growth is independent of JQB attenuation and Nursetulip power', { skip }, () => {
  const runtime = nativeGarden();
  const M = runtime.Game.Objects.Farm.minigame;
  // Funded isolated fixture: the target already exists, but support plants are
  // bought through native inputs chosen from the public observation.
  M.unlockSeed(M.plants.elderwort);
  M.plot[1][1] = [M.plants.queenbeetLump.id + 1, 0];
  let memory = {};
  let supportCount = 0;
  for (let i = 0; i < 12; i++) {
    const decision = decideGardenAction(runtime.snapshot(), memory, seedOnly);
    memory = decision.memory;
    if (decision.action.type === 'wait') break;
    if (decision.action.type === 'garden-plant') {
      assert.equal(decision.action.seed, 'elderwort'); supportCount++;
    }
    runtime.act(decision.action);
  }
  assert.equal(supportCount, 8);
  assert.equal(M.soilsById[M.soil].key, 'fertilizer');
  M.computeBoostPlot();
  assert(Math.abs(M.plotBoost[1][1][0] - 1.00225 ** 8) < 1e-14);
  for (const row of M.plot) for (const tile of row) {
    if (tile[0] === M.plants.elderwort.id + 1) tile[1] = 90;
  }
  M.computeBoostPlot();
  const ageBoost = M.plotBoost[1][1][0];
  assert(Math.abs(ageBoost - 1.0225 ** 8) < 1e-14);
  M.plot[1][1][1] = 80;
  M.plot[1][3] = [M.plants.nursetulip.id + 1, 60];
  M.computeBoostPlot();
  assert.equal(M.plotBoost[1][1][0], ageBoost);
  assert(M.plotBoost[1][2][1] !== 1); // The power channel did change.
});

test('native rounding gives a coupled maturation improvement for all supported slow crops', { skip }, () => {
  const runtime = nativeGarden();
  const M = runtime.Game.Objects.Farm.minigame;
  const random = runtime.context.Math.random;
  const boost = 1.0225 ** 8;
  try {
    // These draws are a controlled kernel fixture, not an admissible policy.
    // Pair the age and rounding uniforms for the two compared plants.
    for (const key of ['queenbeetLump', 'drowsyfern', 'everdaisy', 'duketater']) {
      const p = M.plants[key];
      let ordinary = 0, supported = 0, ordinaryTick, supportedTick;
      for (let tick = 1; tick <= 5000 && !ordinaryTick; tick++) {
        const ageUniform = (tick * 73 % 997) / 997;
        const roundUniform = (tick * 227 % 991) / 991;
        runtime.context.Math.random = () => roundUniform;
        const base = p.ageTick + p.ageTickR * ageUniform;
        const ordinaryStep = runtime.context.randomFloor(base);
        const supportedStep = runtime.context.randomFloor(base * boost);
        assert(supportedStep >= ordinaryStep);
        ordinary += ordinaryStep; supported += supportedStep;
        if (ordinary >= p.mature) ordinaryTick = tick;
        if (supported >= p.mature && !supportedTick) supportedTick = tick;
      }
      assert(ordinaryTick && supportedTick && supportedTick < ordinaryTick, key);
      // Even the largest soil, aura and eight-elderwort multiplier cannot make
      // these crops skip the mature harvest window on one native age step.
      assert(Math.ceil((p.ageTick + p.ageTickR) * 1.0375 ** 8 * 1.055) < 100 - p.mature, key);
    }
  } finally {
    runtime.context.Math.random = random;
  }
});

test('the full plot supports four exact eight-parent juicy-queenbeet rings', () => {
  const state = observation({ known: ['bakerWheat', 'queenbeet'] });
  let memory = { target: 'queenbeetLump' };
  const planted = [];
  for (let i = 0; i < 32; i++) {
    const decision = decideGardenAction(state, memory, seedOnly);
    assert.equal(decision.action.type, 'garden-plant');
    assert.equal(decision.action.seed, 'queenbeet');
    const { x, y } = decision.action;
    planted.push([x, y]); state.garden.plot[y][x] = ['queenbeet', 0]; memory = decision.memory;
  }
  assert.equal(new Set(planted.map(x => x.join(','))).size, 32);
  for (const [x, y] of [[1, 1], [4, 1], [1, 4], [4, 4]]) {
    assert.equal(state.garden.plot[y][x][0], null);
    let neighbors = 0;
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      if ((dx || dy) && state.garden.plot[y + dy][x + dx][0] === 'queenbeet') neighbors++;
    }
    assert.equal(neighbors, 8);
  }
});

test('slow parents start first, and immature duketaters can produce shriekbulbs', () => {
  const state = observation({ known: ['bakerWheat', 'cronerice', 'shimmerlily'] });
  const decision = decideGardenAction(state, { target: 'elderwort' }, seedOnly);
  assert.equal(decision.action.type, 'garden-plant');
  assert.equal(decision.action.seed, 'cronerice');
  const shriek = observation({ known: ['bakerWheat', 'duketater'], level: 1 });
  let memory = { target: 'shriekbulb' };
  for (let i = 0; i < 3; i++) {
    const next = decideGardenAction(shriek, memory, seedOnly);
    assert.equal(next.action.seed, 'duketater');
    shriek.garden.plot[next.action.y][next.action.x] = ['duketater', 0]; memory = next.memory;
  }
  assert.equal(decideGardenAction(shriek, memory, seedOnly).action.type, 'garden-soil');
});

test('a lost queenbeet causes its established ring to restart instead of drifting out of phase', () => {
  const state = observation({ known: ['bakerWheat', 'queenbeet'] });
  for (let y = 0; y < 3; y++) for (let x = 0; x < 3; x++) {
    if (x !== 1 || y !== 1) state.garden.plot[y][x] = ['queenbeet', 90];
  }
  state.garden.plot[0][0] = [null, 0];
  const decision = decideGardenAction(state, { target: 'queenbeetLump', beds: { '1,1': 'established' } }, seedOnly);
  assert.equal(decision.action.type, 'garden-harvest');
  assert.equal(decision.memory.beds['1,1'], 'clearing');
});

test('insufficient plot size and unaffordable planting are explicit resource conditions', () => {
  const state = observation({ known: ['bakerWheat', 'queenbeet'], level: 1 });
  let decision = decideGardenAction(state, { target: 'queenbeetLump' }, seedOnly);
  assert.equal(decision.status, 'needs-level');
  assert.equal(decision.action, null);
  state.garden.level = 9; state.cookies = 0;
  decision = decideGardenAction(state, { target: 'queenbeetLump' }, seedOnly);
  assert.equal(decision.status, 'needs-resources');
  assert.equal(decision.requiredCookies, 10);
});

test('completion requires sacrifice and a rebuilt log, not a one-time seed count', () => {
  const state = observation({ known: seeds.map(x => x.key) });
  let decision = decideGardenAction(state, {}, seedOnly);
  assert.equal(decision.action.type, 'garden-sacrifice');
  state.controls.promptOn = true;
  decision = decideGardenAction(state, decision.memory, seedOnly);
  assert.deepEqual(decision.action, { type: 'prompt', option: 0 });
  state.controls.promptOn = false; state.garden.seedless = true; state.garden.convertTimes = 1;
  for (const p of Object.values(state.garden.plants)) p.unlocked = p.key === 'bakerWheat';
  assert.notEqual(decideGardenAction(state, decision.memory, seedOnly).status, 'complete');
  for (const p of Object.values(state.garden.plants)) p.unlocked = true;
  assert.equal(decideGardenAction(state, {}, seedOnly).status, 'complete');
});

test('Ichor syrup farming spaces ichorpuffs to avoid multiplying their growth penalties', () => {
  const state = observation({ known: seeds.map(x => x.key), seedless: true });
  state.achievements['In the garden of Eden (baby)'] = true;
  let memory = {};
  const cells = [];
  for (let i = 0; i < 9; i++) {
    const decision = decideGardenAction(state, memory, { harvestTarget: 0 });
    assert.equal(decision.action.seed, 'ichorpuff');
    const { x, y } = decision.action; cells.push([x, y]);
    state.garden.plot[y][x] = ['ichorpuff', 0]; memory = decision.memory;
  }
  for (const a of cells) for (const b of cells) {
    if (a !== b) assert(Math.abs(a[0] - b[0]) > 1 || Math.abs(a[1] - b[1]) > 1);
  }
  assert.equal(decideGardenAction(state, memory, { harvestTarget: 0 }).status, 'waiting');
});

test('the controller finishes seeds, sacrifice, rebuilding, drops, and Garden achievements in the native Garden kernel', { skip, timeout: 120000 }, () => {
  const runtime = nativeGarden();
  const M = runtime.Game.Objects.Farm.minigame;
  let memory = {};
  let completed = false;
  // This advances only the Garden's native clocked kernel, with a funded Farm.
  // It verifies the breeding controller, not a legal full-game new-save trace.
  for (let decisionCount = 0; decisionCount < 60000; decisionCount++) {
    const observation = gardenKernelObservation(runtime);
    if (decisionCount % 1000 === 0) assert.deepEqual(observation, projectGardenObservation(runtime.snapshot()));
    const decision = decideGardenAction(observation, memory, { maxWaitMs: 1e9 });
    memory = decision.memory;
    if (decision.status === 'complete') { completed = true; break; }
    assert(decision.action, `${decision.status}: ${decision.reason}`);
    if (decision.action.type === 'wait') {
      runtime.clock.now = Math.max(runtime.clock.now + 1, M.nextStep + 1);
      M.logic();
    } else runtime.act(decision.action);
  }
  assert.equal(completed, true);
  assert.equal(M.plantsUnlockedN, 34);
  assert.equal(M.convertTimes, 1);
  assert.equal(runtime.Game.Achievements['Seedless to nay'].won, 1);
  assert.equal(runtime.Game.Achievements['In the garden of Eden (baby)'].won, 1);
  assert.equal(runtime.Game.Achievements['Green, aching thumb'].won, 1);
  for (const { upgrade } of GARDEN_DROP_CROPS) assert.equal(runtime.Game.Upgrades[upgrade].unlocked, 1, upgrade);
});

test('final cookie-count farming preserves mature frequency crops, reserves planting cost, and stops at the normal count goal', () => {
  const state = observation({ known: seeds.map(x => x.key), seedless: true });
  const options = { ...seedOnly, naturalCookieFarm: true };
  let d = decideGardenAction(state, {}, options);
  assert.deepEqual(d.action, { type: 'garden-soil', soil: 'clay' });
  state.garden.soil = 'clay'; state.cookies = 9;
  d = decideGardenAction(state, d.memory, options);
  assert.equal(d.status, 'needs-resources'); assert.equal(d.requiredCookies, 10);
  assert.equal(d.seed, 'nursetulip'); assert.equal(d.goal, "Black cat's paw");
  state.cookies = 1e100;
  for (let i = 0; i < 36; i++) {
    d = decideGardenAction(state, d.memory, options);
    assert.equal(d.action.type, 'garden-plant');
    const { x, y, seed } = d.action;
    state.garden.plot[y][x] = [seed, state.garden.plants[seed].mature];
  }
  d = decideGardenAction(state, d.memory, options);
  assert.equal(d.action.type, 'wait'); // Mature flowers stay in place.
  assert.deepEqual(decidePolicy(gardenPolicySource(options), state, [], d.memory),
    decideGardenAction(state, d.memory, options));
  state.achievements["Black cat's paw"] = true;
  assert.equal(decideGardenAction(state, d.memory, options).status, 'complete');
  state.achievements["Black cat's paw"] = false;
  assert.equal(decideGardenAction(state, {}, seedOnly).status, 'complete');
});

test('cookie-count crop renews a native dead golden clover without clearing mature Nursetulips', { skip }, () => {
  const r = nativeGarden(), M = r.Game.Objects.Farm.minigame;
  for (const p of M.plantsById) M.unlockSeed(p);
  r.Game.Win('Seedless to nay'); M.convertTimes = 1;
  const options = { ...seedOnly, naturalCookieFarm: true };
  let memory = {}, planted = 0;
  for (let i = 0; i < 40; i++) {
    const d = decideGardenAction(r.snapshot(), memory, options); memory = d.memory;
    if (d.action.type === 'wait') break;
    if (d.action.type === 'garden-plant') planted++;
    r.act(d.action);
  }
  assert.equal(planted, 36); assert.equal(M.soilsById[M.soil].key, 'clay');
  let target;
  for (let y = 0; y < 6; y++) for (let x = 0; x < 6; x++) {
    const tile = M.plot[y][x], p = M.plantsById[tile[0] - 1];
    tile[1] = p.mature;
    if (!target && p.key === 'goldenClover') target = { x, y };
  }
  M.plot[target.y][target.x][1] = 99;
  r.clock.now = Math.max(r.clock.now + 1, M.nextStep + 1); M.logic();
  assert.equal(M.plot[target.y][target.x][0], 0);
  const d = decideGardenAction(r.snapshot(), memory, options);
  assert.deepEqual(d.action, { type: 'garden-plant', seed: 'goldenClover', ...target });
  r.act(d.action);
  assert.equal(M.plot[target.y][target.x][0], M.plants.goldenClover.id + 1);
  assert.equal(M.plantsUnlockedN, 34); assert.equal(M.convertTimes, 1);
});
