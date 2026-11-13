import test from 'node:test';
import assert from 'node:assert/strict';
import { completionPolicySource } from '../model/completion-policy.mjs';
import { evaluatePolicy } from '../model/evaluate-policy.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { readFileSync } from 'node:fs';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
const interfaceGoals = ["What's in a name", 'Tiny cookie', 'Here you go', 'Olden days', 'Tabloid addiction', 'Stifling the press'];
function pastInterface(runtime) {
  for (const name of [...interfaceGoals, 'Cookie-dunker', 'Just wrong', 'Hardcore', 'Neverclick']) runtime.Game.Win(name);
  return { restoreViewport: true, growth: { nextClick: 100, nextPurchase: 0 } };
}

test('composed candidate gains native interface achievements and preserves the Neverclick limit', { skip }, () => {
  const result = evaluatePolicy(completionPolicySource(), { horizonMs: 2000 });
  assert.equal(result.status, 'censored', result.error);
  for (const name of ["What's in a name", 'Tiny cookie', 'Here you go', 'Olden days', 'Tabloid addiction', 'Stifling the press']) {
    assert.equal(result.observation.achievements[name], true, name);
  }
  assert.equal(result.observation.cookieClicks, 15);
  assert(result.observation.progression.buildingAmounts.Cursor >= 1);
  assert.equal(Object.values(result.observation.upgrades).filter(u => u.bought).length, 0);
  assert.equal(result.completion.complete, false);
});

test('candidate reserves native planting costs while leaving the observations unchanged', { skip }, () => {
  const r = createRuntime();
  // Funded fixture only; this is not a reachable new-save trace.
  r.Game.cookies = 1e6;
  pastInterface(r);
  r.evaluate(r.source.sources['minigameGarden.js'], 'minigameGarden.js');
  const farm = r.Game.Objects.Farm;
  farm.level = 9; farm.amount = 300; farm.highest = 300;
  farm.minigame.launch(); farm.minigameLoaded = true;
  r.Game.cookiesPs = 1000;
  const state = r.snapshot();
  // A known mutation chain requests wheat while funds are below its native cost.
  state.garden.plants.meddleweed.unlocked = true;
  state.garden.plants.brownMold.unlocked = true;
  state.garden.plants.crumbspore.unlocked = true;
  state.garden.soil = 'fertilizer';
  state.cookies = state.garden.plants.bakerWheat.cost - 1;
  const before = structuredClone(state);
  const decision = decidePolicy(completionPolicySource({ascension:{earlyCountResets:false}}), state, [], {
    restoreViewport: true, garden: { target: 'thumbcorn' }, growth: { nextClick: 100, nextPurchase: 0 },
  });
  assert(!['buy-building', 'buy-upgrade'].includes(decision.action.type));
  assert.deepEqual(state, before);
});

test('Hardcore protection still blocks affordable upgrades at a large bank until the native award is visible', { skip }, () => {
  const r = createRuntime();
  for (const name of [...interfaceGoals, 'Cookie-dunker', 'Just wrong', 'Neverclick']) r.Game.Win(name);
  const upgrade = r.Game.Upgrades['Reinforced index finger'];
  upgrade.unlocked = 1;
  r.Game.cookies = 1e12;
  const memory = { restoreViewport: true, growth: { nextClick: 100, nextPurchase: 0 } };
  const source = completionPolicySource();
  const protectedDecision = decidePolicy(source, r.snapshot(), [], memory);
  assert.notEqual(protectedDecision.action.type, 'buy-upgrade');
  assert.equal(r.Game.UpgradesOwned, 0);
  r.Game.cookiesEarned = 1e9;
  r.Game.T = 149;
  r.advance(67);
  assert.equal(r.Game.Achievements.Hardcore.won, 1);
  const next = decidePolicy(source, r.snapshot(), [], memory);
  assert.deepEqual(next.action, { type: 'buy-upgrade', id: upgrade.id });
});

test('the first Grandma keeps producing until the no-upgrade challenge is finished', {skip}, () => {
  const r=createRuntime();const memory=pastInterface(r);
  r.Game.Achievements['Just wrong'].won=0;r.Game.Achievements.Hardcore.won=0;
  r.Game.Objects.Grandma.amount=r.Game.Objects.Grandma.highest=1;
  const source=completionPolicySource();
  let d=decidePolicy(source,r.snapshot(),[],memory);
  assert.notEqual(d.action.type,'sell-building');
  r.Game.Win('Hardcore');
  d=decidePolicy(source,r.snapshot(),[],d.memory);
  assert.equal(d.stage,'early-income-growth');assert.notEqual(d.action.type,'sell-building');
  r.Game.resets=100; // Explicit downstream-phase fixture, not a claimed route.
  d=decidePolicy(source,r.snapshot(),[],d.memory);
  assert.equal(d.stage,'misc');assert.deepEqual(d.action,{type:'sell-building',id:1,amount:1});
  r.act(d.action);assert.equal(r.Game.HasAchiev('Just wrong'),1);
});

test('the composed controller confirms the One mind prompt that its own purchase opened', { skip }, () => {
  const r = createRuntime();
  r.Game.Objects.Temple.level=1; // Explicit post-first-lump gate fixture.
  let memory = pastInterface(r);
  const upgrade = r.Game.Upgrades['One mind'];
  upgrade.unlocked = 1;
  r.Game.cookies = 10 * upgrade.getPrice();
  const source = completionPolicySource();
  let decision = decidePolicy(source, r.snapshot(), [], memory);
  assert.deepEqual(decision.action, { type: 'buy-upgrade', id: upgrade.id });
  r.act(decision.action); memory = decision.memory;
  assert.equal(r.Game.promptOn, 1);
  assert.equal(upgrade.bought, 0);
  decision = decidePolicy(source, r.snapshot(), [], memory);
  assert.deepEqual(decision.action, { type: 'prompt', option: 0 });
  r.act(decision.action);
  assert.equal(upgrade.bought, 1);
  assert.equal(r.Game.promptOn, 0);
});

test('the composed controller leaves unrelated or stale prompts unconfirmed', { skip }, () => {
  const r = createRuntime();
  const memory = pastInterface(r);
  r.Game.Prompt('<h3>Unrelated fixture prompt</h3>', ['Close']);
  const source = completionPolicySource();
  let decision = decidePolicy(source, r.snapshot(), [], memory);
  assert.equal(decision.stage, 'unowned-prompt');
  assert.equal(decision.action.type, 'wait');
  r.Game.Upgrades['One mind'].unlocked = 1;
  decision = decidePolicy(source, r.snapshot(), [], { ...memory, confirmOneMind: { elapsedMs: -1 } });
  assert.equal(decision.stage, 'unowned-prompt');
  assert.equal(decision.action.type, 'wait');
  assert.equal(r.Game.Upgrades['One mind'].bought, 0);
});

test('an exhausted subsystem decision budget stops the experiment rather than silently falling back', { skip }, () => {
  const r = createRuntime();
  const memory = pastInterface(r);
  assert.throws(() => decidePolicy(completionPolicySource({ market: { maxDecisions: 1 }, ascension:{earlyCountResets:false} }), r.snapshot(), [], {
    ...memory, market: { decisions: 1 },
  }), /Stock Market controller decision budget exhausted/);
});

test('a native zero-gain Debt evasion reset discards all run-scoped controller memory', { skip }, () => {
  const r = createRuntime();
  const oldMemory = pastInterface(r);
  // Funded milestone fixture: a loan is accessible but the current run has
  // earned no extra prestige. Native reset/reincarnation must still execute.
  r.Game.resets = 100;
  r.Game.cookiesReset = 1e30;
  r.Game.prestige = Math.floor(r.Game.HowMuchPrestige(r.Game.cookiesReset));
  r.Game.cookies = 1e6; r.Game.cookiesEarned = 0;
  for (const u of Object.values(r.Game.Upgrades)) if (u.pool === 'prestige') { u.bought = 1; u.unlocked = 1; }
  for (const name of ['Rebirth', 'Resurrection', 'Reincarnation', 'All the stars in heaven', 'No more room in hell']) r.Game.Win(name);
  r.evaluate(r.source.sources['minigameMarket.js'], 'minigameMarket.js');
  const bank = r.Game.Objects.Bank;
  bank.level = 1; bank.amount = 1; bank.highest = 1;
  bank.minigame.launch(); bank.minigameLoaded = true; bank.minigame.officeLevel = 2;
  bank.switchMinigame(true); r.Game.drawT = 10; bank.minigame.draw();
  assert.equal(r.snapshot().ascension.gainedIfAscend, 0);
  let memory = { ...oldMemory, run: 100, nextHelperBuilding: 1e12 };
  for (const key of ['garden', 'market', 'season', 'misc', 'production', 'combo', 'helperSetup']) memory[key] = { marker: 'previous run' };
  memory.growth.marker = 'previous run';
  const source = completionPolicySource({ helperSetup:false, combo: { castHandOfFate: false } });
  let sawTransition = false, loan = false, cleared = false;
  for (let i = 0; i < 500; i++) {
    const observation = r.snapshot();
    const inTransition = observation.progression.onAscend || observation.progression.ascendTimer || observation.progression.reincarnateTimer;
    const d = decidePolicy(source, observation, [], memory);
    memory = d.memory;
    if (sawTransition && !inTransition) {
      for (const key of ['garden', 'market', 'season', 'growth', 'misc', 'production', 'combo', 'helperSetup']) assert.equal(memory[key]?.marker, undefined, key);
      assert.equal(memory.nextHelperBuilding, undefined);
      cleared = true; break;
    }
    if (d.action.type === 'market-loan') loan = true;
    if (inTransition) sawTransition = true;
    r.act(d.action);
  }
  assert(loan && sawTransition && cleared);
  assert.equal(r.Game.resets, 100); // The zero-gain reset does not increase this counter.
  assert.equal(r.Game.HasAchiev('Debt evasion'), 1);
  assert.equal(bank.minigame.officeLevel, 0);
});

test('a pending planting reserve excludes a cookie-losing Conjure backfire', { skip }, () => {
  const r = createRuntime();
  const memory = pastInterface(r);
  for (const name of ['Farm', 'Wizard tower']) {
    const file = name === 'Farm' ? 'minigameGarden.js' : 'minigameGrimoire.js';
    r.evaluate(r.source.sources[file], file);
    const building = r.Game.Objects[name];
    building.level = name === 'Farm' ? 9 : 1;
    building.amount = name === 'Farm' ? 300 : 2;
    building.highest = building.amount;
    building.minigame.launch(); building.minigameLoaded = true;
  }
  const G = r.Game.Objects.Farm.minigame;
  for (const key of ['meddleweed', 'brownMold', 'crumbspore']) G.plants[key].unlocked = true;
  G.soil = G.soils.fertilizer.id;
  r.Game.cookiesPs = 1000;
  r.Game.cookies = G.getCost(G.plants.bakerWheat) - 1;
  const M = r.Game.Objects['Wizard tower'].minigame;
  M.computeMagicM(); M.magic = M.magicM;
  const decision = decidePolicy(completionPolicySource({combo:{castHandOfFate:false},ascension:{earlyCountResets:false}}), r.snapshot(), [], {
    ...memory, garden: { target: 'thumbcorn' },
  });
  assert.equal(decision.action.type, 'cast-spell');
  assert.notEqual(decision.action.spell, 'conjure baked goods');
  const bank = r.Game.cookies;
  r.act(decision.action);
  assert.equal(r.Game.cookies, bank);
  assert.equal(M.spellsCastTotal, 1);
});

test('the downstream collection controller attempts Hand-picked at maturity and later harvests at ripe', { skip }, () => {
  const r = createRuntime();
  const memory = pastInterface(r);
  const state = r.snapshot();
  state.lump = { available: true, ageMs: 600, matureAge: 600, ripeAge: 900, overripeAge: 1200 };
  const source = completionPolicySource({ascension:{earlyCountResets:false}});
  assert.equal(decidePolicy(source, state, [], memory).action.type, 'harvest-lump');
  state.achievements['Hand-picked'] = true;
  assert.notEqual(decidePolicy(source, state, [], memory).action.type, 'harvest-lump');
  state.lump.ageMs = 900;
  assert.equal(decidePolicy(source, state, [], memory).action.type, 'harvest-lump');
  state.lump.ageMs = 1200;
  assert.notEqual(decidePolicy(source, state, [], memory).action.type, 'harvest-lump');
});

test('every allowed spell consumes magic and advances its counter on both native outcomes', { skip }, () => {
  const r = createRuntime();
  r.evaluate(r.source.sources['minigameGrimoire.js'], 'minigameGrimoire.js');
  const tower = r.Game.Objects['Wizard tower'];
  tower.level = 1; tower.amount = 100; tower.highest = 100;
  tower.minigame.launch(); tower.minigameLoaded = true;
  const M = tower.minigame;
  M.computeMagicM();
  const keys = ['conjure baked goods', 'hand of fate', "haggler's charm", 'summon crafty pixies', 'diminish ineptitude'];
  // Forced win/fail probabilities are test fixtures, never policy capabilities.
  for (const key of keys) for (const failChanceSet of [0, 1]) {
    M.magic = M.magicM;
    const cost = M.getSpellCost(M.spells[key]);
    const casts = M.spellsCastTotal;
    assert.equal(M.castSpell(M.spells[key], { failChanceSet }), true, `${key}: ${failChanceSet}`);
    assert.equal(M.spellsCastTotal, casts + 1);
    assert.equal(M.magic, M.magicM - cost);
  }
  r.Game.killBuffs();
  M.magic = M.magicM;
  const casts = M.spellsCastTotal;
  assert.equal(M.castSpell(M.spells['stretch time'], { failChanceSet: 0 }), false);
  assert.equal(M.magic, M.magicM);
  assert.equal(M.spellsCastTotal, casts);
});

test('the last milk receives a Farm level only when the required flags still leave the normal count at 599', { skip }, () => {
  const r=createRuntime(); const memory=pastInterface(r);
  const contract=JSON.parse(readFileSync(new URL('../model/completion-requirements.json',import.meta.url)));
  // Synthetic final-goal boundary. This fixture does not assert reachability.
  for(const {name} of contract.requiredAchievements) r.Game.Achievements[name].won=1;
  r.Game.Achievements['Freaky jazz hands'].won=1;
  for(const {building,level} of contract.buildingLevels) r.Game.Objects[building].level=level;
  r.Game.Objects.Farm.level=9;r.Game.Objects.Farm.amount=300;
  r.Game.Objects.Cursor.level=12;r.Game.lumps=10;r.Game.cookiesEarned=1e9;
  const before=r.snapshot();
  assert.equal(contract.normalAchievements.filter(({name})=>before.achievements[name]).length,599);
  const source=completionPolicySource({ascension:{allowReset:false,earlyCountResets:false}});
  let decision=decidePolicy(source,before,[],memory);
  assert.equal(decision.stage,'milk-unlock');
  assert.deepEqual(decision.action,{type:'level-building',id:2});
  r.act(decision.action);
  assert.equal(r.Game.Objects.Farm.level,10);assert.equal(r.Game.lumps,0);
  before.achievements['Sugar sugar']=true;
  decision=decidePolicy(source,before,[],memory);
  assert.notEqual(decision.stage,'milk-unlock');
});

test('remaining finite level costs request more Garden sacrifices after Seedless to nay', { skip }, () => {
  const r=createRuntime();const memory=pastInterface(r);
  r.evaluate(r.source.sources['minigameGarden.js'],'minigameGarden.js');
  const farm=r.Game.Objects.Farm;
  farm.level=3;farm.amount=300;farm.highest=300;farm.minigame.launch();farm.minigameLoaded=true;
  const G=farm.minigame;
  for(const plant of Object.values(G.plants)) plant.unlocked=1;
  G.plantsUnlockedN=G.plantsN;G.convertTimes=1;r.Game.Win('Seedless to nay');
  r.Game.lumps=0;
  const d=decidePolicy(completionPolicySource({ascension:{earlyCountResets:false}}),r.snapshot(),[],memory);
  assert.equal(d.action.type,'garden-sacrifice');
  // Farm3 has spent 6 of the 126 mandatory level lumps. Twelve additional
  // ten-lump sacrifices cover the remaining debt before natural harvests.
  assert.equal(d.memory.garden.config.sacrificesRequired,13);
  r.act(d.action);
  const confirm=decidePolicy(completionPolicySource({ascension:{earlyCountResets:false}}),r.snapshot(),[],d.memory);
  assert.deepEqual(confirm.action,{type:'prompt',option:0});r.act(confirm.action);
  assert.equal(r.Game.lumps,10);assert.equal(G.convertTimes,2);
});
