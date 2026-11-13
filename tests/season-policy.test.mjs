import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { decideSeasonAction, seasonPolicySource, RESEARCH_UPGRADES, DRAGON_DROPS } from '../model/season-policy.mjs';

const skip = !hasGameSource() && 'Pinned Steam source is unavailable';
const base = { preserveChallengeAchievements: false, seasons: [], research: false, fortunes: false, dragonDrops: false, wrinklers: false, helperGrandma: false, eldeer: false, reindeerTarget: 0 };
function funded(seed = 1) {
  const r = createRuntime({ randomSeed: seed });
  // Synthetic funded fixture. Neither the bank nor these unlocks are policy actions.
  r.evaluate(`Game.cookies=1e100;Game.cookiesEarned=1e100;
    Game.Upgrades['Season switcher'].earn();Game.Upgrades['Persistent memory'].earn();
    Game.Objects.Grandma.amount=100;Game.Objects.Grandma.highest=100;
    Game.Objects.Grandma.redraw();Game.recalculateGains=1;`);
  r.advance(1000);
  return r;
}
function step(r, memory, config) {
  const d = decideSeasonAction(r.snapshot(), memory, config);
  if (d.action) r.act(d.action);
  return d;
}

test('season source executes with only public JSON observations and agrees with the direct controller', { skip }, () => {
  const r=funded(); const o=r.snapshot(); const options={...base,seasons:['valentines']};
  const direct=decideSeasonAction(o,{},options);
  const sandboxed=decidePolicy(seasonPolicySource(options),o,[],{});
  assert.deepEqual(sandboxed,direct);
  assert.equal(direct.action.type,'buy-upgrade');
  assert.equal(r.Game.UpgradesById[direct.action.id].name,'Lovesick biscuit');
});

test('native Valentine chain, all Santa forms and gifts, and the helper grandma click complete', { skip }, () => {
  const r=funded(); const config={...base,seasons:['valentines','christmas'],helperGrandma:true};
  let m={};let completed=false;
  for(let i=0;i<2000;i++) {
    const d=step(r,m,config);m=d.memory;
    // Synthetic opportunities only. Drops and purchases use unmodified handlers.
    if(d.action?.type==='wait' && r.Game.season==='christmas') r.evaluate("var testReindeer=new Game.shimmer('reindeer');testReindeer.spawnLead=1;");
    if(d.status==='needs-resources' && d.building==='Grandma') {
      r.act({type:'buy-building',id:1,amount:1});r.advance(100);
    }
    if(d.status==='complete'){completed=true;break;}
    assert(d.action || d.building==='Grandma',d.reason);
  }
  assert(completed,'The supplied native opportunity budget did not complete Christmas collection.');
  r.advance(1000);
  for(const name of [...r.Game.heartDrops,...r.Game.santaDrops,...r.Game.reindeerDrops,"Santa's dominion"]) assert.equal(r.Game.Has(name),1,name);
  assert.equal(r.Game.santaLevel,14);
  assert.equal(r.Game.HasAchiev("Baby it's old outside"),1);
  assert.equal(r.Game.mouseDown,0);
  assert.equal(r.Game.HasAchiev('Lovely cookies'),1);
});

test('native research confirmation, timer unlocks and rapid covenant pledge cycles complete', { skip }, () => {
  const r=funded();r.Game.Upgrades['Bingo center/Research facility'].unlock();
  const config={...base,research:true};let m={};let confirmed=false;
  for(let i=0;i<200;i++) {
    const d=step(r,m,config);m=d.memory;
    if(d.action?.type==='prompt')confirmed=true;
    // Each research deadline is a synthetic boundary fixture, not a time-speedup action.
    if(d.action?.type==='wait' && r.Game.researchT>0) {r.Game.researchT=1;r.advance(40);}
    if(d.status==='complete')break;
    assert(d.action,d.reason);
  }
  r.advance(1000);
  assert(confirmed);
  for(const name of RESEARCH_UPGRADES)assert.equal(r.Game.Has(name),1,name);
  assert.equal(r.Game.pledges,10);
  assert.equal(r.Game.Has('Sacrificial rolling pins'),1);
  assert.equal(r.Game.Has('Elder Covenant'),0);
  assert.equal(r.Game.HasAchiev('Elder calm'),1);
  assert.equal(r.Game.HasAchiev('Elder slumber'),1);
});

test('unrelated prompts and changed research confirmation are never accepted', { skip }, () => {
  const r=funded();r.Game.Prompt('Unrelated',['Yes','No']);
  assert.equal(decideSeasonAction(r.snapshot(),{},base).status,'blocked');
  assert.equal(decideSeasonAction(r.snapshot(),{confirm:{name:'One mind',elapsedMs:-1}},base).status,'blocked');
});

test('helper collection waits for drawing, reveals more indices, and requests a run retry at its display limit', { skip }, () => {
  const r=funded();const config={...base,seasons:['christmas'],helperGrandma:true};
  // Synthetic completed Christmas inventory isolates the remaining helper goal.
  r.act({type:'buy-upgrade',id:r.Game.Upgrades['Festive biscuit'].id});
  for(const name of ['A festive hat',...r.Game.santaDrops,...r.Game.reindeerDrops,"Santa's dominion"])r.Game.Upgrades[name].earn();
  r.Game.santaLevel=14;r.Game.Objects.Grandma.amount=1;r.Game.Objects.Grandma.redraw();
  const pending=decideSeasonAction(r.snapshot(),{},config);
  assert.equal(pending.action.type,'wait');assert.equal(pending.building,undefined);
  r.act(pending.action);assert.equal(r.snapshot().seasonal.grandmaDisplay.drawn,1);
  // Explicit no-helper display fixture; no reroll or seed inspection is a policy action.
  r.Game.Objects.Grandma.amount=500;r.advance(100);
  for(const sprite of r.Game.Objects.Grandma.pics)sprite.pic='grandma.png';
  const full=decideSeasonAction(r.snapshot(),{},config);
  assert.equal(full.status,'acting');assert.equal(full.goal,'Santa helper display');
  assert.equal(full.action.type,'resize');assert.equal(full.building,undefined);
  assert(full.action.width > r.snapshot().seasonal.grandmaDisplay.width);
  r.act(full.action);
  const pendingResize = decideSeasonAction(r.snapshot(), full.memory, config);
  assert.equal(pendingResize.action.type, 'wait');
  r.act(pendingResize.action);
  assert(r.snapshot().seasonal.grandmaDisplay.width > full.memory.helperResizePending.previousWidth);
  // At the terminal viewport, an explicitly empty helper set requests a reset.
  const exhausted = r.snapshot();
  exhausted.viewport = { width: 16384, height: 900 };
  exhausted.seasonal.helperGrandmas = [];
  exhausted.progression.buildingAmounts.Grandma = exhausted.seasonal.grandmaDisplay.capacity;
  exhausted.seasonal.grandmaDisplay.drawn = exhausted.seasonal.grandmaDisplay.capacity;
  const retry = decideSeasonAction(exhausted, full.memory, config);
  assert.equal(retry.status, 'needs-ascension');
  assert.equal(retry.retryReason, 'helper-display-exhausted');
  assert.equal(retry.action, null);
  r.evaluate("var helperTestReindeer=new Game.shimmer('reindeer');helperTestReindeer.spawnLead=1;");
  const reward=decideSeasonAction(r.snapshot(),{},config);
  assert.deepEqual(reward.action,{type:'click-shimmer',id:r.context.helperTestReindeer.id});
});

test('season renewal has a bounded use count and permits finishing an already active season', { skip }, () => {
  const r = funded();
  r.Game.season = ''; r.Game.seasonUses = 12;
  const config = { ...base, seasons: ['valentines'] };
  const retry = decideSeasonAction(r.snapshot(), {}, config);
  assert.equal(retry.status, 'needs-ascension');
  assert.equal(retry.retryReason, 'season-switch-limit');
  assert.equal(retry.requiresOrdinaryReset, true);
  assert.equal(retry.action, null);
  r.Game.season = 'valentines';
  assert.notEqual(decideSeasonAction(r.snapshot(), {}, config).status, 'needs-ascension');
  assert.equal(decideSeasonAction(r.snapshot(), {}, { ...config, maxSeasonUses: 0 }).status, 'blocked');
});

test('a cached elf in a muted display is unmuted before native pointer input', { skip }, () => {
  const r = funded();
  r.act({ type: 'buy-upgrade', id: r.Game.Upgrades['Festive biscuit'].id });
  for (const name of ['A festive hat', ...r.Game.santaDrops, ...r.Game.reindeerDrops, "Santa's dominion"]) r.Game.Upgrades[name].earn();
  r.Game.santaLevel = 14;
  r.advance(100);
  assert(r.snapshot().seasonal.helperGrandmas.length > 0);
  r.Game.prefs.extraButtons = 1;
  r.act({ type: 'building-mute', id: 1, muted: true });
  const config = { ...base, seasons: ['christmas'], helperGrandma: true };
  assert.deepEqual(decideSeasonAction(r.snapshot(), {}, config).action,
    { type: 'building-mute', id: 1, muted: false });
  r.Game.prefs.extraButtons = 0;
  let memory = {}, actions = [];
  for (let i = 0; i < 20 && !r.Game.HasAchiev("Baby it's old outside"); i++) {
    const d = decideSeasonAction(r.snapshot(), memory, config); memory = d.memory;
    assert(d.action, d.reason); actions.push(d.action); r.act(d.action);
  }
  // Enabling the native extra-buttons preference also unmutes buildings.
  assert.deepEqual(actions.slice(0, 2), [
    { type: 'preference', name: 'extraButtons' },
    { type: 'open-menu', menu: '' },
  ]);
  assert.equal(actions[2].type, 'building-hover');
  assert.equal(r.Game.HasAchiev("Baby it's old outside"), 1);
});

test('a concrete native run seed gives a clickable helper for every Grandma-synergy count', { skip }, () => {
  const r = funded();
  // Diagnostic witness only. The policy neither reads nor sets the run seed.
  // Ordinary native reincarnation generates one from five fresh letter draws.
  const grandma = r.Game.Objects.Grandma;
  r.Game.seed = 'aaaao'; r.Game.season = 'christmas'; grandma.amount = 1;
  const synergies = Array.from(r.Game.GrandmaSynergies);
  assert.equal(synergies.length, 18);
  for (let count = 0; count <= synergies.length; count++) {
    synergies.forEach((name, index) => { r.Game.Upgrades[name].bought = Number(index < count); });
    grandma.redraw(); grandma.draw();
    assert.equal(grandma.pics[0].pic, 'elfGrandma.png', `List size ${count + 2}`);
  }
  const sprite = grandma.pics[0];
  r.act({ type: 'building-hover', id: 1, x: sprite.x + 32, y: sprite.y + 32 });
  r.act({ type: 'building-press', id: 1, release: false });
  r.advance(100);
  r.act({ type: 'building-press', id: 1, release: true });
  assert.equal(r.Game.HasAchiev("Baby it's old outside"), 1);
});

test('five explicit 53-bit input blocks generate the favorable helper seed with mass at least2^-25', { skip }, () => {
  const r = createRuntime();
  const size = 2n ** 53n, blockSize = 2n ** 48n;
  const block = letter => {
    const centerCeil = (BigInt(2 * letter + 1) * size + 51n) / 52n;
    const first = centerCeil - blockSize / 2n;
    return { first, last: first + blockSize - 1n };
  };
  // Floating multiplication by positive26 is monotone. Both endpoints remain
  // strictly inside one floor bucket, so every intervening grid value does too.
  for (let letter = 0; letter < 26; letter++) {
    const { first, last } = block(letter);
    assert(first >= 0n && last < size);
    assert.equal(Math.floor(Number(first) / Number(size) * 26), letter);
    assert.equal(Math.floor(Number(last) / Number(size) * 26), letter);
  }
  const original = r.context.Math.random;
  try {
    for (const endpoint of ['first', 'last']) {
      const letters = [...'aaaao'].map(letter => letter.charCodeAt(0) - 97);
      let draw = 0;
      r.context.Math.random = () => Number(block(letters[draw++])[endpoint]) / Number(size);
      assert.equal(r.Game.makeSeed(), 'aaaao');
      assert.equal(draw, 5);
    }
  } finally { r.context.Math.random = original; }
  assert.equal(size ** 5n / blockSize ** 5n, 2n ** 25n);
});

test('all Halloween and Easter drops are collected through native wrinkler and shimmer callbacks', { skip, timeout:120000 }, t => {
  const r=funded(7);
  r.evaluate(`Game.Upgrades['One mind'].earn();Game.Upgrades['Communal brainsweep'].earn();Game.Upgrades['Elder Pact'].earn();Game.elderWrath=3;`);
  const config={...base,seasons:['halloween','easter']};let m={};let completed=false;let opportunities=0;
  for(let i=0;i<15000;i++) {
    if(r.Game.season==='easter'&&r.Game.GetHowManyEggs()<20&&!r.Game.shimmers.some(s=>s.type==='golden')){r.evaluate("new Game.shimmer('golden');");opportunities++;}
    const d=step(r,m,config);m=d.memory;
    if(d.status==='complete'){completed=true;break;}
    assert(d.action,`${d.status}: ${d.reason}`);
    if(d.action.type==='wait') {
      // Synthetic event supply, not a claim about natural waiting time or new-save reachability.
      // Native pop callbacks use the ordinary seeded sample stream for every drop.
      if(!r.Game.wrinklers.some(w=>w.phase>0)) {
        r.evaluate('Game.SpawnWrinkler(Game.wrinklers[0]);Game.wrinklers[0].phase=2;Game.wrinklers[0].close=1;Game.wrinklers[0].sucked=1;');
      }
      opportunities++;
    }
  }
  assert(completed,`${r.Game.season}: ${r.Game.GetHowManyHalloweenDrops()} Halloween; ${r.Game.GetHowManyEggs()} eggs`);
  r.advance(5000);
  for(const name of [...r.Game.halloweenDrops,...r.Game.easterEggs])assert.equal(r.Game.Has(name),1,name);
  assert.equal(r.Game.HasAchiev('Spooky cookies'),1);
  assert.equal(r.Game.HasAchiev('Hide & seek champion'),1);
  t.diagnostic(`${opportunities} supplied native event opportunities; no random draw was exposed to the policy.`);
});

test('native wrinkler recovery permits fifty safe pokes and two hundred pops', { skip, timeout:120000 }, t => {
  const r=funded(91);r.evaluate(`Game.Upgrades['One mind'].earn();Game.elderWrath=1;`);
  let m={};let completed=false;let supplied=0;
  const config={...base,wrinklers:true};
  for(let i=0;i<12000;i++) {
    if(!r.Game.wrinklers.some(w=>w.phase>0)) {
      // Synthetic spawn fixture; subsequent pointer input, health recovery and payouts are native.
      r.evaluate('Game.SpawnWrinkler(Game.wrinklers[0]);Game.wrinklers[0].phase=2;Game.wrinklers[0].close=1;Game.wrinklers[0].sucked=1;');supplied++;
    }
    const d=step(r,m,config);m=d.memory;
    if(d.status==='complete'){completed=true;break;}
    assert(d.action,`${d.status}: ${d.reason}`);
  }
  assert(completed,`pops=${r.Game.wrinklersPopped}`);
  r.advance(1000);
  for(const name of ['Wrinkler poker','Itchscratcher','Wrinklesquisher','Moistburster'])assert.equal(r.Game.HasAchiev(name),1,name);
  t.diagnostic(`${supplied} synthetic spawns; ${r.Game.wrinklersPopped} native payouts.`);
});

test('all four dragon drops use observed pet results and actual quarter-hour progression', { skip, timeout:120000 }, t => {
  const r=funded(4);r.evaluate(`Game.Upgrades['Pet the dragon'].earn();Game.Upgrades['A crumbly egg'].earn();Game.dragonLevel=8;`);
  let m={};let completed=false;let pets=0;
  const config={...base,dragonDrops:true,maxWaitMs:900000};
  for(let i=0;i<1000;i++) {
    const d=step(r,m,config);m=d.memory;
    if(d.action?.type==='pet-dragon')pets++;
    if(d.status==='complete'){completed=true;break;}
    assert(d.action,`${d.status}: ${d.reason}`);
  }
  assert(completed,`owned ${DRAGON_DROPS.filter(name=>r.Game.Has(name)).join(', ')}`);
  for(const name of DRAGON_DROPS)assert.equal(r.Game.Has(name),1,name);
  t.diagnostic(`${pets} native pets across ${(r.snapshot().elapsedMs/60000).toFixed(2)} simulated minutes.`);
});

test('fresh dragon drop retries use the same timestamp, while unknown partial ownership advances time', { skip }, () => {
  const r = funded(4);
  r.evaluate("Game.Upgrades['Pet the dragon'].earn();Game.Upgrades['A crumbly egg'].earn();Game.dragonLevel=8;");
  const config = { ...base, dragonDrops: true };
  const start = r.snapshot().wallTimeMs;
  let memory = {}, pets = 0;
  for (let i = 0; i < 1000 && !DRAGON_DROPS.some(name => r.Game.Has(name)); i++) {
    const d = decideSeasonAction(r.snapshot(), memory, config); memory = d.memory;
    assert(['pet-dragon', 'buy-upgrade'].includes(d.action?.type), d.reason);
    if (d.action.type === 'pet-dragon') pets++;
    r.act(d.action);
  }
  assert(DRAGON_DROPS.some(name => r.Game.Has(name)));
  assert(pets > 0);
  assert.equal(r.snapshot().wallTimeMs, start);
  const learned = decideSeasonAction(r.snapshot(), memory, config);
  assert.equal(learned.action.type, 'wait');
  assert.equal(Object.keys(learned.memory.dragonQuarterDrops).length, 1);
  // Discarding policy memory simulates a retained permanent drop with no known
  // phase. A duplicate trial must be followed by a positive time advance.
  const cold = decideSeasonAction(r.snapshot(), {}, config);
  assert.equal(cold.action.type, 'pet-dragon'); r.act(cold.action);
  const next = decideSeasonAction(r.snapshot(), cold.memory, config);
  assert.equal(next.action.type, 'wait');
  assert(next.action.milliseconds > 0);
});

test('natural ticker selection and native clicks collect every fortune without seed inspection', { skip, timeout:120000 }, t => {
  const r=funded(31);r.evaluate(`Game.Upgrades['Fortune cookies'].earn();Game.T=Game.fps*11;`);
  let m={};let completed=false;let opportunities=0;
  const config={...base,fortunes:true};
  for(let i=0;i<10000;i++) {
    const d=decideSeasonAction(r.snapshot(),m,config);m=d.memory;
    if(d.status==='complete'){completed=true;break;}
    assert(d.action,`${d.status}: ${d.reason}`);
    if(d.action.type==='wait') {
      // Supply a native automatic ticker opportunity; this omits its waiting interval.
      r.Game.getNewTicker();opportunities++;
      if(r.Game.Tiers.fortune.upgrades.every(u=>u.bought))r.advance(5000);
    } else r.act(d.action);
  }
  assert(completed);
  r.advance(1000);
  for(const u of r.Game.Tiers.fortune.upgrades)assert.equal(r.Game.Has(u.name),1,u.name);
  assert.equal(r.Game.HasAchiev('O Fortuna'),1);
  t.diagnostic(`${opportunities} automatic ticker opportunities.`);
});

test('reindeer are held for Eldeer, then native clicks and drop rolls reach 200', { skip, timeout:120000 }, t => {
  const r=funded(6);const config={...base,seasons:['christmas'],reindeerTarget:200,eldeer:true};
  let m={};let completed=false;let supplied=0;let held=false;
  for(let i=0;i<2000;i++) {
    const d=step(r,m,config);m=d.memory;
    if(d.status==='complete'){completed=true;break;}
    assert(d.action,d.reason);
    if(d.action.type==='wait') {
      if(!r.Game.shimmers.some(s=>s.type==='reindeer')) {
        // Fixture supplies a native reindeer opportunity; the policy never selects its drops.
        r.evaluate("var testReindeer=new Game.shimmer('reindeer');testReindeer.spawnLead=1;");supplied++;
      } else if(!r.Game.HasAchiev('Eldeer')) {
        held=true;
        // Synthetic observed buff boundary. No claim that this test establishes its waiting time.
        r.Game.gainBuff('blood frenzy',6,666);
      }
    }
  }
  assert(held);assert(completed);
  assert(r.Game.reindeerClicked>=200);assert.equal(r.Game.HasAchiev('Eldeer'),1);
  assert.equal(r.Game.HasAchiev('Reindeer sleigher'),1);
  for(const name of r.Game.reindeerDrops)assert.equal(r.Game.Has(name),1,name);
  t.diagnostic(`${supplied} supplied reindeer opportunities.`);
});

test('default collection preserves Hardcore and resumes wrinklers through native covenant revocation', { skip }, () => {
  const fresh=createRuntime();
  const protectedDecision=decideSeasonAction(fresh.snapshot());
  assert.equal(protectedDecision.status,'needs-achievement');assert.equal(protectedDecision.goal,'Hardcore');
  assert.equal(protectedDecision.action,null);
  const r=funded();r.evaluate(`Game.Upgrades['One mind'].earn();Game.Upgrades['Elder Pact'].earn();
    Game.Upgrades['Elder Covenant'].unlock();Game.Upgrades['Elder Covenant'].buy();`);
  const decision=decideSeasonAction(r.snapshot(),{}, {...base,wrinklers:true});
  assert.equal(r.Game.UpgradesById[decision.action.id].name,'Revoke Elder Covenant');
  r.act(decision.action);assert.equal(r.Game.Has('Elder Covenant'),0);
});

test('the final natural-cookie crop keeps its paid Covenant after wrath and pledge goals finish', { skip }, () => {
  const r = funded();
  for (const name of RESEARCH_UPGRADES) r.Game.Upgrades[name].earn();
  for (const name of ['Grandmapocalypse', 'Elder nap', 'Elder slumber', 'Elder calm']) r.Game.Win(name);
  r.Game.pledges = 10; r.Game.Upgrades['Sacrificial rolling pins'].earn();
  r.Game.Unlock('Elder Covenant');
  const options = { ...base, research: true, suppressWrathForCookieCount: true };
  let d = decideSeasonAction(r.snapshot(), {}, options);
  assert.equal(d.action.type, 'buy-upgrade');
  assert.equal(r.Game.UpgradesById[d.action.id].name, 'Elder Covenant');
  r.act(d.action); assert.equal(r.Game.Has('Elder Covenant'), 1);
  d = decideSeasonAction(r.snapshot(), d.memory, options);
  assert.equal(d.status, 'complete'); assert.equal(d.action, null);
  assert.equal(r.Game.Has('Elder Covenant'), 1);
  // The cookie-count phase must not suppress still-required wrinkler rewards.
  d = decideSeasonAction(r.snapshot(), {}, { ...options, wrinklers: true });
  assert.equal(r.Game.UpgradesById[d.action.id].name, 'Revoke Elder Covenant');
  r.act(d.action); assert.equal(r.Game.Has('Elder Covenant'), 0);
  r.Game.Win("Black cat's paw");
  assert.equal(decideSeasonAction(r.snapshot(), {}, options).status, 'complete');
});
