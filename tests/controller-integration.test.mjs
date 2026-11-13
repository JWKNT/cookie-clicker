import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { completionPolicySource } from '../model/completion-policy.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { decideComboAction } from '../model/combo-policy.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip=!hasGameSource()&&'Pinned Steam source is unavailable';
const interfaceGoals=["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press'];
const miscGoals=['Cookie-dunker','Just wrong','Early bird','Fading luck','Thick-skinned','No time like the present'];
const idleSeason={seasons:[],research:false,fortunes:false,dragonDrops:false,wrinklers:false,helperGrandma:false,eldeer:false,reindeerTarget:0};
function prepared(except=[]) {
  const r=createRuntime();r.advance(1000);
  // Synthetic already-completed side goals isolate controller arbitration.
  for(const name of [...interfaceGoals,...miscGoals,'Neverclick','Hardcore'])if(!except.includes(name))r.Game.Win(name);
  return r;
}
function next(r,source,memory) {
  const result=decidePolicy(source,r.snapshot(),[],memory);
  r.act(result.action);return result;
}

function finishResetMilestones(r) {
  const G=r.Game;
  G.resets=100;
  for(const u of Object.values(G.Upgrades))if(u.pool==='prestige'){u.bought=1;u.unlocked=1;}
  for(const name of ['Rebirth','Resurrection','Reincarnation','All the stars in heaven','No more room in hell','Debt evasion',
    'And a little extra',"Speed's the name of the game (no it's not it's called Cookie Clicker)","What's not clicking"])G.Win(name);
}

test('season renewal requests an ordinary reset and preserves the explicit reset restriction', {skip}, () => {
  const r=prepared();finishResetMilestones(r);
  r.Game.season='';r.Game.seasonUses=12;
  const season={...idleSeason,seasons:['valentines']};
  const source=completionPolicySource({inputBatchMilliseconds:0,season});
  const d=decidePolicy(source,r.snapshot(),[],{restoreViewport:true});
  assert.equal(d.stage,'season-retry');assert.deepEqual(d.action,{type:'ascend'});
  const restricted=decidePolicy(completionPolicySource({inputBatchMilliseconds:0,season,ascension:{allowReset:false}}),
    r.snapshot(),[],{restoreViewport:true});
  assert.notEqual(restricted.action.type,'ascend');
  r.act(d.action);assert(r.Game.AscendTimer>0);
});

test('final market collection waits for reset, seasonal and spell-count goals', {skip}, () => {
  const r=prepared();finishResetMilestones(r);
  const G=r.Game;
  for(const b of Object.values(G.Objects)){b.amount=700;b.highest=700;}
  G.Objects.Cursor.amount=2000;G.Objects.Cursor.level=12;G.Objects.Bank.level=1;
  r.evaluate(r.source.sources['minigameMarket.js'],'minigameMarket.js');
  const M=G.Objects.Bank.minigame;M.launch();G.Objects.Bank.minigameLoaded=true;G.Objects.Bank.switchMinigame(true);M.officeLevel=2;
  G.cookies=G.cookiesEarned=1e60;r.advance(1000);
  // Pet the dragon is available, but the dragon drops remain missing. The
  // ordinary reset goals alone must not release reset-sensitive investments.
  const source=completionPolicySource({inputBatchMilliseconds:0,season:{...idleSeason,dragonDrops:true},ascension:{allowReset:false}});
  let d=decidePolicy(source,r.snapshot(),[],{restoreViewport:true});
  assert.equal(d.memory.market.config.collectTrades,false);
  assert.equal(d.memory.production.config.finalCollection,false);
  assert.notEqual(d.action.type,'market-office');
  const ready=completionPolicySource({inputBatchMilliseconds:0,season:idleSeason,ascension:{allowReset:false}});
  d=decidePolicy(ready,r.snapshot(),[],{restoreViewport:true});
  assert.equal(d.memory.market.config.collectTrades,false);
  assert.equal(d.memory.production.config.finalCollection,false);
  // Supply the last phase's native achievement in this arbitration fixture.
  G.Win('A wizard is you');
  d=decidePolicy(ready,r.snapshot(),[],{restoreViewport:true});
  assert.equal(d.memory.market.config.collectTrades,true);
  assert.equal(d.action.type,'market-office');
});

test('composed native ascent buys Legacy, reincarnates, and clears prior-run control ownership', {skip}, () => {
  const r=prepared();r.Game.cookies=r.Game.cookiesEarned=2e12;
  const source=completionPolicySource({inputBatchMilliseconds:0,season:idleSeason,ascension:{allowReset:true,earlyCountResets:false}});
  let memory={restoreViewport:true,run:0,season:{fixture:'old run'},garden:{fixture:'old run'},market:{fixture:'old run'}};
  const kinds=[];
  for(let i=0;i<100;i++) {
    const decision=next(r,source,memory);memory=decision.memory;kinds.push(decision.action.type);
    if(r.Game.resets===1&&!r.Game.OnAscend&&!r.Game.AscendTimer&&!r.Game.ReincarnateTimer)break;
  }
  assert(kinds.includes('ascend'));assert(kinds.includes('key'));assert(kinds.includes('buy-upgrade'));assert(kinds.includes('reincarnate'));
  assert.equal(r.Game.Has('Legacy'),1);assert.equal(r.Game.resets,1);assert.equal(r.Game.OnAscend,0);
  const decision=decidePolicy(source,r.snapshot(),[],memory);
  assert.equal(decision.memory.run,1);
  assert.notEqual(decision.memory.season?.fixture,'old run');
  assert.notEqual(decision.memory.garden?.fixture,'old run');
});

test('misc Fading luck ownership prevents seasonal and growth clicks until the last second', {skip}, () => {
  const r=prepared(['Fading luck']);
  // Synthetic natural-cookie age boundary; pop and award callbacks remain native.
  r.evaluate("var heldGolden=new Game.shimmer('golden');heldGolden.spawnLead=1;heldGolden.life=Game.fps*3;");
  const id=r.context.heldGolden.id;
  const source=completionPolicySource({inputBatchMilliseconds:0,season:idleSeason,ascension:{allowReset:false}});
  let memory={restoreViewport:true};let clicked=false;
  for(let i=0;i<200;i++) {
    const before=r.Game.shimmers.find(s=>s.id===id);
    const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
    if(d.action.type==='click-shimmer'&&d.action.id===id){assert(before.life<r.Game.fps);assert.equal(d.stage,'misc');clicked=true;}
    r.act(d.action);
    if(clicked)break;
  }
  assert(clicked);assert.equal(r.Game.HasAchiev('Fading luck'),1);
});

test('a seasonal reindeer hold survives the growth fallback and ends on observed Elder frenzy', {skip}, () => {
  const r=prepared();r.evaluate("var heldReindeer=new Game.shimmer('reindeer');heldReindeer.spawnLead=1;");
  const id=r.context.heldReindeer.id;
  const source=completionPolicySource({inputBatchMilliseconds:0,clickRate:0,season:{...idleSeason,eldeer:true},ascension:{allowReset:false}});
  let memory={restoreViewport:true};
  for(let i=0;i<10;i++) {
    const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
    assert.notEqual(d.action.type,'click-shimmer');r.act(d.action);
  }
  assert(r.Game.shimmers.some(s=>s.id===id));
  // Synthetic observed buff boundary; scheduling its occurrence is not established here.
  r.Game.gainBuff('blood frenzy',6,666);
  const d=decidePolicy(source,r.snapshot(),[],memory);
  assert.deepEqual(d.action,{type:'click-shimmer',id});assert.equal(d.stage,'season');
  r.act(d.action);assert.equal(r.Game.HasAchiev('Eldeer'),1);
});

test('composed self-gift flow closes its own code prompt without consuming a stale prompt', {skip}, () => {
  const r=prepared(['No time like the present']);r.Game.cookies=2e9;r.Game.Upgrades['Wrapping paper'].earn();
  const source=completionPolicySource({inputBatchMilliseconds:0,season:idleSeason,ascension:{allowReset:false}});
  let d=next(r,source,{restoreViewport:true});
  assert.equal(d.action.type,'gift-send');assert.equal(r.Game.promptOn,1);assert(d.memory.misc.giftPending);
  d=next(r,source,d.memory);assert.equal(d.action.type,'close-prompt');assert(d.memory.misc.giftCode);
  assert.equal(r.Game.promptOn,0);
  // A changed run must invalidate prompt ownership from an earlier controller step.
  r.Game.Prompt('Unrelated next-run prompt',['Close']);
  const stale=decidePolicy(source,r.snapshot(),[],{restoreViewport:true,run:-1,misc:{giftPending:true},season:{confirm:{name:'One mind',elapsedMs:r.snapshot().elapsedMs}}});
  assert.equal(stale.stage,'unowned-prompt');assert.equal(stale.action.type,'wait');
  assert.equal(stale.memory.misc?.giftPending,undefined);
});

test('held Grandma pointer is released before the composed scheduler can ascend', {skip}, () => {
  const r=prepared();r.Game.cookies=r.Game.cookiesEarned=2e12;
  r.Game.Objects.Grandma.amount=1;
  r.act({type:'building-press',id:1,release:false});assert.equal(r.Game.mouseDown,1);
  const source=completionPolicySource({inputBatchMilliseconds:0,season:idleSeason,ascension:{allowReset:true}});
  const d=decidePolicy(source,r.snapshot(),[],{restoreViewport:true,season:{helperReleaseAt:r.snapshot().wallTimeMs}});
  assert.deepEqual(d.action,{type:'building-press',id:1,release:true});
  r.act(d.action);assert.equal(r.Game.mouseDown,0);assert.equal(r.Game.AscendTimer,0);
});

test('composed resource requests buy the final office cursor and warehouse building before growth', {skip}, () => {
  const r=prepared();
  // Synthetic market access and prior goals isolate the two resource handoffs.
  for(const b of Object.values(r.Game.Objects)){b.amount=10;b.highest=10;}
  r.Game.Objects.Cursor.amount=99;r.Game.Objects.Cursor.level=12;r.Game.Objects.Bank.level=1;
  r.evaluate(r.source.sources['minigameMarket.js'],'minigameMarket.js');
  const M=r.Game.Objects.Bank.minigame;M.launch();r.Game.Objects.Bank.minigameLoaded=true;r.Game.Objects.Bank.switchMinigame(true);
  r.Game.cookies=r.Game.cookiesEarned=1e100;r.advance(1000);
  for(const name of ['Initial public offering','Rookie numbers','No nobility in poverty','Full warehouses','Make my day','Buy buy buy','Pyramid scheme','Liquid assets'])r.Game.Win(name);
  const source=completionPolicySource({inputBatchMilliseconds:0,season:idleSeason,ascension:{allowReset:false},market:{brokerTarget:0,collectTrades:true}});
  let d=next(r,source,{restoreViewport:true});
  assert.equal(d.stage,'required-building');assert.deepEqual(d.action,{type:'buy-building',id:0,amount:1});
  d=next(r,source,d.memory);assert.equal(d.action.type,'market-office');
  assert.equal(M.officeLevel,1);assert.equal(r.Game.Objects.Cursor.amount,0);

  M.officeLevel=5;r.Game.Achievements['Full warehouses'].won=0;
  for(const good of M.goodsById){good.building.amount=499;good.building.highest=499;good.building.level=0;}
  r.Game.Objects.Bank.amount=r.Game.Objects.Bank.highest=480;r.Game.Objects.Bank.level=1;
  d=next(r,source,d.memory);
  assert.equal(d.stage,'required-building');assert.deepEqual(d.action,{type:'buy-building',id:2,amount:1});
  assert.equal(M.getGoodMaxStock(M.goodsById[0]),1000);
  d=next(r,source,d.memory);assert.equal(d.action.type,'market-buy');
  assert.equal(r.Game.HasAchiev('Full warehouses'),1);
});

test('an otherwise ready ascent cannot interrupt a native Godzamok sale and buyback', {skip}, () => {
  const r=prepared();const G=r.Game;
  // Synthetic funded combo opportunity, not a completing new-save run.
  G.cookies=G.cookiesEarned=2e12;G.Objects.Mine.amount=G.Objects.Mine.highest=11;G.Objects.Mine.locked=false;
  G.Objects.Mine.l.classList.remove('toggledOff');
  G.Objects.Temple.amount=1;G.Objects.Temple.level=1;
  r.evaluate(r.source.sources['minigamePantheon.js'],'minigamePantheon.js');
  const M=G.Objects.Temple.minigame;M.launch();G.Objects.Temple.minigameLoaded=true;M.slotGod(M.gods.ruin,0);
  G.gainBuff('click frenzy',20,1e12);G.CalculateGains();
  const config={configurePantheon:false,configureAuras:false,castHandOfFate:false};
  const sale=decideComboAction(r.snapshot(),{},config);
  assert.equal(sale.action.type,'sell-building');assert.equal(sale.action.id,3);
  const amount=G.Objects.Mine.amount;r.act(sale.action);assert(G.Objects.Mine.amount<amount);
  const source=completionPolicySource({inputBatchMilliseconds:0,season:idleSeason,combo:config,ascension:{allowReset:true,earlyCountResets:false}});
  let d=next(r,source,{restoreViewport:true,combo:sale.memory});
  assert.equal(d.stage,'combo-transaction');assert.equal(d.action.type,'buy-building');
  assert.equal(G.Objects.Mine.amount,amount);assert.equal(G.AscendTimer,0);
  for(let i=0;i<3&&d.action.type!=='ascend';i++)d=next(r,source,d.memory);
  assert.equal(d.action.type,'ascend');
});

test('an otherwise ready ascent waits for owned aura confirmation and native sacrifice replacement', {skip}, () => {
  const r=prepared();const G=r.Game;
  // Synthetic unlocked dragon and funded replacement; all inputs remain native.
  G.cookies=G.cookiesEarned=2e12;G.Objects.Mine.amount=G.Objects.Mine.highest=1;G.Objects.Mine.locked=false;
  G.Objects.Mine.l.classList.remove('toggledOff');
  G.Upgrades['A crumbly egg'].earn();G.dragonLevel=G.dragonLevels.length-1;G.CalculateGains();
  const config={clickRate:0,configurePantheon:false,castHandOfFate:false,godzamok:false};
  const aura=decideComboAction(r.snapshot(),{},config);
  assert.equal(aura.action.type,'dragon-aura');r.act(aura.action);assert.equal(G.promptOn,1);
  const source=completionPolicySource({inputBatchMilliseconds:0,clickRate:0,season:idleSeason,combo:config,ascension:{allowReset:true,earlyCountResets:false}});
  let d=next(r,source,{restoreViewport:true,combo:aura.memory});
  assert.equal(d.stage,'combo-transaction');assert.equal(d.action.type,'prompt');
  assert.equal(G.Objects.Mine.amount,0);assert.equal(G.AscendTimer,0);
  d=next(r,source,d.memory);assert.equal(d.stage,'combo-transaction');assert.equal(d.action.type,'buy-building');
  assert.equal(G.Objects.Mine.amount,1);assert.equal(G.AscendTimer,0);assert.equal(G.dragonAura,G.dragonAurasBN['Radiant Appetite'].id);
  d=next(r,source,d.memory);assert.equal(d.action.type,'ascend');
});
