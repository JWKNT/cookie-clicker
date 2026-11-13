import test from 'node:test';
import assert from 'node:assert/strict';
import { decideComboAction, comboPolicySource, COMBO_IDENTITIES } from '../model/combo-policy.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
const skip = !hasGameSource() && 'Pinned Steam source unavailable';
const active = { configurePantheon: false, configureAuras: false, castHandOfFate: false, preserveChallengeAchievements: false };
function observation() {
  return { elapsedMs: 100, ascensions: 0, fps: 30, cookies: 1e9, cookiesPs: 1e6, cookiesPerClick: 1e6,
    achievements: { Hardcore: true, Neverclick: true }, upgrades: {}, buffs: {}, shimmers: [],
    progression: { onAscend: false, ascendTimer: 0, reincarnateTimer: 0, ascensionMode: 0, minigames: { Temple: true, 'Wizard tower': true } },
    controls: { promptOn: false, pantheon: { swaps: 0, slots: [2,6,8] }, grimoire: { magic: 50, magicMax: 50, spells: { 'hand of fate': { cost: 40 } } } },
    dragon: { level: 0, aura: 0, aura2: 0, auras: [] },
    shop: { buildings: [{ id: 3, name: 'Mine', amount: 20, locked: false, buy1price: 100,
      godzamokCycle: { amount: 19, rebuy: 1000, refund: 300, net: 700 } }] } };
}
function native() {
  const r = createRuntime(); const G = r.Game;
  for (const [name, amount] of [['Cursor',100],['Mine',20],['Temple',1],['Wizard tower',100]]) {
    G.Objects[name].amount=amount; G.Objects[name].bought=amount; G.Objects[name].highest=amount;
    G.Objects[name].locked=0;
    G.Objects[name].l.classList.remove('toggledOff');
  }
  G.BuildingsOwned = Object.values(G.Objects).reduce((n,b)=>n+b.amount,0);
  for (const [name, source] of [['Temple','minigamePantheon.js'],['Wizard tower','minigameGrimoire.js']]) {
    const b=G.Objects[name]; b.level=1;
    r.evaluate(r.source.sources[source],source); b.minigame.launch(); b.minigameLoaded=true;
  }
  G.cookies=G.cookiesEarned=1e30; G.prestige=1e12;
  G.Upgrades.Legacy.earn(); G.Upgrades['Heavenly key'].earn(); G.Upgrades['Plastic mouse'].earn();
  G.Achievements.Hardcore.won=1; G.Achievements.Neverclick.won=1;
  r.advance(100); G.cookies=1e12;
  return r;
}

test('combo source uses the same frozen public-input decision as the direct function', () => {
  const o=observation();
  assert.deepEqual(decidePolicy(comboPolicySource(active),o,[],null),decideComboAction(o,{},active));
  assert.equal(decideComboAction(o,{},active).optimalityCertified,false);
  assert.equal(decideComboAction(o,{}, {...active,clickRate:51}).status,'blocked');
  o.achievements.Hardcore=false;
  assert.equal(decideComboAction(o).status,'needs-achievement');
});

test('Godzamok uses complete pre-funded round trips, reserves them, and avoids protected buildings', () => {
  const o=observation();
  const sell=decideComboAction(o,{},active);
  assert.deepEqual(sell.action,{type:'sell-building',id:3,amount:19});
  assert.equal(sell.exclusive,true); assert.equal(sell.reserveCookies,1000);
  const after=structuredClone(o); after.shop.buildings[0].amount=1; after.cookies+=300;
  const buy=decideComboAction(after,sell.memory,active);
  assert.deepEqual(buy.action,{type:'buy-building',id:3,amount:19});
  const underfunded=structuredClone(o); underfunded.cookies=999;
  assert.notEqual(decideComboAction(underfunded,{}, {...active,maximumCycleBankShare:1}).action?.type,'sell-building');
  for(const name of ['Cursor','Grandma','Farm','Bank','Temple','Wizard tower','You']) {
    const protectedState=structuredClone(o); protectedState.shop.buildings[0].name=name;
    assert.notEqual(decideComboAction(protectedState,{},active).action?.type,'sell-building');
  }
  const short=structuredClone(o); short.buffs['Click frenzy']={time:1,multClick:777};
  assert.notEqual(decideComboAction(short,{},active).action?.type,'sell-building');
});

test('stale buybacks recheck current costs and remain exclusive instead of selling again', () => {
  const o=observation(); const first=decideComboAction(o,{},active);
  o.shop.buildings[0].amount=1; o.elapsedMs+=100; o.cookies=10;
  const next=decideComboAction(o,first.memory,active);
  assert.equal(next.status,'needs-resources'); assert.equal(next.exclusive,true); assert.equal(next.action,null);
  assert(next.requiredCookies>10);
  o.cookies=100;
  assert.deepEqual(decideComboAction(o,first.memory,active).action,{type:'buy-building',id:3,amount:1});
  o.ascensions=1;
  assert.equal(decideComboAction(o,first.memory,active).memory.rebuy,undefined,'A new run cannot inherit an old transaction');
});

test('unowned or stale aura prompts are never confirmed', () => {
  const o=observation(); o.controls.promptOn=true;
  assert.equal(decideComboAction(o,{},active).action,null);
  const memory={run:0,confirmAura:{time:o.elapsedMs-1,level:19,buildingId:3,beforeAmount:20}};
  const d=decideComboAction(o,memory,active);
  assert.equal(d.status,'blocked'); assert.equal(d.exclusive,true); assert.equal(d.action,null);
});

test('FtHoF uses observed buffs, respects held cookies, and reserves magic without future lookup', () => {
  const o=observation(); const opts={...active,castHandOfFate:true,godzamok:false,clickRate:0};
  assert.equal(decideComboAction(o,{},opts).action,null);
  o.buffs.Frenzy={time:300,multCpS:7};
  assert.deepEqual(decideComboAction(o,{},opts).action,{type:'cast-spell',spell:'hand of fate'});
  o.shimmers=[{id:8,type:'golden'}];
  assert.equal(decideComboAction(o,{}, {...opts,deferredShimmerIds:[8]}).action,null);
  assert.equal(decideComboAction(o,{},opts).action.type,'click-shimmer');
});

test('native Pantheon actions install the intended gods using only the available swaps', {skip}, () => {
  const r=native(); let memory={}; const opts={...active,configurePantheon:true,godzamok:false,clickRate:20};
  for(let i=0;i<3;i++) {
    const d=decideComboAction(r.snapshot(),memory,opts); memory=d.memory;
    assert.deepEqual(d.action,{type:'pantheon-slot',god:['ruin','labor','mother'][i],slot:i}); r.act(d.action);
  }
  assert.deepEqual(Array.from(r.Game.Objects.Temple.minigame.slot),[2,6,8]);
  assert.equal(r.Game.Objects.Temple.minigame.swaps,0);
});

test('a funded native Godzamok sale/rebuy restores holdings and raises observed click power', {skip}, () => {
  const r=native(); const G=r.Game; const P=G.Objects.Temple.minigame;
  r.act({type:'pantheon-slot',god:'ruin',slot:0}); G.CalculateGains(); G.cookies=1e12;
  const before=r.snapshot(); const source=comboPolicySource(active);
  const insufficient=structuredClone(before);
  insufficient.cookies=insufficient.shop.buildings[3].godzamokCycle.rebuy-1;
  assert.notEqual(decideComboAction(insufficient,{}, {...active,maximumCycleBankShare:1}).action?.type,'sell-building');
  const sell=decideComboAction(before,{},active);
  assert.deepEqual(decidePolicy(source,before,[],null),sell);
  assert.equal(sell.action.type,'sell-building');
  const b=G.ObjectsById[sell.action.id], amount=b.amount, q=before.shop.buildings[b.id].godzamokCycle;
  r.act(sell.action); assert.equal(b.amount,amount-q.amount);
  const buy=decideComboAction(r.snapshot(),sell.memory,active);
  assert.equal(buy.action.type,'buy-building'); r.act(buy.action);
  assert.equal(b.amount,amount); assert.equal(G.cookies,1e12+q.refund-q.rebuy);
  assert.equal(G.hasBuff('Devastation').multClick,1+q.amount*0.01);
  G.CalculateGains(); assert(G.computedMouseCps>before.cookiesPerClick);
  const after=decideComboAction(r.snapshot(),buy.memory,active);
  assert.notEqual(after.action?.type,'sell-building','Cycle spacing prevents zero-time churn');
  assert.equal(P.slot[0],COMBO_IDENTITIES.gods.ruin);
});

test('native aura selection owns its prompt and restores the sacrificed highest building', {skip}, () => {
  const r=native(); const G=r.Game; G.Upgrades['A crumbly egg'].earn(); G.dragonLevel=19;
  G.cookies=1e18;
  const opts={...active,configureAuras:true,godzamok:false,clickRate:0};
  const highest=[...Object.values(G.Objects)].reverse().find(b=>b.amount>0); const amount=highest.amount;
  const choose=decideComboAction(r.snapshot(),{},opts);
  assert.deepEqual(choose.action,{type:'dragon-aura',id:15,slot:0}); r.act(choose.action);
  assert(G.promptOn); assert.equal(G.dragonAura,0);
  const confirm=decideComboAction(r.snapshot(),choose.memory,opts);
  assert.deepEqual(confirm.action,{type:'prompt',option:0}); r.act(confirm.action);
  assert.equal(G.dragonAura,15); assert.equal(highest.amount,amount-1);
  const restore=decideComboAction(r.snapshot(),confirm.memory,opts);
  assert.deepEqual(restore.action,{type:'buy-building',id:highest.id,amount:1}); r.act(restore.action);
  assert.equal(highest.amount,amount);
});

test('native FtHoF spends magic and clicks its actual observed result without predicting it', {skip}, () => {
  const r=native(); const G=r.Game; const M=G.Objects['Wizard tower'].minigame;
  M.magic=M.magicM; G.gainBuff('frenzy',77,7); G.CalculateGains();
  const opts={...active,castHandOfFate:true,godzamok:false,clickRate:0};
  const beforeMagic=M.magic, beforeSpells=M.spellsCastTotal;
  const cast=decideComboAction(r.snapshot(),{},opts);
  assert.deepEqual(cast.action,{type:'cast-spell',spell:'hand of fate'}); r.act(cast.action);
  assert(M.magic<beforeMagic); assert.equal(M.spellsCastTotal,beforeSpells+1); assert.equal(G.shimmers.length,1);
  const pop=decideComboAction(r.snapshot(),cast.memory,opts);
  assert.deepEqual(pop.action,{type:'click-shimmer',id:G.shimmers[0].id}); r.act(pop.action);
  assert.equal(G.shimmers.length,0);
});
