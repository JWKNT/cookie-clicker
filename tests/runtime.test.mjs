import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, rmSync, writeFileSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { createRuntime, buildCatalogue, replayRuntime, ACTION_TYPES } from '../model/runtime.mjs';
import { hasGameSource, loadGameSource, SOURCE_HASHES } from '../model/game-source.mjs';
import { captureCompletionSnapshot } from '../model/completion.mjs';

const installed = hasGameSource();
const engineTest = (name, fn) => test(name, { skip: !installed && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory' }, fn);

test('Source reader rejects an altered engine before evaluation', () => {
  const dir = mkdtempSync(join(tmpdir(), 'cookie-model-hash-'));
  try {
    writeFileSync(join(dir, 'main.js'), 'throw new Error("should not run");');
    assert.throws(() => loadGameSource(dir), /SHA-256 mismatch for main.js/);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test('Every engine, locale and page source consumed by the adapter has a pinned hash', () => {
  assert.equal(Object.keys(SOURCE_HASHES).length, 8);
  for (const value of Object.values(SOURCE_HASHES)) assert.match(value, /^[a-f0-9]{64}$/);
});

engineTest('Pinned Steam engine starts a fresh isolated save and advances actual scheduled frames', () => {
  const r = createRuntime();
  const before = r.snapshot();
  assert.equal(before.cookies, 0);
  assert.equal(before.cookiesEarned, 0);
  assert.equal(before.edition, 'steam');
  assert.equal(Object.values(before.progression.buildingAmounts).reduce((a, b) => a + b, 0), 0);
  r.advance(1000);
  assert.equal(r.Game.T - before.frame, 30);
  assert.equal(r.Game.cookies, 0);
  assert.equal(r.Game.heralds, 100);
  assert.equal(r.Game.Upgrades['Web cookies'].pool, 'debug');
  assert.equal(r.Game.Upgrades['Steamed cookies'].pool, 'cookie');
  assert.equal(r.environment.timezone, 'UTC');
});

engineTest('native page startup retains the inline globe draw, launch greeting and filler-image initialization order', () => {
  const draws = [];
  const tape = Array(1000).fill(0.01);
  tape[1] = 0.7; tape[4] = 0.85;
  [0, 0.2, 0.4, 0.6, 0.8].forEach((value, i) => { tape[5 + i] = value; });
  tape[13] = 0.25;
  // Diagnostic stack capture identifies native draw callsites; it is not a
  // policy observation and supplies neither hidden state nor future samples.
  const randomTape = new Proxy(tape, { get(target, key, receiver) {
    if (/^\d+$/.test(String(key))) draws.push({ index: Number(key), stack: new Error().stack });
    return Reflect.get(target, key, receiver);
  } });
  const r = createRuntime({ randomTape });
  const document = r.context.document;
  assert.match(draws[0].stack, /main\.js:702:/); // Seedrandom entropy-pool initialization.
  assert.match(draws[1].stack, /index\.html:51:/); // Present even though the Steam top bar is hidden.
  assert.match(draws[2].stack, /Game\.Launch \(main\.js:1612:/);
  assert.match(draws[3].stack, /Game\.Launch \(main\.js:1684:/);
  assert.match(draws[4].stack, /launch \(main\.js:16870:/); // Native console greeting.
  for (let i = 5; i < 10; i++) assert.match(draws[i].stack, /Game\.makeSeed \(main\.js:2057:/);
  assert.match(draws[12].stack, /Game\.Init \(main\.js:4758:/);
  assert.match(draws[12].stack, /Loader\.onLoad \(main\.js:842:/);
  assert.match(draws[13].stack, /Game\.Init \(main\.js:5191:/);
  assert.equal(document.getElementById('tinyglobe').style.backgroundPosition, '-594px');
  assert.match(document.getElementById('versionNumber').textContent, /2\.053/);
  assert.equal(r.Game.seed, 'afkpu');
  assert.equal(r.Game.shimmersN, 2500);
  assert.equal(r.Game.Loader.assetsLoaded[0], 'filler.png');
  assert.equal(r.Game.Loader.doneLoading, 1);
  assert.equal(r.Game.Loader.loadingN, 0);
  assert.deepEqual(document.head.getElementsByTagName('script').map(el => el.src), ['loc/EN.js?v=2.053', 'loc/EN.js?v=2.053']);
  assert.equal(r.context.localStorage.getItem('CookieClickerLang'), 'EN');
  assert.equal(r.Game.T, 1);
  assert.equal(r.snapshot().elapsedMs, 0);
  assert.equal(r.auditCounts().randomDrawCount, 21);
  // The old manual Launch/Init path used 19 draws on this branch: it omitted
  // the globe and greeting, placing Game.makeSeed at indices 3..7, not 5..9.
  assert.equal(Array.from(r.timers.values()).some(timer => timer.due <= r.clock.now), false);
  r.context.onload(); // Native ready guard must not initialize twice.
  assert.equal(r.auditCounts().randomDrawCount, 21);
  assert.equal(r.Game.T, 1);
  r.advance(1000);
  assert.equal(r.Game.T, 31);
  assert.deepEqual(replayRuntime(r.events, { randomTape: r.consumedRandom }).snapshot(), r.snapshot());
});

engineTest('Actual click throttle, purchase cost and passive production use engine transitions', () => {
  const r = createRuntime(); r.act({ type: 'wait', milliseconds: 1000 });
  r.act({ type: 'click' }); const first = r.Game.cookies;
  r.act({ type: 'click' }); assert.equal(r.Game.cookies, first);
  for (let i = 0; i < 19; i++) { r.act({ type: 'wait', milliseconds: 50 }); r.act({ type: 'click' }); }
  assert.equal(r.Game.cookies, 20);
  r.act({ type: 'buy-building', id: 0, amount: 1 });
  assert.equal(r.Game.cookies, 5);
  r.act({ type: 'wait', milliseconds: 1000 });
  assert.equal(r.Game.Objects.Cursor.amount, 1);
  assert.equal(r.Game.cookiesPs, 0.1);
  assert.ok(Math.abs(r.Game.cookies - 5.1) < 1e-10);
});

engineTest('native cookie-pointer phases preserve target-before-document ordering, incidental sound draws and click throttle', () => {
  const r=createRuntime();r.advance(1000);const G=r.Game;const cookie=r.context.document.getElementById('bigCookie');
  if(!G.prefs.cookiesound)r.act({type:'preference',name:'cookiesound'});
  r.act({type:'open-menu',menu:''});
  const checkpoints=[];const note=type=>r.context.document.addEventListener(type,()=>checkpoints.push({type,state:G.BigCookieState,down:G.mouseDown,clicks:G.cookieClicks,click:G.Click,target:G.lastClickedEl?.id}));
  for(const type of ['mousedown','mouseup','click'])note(type);
  r.act({type:'cookie-pointer',phase:'enter'});
  assert.equal(G.BigCookieState,2);assert.equal(G.mouseX,G.cookieOriginX);assert.equal(G.mouseY,G.cookieOriginY);
  const draws=r.auditCounts().randomDrawCount;
  r.act({type:'cookie-pointer',phase:'down'});
  // Diagnostic counter only: the policy never receives this draw or its value.
  assert.equal(r.auditCounts().randomDrawCount,draws+1);
  assert.equal(G.BigCookieState,1);assert.equal(G.mouseDown,1);assert.equal(G.clickFrom,cookie);assert.equal(G.cookieClicks,0);
  r.act({type:'cookie-pointer',phase:'up'});assert.equal(G.BigCookieState,2);assert.equal(G.mouseDown,0);assert.equal(G.clickFrom,0);
  r.act({type:'cookie-pointer',phase:'click'});assert.equal(G.cookieClicks,1);assert.equal(G.Click,1);assert.equal(G.lastClickedEl,cookie);
  assert.deepEqual(checkpoints,[{type:'mousedown',state:1,down:1,clicks:0,click:0,target:undefined},
    {type:'mouseup',state:2,down:0,clicks:0,click:0,target:undefined},
    {type:'click',state:2,down:0,clicks:1,click:1,target:'bigCookie'}]);
  r.act({type:'cookie-pointer',phase:'click'});assert.equal(G.cookieClicks,1);
  r.advance(20);r.act({type:'cookie-pointer',phase:'click'});assert.equal(G.cookieClicks,2);
  r.act({type:'cookie-pointer',phase:'leave'});assert.equal(r.snapshot().controls.cookieState,0);
  assert.deepEqual(replayRuntime(r.events,{randomTape:r.consumedRandom}).snapshot(),r.snapshot());
});

engineTest('cookie-pointer input respects native propagation stops and prompt coverage while direct click retains its semantics', () => {
  const r=createRuntime();r.advance(1000);const G=r.Game;const cookie=r.context.document.getElementById('bigCookie');
  r.act({type:'click'});assert.equal(G.Click,0);assert.equal(G.BigCookieState,0);assert.equal(G.cookieClicks,1);
  r.advance(20);
  // Synthetic listener tests DOM propagation, not an admissible policy action.
  cookie.addEventListener('click',event=>event.stopPropagation());
  r.act({type:'cookie-pointer',phase:'click'});assert.equal(G.cookieClicks,2);assert.equal(G.Click,0);assert.equal(G.lastClickedEl,0);
  G.Prompt('Unrelated prompt',['Close']);
  assert.throws(()=>r.act({type:'cookie-pointer',phase:'down'}),/prompt covers/);
  r.act({type:'cookie-pointer',phase:'up'});r.act({type:'cookie-pointer',phase:'leave'});
  assert.throws(()=>r.act({type:'cookie-pointer',phase:'arbitrary'}),/unknown cookie pointer phase/);
});

engineTest('native tooltip entry, delayed leave and tooltip exit preserve visible text and replay', () => {
  const r=createRuntime();r.advance(1000);
  const point=(id,phase)=>r.act({type:'tooltip-pointer',target:{kind:'control',id},phase});
  point('heralds','enter');
  let state=r.snapshot().controls.tooltip;
  assert.equal(state.visible,true);assert.equal(state.dynamic,true);assert.match(state.text,/100 heralds/);assert.equal(state.crate,null);
  point('heralds','leave');state=r.snapshot().controls.tooltip;
  assert.equal(state.pendingHide,true);assert.equal(state.visible,true);
  r.advance(100);state=r.snapshot().controls.tooltip;
  assert.equal(state.visible,false);assert.equal(state.dynamic,false);assert.equal(state.text,'');
  point('storeBulk','enter');state=r.snapshot().controls.tooltip;
  assert.equal(state.visible,true);assert.equal(state.dynamic,false);assert.match(state.text,/bulk|Shift/i);
  point('tooltip','leave');assert.equal(r.snapshot().controls.tooltip.visible,false);
  r.act({type:'open-menu',menu:'stats'});
  const crate={kind:'stats-crate',item:'achievement',id:0};
  r.act({type:'tooltip-pointer',target:crate,phase:'enter'});
  state=r.snapshot().controls.tooltip;
  assert.deepEqual(state.crate,{id:null,itemId:0,type:'achievement'});
  assert.match(state.text,/\?\?\?/);assert.doesNotMatch(state.text,/Wake and bake/);
  r.act({type:'tooltip-pointer',target:crate,phase:'leave'});
  assert.equal(r.Game.onCrate,0);assert.equal(r.snapshot().controls.tooltip.pendingHide,true);
  r.advance(100);
  assert.deepEqual(replayRuntime(r.events,{randomTape:r.consumedRandom}).snapshot(),r.snapshot());
});

engineTest('native store-crate focus respects held pointer state and modifier-triggered dynamic redraw', () => {
  const r=createRuntime();r.advance(1000);const G=r.Game;
  // Prepared owned-upgrade fixture isolates native crate and keyboard handlers.
  G.cookies=1e6;G.Upgrades['Inspired checklist'].earn();G.Upgrades['Reinforced index finger'].unlocked=1;G.RebuildUpgrades();
  const u=G.Upgrades['Reinforced index finger'];
  const element=r.context.document.getElementById('upgrades').querySelector(`.crate.upgrade[data-id="${u.id}"]`);
  assert.ok(element);
  const action={type:'tooltip-pointer',target:{kind:'control',id:element.id},phase:'enter'};
  r.act({type:'cookie-pointer',phase:'down'});r.act(action);
  assert.equal(G.onCrate,0);assert.equal(r.snapshot().controls.tooltip.visible,false);
  r.act({type:'cookie-pointer',phase:'up'});r.act(action);
  assert.equal(G.onCrate,element);assert.equal(r.snapshot().controls.tooltip.dynamic,true);
  assert.match(r.snapshot().controls.tooltip.text,/Reinforced index finger/);
  r.act({type:'key',code:16,down:true});r.advance(350);
  assert.match(r.snapshot().controls.tooltip.text,/holding Shift/);
  r.act({type:'tooltip-pointer',target:{kind:'control',id:'heralds'},phase:'enter'});
  assert.equal(G.onCrate,0,'moving to another tooltip leaves the old crate');assert.equal(G.keys[16],1);
  assert.match(r.snapshot().controls.tooltip.text,/Heralds/);
  r.act({type:'cookie-pointer',phase:'enter'});assert.equal(r.snapshot().controls.tooltip.pendingHide,true);
});

engineTest('tooltip input rejects absent, hidden, covered and non-tooltip controls without entering the clone renderer', () => {
  const r=createRuntime();r.advance(1000);
  const enter=id=>r.act({type:'tooltip-pointer',target:{kind:'control',id},phase:'enter'});
  assert.throws(()=>enter('absentControl'),/absent/);
  assert.throws(()=>enter('bigCookie'),/no native tooltip/);
  assert.throws(()=>enter('heralds;Game.seedrandom()'),/invalid native tooltip control/);
  const before=r.auditCounts().randomDrawCount;
  assert.throws(()=>enter('rowCanvas19'),/guarded building-hover/);
  assert.equal(r.auditCounts().randomDrawCount,before);
  assert.throws(()=>enter('mutedProduct1'),/hidden/);
  assert.throws(()=>enter('product19'),/hidden/);
  assert.throws(()=>enter('lumps'),/hidden/);
  assert.throws(()=>r.act({type:'tooltip-pointer',target:{kind:'stats-crate',item:'achievement',id:0},phase:'enter'}),/visible statistics/);
  r.Game.Prompt('Unrelated prompt',['Close']);
  assert.throws(()=>enter('heralds'),/prompt covers/);
  r.act({type:'close-prompt'});
  r.act({type:'open-menu',menu:'stats'});
  assert.throws(()=>r.act({type:'tooltip-pointer',target:{kind:'stats-crate',item:'upgrade',id:0},phase:'enter'}),/crate is absent/);
  r.act({type:'open-menu',menu:''});
  r.act({type:'ascend'});r.act({type:'key',code:27,down:false});r.advance(100);
  assert.throws(()=>enter('heralds'),/ascension screen covers/);
});

engineTest('public cycle quotes match native unit rounding and the free-building floor', () => {
  const r=createRuntime();assert.equal(r.snapshot().shop.buildings[0].godzamokCycle.amount,0);
  // Synthetic Pantheon access and small holdings isolate native pricing.
  r.Game.Objects.Temple.level=1;r.evaluate(r.source.sources['minigamePantheon.js'],'minigamePantheon.js');
  r.Game.Objects.Temple.minigame.launch();r.Game.Objects.Temple.minigameLoaded=true;
  r.Game.Upgrades['A crumbly egg'].earn();r.Game.dragonLevel=r.Game.dragonLevels.length-1;
  r.Game.dragonAura=r.Game.dragonAurasBN['Earth Shatterer'].id;
  for(const name of ['Cursor','Farm']) {
    const b=r.Game.Objects[name];b.amount=12;b.highest=12;b.free=name==='Cursor'?10:0;b.locked=false;
    b.l.classList.remove('toggledOff');
    r.Game.cookies=1000000000;
    const quote=r.snapshot().shop.buildings[b.id].godzamokCycle;
    assert.equal(quote.amount,11);
    const start=r.Game.cookies;r.act({type:'sell-building',id:b.id,amount:quote.amount});
    assert.equal(r.Game.cookies-start,quote.refund);
    const afterSale=r.Game.cookies;r.act({type:'buy-building',id:b.id,amount:quote.amount});
    assert.equal(afterSale-r.Game.cookies,quote.rebuy);
    assert.equal(start-r.Game.cookies,quote.net);assert.equal(b.amount,12);
    const one=r.snapshot().shop.buildings[b.id].rebuyOnePrice;
    b.sacrifice(1);assert.equal(b.getPrice(),one);
  }
  const aura=r.snapshot().dragon.auras.find(a=>a.name==='Earth Shatterer');
  assert.equal(aura.unlocked,true);assert.equal(aura.id,r.Game.dragonAura);
});

engineTest('cached count quotes equal native sums across raw inputs and every live price modifier', () => {
  const r=createRuntime();const G=r.Game;const b=G.Objects.Farm;const base=b.basePrice;
  const check=()=>{
    const o=r.snapshot();
    for(const quote of o.shop.buildings)assert.equal(quote.goalPurchase.price,quote.goalPurchase.amount?G.ObjectsById[quote.id].getSumPrice(quote.goalPurchase.amount):0,quote.name);
    return o.shop.buildings[b.id].goalPurchase.price;
  };
  // Synthetic raw-price boundaries. No native pricing function is replaced.
  for(const amount of [0,1,599,699,700,701])for(const free of [0,10,700])for(const increase of [1,1.0001,1.1,1.15])for(const price of [0.5,base]) {
    b.amount=amount;b.free=free;b.basePrice=price;G.priceIncrease=increase;
    check();check();
  }
  b.amount=12;b.free=0;b.basePrice=base;G.priceIncrease=1.15;
  for(const name of ['Season savings',"Santa's dominion",'Faberge egg','Divine discount','Fortune #100',b.fortune.name]) {
    const old=check();G.Upgrades[name].earn();assert.notEqual(check(),old,name);
  }
  G.Upgrades['A crumbly egg'].earn();G.dragonLevel=G.dragonLevels.length-1;
  G.dragonAura=G.dragonAurasBN['Fierce Hoarder'].id;check();
  G.dragonAura2=G.dragonAurasBN['Reality Bending'].id;check();
  for(const name of ['everything must go','pixie luck','pixie misery']){G.gainBuff(name,60,5);check();}
  G.killBuff('Everything must go');G.killBuff('Crafty pixies');G.killBuff('Nasty goblins');check();
  for(const [name,file] of [['Farm','minigameGarden.js'],['Temple','minigamePantheon.js']]) {
    G.Objects[name].level=9;r.evaluate(r.source.sources[file],file);G.Objects[name].minigame.launch();G.Objects[name].minigameLoaded=true;
  }
  const garden=G.Objects.Farm.minigame;const cheapcap=garden.plants.cheapcap;
  garden.plot[0][0]=[cheapcap.id+1,cheapcap.mature];garden.computeBoostPlot();garden.computeEffs();G.CalculateGains();
  assert(G.eff('buildingCost')<1);check();
  garden.freeze=true;garden.computeEffs();G.CalculateGains();assert.equal(G.eff('buildingCost'),1);check();
  const pantheon=G.Objects.Temple.minigame;
  for(const slot of [0,1,2,-1]){pantheon.slotGod(pantheon.gods.creation,slot);check();}
});

engineTest('A recorded action history replays to the same observation and random draw sequence', () => {
  const r = createRuntime({ randomSeed: 952 });
  r.advance(1000);
  for (let i = 0; i < 20; i++) { r.act({ type: 'wait', milliseconds: 50 }); r.act({ type: 'click' }); }
  r.act({ type: 'buy-building', id: 0 }); r.act({ type: 'wait', milliseconds: 2000 });
  const replay = replayRuntime(r.events, { randomTape: r.consumedRandom });
  assert.deepEqual(replay.snapshot(), r.snapshot());
  assert.deepEqual(replay.consumedRandom, r.consumedRandom);
});

engineTest('summary recording preserves every native checkpoint and count without retaining histories', () => {
  const fullEvents=[];const summaryEvents=[];
  const full=createRuntime({randomSeed:71,onTransition:event=>fullEvents.push(event)});
  const summary=createRuntime({randomSeed:71,recordAudit:false,onTransition:event=>summaryEvents.push(event)});
  for(const action of [{type:'wait',milliseconds:100},{type:'click'},{type:'tiny-cookie'},
    {type:'wait',milliseconds:100},{type:'click'},{type:'name-bakery',name:'Recording fixture'}]) {
    full.act(action);summary.act(action);
  }
  assert.deepEqual(summary.snapshot(),full.snapshot());assert.deepEqual(summaryEvents,fullEvents);
  assert.equal(summary.events,null);assert.equal(summary.consumedRandom,null);
  assert.equal(summary.auditCounts().actionCount,full.events.length);
  assert.equal(summary.auditCounts().randomDrawCount,full.consumedRandom.length);
  assert.throws(()=>replayRuntime(summary.events),/not a full replay/);
  assert.throws(()=>createRuntime({recordAudit:false,randomTape:[]}),/requires the LCG/);
  assert.throws(()=>summary.act({type:'grant-cookies'}),/unknown action/);
  assert.equal(summary.auditCounts().actionCount,full.events.length);
});

engineTest('Runtime completion fields agree with the independent read-only completion adapter', () => {
  const r = createRuntime(); r.advance(1000);
  const observation = r.snapshot();
  const captured = captureCompletionSnapshot(r.Game, observation.history, { edition: 'steam' });
  for (const key of ['gameVersion', 'edition', 'achievements', 'history']) assert.deepEqual(observation[key], captured[key]);
  for (const [key, value] of Object.entries(captured.progression)) assert.deepEqual(observation.progression[key], value, key);
  for (const name of Object.keys(captured.upgrades)) {
    assert.equal(observation.upgrades[name].bought, captured.upgrades[name].bought, name);
    assert.equal(observation.upgrades[name].unlocked, captured.upgrades[name].unlocked, name);
  }
});

engineTest('Runtime rejects exhausted or invalid random tapes and unknown or illegal actions', () => {
  assert.throws(() => createRuntime({ randomTape: [] }), /Random tape exhausted/);
  assert.throws(() => createRuntime({ randomTape: [1] }), /must be in \[0, 1\)/);
  const r = createRuntime();
  assert.throws(() => r.act({ type: 'grant-cookies', amount: 1e100 }), /unknown action type/);
  assert.throws(() => r.act({ type: 'buy-building', id: 0 }), /unaffordable/);
  assert.throws(() => r.act({ type: 'cast-spell', spell: 'hand of fate' }), /locked/);
  assert.equal(r.Game.cookies, 0);
  assert.equal(r.events.length, 0);
  assert.ok(!ACTION_TYPES.includes('load-save'));
});

engineTest('Four minigames load through the engine loader in an explicitly synthetic unlocked fixture', () => {
  const r = createRuntime();
  // Test fixture only. This mutation is not in act(), events or a claimed legal new-save policy.
  r.evaluate('for (var name of ["Farm","Bank","Temple","Wizard tower"]) { Game.Objects[name].level=1; Game.Objects[name].amount=1; Game.Objects[name].highest=1; } Game.LoadMinigames();');
  r.advance(1000);
  for (const name of ['Farm', 'Bank', 'Temple', 'Wizard tower']) assert.equal(r.Game.isMinigameReady(r.Game.Objects[name]), true);
  assert.equal(Object.keys(r.Game.Objects.Farm.minigame.plants).length, 34);
  r.act({ type: 'garden-freeze' }); assert.equal(r.Game.Objects.Farm.minigame.freeze, 1);
  r.act({ type: 'garden-freeze' }); assert.equal(r.Game.Objects.Farm.minigame.freeze, 0);
  r.act({ type: 'pantheon-slot', god: 'ruin', slot: 0 });
  assert.equal(r.Game.hasGod('ruin'), 1);
  assert.equal(r.Game.Objects.Temple.minigame.swaps, 2);
});

engineTest('Runtime constructor catalogue equals the checked-in Steam identity catalogue', () => {
  const actual = buildCatalogue();
  const saved = JSON.parse(readFileSync(new URL('../model/catalogue.json', import.meta.url), 'utf8'));
  assert.deepEqual(actual, saved);
  assert.equal(actual.achievements.length, 643);
  assert.equal(actual.achievements.filter(x => x.normal).length, 622);
  assert.equal(actual.upgrades.length, 875);
  assert.equal(actual.buildings.length, 20);
  assert.equal(actual.garden.seeds.length, 34);
  assert.equal(actual.market.goods.length, 18);
});

engineTest('Native name, stats, info and ticker controls award their ordinary interaction achievements', () => {
  const r = createRuntime(); r.advance(1000);
  r.act({ type: 'name-bakery', name: 'Runtime Bakery' });
  r.act({ type: 'tiny-cookie' });
  r.act({ type: 'achievement-slot', id: r.Game.Achievements['Here you go'].id });
  assert.equal(r.Game.HasAchiev('Here you go'), 1);
  assert.throws(() => r.act({ type: 'achievement-slot', id: r.Game.Achievements['Wake and bake'].id }), /no click action/);
  r.act({ type: 'forgotten-madeleine' });
  r.act({ type: 'resize', width: 800, height: 900 }); r.act({ type: 'click-news' });
  for (const name of ["What's in a name", 'Tiny cookie', 'Olden days', 'Stifling the press']) assert.equal(r.Game.HasAchiev(name), 1, name);
  assert.throws(() => r.act({ type: 'name-bakery', name: 'saysopensesame' }), /debug bakery name/);
  r.act({ type: 'store-bulk', id: 3 }); assert.equal(r.Game.buyBulk, 10);
  assert.deepEqual(replayRuntime(r.events, { randomTape: r.consumedRandom }).snapshot(), r.snapshot());
});

engineTest('public ticker text preserves native seeded lucky numbers without exposing the seed or an undrawn message', () => {
  const r=createRuntime();const G=r.Game;
  // Diagnostic startup seed and unlocks select one native fortune branch.
  // No policy receives this seed or installs its random generator.
  G.seed='abcde';G.Upgrades['Fortune cookies'].bought=1;
  G.fortuneGC=1;G.fortuneCPS=0;G.T=G.fps*10+1;
  for(const upgrade of G.Tiers.fortune.upgrades)upgrade.unlocked=1;
  r.context.Math.random=()=>0;G.getNewTicker();
  const text='Your lucky numbers are: 72 62 64 92';
  assert.equal(G.tickerL.textContent,text);
  let observation=r.snapshot();
  assert.deepEqual(observation.seasonal.ticker,{visible:true,text});
  assert.equal(observation.seasonal.fortuneVisible,true);
  assert.equal(Object.hasOwn(observation,'seed'),false);
  assert.equal(Object.hasOwn(observation.seasonal,'seed'),false);
  assert.equal(JSON.stringify(observation).includes('abcde'),false);
  assert.equal(Object.hasOwn(observation.seasonal,'TickerEffect'),false);
  G.seed='zzzzz';G.Ticker='This message has not been drawn.';
  assert.equal(r.snapshot().seasonal.ticker.text,text,'private backing fields do not replace rendered text');
  r.act({type:'click-news'});
  observation=r.snapshot();
  assert.equal(observation.seasonal.ticker.text,text,'native text remains until the next ticker draw');
  assert.equal(observation.seasonal.fortuneVisible,false,'the already-consumed fortune is not offered again');
  G.TickerDraw();assert.equal(r.snapshot().seasonal.ticker.text,'');
});

engineTest('ticker observation respects covered or hidden controls and the native narrow-window replacement', () => {
  const r=createRuntime();const G=r.Game;r.advance(1000);
  assert.equal(r.snapshot().seasonal.ticker.visible,true);
  const displayed=G.tickerL.textContent;
  G.Prompt('Unrelated prompt',['Close']);
  assert.deepEqual(r.snapshot().seasonal.ticker,{visible:false,text:''});
  r.act({type:'close-prompt'});assert.equal(r.snapshot().seasonal.ticker.text,displayed);
  G.tickerL.style.visibility='hidden';
  assert.deepEqual(r.snapshot().seasonal.ticker,{visible:false,text:''});
  G.tickerL.style.visibility='visible';
  G.seed='abcde';G.Upgrades['Fortune cookies'].bought=1;G.fortuneGC=1;G.fortuneCPS=0;G.T=G.fps*10+1;
  for(const upgrade of G.Tiers.fortune.upgrades)upgrade.unlocked=1;
  r.act({type:'resize',width:800,height:900});
  r.context.Math.random=()=>0;G.getNewTicker();
  assert.equal(G.TickerEffect.sub,'fortuneCPS','the diagnostic branch still selected the fortune');
  const ticker=r.snapshot().seasonal.ticker;
  assert.equal(ticker.visible,true);assert.equal(ticker.text,G.tickerL.textContent);
  assert.match(ticker.text,/help!/);assert.doesNotMatch(ticker.text,/72 62 64 92/);
  assert.equal(r.snapshot().seasonal.fortuneVisible,false,'undisplayed fortune identity is private');
  r.act({type:'ascend'});
  assert.deepEqual(r.snapshot().seasonal.ticker,{visible:false,text:''});
});

engineTest('Gift forms deduct and redeem cookies and enforce the native one-hour cooldown in a synthetic unlocked fixture', () => {
  const r = createRuntime(); r.advance(1000);
  assert.throws(() => r.act({ type: 'gift-send' }), /unavailable/);
  // Fixture only: a real policy must acquire Wrapping paper and the bank first.
  r.evaluate("Game.Upgrades['Wrapping paper'].bought=1; Game.cookies=2e9;");
  r.act({ type: 'gift-send', amount: 37, message: 'A self gift' });
  const code = r.snapshot().giftCode;
  assert.equal(typeof code, 'string'); assert.equal(r.Game.cookiesSent, 37); assert.equal(r.Game.cookies, 2e9 - 37);
  assert.equal(r.Game.hasBuff('Gifted out').time, 60 * 60 * r.Game.fps);
  assert.throws(() => r.act({ type: 'gift-redeem', code }), /unavailable/);
  assert.throws(() => r.act({ type: 'gift-send' }), /unavailable/);
  // Fixture only: shorten the remaining buff to check the real expiration transition quickly.
  r.evaluate("Game.hasBuff('Gifted out').time=1;"); r.advance(100);
  r.act({ type: 'gift-redeem', code });
  assert.equal(r.Game.cookiesReceived, 37); assert.equal(r.Game.cookies, 2e9);
  assert.equal(r.Game.HasAchiev('No time like the present'), 1);
  assert.equal(r.Game.hasBuff('Gifted out').time, 60 * 60 * r.Game.fps);
});

engineTest('Wrinkler clicks use native pointer hit testing and frame processing, with no direct HP action', () => {
  const r = createRuntime(); r.advance(1000);
  // Fixture only: spawn one wrinkler and place it at the cookie to avoid a stochastic wait.
  r.evaluate('Game.SpawnWrinkler(Game.wrinklers[0]); Game.wrinklers[0].close=1;'); r.advance(200);
  assert.throws(() => r.act({ type: 'wrinkler-poke', id: 0 }), /hover/);
  r.act({ type: 'wrinkler-hover', id: 0 }); r.advance(200);
  assert.equal(r.Game.wrinklers[0].selected, 1);
  const hp = r.Game.wrinklers[0].hp;
  r.act({ type: 'wrinkler-poke', id: 0 }); assert.equal(r.Game.wrinklers[0].hp, hp);
  r.advance(40); assert.ok(r.Game.wrinklers[0].hp < hp); assert.equal(r.Game.wrinklers[0].clicks, 1);
  for (let i = 0; i < 8 && r.Game.wrinklers[0].phase > 0; i++) { r.act({ type: 'wrinkler-poke', id: 0 }); r.advance(40); }
  assert.equal(r.Game.wrinklersPopped, 1); assert.equal(r.Game.wrinklers[0].phase, 0);
});

engineTest('Permanent-slot selection uses the native owned-upgrade list and confirmation in a synthetic ascended fixture', () => {
  const r = createRuntime(); r.advance(1000);
  const id = r.Game.Upgrades['Reinforced index finger'].id;
  assert.throws(() => r.act({ type: 'permanent-slot', slot: 0, id }), /ascension screen/);
  // Fixture only: ownership and ascension cannot be granted by act().
  r.evaluate("Game.Upgrades['Permanent upgrade slot I'].bought=1;Game.Upgrades['Reinforced index finger'].bought=1;Game.Upgrades['Reinforced index finger'].unlocked=1;Game.OnAscend=1;");
  r.act({ type: 'permanent-slot', slot: 0, id });
  assert.equal(r.Game.permanentUpgrades[0], id); assert.equal(r.Game.promptOn, 0);
  assert.throws(() => r.act({ type: 'permanent-slot', slot: 1, id }), /locked/);
});

engineTest('Minigame refill preserves native lump confirmation, cost and shared cooldown in a synthetic unlocked fixture', () => {
  const r = createRuntime();
  r.evaluate('Game.Objects.Temple.level=1; Game.Objects.Temple.amount=1; Game.Objects.Temple.highest=1; Game.LoadMinigames(); Game.lumps=5;Game.lumpsTotal=5;Game.prefs.askLumps=1;');
  r.advance(1000); r.act({ type: 'pantheon-slot', god: 'ruin', slot: 0 });
  r.act({ type: 'minigame-refill', building: 'Temple' }); assert.equal(r.Game.promptOn, 1); assert.equal(r.Game.lumps, 5);
  r.act({ type: 'prompt', option: 0 });
  assert.equal(r.Game.lumps, 4); assert.equal(r.Game.Objects.Temple.minigame.swaps, 3);
  assert.equal(r.Game.lumpRefill, 15 * 60 * r.Game.fps);
  assert.throws(() => r.act({ type: 'minigame-refill', building: 'Temple' }), /unavailable/);
});

engineTest('A timer can cancel its own interval without running again', () => {
  const r = createRuntime();
  // Adapter fixture, independent of gameplay: cancellation must match browser timer semantics.
  r.evaluate('var timerCalls=0; var fixtureTimer=setInterval(function(){timerCalls++;clearInterval(fixtureTimer);},10);');
  r.advance(100); assert.equal(r.context.timerCalls, 1);
});

engineTest('The default policy rejects reload retry and You-hover RNG manipulation; diagnostics are explicit', () => {
  const r = createRuntime(); r.advance(1000);
  // Fixture only: display a You building without a purchase trajectory.
  r.evaluate('Game.Objects.You.amount=1;');
  assert.equal(r.environment.policyMode, 'no-retry-no-rng-manipulation');
  assert.equal(r.environment.saveReloadRetries, false);
  assert.throws(() => r.act({ type: 'reload' }), /unknown action type/);
  assert.throws(() => r.act({ type: 'load-save' }), /unknown action type/);
  assert.throws(() => r.act({ type: 'building-hover', id: 19, x: 32, y: 32 }), /no-manipulation policy/);
  assert.equal(r.Game.Objects.You.mouseOn, false);
  const d = createRuntime({ diagnosticMode: true }); d.advance(1000); d.evaluate('Game.Objects.You.amount=1;');
  assert.equal(d.environment.policyMode, 'diagnostic-only');
  d.act({ type: 'building-hover', id: 19, x: 32, y: 32 }); assert.equal(d.Game.Objects.You.mouseOn, true);
});

engineTest('Viewport input runs native resize listeners and permits the ordinary cookie-dunk interaction', () => {
  const r = createRuntime(); r.advance(1000);
  for (const action of [{ type: 'name-bakery', name: 'Dunk Bakery' }, { type: 'tiny-cookie' }, { type: 'forgotten-madeleine' }]) r.act(action);
  r.act({ type: 'resize', width: 800, height: 200 });
  assert.equal(r.Game.LeftBackground.canvas.height, 200);
  r.advance(12000);
  assert.equal(r.Game.HasAchiev('Cookie-dunker'), 1);
});

engineTest('native resize uses parent pane geometry and reveals new Grandma indices without rerolling old sprites', () => {
  const r=createRuntime();const b=r.Game.Objects.Grandma;
  // Synthetic holdings supply more sprites than fit in the initial viewport.
  b.amount=b.highest=500;r.advance(100);
  assert.deepEqual(r.snapshot().viewport,{width:1200,height:900});
  assert.equal(b.canvas.clientWidth,474);assert.equal(b.canvas.height,128);assert.equal(b.pics.length,45);
  const previous=Array.from(b.pics,pic=>({...pic}));
  r.act({type:'resize',width:16384,height:900});
  assert.equal(b.canvas.clientWidth,11103);assert.equal(b.canvas.width,474);assert.equal(b.toResize,true);
  r.advance(100);assert.equal(b.canvas.width,11103);assert.equal(b.canvas.height,128);assert.equal(b.pics.length,500);
  for(const pic of previous)assert.deepEqual({...b.pics.find(next=>next.id===pic.id)},pic);
  assert.equal(r.snapshot().seasonal.grandmaDisplay.capacity,1041);
  // Native scaling keeps its logical minimum800×200 while physical bounds halve.
  r.act({type:'resize',width:400,height:100});r.advance(100);
  assert.equal(r.Game.scale,0.5);assert.deepEqual(r.snapshot().viewport,{width:800,height:200});
  assert.equal(b.canvas.clientWidth,194);assert.equal(b.canvas.width,194);assert.equal(b.canvas.height,128);
  assert.equal(b.canvas.getBoundingClientRect().width,97);assert.equal(b.canvas.getBounds().width,194);
  assert.equal(r.context.document.getElementById('centerArea').clientWidth,194);
  assert.equal(r.context.document.getElementById('centerArea').offsetWidth,211);
});

engineTest('Native Escape skips only the five-second ascension animation', () => {
  const r = createRuntime(); r.advance(1000); r.act({ type: 'ascend' });
  assert.equal(r.Game.AscendDuration, 5 * r.Game.fps); assert.equal(r.Game.OnAscend, 0);
  r.act({ type: 'key', code: 27, down: false });
  assert.equal(r.Game.AscendTimer, r.Game.AscendDuration);
  r.advance(40); assert.equal(r.Game.OnAscend, 1); assert.equal(r.Game.AscendTimer, 0);
});

engineTest('Native settings and keyboard modifiers retain prompts, purchase bulk and reload exclusions', () => {
  const r = createRuntime(); r.advance(1000);
  r.act({ type: 'open-menu', menu: 'prefs' });
  r.act({ type: 'preference', name: 'askLumps' }); assert.equal(r.Game.prefs.askLumps, 1);
  r.act({ type: 'volume', channel: 'sound', value: 0 }); assert.equal(r.Game.volume, 0);
  r.act({ type: 'volume', channel: 'music', value: 0 }); assert.equal(r.Game.volumeMusic, 0);
  r.act({ type: 'key', code: 16, down: true }); r.advance(40); assert.equal(r.Game.buyBulk, 100);
  r.act({ type: 'key', code: 16, down: false }); r.advance(40); assert.equal(r.Game.buyBulk, 1);
  r.act({ type: 'key', code: 17, down: true });
  assert.throws(() => r.act({ type: 'key', code: 79, down: true }), /excluded/);
  assert.throws(() => r.act({ type: 'preference', name: 'screenreader' }), /excluded reload/);
  r.act({ type: 'visibility', visible: false }); assert.equal(r.Game.visible, false); assert.equal(r.Game.keys.length, 0);
  r.act({ type: 'visibility', visible: true }); assert.equal(r.Game.visible, true);
});

engineTest('Native clone gene controls can earn In her likeness without hovering or assigning achievements', () => {
  const r = createRuntime(); r.advance(1000);
  // Fixture only: access the You building; all subsequent gene changes use native UI controls.
  r.evaluate('Game.Objects.You.amount=1;');
  for (const [gene, value] of [['hair',9],['hairCol',1],['head',2],['acc1',2],['acc2',0]]) {
    const index = r.Game.YouCustomizer.genesById[gene].n;
    while (r.Game.YouCustomizer.currentGenes[index] !== value) r.act({ type: 'customizer-gene', gene, direction: 1 });
  }
  assert.equal(r.Game.HasAchiev('In her likeness'), 1);
  assert.equal(r.Game.Objects.You.mouseOn, false);
  r.act({ type: 'customizer-random' }); assert.equal(r.Game.YouCustomizer.currentGenes.length, 7);
});

engineTest('Frozen Garden planting and harvesting remain legal while locked and unplantable seeds reject', () => {
  const r = createRuntime();
  // Fixture only: unlock the Garden and provide a bank; no mature plants or achievements are granted.
  r.evaluate('Game.Objects.Farm.level=1;Game.Objects.Farm.amount=1;Game.Objects.Farm.highest=1;Game.LoadMinigames();Game.cookies=1e9;'); r.advance(1000);
  r.act({ type: 'garden-freeze' });
  const bank = r.Game.cookies;
  r.act({ type: 'garden-plant', seed: 'bakerWheat', x: 2, y: 2 });
  assert.equal(r.Game.Objects.Farm.minigame.freeze, 1); assert.ok(r.Game.cookies < bank);
  assert.equal(r.snapshot().garden.plot[2][2][0], 'bakerWheat');
  r.act({ type: 'garden-harvest', x: 2, y: 2 }); assert.equal(r.snapshot().garden.plot[2][2][0], null);
  assert.throws(() => r.act({ type: 'garden-plant', seed: 'queenbeetLump', x: 2, y: 2 }), /cannot be planted/);
  assert.throws(() => r.act({ type: 'garden-plant', seed: 'thumbcorn', x: 2, y: 2 }), /cannot be planted/);
});

engineTest('Atomic observers see every completed timer and action boundary with frozen integer-clock records', () => {
  const records = [];
  const r = createRuntime({ onTransition: event => records.push(event) });
  assert.equal(records[0].kind, 'initial');
  r.advance(1000); r.act({ type: 'click' });
  assert.equal(records.at(-1).kind, 'action'); assert.equal(records.at(-1).action.type, 'click');
  assert.ok(records.filter(x => x.kind === 'timer').length >= 30);
  for (let i = 0; i < records.length; i++) {
    assert.equal(Number.isInteger(records[i].elapsedMs), true);
    if (i) assert.ok(records[i].elapsedMs >= records[i-1].elapsedMs);
    assert.equal(Object.isFrozen(records[i].observation.upgrades), true);
  }
  assert.throws(() => { records.at(-1).observation.cookies = 1e100; }, TypeError);
});

engineTest('Public resource and market observations preserve hidden lump type and native displayed costs', () => {
  const r = createRuntime();
  // Synthetic resource fixture only; the observation remains read-only.
  r.evaluate(`Game.cookiesEarned=1e12;Game.lumps=10;Game.lumpCurrentType=2;Game.lumpT=Date.now();
    Game.Objects.Bank.level=1;Game.Objects.Bank.amount=1;Game.Objects.Bank.highest=1;Game.LoadMinigames();`);
  r.advance(1000);
  let observation = r.snapshot();
  assert.equal(observation.lump.available, true);
  assert.equal(observation.lump.type, null);
  assert.equal(observation.lump.ageMs, Math.floor(r.clock.now) - r.Game.lumpT);
  const M = r.Game.Objects.Bank.minigame;
  M.brokers = 23;
  r.Game.cookiesPsRawHighest = 1e8;
  observation = r.snapshot();
  const overhead = 1 + 0.01 * (20 * Math.pow(0.95, M.brokers));
  assert.equal(observation.market.overheadMultiplier, overhead);
  assert.equal(observation.market.goods[0].buyCookiePrice, (r.Game.cookiesPsRawHighest * M.getGoodPrice(M.goodsById[0])) * overhead);
  assert.equal(observation.market.goods[0].restingPrice, M.getRestingVal(0));
  r.Game.lumpCurrentType = 2;
  r.Game.lumpT = Math.floor(r.clock.now) - Math.ceil(r.Game.lumpOverripeAge * 3 / 7);
  assert.equal(r.snapshot().lump.type, 2);
});

engineTest('Visible notification dismissal and native sound selection have explicit legal actions', () => {
  const r = createRuntime(); r.advance(1000);
  r.Game.Notify('First test notice', 'Synthetic UI fixture');
  r.Game.Notify('Second test notice', 'Synthetic UI fixture');
  const id = r.snapshot().controls.notes[0].id;
  r.act({ type: 'dismiss-note', id });
  assert.equal(r.Game.NotesById[id], null);
  r.Game.Notify('Third test notice', 'Synthetic UI fixture');
  r.act({ type: 'dismiss-note', all: true });
  assert.equal(r.Game.Notes.length, 0);
  assert.throws(() => r.act({ type: 'dismiss-note', id }), /absent/);
  assert.throws(() => r.act({ type: 'jukebox-sound', id: 1 }), /locked/);
  // Synthetic unlock; the operation calls the original native sound callback.
  r.Game.Upgrades.Jukebox.unlocked = 1;
  r.act({ type: 'jukebox-sound', id: 1 });
  assert.equal(r.Game.jukebox.onSound, 1);
  assert.throws(() => r.act({ type: 'jukebox-sound', id: 999 }), /sound id/);
});

engineTest('The actual bundled mod initializes, plays and renders its three menus in the isolated engine', () => {
  const r = createRuntime(); r.advance(1000);
  r.evaluate(readFileSync(new URL('../mod/main.js', import.meta.url), 'utf8'), 'mod/main.js');
  r.advance(5000);
  assert.equal(r.Game.mods.CookieMonster.cookieMonsterPlus, true);
  assert.ok(r.Game.modHooks.logic.length > 0);
  assert.ok(r.Game.cookieClicks > 0);
  assert.ok(r.Game.Objects.Cursor.amount > 0);
  assert.ok(r.context.document.querySelector('head'));
  for (const menu of ['prefs', 'stats', 'log', '']) {
    r.act({ type: 'open-menu', menu }); r.advance(100);
    assert.equal(r.Game.onMenu, menu);
    if (menu === 'log') assert.ok(r.context.document.getElementById('cookieMonsterFrameworkMenuSection'));
  }
});

engineTest('The full bundle preserves payout order and skips native ascent in a timed-out challenge fixture', () => {
  const r = createRuntime(); r.advance(1000);
  r.evaluate(readFileSync(new URL('../mod/main.js', import.meta.url), 'utf8'), 'mod/main.js');
  r.advance(2100);
  // Synthetic preparation only: a timed-out Born again run with bank, egg and shiny wrinkler.
  // The complete bundled planner, caches and autoplay phases execute without replacement.
  r.evaluate(`Game.ascensionMode=1;Game.startDate=Date.now()-9*3600*1000;
    Game.cookies=2e12;Game.cookiesEarned=2e12;Game.Upgrades['Chocolate egg'].unlocked=1;
    Game.SpawnWrinkler(Game.wrinklers[0]);Object.assign(Game.wrinklers[0],{type:1,phase:2,close:1,sucked:1e12,hp:3});
    var observed=[];for(var name of ['Ascend','Reincarnate']){let key=name;let original=Game[key];
      Game[key]=function(){observed.push({event:key,time:Date.now()});return original.apply(this,arguments);};}
    var buyEgg=Game.Upgrades['Chocolate egg'].buy;Game.Upgrades['Chocolate egg'].buy=function(){
      observed.push({event:'egg',time:Date.now(),bank:Game.cookies});return buyEgg.apply(this,arguments);};`);
  r.advance(2000);
  const events = Array.from(r.context.observed, event => ({ ...event }));
  assert.deepEqual(events.map(event => event.event), ['egg', 'Ascend', 'Reincarnate']);
  assert.equal(events[0].bank, 5.3e12);
  assert.ok(events[2].time - events[1].time < 200);
  assert.equal(r.Game.OnAscend, 0);
  assert.equal(r.Game.ReincarnateTimer, 0);
  assert.equal(r.Game.ascensionMode, 0);
  assert.equal(r.Game.resets, 1);
  assert.equal(r.Game.Has('Legacy'), 1);
});

engineTest('Optional necessary-achievement gates suppress snapshot allocation without losing event boundaries', () => {
  const complete=[];const gated=[];
  const a=createRuntime({onTransition:event=>complete.push(event)});
  const b=createRuntime({transitionAchievementGate:['Tiny cookie'],onTransition:event=>gated.push(event)});
  for(const action of [{type:'wait',milliseconds:1000},{type:'tiny-cookie'},{type:'wait',milliseconds:100}]){a.act(action);b.act(action);}
  assert.equal(gated.length,complete.length);
  let observations=0;
  for(let i=0;i<gated.length;i++) {
    assert.equal(gated[i].kind,complete[i].kind);assert.equal(gated[i].elapsedMs,complete[i].elapsedMs);
    const reached=!!complete[i].observation.achievements['Tiny cookie'];
    assert.equal(gated[i].gateSatisfied,reached);
    if(reached){assert.deepEqual(gated[i].observation,complete[i].observation);observations++;}
    else assert.equal(gated[i].observation,null);
  }
  assert(observations>0&&observations<gated.length);
  assert.deepEqual(a.snapshot(),b.snapshot());
  assert.throws(()=>createRuntime({transitionAchievementGate:['invented achievement']}),/known achievement names/);
});
