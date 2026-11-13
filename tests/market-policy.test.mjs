import test from 'node:test';
import assert from 'node:assert/strict';
import { MARKET_ACHIEVEMENTS, decideMarketAction, marketPolicySource, requiredMarketBuildingHighest } from '../model/market-policy.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
const noBrokers = { brokerTarget: 0 };
function observation() {
  const overheadMultiplier = 1.2;
  return { cookies: 1e100, progression: { onAscend: false, ascensionMode: 0,
    buildingAmounts: { Cursor: 2000 }, buildingLevels: { Cursor: 12 } }, controls: { promptOn: false }, achievements: {},
    market: { ready: true, bankLevel: 1, officeLevel: 5,
      offices: [[100,2],[200,4],[350,8],[500,10],[700,12],[]].map(([cursorAmount,cursorLevel],id) => ({id,cursorAmount,cursorLevel})),
      brokers: 0, maxBrokers: 70, brokerPrice: 12000, overheadMultiplier,
      goods: Array.from({length:18}, (_,id) => ({ id, key:`g${id}`, active:true, price:10*(id+1), stock:0, maxStock:1300,
        buyCookiePrice:10*10*(id+1)*overheadMultiplier, sellCookiePrice:10*10*(id+1), canBuy:true, canSell:true })),
      profit:0, nextTickMs:60000, loans: [1,2,3].map(id => ({id,unlocked:true,activeFrames:0,interestFrames:0})),
    } };
}
function nativeMarket(randomSeed = 1) {
  const runtime = createRuntime({randomSeed});
  for (const building of Object.values(runtime.Game.Objects)) { building.amount=700; building.highest=700; }
  runtime.Game.Objects.Cursor.amount=2000;
  runtime.Game.Objects.Cursor.level=12;
  runtime.Game.Objects.Bank.level=1;
  runtime.evaluate(runtime.source.sources['minigameMarket.js'], 'minigameMarket.js');
  runtime.Game.Objects.Bank.minigame.launch(); runtime.Game.Objects.Bank.minigameLoaded=true;
  runtime.Game.Objects.Bank.switchMinigame(true);
  runtime.Game.T=10;runtime.Game.Objects.Bank.minigame.logic();
  runtime.Game.cookies=1e100; runtime.Game.cookiesPsRawHighest=10;
  return runtime;
}
function markCollection(state) {
  for (const name of ['Rookie numbers','No nobility in poverty','Full warehouses','Buy buy buy','Make my day','Pyramid scheme']) state.achievements[name]=true;
}

test('the Market source runs with frozen inputs and no external closure', () => {
  const state=observation();
  assert.deepEqual(decidePolicy(marketPolicySource(noBrokers), state, [], null), decideMarketAction(state, {}, noBrokers));
});

test('office upgrades require and sacrifice current cursors, with explicit level and amount requests', () => {
  const state=observation(); state.market.officeLevel=0;
  assert.deepEqual(decideMarketAction(state).action, {type:'market-office'});
  for (const name of MARKET_ACHIEVEMENTS) state.achievements[name]=true;
  state.progression.buildingLevels.Cursor=1;
  assert.equal(decideMarketAction(state).status,'needs-level');
  state.progression.buildingLevels.Cursor=12; state.progression.buildingAmounts.Cursor=99;
  assert.equal(decideMarketAction(state).amount,100);
});

test('single trade achievement thresholds include overhead and do not use cookie totals', () => {
  const state=observation();
  const decision=decideMarketAction(state, {}, noBrokers);
  assert.equal(decision.goal,'Buy buy buy');
  const good=state.market.goods.find(g=>g.id===decision.action.id);
  assert(good.price*state.market.overheadMultiplier*decision.action.amount>=86400);
  assert(good.price*state.market.overheadMultiplier*(decision.action.amount-1)<86400);
  // 86400 cookies can be insufficient because one market dollar is 10 cookies.
  state.cookies=86400;
  assert.notEqual(decideMarketAction(state, {}, noBrokers).goal,'Buy buy buy');
});

test('preparation stops at loan access and does not buy brokers, stocks or later offices', () => {
  const state=observation();state.market.officeLevel=0;
  assert.equal(decideMarketAction(state,{}, {collectTrades:false}).action.type,'market-office');
  state.market.officeLevel=1;state.progression.buildingLevels.Cursor=3;
  let d=decideMarketAction(state,{}, {collectTrades:false});
  assert.equal(d.status,'needs-level');assert.equal(d.level,4);
  state.progression.buildingLevels.Cursor=4;
  assert.equal(decideMarketAction(state,{}, {collectTrades:false}).action.type,'market-office');
  state.market.officeLevel=2;
  d=decideMarketAction(state,{}, {collectTrades:false});
  assert.equal(d.status,'prepared');assert.equal(d.action,null);
  assert.notEqual(decideMarketAction(state,{}, {collectTrades:true}).status,'prepared');
  assert.equal(decideMarketAction(state,{}, {collectTrades:'later'}).status,'blocked');
});

test('all18 holdings are preserved until their native achievements are won', () => {
  const state=observation(); state.achievements['Buy buy buy']=true;
  for (const good of state.market.goods) { good.stock=500; good.price=10000; }
  state.market.goods[0].stock=499;
  const decision=decideMarketAction(state, {}, noBrokers);
  assert.deepEqual(decision.action,{type:'market-buy',id:0,amount:1});
  state.market.goods[0].canBuy=false;
  assert.equal(decideMarketAction(state, {}, noBrokers).status,'waiting');
});

test('an affordable-capacity warehouse reserves its fill cost before unrelated trades', () => {
  const state=observation();
  for(const name of ['Buy buy buy','Rookie numbers','No nobility in poverty'])state.achievements[name]=true;
  for(const good of state.market.goods)good.stock=500;
  state.cookies=0;
  const decision=decideMarketAction(state,{},noBrokers);
  assert.equal(decision.goal,'Full warehouses');assert.equal(decision.status,'needs-resources');
  assert.equal(decision.good,0);assert.equal(decision.requiredCookies,500*state.market.goods[0].buyCookiePrice);
  state.market.goods[0].canBuy=false;
  assert.equal(decideMarketAction(state,{},noBrokers).good,1);
  for(const good of state.market.goods)good.canBuy=false;
  assert.equal(decideMarketAction(state,{},noBrokers).status,'waiting');
});

test('trade direction restrictions, affordability and malformed configuration are checked', () => {
  const state=observation(); markCollection(state);
  state.market.goods[0].stock=100; state.market.goods[0].price=100;
  state.market.goods[0].canSell=false;
  for (const good of state.market.goods) good.canBuy=false;
  assert.equal(decideMarketAction(state, {}, noBrokers).status,'waiting');
  state.market.goods[0].canSell=true;
  assert.equal(decideMarketAction(state, {}, noBrokers).action.type,'market-sell');
  assert.equal(decideMarketAction(state, {}, {buyFactor:1,sellFactor:1}).status,'blocked');
  assert.equal(decideMarketAction(state, {decisions:5}, {maxDecisions:5}).status,'budget-exhausted');
});

test('the default policy has no lifetime counter cap before or after market completion', () => {
  const state = observation();
  let decision = decideMarketAction(state, { decisions: Number.MAX_SAFE_INTEGER }, noBrokers);
  assert.notEqual(decision.status, 'budget-exhausted');
  assert.equal(decision.memory.decisions, null);
  assert.equal(decision.memory.config.maxDecisions, null);
  for (const name of MARKET_ACHIEVEMENTS) state.achievements[name] = true;
  decision = decideMarketAction(state, { decisions: Number.MAX_SAFE_INTEGER }, noBrokers);
  assert.equal(decision.status, 'complete');
  assert.equal(decision.memory.decisions, null);
  assert.equal(decideMarketAction(state, { decisions: 5 }, { maxDecisions: 5 }).status, 'budget-exhausted');
  assert.equal(decideMarketAction(state, { decisions: 5, config: { maxDecisions: 5 } }, { maxDecisions: null }).status, 'complete');
});

test('only an active loan supports the Debt evasion handoff, and the controller does not ascend', () => {
  const state=observation(); for (const name of MARKET_ACHIEVEMENTS) state.achievements[name]=true;
  assert.equal(decideMarketAction(state).status,'complete');
  let decision=decideMarketAction(state, {}, {prepareDebtEvasion:true});
  assert.deepEqual(decision.action,{type:'market-loan',id:1});
  state.market.loans[0].interestFrames=300;
  decision=decideMarketAction(state, {}, {prepareDebtEvasion:true});
  assert.deepEqual(decision.action,{type:'market-loan',id:2});
  state.market.loans[1].activeFrames=300;
  decision=decideMarketAction(state, {}, {prepareDebtEvasion:true});
  assert.equal(decision.status,'needs-ascension'); assert.equal(decision.action,null);
});

test('native office sacrifices, dollar accounting, and the same-tick trade lock match the controller', {skip}, () => {
  const runtime=nativeMarket(); const M=runtime.Game.Objects.Bank.minigame;
  let memory={};
  for (let i=0;i<5;i++) { const d=decideMarketAction(runtime.snapshot(),memory,noBrokers); memory=d.memory; runtime.act(d.action); }
  assert.equal(M.officeLevel,5); assert.equal(runtime.Game.Objects.Cursor.amount,150);
  const decision=decideMarketAction(runtime.snapshot(),memory,noBrokers);
  assert.equal(decision.goal,'Buy buy buy');
  const good=M.goodsById[decision.action.id]; const oldProfit=M.profit;
  runtime.act(decision.action);
  assert.equal(runtime.Game.Achievements['Buy buy buy'].won,1);
  assert.equal(M.profit,oldProfit-good.val*1.2*decision.action.amount);
  assert.equal(M.sellGood(good.id,1),false);
  M.tick(); assert.equal(M.sellGood(good.id,1),true);
});

test('the single-sale goal preserves startup stock across adverse quotes instead of repeating a losing trade', {skip}, () => {
  const runtime = nativeMarket(); const M = runtime.Game.Objects.Bank.minigame;
  M.officeLevel = 5;
  for (const name of ['Buy buy buy', 'Rookie numbers', 'No nobility in poverty', 'Full warehouses']) runtime.Game.Win(name);
  // Quote fixtures isolate the controller and unmodified purchase callbacks.
  // They do not assert that this exact quote sequence has positive probability.
  for (const good of M.goodsById) { good.stock = M.getGoodMaxStock(good); good.val = 1; good.last = 0; }
  const good = M.goodsById[0]; good.stock = 0; good.val = 80;
  let memory = {};
  const first = decideMarketAction(runtime.snapshot(), memory, noBrokers); memory = first.memory;
  assert.deepEqual(first.action, {type:'market-buy', id:0, amount:1080});
  runtime.act(first.action);
  const initialDebit = M.profit;
  assert(initialDebit < 0);
  for (let i = 0; i < 100; i++) {
    good.val = i % 2 ? 66.1 : 66; good.last = 0;
    const d = decideMarketAction(runtime.snapshot(), memory, noBrokers); memory = d.memory;
    assert.equal(d.goal, 'Make my day'); assert.equal(d.action.type, 'wait');
    assert.equal(good.stock, 1080); assert.equal(M.profit, initialDebit);
  }
  // The former fallthrough sold at66 and could buy again at80. The corrected
  // policy waits for the native86400-dollar callback, then releases the stock.
  good.val = 81; good.last = 0;
  const sale = decideMarketAction(runtime.snapshot(), memory, noBrokers);
  assert.deepEqual(sale.action, {type:'market-sell', id:0, amount:10000});
  runtime.act(sale.action);
  assert.equal(runtime.Game.HasAchiev('Make my day'), 1);
  assert.equal(good.stock, 0);
});

test('ceil-aware warehouse inversion is minimal under every native office bonus', {skip}, () => {
  const runtime=nativeMarket(); const M=runtime.Game.Objects.Bank.minigame; const good=M.goodsById[0];
  // Synthetic office/level boundaries isolate the unmodified capacity function.
  for(let office=0;office<=5;office++)for(const level of [0,1,9,12,100])for(const capacity of [0,1,2,249,250,251,252,500,1000,Number.MAX_SAFE_INTEGER]) {
    M.officeLevel=office;good.building.level=level;
    const needed=requiredMarketBuildingHighest(capacity,office,level);
    good.building.highest=needed;assert(M.getGoodMaxStock(good)>=capacity);
    if(needed>0){good.building.highest=needed-1;assert(M.getGoodMaxStock(good)<capacity);}
  }
  assert.equal(requiredMarketBuildingHighest(500,5,0),167);
  assert.equal(requiredMarketBuildingHighest(1000,5,0),500);
  assert.equal(requiredMarketBuildingHighest(252,5,0),1);
});

test('warehouse resource requests identify a native building target and stop at its actual capacity', {skip}, () => {
  const runtime=nativeMarket();const M=runtime.Game.Objects.Bank.minigame;M.officeLevel=5;
  for(const good of M.goodsById){good.building.amount=10;good.building.highest=10;good.building.level=0;}
  runtime.Game.Objects.Bank.level=1;
  runtime.advance(1000);
  runtime.Game.Win('Buy buy buy');
  let decision=decideMarketAction(runtime.snapshot(),{},noBrokers);
  assert.equal(decision.requiredCapacity,500);assert.equal(decision.requiredBuildingHighest,167);
  assert.equal(decision.amount,167);assert.equal(typeof decision.building,'string');
  runtime.Game.Win('Rookie numbers');runtime.Game.Win('No nobility in poverty');
  decision=decideMarketAction(runtime.snapshot(),{},noBrokers);
  assert.equal(decision.building,'Farm');assert.equal(decision.requiredCapacity,1000);
  assert.equal(decision.requiredBuildingHighest,500);
  runtime.act({type:'buy-building',id:decision.buildingId,amount:decision.amount-runtime.Game.Objects.Farm.amount});
  decision=decideMarketAction(runtime.snapshot(),{},noBrokers);
  assert.equal(decision.action.type,'market-buy');assert.equal(decision.action.id,0);assert.equal(decision.action.amount,1000);
  runtime.act(decision.action);assert.equal(runtime.Game.HasAchiev('Full warehouses'),1);
});

test('the native reset awards Debt evasion for a loan but not for its interest period', {skip}, () => {
  for (const interest of [false,true]) {
    const runtime=nativeMarket(); const M=runtime.Game.Objects.Bank.minigame;
    M.takeLoan(1,interest);
    runtime.Game.Reset();
    assert.equal(runtime.Game.Achievements['Debt evasion'].won,interest?0:1);
    assert.equal(M.officeLevel,0);
    assert.equal(M.profit,0);
  }
});

test('the baseline wins all eight trading/office goals under the unmodified native price kernel', {skip,timeout:120000}, t => {
  // Funded synthetic fixture. Native ticks drive every random price update;
  // the policy sees only snapshots and cannot inspect modes, durations or RNG.
  // This is not a full-game new-save trajectory or an optimality certificate.
  for (const randomSeed of [1, 7, 91]) {
    const runtime=nativeMarket(randomSeed); const M=runtime.Game.Objects.Bank.minigame;
    let memory={}; let completed=false; let ticks=0;
    for (let i=0;i<100000;i++) {
      const decision=decideMarketAction(runtime.snapshot(),memory,{maxWaitMs:60000}); memory=decision.memory;
      if (decision.status==='complete') { completed=true; break; }
      assert(decision.action,`${decision.status}: ${decision.reason}`);
      if (decision.action.type==='wait') { M.tick(); ticks++; }
      else runtime.act(decision.action);
    }
    assert(completed,`market incomplete after ${ticks} ticks; profit ${M.profit}`);
    assert.equal(M.officeLevel,5); assert(M.profit>=1e7);
    for (const name of MARKET_ACHIEVEMENTS) assert.equal(runtime.Game.Achievements[name].won,1,name);
    assert.equal(runtime.Game.Achievements['Gaseous assets'].won,0);
    t.diagnostic(`Seed ${randomSeed}: ${ticks} native market ticks; final profit ${M.profit.toFixed(2)} dollars.`);
  }
});
