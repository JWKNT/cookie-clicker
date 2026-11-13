import test from 'node:test';
import assert from 'node:assert/strict';
import {createRuntime} from '../model/runtime.mjs';
import {hasGameSource} from '../model/game-source.mjs';
import {decidePolicy} from '../model/policy-runtime.mjs';
import {godzamokLoopPolicySource, GODZAMOK_LOOP_CYCLES, GODZAMOK_LOOP_CONTRACT} from '../model/godzamok-loop-policy.mjs';
const skip = !hasGameSource();

function prepared({amount=1,free=0,bank=2**60,discount=false}={}) {
  // Explicit funded/Pantheon boundary. This does not prove new-save reachability.
  const r=createRuntime({recordAudit:false});r.advance(200);const G=r.Game;
  G.Win('Hardcore');G.Win('Neverclick');
  const temple=G.Objects.Temple;
  r.evaluate(r.source.sources['minigamePantheon.js'],'minigamePantheon.js');
  temple.level=1;temple.amount=1;temple.highest=1;temple.bought=1;temple.locked=0;
  temple.minigame.launch();temple.minigameLoaded=true;
  const cursor=G.Objects.Cursor;
  cursor.amount=amount;cursor.highest=amount;cursor.bought=amount;cursor.free=free;cursor.locked=0;
  cursor.l.classList.remove('toggledOff');
  G.BuildingsOwned=amount+1;G.cookies=bank;G.cookiesEarned=bank*2;
  if(discount)for(const n of ['Season savings',"Santa's dominion",'Faberge egg','Divine discount','Fortune #100'])G.Upgrades[n].earn();
  G.CalculateGains();r.act({type:'pantheon-slot',god:'ruin',slot:0},{observe:false});
  return r;
}
const inputs = d => d.action?.type==='sequence' ? d.action.actions : d.action ? [d.action] : [];
function execute(r,d,onInput=()=>{}) {
  for(const a of inputs(d)){r.act(a,{observe:false});onInput(a);}
}
function run(r,options,limit=100) {
  const source=godzamokLoopPolicySource(options);let memory={},decisions=0,actions=0;
  for(;decisions<limit;decisions++) {
    const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
    if(d.status==='complete')return {memory,decisions,actions,source};
    assert.equal(d.status,'acting',d.reason);assert(inputs(d).length<=1000);
    execute(r,d,()=>actions++);
  }
  throw new Error('Diagnostic decision budget exhausted; no terminal state was asserted.');
}

test('a real1024-cycle native prefix preserves bank, earned, other holdings, prices, time and deadline',{skip},()=>{
  const r=prepared(),G=r.Game,cursor=G.Objects.Cursor;
  const before={bank:G.cookies,earned:G.cookiesEarned,clock:r.clock.now,frame:G.T,price:cursor.getPrice(),refund:Math.floor(cursor.getPrice()*cursor.getSellMultiplier()),rebuy:G.modifyBuildingPrice(cursor,15),bought:cursor.bought,total:G.BuildingsOwned,mouse:G.computedMouseCps};
  const draws=r.auditCounts().randomDrawCount;const result=run(r,{cycles:'1024',batchCycles:128});
  let expected=1;for(let i=0;i<1024;i++)expected+=.01;
  assert.equal(G.cookies,before.bank);assert.equal(G.cookiesEarned,before.earned);
  assert.equal(r.clock.now,before.clock);assert.equal(G.T,before.frame);
  assert.equal(cursor.amount,1);assert.equal(G.Objects.Temple.amount,1);assert.equal(G.BuildingsOwned,before.total);
  assert.equal(cursor.getPrice(),before.price);assert.equal(cursor.getSellMultiplier(),.25);
  assert.equal(before.refund,4);assert.equal(before.rebuy,15);
  assert.equal(cursor.bought,before.bought+1024);assert.equal(cursor.highest,1);
  assert.equal(G.buffs.Devastation.multClick,expected);assert.equal(G.buffs.Devastation.time,300);
  assert.equal(G.recalculateGains,1);assert.equal(G.computedMouseCps,before.mouse,'gains wait for a real frame');
  assert.equal(result.memory.completedCycles,'1024');assert.equal(result.memory.remainingCycles,'0');
  assert.equal(result.memory.originalCursors,1);assert.equal(result.memory.capReached,false);
  assert.equal(result.actions,8*(1+4*128));
  assert.ok(r.auditCounts().randomDrawCount>draws,'native sound selection draws are retained');
});

test('free-copy floors and current native discounts remain ordinary source transactions',{skip},()=>{
  for(const fixture of [{free:10},{free:10,discount:true},{discount:true}]) {
    const r=prepared(fixture),G=r.Game,b=G.Objects.Cursor;
    const price=b.getPrice(),refund=Math.floor(price*b.getSellMultiplier()),bank=G.cookies;
    const result=run(r,{cycles:'257',batchCycles:249});
    assert(price<=18);assert(refund<=4);assert.equal(G.cookies,bank);
    assert.equal(b.amount,1);assert.equal(b.free,fixture.free??0);assert.equal(b.getPrice(),price);
    assert.equal(result.memory.completedCycles,'257');assert.equal(result.decisions,2);
  }
});

test('setup sells the real original holdings, retains proceeds, expires the old buff once and records the production change',{skip},()=>{
  const r=prepared({amount:100}),G=r.Game,cursor=G.Objects.Cursor,source=godzamokLoopPolicySource({cycles:'17',batchCycles:8});
  G.gainBuff('devastation',10,4);const beforeBank=G.cookies,beforeCps=G.cookiesPs;
  let d=decidePolicy(source,r.snapshot(),[],{});
  assert.deepEqual(inputs(d),[{type:'store-bulk',id:1},{type:'store-bulk',id:5},{type:'click-product',id:0},{type:'store-bulk',id:0},{type:'store-bulk',id:2},{type:'click-product',id:0}]);
  execute(r,d);const saleBank=G.cookies;assert(saleBank>beforeBank);assert.equal(cursor.amount,1);
  const setup=d.memory;d=decidePolicy(source,r.snapshot(),[],setup);
  assert.equal(d.action.type,'wait');assert.equal(d.action.milliseconds,10100);execute(r,d);
  assert(!G.hasBuff('Devastation'));assert(G.cookiesPs<beforeCps,'the lower Cursor production is not erased');
  let memory=d.memory;
  for(let n=0;n<5;n++){d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;if(d.status==='complete')break;assert.equal(d.status,'acting',d.reason);execute(r,d);}
  assert.equal(d.status,'complete');assert.equal(memory.originalCursors,100);assert.equal(cursor.amount,1);
  assert.equal(memory.beforeSetupBank,beforeBank);assert(memory.startBank>=saleBank);
  assert.equal(memory.completedCycles,'17');assert.equal(memory.startElapsedMs,10300);
});

test('the default2^56 counter is exact, lazy and never assigns a game endpoint',{skip},()=>{
  const r=prepared(),source=godzamokLoopPolicySource();
  let d=decidePolicy(source,r.snapshot(),[],{});
  assert.equal(d.memory.totalCycles,GODZAMOK_LOOP_CYCLES);assert.equal(d.memory.remainingCycles,GODZAMOK_LOOP_CYCLES);
  assert.equal(d.memory.completedCycles,'0');assert.equal(d.memory.pending.cycles,128);
  assert.equal(inputs(d).length,513);assert(inputs(d).every(a=>['store-bulk','click-product'].includes(a.type)));
  execute(r,d);d=decidePolicy(source,r.snapshot(),[],d.memory);
  assert.equal(d.memory.completedCycles,'128');assert.equal(d.memory.remainingCycles,'72057594037927808');
  assert.equal(d.memory.pending.cycles,128);assert.equal(r.Game.Objects.Cursor.amount,1);
  assert.notEqual(r.Game.buffs.Devastation.multClick,2**47);
  assert(!source.includes('Game.'));assert(!source.includes('random('));assert(!source.includes('saveExport'));
  assert.match(GODZAMOK_LOOP_CONTRACT.status,/open-source-refinement/);
});

test('each batch is checked before more actions; changed premises stop with no recovery or reset',{skip},()=>{
  const r=prepared(),source=godzamokLoopPolicySource({cycles:'5',batchCycles:2});
  const first=decidePolicy(source,r.snapshot(),[],{});execute(r,first);const good=r.snapshot();
  const mutate=[o=>o.cookies+=256,o=>o.cookiesEarned+=512,o=>o.elapsedMs++,o=>o.frame++,o=>o.buffs.Devastation.time--,
    o=>o.shop.buildings[0].price++,o=>o.shop.buildings[0].amount=2,
    o=>o.shop.buildings[6].amount++,o=>o.controls.buyBulk=10,o=>o.ascensions++,o=>o.controls.promptOn=true,
    o=>o.controls.pantheon.slots[0]=-1,o=>o.dragon.aura=1];
  for(const change of mutate){const o=structuredClone(good);change(o);const d=decidePolicy(source,o,[],first.memory);assert.equal(d.status,'blocked',change.toString());assert.equal(d.action,null);}
  const next=decidePolicy(source,good,[],first.memory);assert.equal(next.status,'acting');assert.equal(next.memory.completedCycles,'2');
});

test('entry conditions, quoted prices, resource gates and exact count configuration are explicit',{skip},()=>{
  const r=prepared(),good=r.snapshot();
  for(const change of [o=>o.cookies=2**60-128,o=>o.cookiesEarned=o.cookies-256,o=>o.dragon.aura2=1,
    o=>o.achievements.Hardcore=false,o=>o.achievements.Neverclick=false,o=>o.progression.ascensionMode=1,
    o=>o.progression.minigames.Temple=false,o=>o.controls.menu='stats',o=>o.shop.buildings[0].amount=1001]) {
    const o=structuredClone(good);change(o);const d=decidePolicy(godzamokLoopPolicySource(),o,[],{});assert.equal(d.status,'deferred',change.toString());assert.equal(d.action,null);
  }
  for(const change of [o=>o.shop.buildings[0].rebuyOnePrice=16,o=>o.shop.buildings[0].price=19]){
    const o=structuredClone(good);change(o);const d=decidePolicy(godzamokLoopPolicySource(),o,[],{});assert.equal(d.status,'blocked');assert.equal(d.action,null);
  }
  for(const options of [{cycles:2**56},{cycles:'72057594037927937'},{cycles:'0'},{cycles:'1.0'},{batchCycles:0},{batchCycles:250}]){
    const d=decidePolicy(godzamokLoopPolicySource(options),good,[],{});assert.equal(d.status,'blocked');assert.equal(d.action,null);
  }
});

test('native bought-counter saturation is retained and does not change one-copy prices',{skip},()=>{
  const r=prepared(),G=r.Game;G.Objects.Cursor.bought=2**53;
  const {memory}=run(r,{cycles:'9',batchCycles:4});
  assert.equal(G.Objects.Cursor.bought,2**53);assert.equal(G.Objects.Cursor.amount,1);
  assert.equal(G.cookies,2**60);assert.equal(memory.completedCycles,'9');
});


test('a separately prepared near-cap boundary stops after native saturation, without unused batches',{skip},()=>{
  const r=prepared(),source=godzamokLoopPolicySource({cycles:'1024',batchCycles:2});
  const d=decidePolicy(source,r.snapshot(),[],{}),m=structuredClone(d.memory);
  // This prepares a scalar/source boundary and the matching controller receipt.
  // It does not execute or certify the enormous preceding prefix.
  const near=2**47-2**-5;r.Game.gainBuff('devastation',10,near);
  m.multiplier=near;let expected=near;for(let i=0;i<2;i++)expected+=.01;
  m.pending.multiplier=expected;
  assert.notEqual(r.Game.buffs.Devastation.multClick,2**47);
  execute(r,d);assert.equal(r.Game.buffs.Devastation.multClick,2**47);
  const publicView=r.snapshot();delete publicView.buffs.Devastation.multClick;
  const done=decidePolicy(source,publicView,[],m);
  assert.equal(done.status,'complete');assert.equal(done.action,null);
  assert.equal(done.memory.stopReason,'recurrence-cap');assert.equal(done.memory.completedCycles,'2');
  assert.equal(done.memory.remainingCycles,'1022');assert.equal(done.memory.capReached,true);
});


test('the controller does not read exact native buff multipliers',{skip},()=>{
  const r=prepared(),source=godzamokLoopPolicySource({cycles:'4',batchCycles:2});
  assert(!source.includes('multClick'));
  let memory={};
  for(let i=0;i<3;i++){
    const o=r.snapshot();for(const buff of Object.values(o.buffs))delete buff.multClick;
    const d=decidePolicy(source,o,[],memory);memory=d.memory;
    if(i===2){assert.equal(d.status,'complete');assert.equal(d.action,null);}
    else {assert.equal(d.status,'acting');execute(r,d);}
  }
  let expected=1;for(let i=0;i<4;i++)expected+=.01;
  assert.equal(r.Game.buffs.Devastation.multClick,expected,'the separate test may inspect native state');
});
