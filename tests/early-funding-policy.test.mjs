import test from 'node:test';
import assert from 'node:assert/strict';
import {createRuntime} from '../model/runtime.mjs';
import {hasGameSource} from '../model/game-source.mjs';
import {earlyFundingPolicySource} from '../model/early-funding-policy.mjs';
import {completionPolicySource} from '../model/completion-policy.mjs';
import {decidePolicy} from '../model/policy-runtime.mjs';
const skip=!hasGameSource();
function prepared(bank=200000,options={}){
 // A supplied boundary tests actual transactions; it is not a new-save route.
 const r=createRuntime({recordAudit:false,...options}),G=r.Game;r.advance(200);
 G.Win('Hardcore');G.Win('Neverclick');
 for(const name of ['Reinforced index finger','Carpal tunnel prevention cream','Ambidextrous','Plastic mouse'])G.Upgrades[name].earn();
 const t=G.Objects.Temple,b=G.Objects.Cursor;
 r.evaluate(r.source.sources['minigamePantheon.js'],'minigamePantheon.js');
 t.level=1;t.amount=1;t.highest=1;t.bought=1;t.locked=0;t.minigame.launch();t.minigameLoaded=true;
 b.amount=10;b.bought=10;b.highest=10;b.locked=0;b.l.classList.remove('toggledOff');G.BuildingsOwned=11;
 G.cookies=bank;G.cookiesEarned=bank*2;G.CalculateGains();r.act({type:'pantheon-slot',god:'ruin',slot:0},{observe:false});return r;
}
function execute(r,d){for(const a of d.action.type==='sequence'?d.action.actions:[d.action])r.act(a,{observe:false});}
test('a bounded native low-bank burst spends actual prices and then earns through400acceptedclicks',{skip},()=>{
 const r=prepared(),source=earlyFundingPolicySource({cycles:1024,batchCycles:128});let memory={},d,actions=0;
 const before=r.snapshot();
 for(let i=0;i<30;i++){
  d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
  if(d.status==='complete')break;
  assert.equal(d.status,'acting',d.reason);actions+=d.action.type==='sequence'?d.action.actions.length:1;execute(r,d);
 }
 assert.equal(d.status,'complete');assert.equal(memory.completed,1024);assert.equal(memory.acceptedClicks,400);
 assert.equal(r.Game.Objects.Cursor.amount,1);assert(r.Game.cookies>before.cookies);
 assert(r.Game.cookiesEarned>before.cookiesEarned);assert(r.snapshot().elapsedMs>before.elapsedMs);
 assert(actions>4000);assert(!source.includes('Game.'));assert(!source.includes('random('));
});
test('unchanged same-time source gates are checked before issuing another native batch',{skip},()=>{
 const r=prepared(),source=earlyFundingPolicySource({cycles:4,batchCycles:2});let m={};
 for(let n=0;n<5;n++){const d=decidePolicy(source,r.snapshot(),[],m);m=d.memory;execute(r,d);if(m.phase==='cycles')break;}
 const o=r.snapshot();o.elapsedMs++;
 const d=decidePolicy(source,o,[],m);assert.equal(d.status,'blocked');assert.equal(d.action,null);
});
test('new bursts defer before challenges, without nativePantheon, withoutPlasticmouse, or withoutreservedbank',{skip},()=>{
 const r=prepared(),good=r.snapshot(),source=earlyFundingPolicySource({cycles:4});
 for(const mutate of [o=>o.achievements.Hardcore=false,o=>o.controls.pantheon.slots[0]=-1,o=>o.upgrades['Plastic mouse'].bought=false,o=>o.cookies=100000]){
  const o=structuredClone(good);mutate(o);const d=decidePolicy(source,o,[],{});assert.equal(d.status,'deferred');assert.equal(d.action,null);
 }
});

test('the composed early opening withholds One mind until the first Temple level',{skip},()=>{
 const r=createRuntime();for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press','Hardcore','Neverclick'])r.Game.Win(n);
 const u=r.Game.Upgrades['One mind'];u.unlocked=1;r.Game.cookies=10*u.getPrice();
 const memory={restoreViewport:true,growth:{nextClick:100,nextPurchase:0}};
 let d=decidePolicy(completionPolicySource(),r.snapshot(),[],memory);
 assert.notDeepEqual(d.action,{type:'buy-upgrade',id:u.id});assert.equal(u.bought,0);
 r.Game.Objects.Temple.level=1;d=decidePolicy(completionPolicySource(),r.snapshot(),[],memory);
 assert.deepEqual(d.action,{type:'buy-upgrade',id:u.id});
});

test('the full scheduler owns a bounded burst through its actual click receipt',{skip},()=>{
 const r=prepared();for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press'])r.Game.Win(n);
 const source=completionPolicySource({clickRate:50,earlyFunding:{cycles:16,batchCycles:8}});
 let memory={restoreViewport:true,growth:{nextClick:100000,nextPurchase:0}},issued=false,finished=false;
 for(let i=0;i<20;i++){
  const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
  if(memory.nextFundingAt){finished=true;break;}
  if(d.stage==='early-income-pantheon'){assert(!issued);execute(r,d);continue;}
  assert.equal(d.stage,'early-income-burst');issued=true;execute(r,d);
 }
 assert(issued);assert(finished);assert.equal(memory.earlyFunding,undefined);
 assert.equal(r.Game.cookieClicks,400);assert.equal(r.Game.Objects.Cursor.amount,1);
 assert(memory.nextFundingAt>r.snapshot().elapsedMs);
});

test('a funded100-Cursor native batch increases the buff through real sales and pays real bulk costs',{skip},()=>{
 const r=prepared(2**50),G=r.Game;
 // Supplied production boundary only; no new-save reachability is asserted.
 const t=G.Objects['Time machine'];t.amount=1000;t.highest=1000;t.bought=1000;t.locked=0;G.BuildingsOwned+=1000;G.CalculateGains();
 const source=earlyFundingPolicySource({cycles:64,batchCycles:32});let memory={},done;
 const before=G.cookies,earned=G.cookiesEarned;
 for(let i=0;i<12;i++){
  const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
  if(d.status==='complete'){done=d;break;}
  assert.equal(d.status,'acting',d.reason);execute(r,d);
 }
 assert(done);assert.equal(memory.amount,100);assert.equal(memory.completed,64);
 assert.equal(G.Objects.Cursor.amount,100);assert.equal(memory.acceptedClicks,400);
 assert(G.buffs.Devastation.multClick>64);assert(G.cookies>before);assert(G.cookiesEarned>earned);
 assert.equal(G.Objects['Time machine'].amount,1000);
});

test('the composed zero-click policy does not activate default funding clicks',{skip},()=>{
 const r=prepared();for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press'])r.Game.Win(n);
 r.act({type:'minigame-open',id:6});
 const memory={restoreViewport:true,growth:{nextClick:100000,nextPurchase:100000}};
 const d=decidePolicy(completionPolicySource({clickRate:0}),r.snapshot(),[],memory);
 assert.notEqual(d.stage,'early-income-burst');
 assert(!(d.action.type==='click'||d.action.type==='sequence'&&d.action.actions.some(a=>a.type==='click')));
 const explicit=decidePolicy(completionPolicySource({clickRate:0,earlyFunding:{clickRate:50,cycles:4}}),r.snapshot(),[],memory);
 assert.equal(explicit.stage,'early-income-burst');
});

test('consecutive bursts wait for a short old duration because sales do not refresh it',{skip},()=>{
 const r=prepared(1e9),source=earlyFundingPolicySource({cycles:32,batchCycles:16});let expiryWaits=0;
 for(let burst=0;burst<2;burst++){
  let memory={},done=false;
  for(let i=0;i<20;i++){
   const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
   if(d.status==='complete'){done=true;break;}
   assert.equal(d.status,'acting',d.reason);if(memory.phase==='expiry')expiryWaits++;
   const actions=d.action.type==='sequence'?d.action.actions:[d.action];
   for(const a of actions){if(a.type==='click')assert(r.Game.hasBuff('Devastation'),'every click retains the native buff');r.act(a,{observe:false});}
  }
  assert(done);assert.equal(memory.acceptedClicks,400);
 }
 assert.equal(expiryWaits,1);assert.equal(r.Game.cookieClicks,800);
});


test('the duration gate covers the33ms logic cadence before an eight-second click burst',{skip},()=>{
 const r=prepared(1e9);
 // This supplied buff boundary discriminates nominal30fps from33ms ticks.
 // A fresh native sale makes the buff; elapsed time consumes its real ticks.
 r.act({type:'store-bulk',id:1},{observe:false});r.act({type:'store-bulk',id:2},{observe:false});r.act({type:'click-product',id:0},{observe:false});
 r.advance(1500);
 assert(r.Game.buffs.Devastation.time/r.Game.fps>8.1);assert(r.Game.buffs.Devastation.time/r.Game.fps<9);
 const source=earlyFundingPolicySource({cycles:4});let memory={},d;
 for(let i=0;i<3;i++){d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;if(memory.phase==='expiry')break;assert.equal(d.status,'acting');execute(r,d);}
 assert.equal(memory.phase,'expiry');assert.equal(d.action.type,'wait');
 execute(r,d);assert.equal(r.Game.hasBuff('Devastation'),0);
});


test('a scheduled current-save reload retains partial clicks and interrupts rather than certifies a burst',{skip},()=>{
 const r=prepared(1e9,{maintenanceReload:{atMs:[4000]}}),source=earlyFundingPolicySource({cycles:32,batchCycles:16});let memory={},d;
 for(let i=0;i<20;i++){
  d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
  if(d.status!=='acting')break;execute(r,d);
 }
 assert.equal(r.auditCounts().reloadCount,1);assert.equal(d.status,'interrupted');assert.equal(d.exclusive,false);
 assert(memory.acceptedClicks>0&&memory.acceptedClicks<400);assert.equal(memory.acceptedClicks,r.Game.cookieClicks);
 assert.equal(memory.afterBank,r.Game.cookies);assert.equal(memory.afterEarned,r.Game.cookiesEarned);
 assert.equal(r.Game.buffs.Devastation.multClick,1.1,'native save retains initial arg1, not the later stacked multiplier');
});

test('the composed controller releases an interrupted burst and returns to actual native funding',{skip},()=>{
 const r=prepared(1e9,{maintenanceReload:{atMs:[4000]}});
 for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press'])r.Game.Win(n);
 const source=completionPolicySource({clickRate:50,earlyFunding:{cycles:32,batchCycles:16}});
 let memory={restoreViewport:true,growth:{nextClick:100000,nextPurchase:0}},interrupted=false,resumed=false;
 for(let i=0;i<40;i++){
  const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
  if(d.stage==='early-income-interrupted'){interrupted=true;assert.equal(memory.earlyFunding,undefined);assert.equal(d.action.type,'wait');}
  if(interrupted&&memory.earlyFunding?.phase==='cycles')resumed=true;
  execute(r,d);
  if(resumed&&memory.nextFundingAt&&r.Game.cookieClicks>700)break;
 }
 assert(interrupted);assert(resumed);assert.equal(r.auditCounts().reloadCount,1);assert(r.Game.cookieClicks>700);
});


test('growth during Cursor funding invests in another building instead of its next disposable Cursor',{skip},()=>{
 const r=prepared(1e9);for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press'])r.Game.Win(n);
 r.act({type:'minigame-open',id:6});r.advance(100);
 const options={clickRate:50,combo:{configurePantheon:false,godzamok:false}};
 const memory={restoreViewport:true,growth:{nextClick:1e9,nextPurchase:0},nextFundingAt:1e9},o=r.snapshot();
 const old=decidePolicy(completionPolicySource({...options,earlyFunding:{enabled:false}}),o,[],memory);
 assert.equal(old.action.type,'buy-building');assert.equal(old.action.id,0);
 const d=decidePolicy(completionPolicySource(options),o,[],memory);
 assert.equal(d.stage,'early-income-growth');assert.equal(d.action.type,'buy-building');assert.notEqual(d.action.id,0);
 assert.equal(o.shop.buildings[0].locked,false,'the public observation remains unchanged');
 const cursor=r.Game.Objects.Cursor.amount,b=r.Game.ObjectsById[d.action.id],before=b.amount;execute(r,d);
 assert.equal(b.amount,before+1);assert.equal(r.Game.Objects.Cursor.amount,cursor);
});


test('a maintenance preload waits for observed persistent progress instead of treating it as a new save',{skip},()=>{
 // Supplied pre-maintenance boundary only; this is not a new-save route.
 const r=prepared(1e9,{maintenanceReload:{atMs:[210]}});r.Game.resets=3;
 for(const n of ["What's in a name",'Tiny cookie','Here you go','Olden days','Tabloid addiction','Stifling the press'])r.Game.Win(n);
 r.act({type:'minigame-open',id:6});r.advance(50);
 const source=completionPolicySource({clickRate:50,earlyFunding:{cycles:4,batchCycles:4}});
 let memory={restoreViewport:true,growth:{nextClick:1e9,nextPurchase:1e9}};
 let d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
 assert.equal(memory.run,3);assert.equal(memory.hardcoreObserved,true);execute(r,d);
 assert.equal(r.Game.resets,0);assert.equal(r.Game.Achievements.Hardcore.won,0);
 d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
 assert.equal(d.stage,'current-save-restoration');assert.equal(d.action.type,'wait');assert.equal(memory.run,3);execute(r,d);
 assert.equal(r.Game.resets,3);assert.equal(r.Game.Achievements.Hardcore.won,1);
 d=decidePolicy(source,r.snapshot(),[],memory);assert.notEqual(d.stage,'current-save-restoration');
 assert.equal(r.auditCounts().reloadCount,1);
});
