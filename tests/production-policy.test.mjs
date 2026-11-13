import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { decidePolicy } from '../model/policy-runtime.mjs';
import { decideProductionAction,productionPolicySource } from '../model/production-policy.mjs';
const skip=!hasGameSource()&&'Pinned Steam source unavailable';
const options={finalCollection:true,preserveChallengeAchievements:false,buyOrdinaryUpgrades:false,clickRate:0};
function funded(){const r=createRuntime();r.Game.cookies=r.Game.cookiesEarned=1e100;r.advance(1000);return r;}

test('production metadata preserves native binary64 thresholds and distinguishes raw CpS', {skip},()=>{
 const r=createRuntime();const o=r.snapshot();
 assert.equal(o.production.bankAchievements.at(-1).threshold,1e72);
 assert.equal(o.production.cpsAchievements.at(-1).threshold,1e56);
 assert.equal(o.production.handmadeAchievements.at(-1).threshold,1e31);
 assert.equal(o.shop.buildings[0].countAchievements.length,13);
 for(const b of o.shop.buildings){assert.equal(b.goalAmount,b.id===0?1000:700);assert.deepEqual(b.productionAchievements,Array.from(r.Game.ObjectsById[b.id].productionAchievs,a=>({name:a.achiev.name,threshold:a.pow})));}
 assert.equal(decideProductionAction(o).status,'deferred');
 assert.equal(decideProductionAction(o,{}, {finalCollection:true}).status,'needs-achievement');
});

test('the observation-only controller buys all final count targets through native batches', {skip},()=>{
 const r=funded();let memory={};const source=productionPolicySource(options);
 for(let i=0;i<20;i++){
  const o=r.snapshot();const d=decideProductionAction(o,memory,options);
  assert.deepEqual(decidePolicy(source,o,[],memory),d);memory=d.memory;
  assert.equal(d.action.type,'buy-building');r.act(d.action);
 }
 r.advance(5000);
 const o=r.snapshot();
 for(const b of o.shop.buildings){assert.equal(b.amount,b.goalAmount,b.name);for(const a of b.countAchievements)assert.equal(r.Game.HasAchiev(a.name),1,a.name);}
 assert.equal(r.Game.HasAchiev('Septcentennial'),1);
 const decision=decideProductionAction(o,memory,options);
 assert.equal(decision.status,'needs-production');assert.equal(decision.requiredRawCps,1e56);
 assert.equal(decision.requiredHandmadeCookies,1e31);
 assert.equal(decision.missingProduction.length,60);
});

test('native production counters cross their real award boundary under scheduled frames', {skip},()=>{
 const r=funded();r.act({type:'buy-building',id:2,amount:1});r.advance(100);
 const b=r.Game.Objects.Farm;const a=b.productionAchievs[0];
 // Synthetic near-boundary total. Production and achievement checks remain unmodified.
 b.totalCookies=a.pow-(b.storedTotalCps*r.Game.globalCpsMult)/r.Game.fps/2;
 r.Game.T=149;r.advance(67);
 assert(b.totalCookies>=a.pow);assert.equal(r.Game.HasAchiev(a.achiev.name),1);
 assert.equal(r.snapshot().shop.buildings[2].totalCookies,b.totalCookies);
});

test('a huge temporary frenzy does not satisfy the raw-CpS family; native prestige production does', {skip},()=>{
 const r=funded();r.act({type:'buy-building',id:0,amount:1});r.advance(100);
 r.Game.gainBuff('frenzy',77,1e60);r.Game.CalculateGains();
 const target=r.Game.CpsAchievements.at(-1);
 assert(r.Game.cookiesPs>target.threshold);assert(r.Game.cookiesPsRaw<target.threshold);
 assert.equal(r.Game.HasAchiev(target.name),0);
 // Funded prestige fixture, not a claimed legal new-save progression.
 r.Game.prestige=1e60;r.Game.Upgrades.Legacy.earn();r.Game.Upgrades['Heavenly key'].earn();r.Game.CalculateGains();
 assert(r.Game.cookiesPsRaw>=target.threshold);assert.equal(r.Game.HasAchiev(target.name),1);
});

test('native click and earned-cookie checks award the first handmade and final bank goals', {skip},()=>{
 const r=createRuntime();r.advance(1000);
 r.Game.handmadeCookies=999;r.act({type:'click'});r.advance(5000);
 assert.equal(r.Game.HasAchiev('Clicktastic'),1);assert.equal(r.Game.Upgrades['Plastic mouse'].unlocked,1);
 // Synthetic earned-cookie boundary; a native Earn call crosses it before the scheduled check.
 const target=r.Game.BankAchievements.at(-1);r.Game.cookiesEarned=target.threshold*(1-1e-10);
 r.Game.Earn(target.threshold*1e-10*2);r.advance(5000);
 assert.equal(r.Game.HasAchiev(target.name),1);
});
