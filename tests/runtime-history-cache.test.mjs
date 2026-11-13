import test from 'node:test';
import assert from 'node:assert/strict';
import {createRuntime} from '../model/runtime.mjs';
import {hasGameSource} from '../model/game-source.mjs';
const skip=!hasGameSource();

function checkedRuntime(options={}){
 let runtime,checks=0;const expected=new Set();
 const check=()=>{
  if(!runtime)return;
  // Independent reference: the original full scan at every retained boundary.
  for(const u of Object.values(runtime.Game.Upgrades))if(u.unlocked||u.bought)expected.add(u.name);
  assert.deepEqual(runtime.snapshot().history.accessedUpgrades,[...expected].sort());checks++;
 };
 runtime=createRuntime({...options,onTransition:check});check();
 return {runtime,check,checks:()=>checks};
}

test('history worklist matches a full reference scan through native actions and maintenance',{skip},()=>{
 const c=checkedRuntime({randomSeed:37,maintenanceReload:{atMs:[400]}}),r=c.runtime;
 r.act({type:'wait',milliseconds:200});
 for(let i=0;i<40;i++){r.act({type:'wait',milliseconds:20});r.act({type:'click'});}
 r.act({type:'wait',milliseconds:1000});
 assert.equal(r.auditCounts().reloadCount,1);assert(c.checks()>100);c.check();
});

test('history retains relocked names and validates native constructor additions',{skip},()=>{
 const c=checkedRuntime(),r=c.runtime;
 // Supplied catalogue boundary only: each addition runs the native constructor.
 for(const name of ['History probe','History duplicate','History duplicate']){
  r.evaluate(`new Game.Upgrade(${JSON.stringify(name)},'diagnostic',1,[0,0]);Game.Upgrades[${JSON.stringify(name)}].unlocked=1;`);
  r.remember();c.check();r.evaluate(`Game.Upgrades[${JSON.stringify(name)}].unlocked=0;`);c.check();
 }
 assert(r.snapshot().history.accessedUpgrades.includes('History probe'));
 assert(r.snapshot().history.accessedUpgrades.includes('History duplicate'));
});

test('reused timer dispatch reads the current callback, arguments and realm receiver',{skip},()=>{
 const r=createRuntime();
 r.evaluate("window.dispatchReceipts=[];setTimeout(function(x){dispatchReceipts.push(['first',x,this===window]);},0,7);setTimeout(function(x){dispatchReceipts.push(['second',x,this===window]);},0,9);");
 r.advance(1);
 assert.deepEqual(JSON.parse(r.evaluate('JSON.stringify(dispatchReceipts)')),[['first',7,true],['second',9,true]]);
});
