import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRuntime} from '../model/runtime.mjs';
import {decidePolicy, EXECUTION_RUNTIME} from '../model/policy-runtime.mjs';
import {godzamokLoopPolicySource,GODZAMOK_LOOP_CONTRACT} from '../model/godzamok-loop-policy.mjs';

const check=process.argv.includes('--check');
const paths=process.argv.slice(2).filter(arg=>arg!=='--check');
if(paths.length>1 || paths.some(arg=>arg.startsWith('--')))throw new Error('Use at most one output path and optional --check.');
const out=paths[0] || new URL('../model/godzamok-loop-witness.json',import.meta.url);
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
const cases=[];
for(const config of [
  {name:'fresh-1024',amount:1,free:0,cycles:1024,bank:2**60},
  {name:'free-floor-257',amount:1,free:10,cycles:257,bank:2**60},
  {name:'discounts-257',amount:1,free:0,cycles:257,bank:2**60+256,discount:true},
  {name:'lower-binade-257',amount:1,free:0,cycles:257,bank:2**61-256},
  {name:'actual-setup-129',amount:100,free:10,cycles:129,bank:2**60},
  {name:'bought-counter-stalled-257',amount:1,free:0,cycles:257,bank:2**60,bought:2**53},
]) {
  // These are explicit entry boundaries, not saved-player data or new-save routes.
  const r=createRuntime({recordAudit:false}),G=r.Game;r.advance(200);
  G.Win('Hardcore');G.Win('Neverclick');
  const temple=G.Objects.Temple,cursor=G.Objects.Cursor;
  r.evaluate(r.source.sources['minigamePantheon.js'],'minigamePantheon.js');
  temple.level=1;temple.amount=1;temple.highest=1;temple.bought=1;temple.locked=0;
  temple.minigame.launch();temple.minigameLoaded=true;
  cursor.amount=config.amount;cursor.highest=config.amount;cursor.bought=config.bought??config.amount;
  cursor.free=config.free;cursor.locked=0;cursor.l.classList.remove('toggledOff');
  G.BuildingsOwned=config.amount+1;G.cookies=config.bank;G.cookiesEarned=config.bank*2;
  if(config.discount)for(const name of ['Season savings',"Santa's dominion",'Faberge egg','Divine discount','Fortune #100'])G.Upgrades[name].earn();
  G.CalculateGains();r.act({type:'pantheon-slot',god:'ruin',slot:0},{observe:false});
  const snapshot=()=>({bank:G.cookies,earned:G.cookiesEarned,elapsedMs:r.snapshot().elapsedMs,frame:G.T,
    cursor:{amount:cursor.amount,bought:cursor.bought,free:cursor.free,highest:cursor.highest,price:cursor.getPrice(),
      sellMultiplier:cursor.getSellMultiplier()},templeAmount:temple.amount,totalBuildings:G.BuildingsOwned,
    cps:G.cookiesPs,mouseCps:G.computedMouseCps,recalculateGains:G.recalculateGains,
    buff:G.hasBuff('Devastation')?{multClick:G.buffs.Devastation.multClick,time:G.buffs.Devastation.time,maxTime:G.buffs.Devastation.maxTime}:null,
    counts:r.auditCounts()});
  const before=snapshot(),source=godzamokLoopPolicySource({cycles:String(config.cycles),batchCycles:128});
  let memory={},decisions=0,actionCount=0,waitCount=0,batches=0,loopEntry=null;
  const historyHash=createHash('sha256'),batchReceipts=[];
  for(;decisions<100;decisions++){
    const d=decidePolicy(source,r.snapshot(),[],memory);memory=d.memory;
    if(d.status==='complete')break;
    assert.equal(d.status,'acting',d.reason);
    if(memory.phase==='counting' && !loopEntry)loopEntry=snapshot();
    const flat=d.action.type==='sequence'?d.action.actions:[d.action];
    for(const a of flat){
      assert(['store-bulk','click-product','wait'].includes(a.type));
      historyHash.update(JSON.stringify(a)+'\n');r.act(a,{observe:false});actionCount++;
      if(a.type==='wait')waitCount++;
      if(memory.phase==='counting'){
        // Check after every individual store input, not only batch endpoints.
        assert.equal(G.cookies,loopEntry.bank);assert.equal(G.cookiesEarned,loopEntry.earned);
        assert.equal(r.clock.now-r.environment.epochMs,loopEntry.elapsedMs);assert.equal(G.T,loopEntry.frame);
        assert.equal(temple.amount,1);assert.equal(cursor.free,config.free);
        assert.equal(cursor.getSellMultiplier(),.25);
        if(a.type==='click-product')assert.equal(cursor.amount,G.buyMode===-1?0:1);
        assert.equal(G.BuildingsOwned,1+cursor.amount);
        if(G.hasBuff('Devastation')){
          assert.equal(G.buffs.Devastation.time,300);assert.equal(G.buffs.Devastation.maxTime,300);
        }
      }
    }
    if(memory.phase==='counting'){
      batches++;const actual=snapshot();
      assert.equal(actual.bank,loopEntry.bank);assert.equal(actual.earned,loopEntry.earned);
      assert.equal(actual.elapsedMs,loopEntry.elapsedMs);assert.equal(actual.frame,loopEntry.frame);
      assert.equal(actual.cursor.amount,1);assert.equal(actual.cursor.free,config.free);
      assert.equal(actual.cursor.price,loopEntry.cursor.price);assert.equal(actual.cursor.sellMultiplier,.25);
      assert.equal(actual.templeAmount,1);assert.equal(actual.totalBuildings,2);
      assert.equal(actual.buff.multClick,memory.pending.multiplier);assert.equal(actual.buff.time,300);
      assert.equal(actual.buff.maxTime,300);assert.equal(actual.recalculateGains,1);
      batchReceipts.push({issued:memory.pending.cycles,confirmedBefore:memory.completedCycles,multClick:actual.buff.multClick,
        bank:actual.bank,earned:actual.earned,time:actual.buff.time,maxTime:actual.buff.maxTime,elapsedMs:actual.elapsedMs,
        cursorAmount:actual.cursor.amount,cursorBought:actual.cursor.bought,price:actual.cursor.price});
    }
  }
  assert(decisions<100);assert.equal(memory.completedCycles,String(config.cycles));
  let expected=1;for(let i=0;i<config.cycles;i++)expected+=.01;
  assert.equal(G.buffs.Devastation.multClick,expected);
  cases.push({fixture:config,before,loopEntry,after:snapshot(),decisions,actionCount,waitCount,batches,
    expandedActionsSha256:historyHash.digest('hex'),policySha256:sha(source),memory,individualInputChecks:true,batchReceipts});
}
const witness={schemaVersion:1,scope:'Pinned-source short-prefix diagnostics at explicitly supplied funded/Pantheon boundaries. No complete 2^56-cycle execution, new-save funding, physical-input refinement, expected-time or optimality claim.',
  contract:GODZAMOK_LOOP_CONTRACT,sourceHashes:createRuntime({recordAudit:false}).source.hashes,executionRuntime:EXECUTION_RUNTIME,
  fileHashes:Object.fromEntries(['model/godzamok-loop-policy.mjs','model/runtime.mjs','model/policy-runtime.mjs','tools/probe-godzamok-loop.mjs'].map(name=>[name,sha(readFileSync(new URL('../'+name,import.meta.url)))])),
  cases};
if(check)assert.deepEqual(witness,JSON.parse(readFileSync(out,'utf8')),'The finite Godzamok witness is stale.');
else writeFileSync(out,JSON.stringify(witness,null,2)+'\n');
console.log(JSON.stringify({check,cases:cases.length,executedCycles:cases.reduce((n,c)=>n+c.fixture.cycles,0),out:String(out)}));
