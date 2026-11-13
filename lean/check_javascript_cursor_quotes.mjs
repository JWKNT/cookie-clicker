/** Finite pinned quote/helper comparisons. Supplied entry frames are not new-save reachability proofs. */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {createRuntime} from '../model/runtime.mjs';
import {inspectNativeEngine,runNativeEngine} from '../model/native-engine.mjs';
if (!process.argv.includes('--engine')) throw new Error('Pass --engine for the pinned native comparison.');
const root=fileURLToPath(new URL('..',import.meta.url));
const sha=text=>createHash('sha256').update(text).digest('hex');
const bits=n=>{const b=Buffer.alloc(8);b.writeDoubleBE(n);return b.readBigUInt64BE().toString();};
const r=createRuntime({recordAudit:false});r.advance(200);const G=r.Game,c=G.Objects.Cursor,t=G.Objects.Temple;
r.evaluate(r.source.sources['minigamePantheon.js'],'minigamePantheon.js');
Object.assign(t,{level:1,amount:1,highest:1,bought:1,locked:0});t.minigame.launch();t.minigameLoaded=true;
t.minigame.slot[0]=t.minigame.gods.ruin.id;
G.volume=0;G.ascensionMode=0;G.dragonAura=0;G.dragonAura2=0;
const names=["Season savings","Santa's dominion","Faberge egg","Divine discount","Fortune #100",c.fortune.name];
const gameFns=Object.fromEntries(['Has','hasAura','auraMult','hasBuff','eff','hasGod','modifyBuildingPrice'].map(k=>[k,G[k].toString()]));
const cursorFns=Object.fromEntries(['getPrice','getSumPrice','getReverseSumPrice','getSellMultiplier'].map(k=>[k,c[k].toString()]));
const fixture={game:{ascensionMode:0,priceIncrease:G.priceIncrease,dragonAura:0,dragonAura2:0,dragonLevel:G.dragonLevel,
  dragonAuras:[{name:G.dragonAuras[0].name}],Upgrades:Object.fromEntries(names.map(n=>[n,{name:n,bought:0,pool:G.Upgrades[n].pool,tier:G.Upgrades[n].tier}])),buffs:{},effs:{}},
  pantheon:{gods:{creation:{id:t.minigame.gods.creation.id}},slot:Array.from(t.minigame.slot)},
  cursor:{basePrice:c.basePrice,fortune:{name:c.fortune.name}},gameFns,cursorFns};
const cases=[];
for(const free of [0,10])for(const owned of [0,1]){
  Object.assign(c,{free,amount:owned});
  const before={amount:c.amount,free:c.free,draws:r.auditCounts().randomDrawCount,bank:G.cookies,time:r.clock.now};
  const values=[c.getPrice(),c.getSumPrice(1),c.getReverseSumPrice(1),c.getSellMultiplier()];
  assert.deepEqual(values,[owned&&!free?18:15,owned&&!free?18:15,owned?4:0,.25]);
  assert.deepEqual({amount:c.amount,free:c.free,draws:r.auditCounts().randomDrawCount,bank:G.cookies,time:r.clock.now},before);
  cases.push({free,owned,values,bits:values.map(bits)});
}
const script=String.raw`
var fs=require('fs'),vm=require('vm'),input=JSON.parse(fs.readFileSync(0,'utf8'));var scope={Game:input.fixture.game,M:input.fixture.pantheon};vm.createContext(scope);
Object.keys(input.fixture.gameFns).forEach(function(k){scope.Game[k]=vm.runInContext('('+input.fixture.gameFns[k]+')',scope);});
var cursor=input.fixture.cursor;scope.cursor=cursor;Object.keys(input.fixture.cursorFns).forEach(function(k){cursor[k]=vm.runInContext('('+input.fixture.cursorFns[k]+')',scope);});
var rows=input.cases.map(function(row){cursor.amount=row.owned;cursor.free=row.free;return [cursor.getPrice(),cursor.getSumPrice(1),cursor.getReverseSumPrice(1),cursor.getSellMultiplier()].map(function(n){var b=Buffer.alloc(8);b.writeDoubleBE(n);return b.readBigUInt64BE().toString();});});
process.stdout.write(JSON.stringify(rows));`;
const engine=inspectNativeEngine();
const actual=runNativeEngine(script,{fixture,cases});
assert.deepEqual(actual,cases.map(c=>c.bits));
const receipt={schemaVersion:1,scope:'Finite differential check of actual pinned quote and nested helper source in supplied no-discount/no-aura/Pantheon fixtures. Native helper bodies are unchanged. This is not a physical input, new-save reachability, arbitrary-cycle, or whole-engine refinement proof.',
  engine,sourceMainSha256:r.source.hashes['main.js'],sourcePantheonSha256:r.source.hashes['minigamePantheon.js'],
  hashes:Object.fromEntries(['model/runtime.mjs','model/game-source.mjs','model/native-engine.mjs'].map(n=>[n,sha(readFileSync(root+'/'+n))])),
  functions:Object.fromEntries([...Object.entries(gameFns),...Object.entries(cursorFns)].map(([k,v])=>[k,sha(v)])),
  cases,nativeComparisons:cases.length*4,freeRandomDrawsDuringQuotes:0,notes:['The reverse quote at amount1 is4. The sale refund uses floor and is3.','After sale, amount0 yields reverse quote0. After buyback, the sum quote is18 without free copies and15 with10 free copies.']};
console.log(JSON.stringify({cases:cases.length,nativeComparisons:receipt.nativeComparisons,engine:engine.versions.electron,gameEntryPointExecuted:false}));
