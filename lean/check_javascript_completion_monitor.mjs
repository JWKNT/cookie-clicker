/** Source microstate tests. Synthetic terminal fixtures are not new-save routes. */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
import {r} from './completion-fixtures.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {captureCompletionSnapshot,assessCompletion} from '../model/completion.mjs';
import {runNativeEngine} from '../model/native-engine.mjs';

const catalogue=JSON.parse(readFileSync(new URL('../model/catalogue.json',import.meta.url)));
const terminal={version:2.053,dragonLevel:r.dragonLevel,santaLevel:r.santaLevel,
  ascensionMode:0,OnAscend:0,AscendTimer:0,ReincarnateTimer:0,AchievementsOwned:599,
  Achievements:Object.fromEntries(r.normalAchievements.map(({name})=>[name,{name,won:1}])),
  Upgrades:Object.fromEntries([...r.ownedUpgrades,...r.accessUpgrades].map(({name,id})=>[name,{name,id,bought:1,unlocked:1}])),
  Objects:Object.fromEntries(catalogue.buildings.map(({name})=>[name,{name,level:12,amount:name==='Farm'?300:1,highest:1,
    minigameUrl:'',minigameLoaded:false,minigame:0}]))};
for(const {building} of r.minigames)Object.assign(terminal.Objects[building],{minigameUrl:'fixture.js',minigameLoaded:true,minigame:{}});
terminal.Objects.Farm.minigame.plants=Object.fromEntries(r.seeds.map(({key})=>[key,{unlocked:1}]));
terminal.Objects.Bank.minigame.officeLevel=r.officeLevel;
terminal.Objects['Wizard tower'].minigame.spells=Object.fromEntries(r.spells.map(({key})=>[key,{}]));
terminal.Objects.Temple.minigame.gods=Object.fromEntries(r.gods.map(({key})=>[key,{}]));
const base='var Game='+JSON.stringify(terminal)+';Game;';
const seed=JSON.stringify(r.seeds[0].key),selector=JSON.stringify(r.accessUpgrades[0].name);
const cases=[
  {name:'first completion before later seed lock',setup:base,
    body:`Game.AchievementsOwned=600;Game.Objects.Farm.minigame.plants[${seed}].unlocked=0;Game;`,status:'complete',boundary:false},
  {name:'access survives a transient within-callback unlock',setup:base+`Game.Upgrades[${selector}].bought=0;Game.Upgrades[${selector}].unlocked=0;Game;`,
    body:`Game.Upgrades[${selector}].unlocked=1;Game.Upgrades[${selector}].unlocked=0;Game.AchievementsOwned=600;Game;`,status:'complete',boundary:false},
  {name:'no invented access',setup:base+`Game.Upgrades[${selector}].bought=0;Game.Upgrades[${selector}].unlocked=0;Game;`,
    body:'Game.AchievementsOwned=600;Game;',status:'pending',boundary:true,missingAccess:r.accessUpgrades[0].name},
  {name:'known absent Game during startup',setup:'var Game;Game;',body:'Game={};Game.AchievementsOwned=0;Game;',status:'pending',boundary:true},
  {name:'known absent counter during startup',setup:'var Game={};Game;',body:'Game.Upgrades={};Game;',status:'pending',boundary:true},
  {name:'counter stays below native milk threshold',setup:base,body:'Game;',status:'pending',boundary:true},
  {name:'upgrade entry accessor is unresolved',setup:base+`Object.defineProperty(Game.Upgrades,${selector},{get:function(){throw 'getter must not run';}});Game;`,
    body:'Game;',status:'missing'},
  {name:'upgrade flag accessor is unresolved',setup:base+`Object.defineProperty(Game.Upgrades[${selector}],'bought',{get:function(){throw 'getter must not run';}});Game;`,
    body:'Game;',status:'missing'},
  {name:'counter accessor is unresolved',setup:base+`Object.defineProperty(Game,'AchievementsOwned',{get:function(){throw 'getter must not run';}});Game;`,
    body:'Game;',status:'missing'},
  {name:'first hit precedes a later source failure',setup:base,body:'Game.AchievementsOwned=600;unprovidedOperation();',status:'complete',boundary:false},
];
const requests=cases.map(c=>({setup:compileJavaScript(c.setup),body:compileJavaScript(c.body)}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscompletionmonitorcheck',import.meta.url)),[],{
  input:JSON.stringify(requests),encoding:'utf8',timeout:180000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);
const actual=JSON.parse(child.stdout);assert.equal(actual.length,cases.length);
for(let i=0;i<cases.length;i++){
  const c=cases[i],got=actual[i];assert.equal(got.status,c.status,c.name+': '+JSON.stringify(got));
  if(c.boundary!==undefined)assert.equal(got.boundary,c.boundary,c.name);
  assert.equal(got.elapsed,'0',c.name);assert.equal(got.actions,0,c.name);
  if(c.missingAccess)assert(!got.accessed.includes(c.missingAccess),c.name);
  if(c.status==='missing')assert.match(got.error,/accessor/i,c.name);
}
// The corresponding source program has a complete intermediate heap and an
// incomplete returned heap in the pinned engine too. This does not prove that
// the supplied late-game state is reachable from a new save.
const native=runNativeEngine(`const fs=require('fs'),vm=require('vm');const c=JSON.parse(fs.readFileSync(0,'utf8'));const s={};vm.createContext(s);vm.runInContext(c.setup,s);vm.runInContext('Game.AchievementsOwned=600',s);const hit=JSON.parse(JSON.stringify(s.Game));vm.runInContext(c.tail,s);process.stdout.write(JSON.stringify([hit,s.Game]));`,
  {setup:base,tail:`Game.Objects.Farm.minigame.plants[${seed}].unlocked=0;`});
assert.equal(assessCompletion(captureCompletionSnapshot(native[0],{},{edition:'steam'}),r).complete,true);
assert.equal(assessCompletion(captureCompletionSnapshot(native[1],{},{edition:'steam'}),r).complete,false);
console.log(JSON.stringify({sourceMicrostateCases:cases.length,nativeTransientComparisons:2,newSaveReachabilityProved:false}));
