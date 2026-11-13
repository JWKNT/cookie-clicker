/** Compare direct source-heap projection with the established game extractor.
 * Fixtures execute as JavaScript source in Lean. Terminal fixtures are not
 * reachability evidence, and these finite checks are not source refinement.
 */
import assert from 'node:assert/strict';
import vm from 'node:vm';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { readFileSync } from 'node:fs';
import { r } from './completion-fixtures.mjs';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { assessCompletion, captureCompletionSnapshot } from '../model/completion.mjs';

const catalogue = JSON.parse(readFileSync(new URL('../model/catalogue.json', import.meta.url)));
const terminal = {
  version: 2.053, dragonLevel: r.dragonLevel, santaLevel: r.santaLevel,
  ascensionMode: 0, OnAscend: 0, AscendTimer: 0, ReincarnateTimer: 0,
  AchievementsOwned: r.normalAchievements.length,
  Achievements: Object.fromEntries(r.normalAchievements.map(({ name }) => [name, { name, won: 1 }])),
  Upgrades: Object.fromEntries([...r.ownedUpgrades, ...r.accessUpgrades].map(({ name, id }) =>
    [name, { name, id, bought: 1, unlocked: 1 }])),
  Objects: Object.fromEntries(catalogue.buildings.map(({ name }) => [name, {
    name, level: 12, amount: name === 'Farm' ? 300 : 1, highest: 1,
    minigameUrl: '', minigameLoaded: false, minigame: 0,
  }])),
};
for (const { building } of r.minigames) Object.assign(terminal.Objects[building], {
  minigameUrl: 'fixture.js', minigameLoaded: true, minigame: {},
});
terminal.Objects.Farm.minigame.plants = Object.fromEntries(r.seeds.map(({ key }) => [key, { unlocked: 1 }]));
terminal.Objects.Bank.minigame.officeLevel = r.officeLevel;
terminal.Objects['Wizard tower'].minigame.spells = Object.fromEntries(r.spells.map(({ key }) => [key, {}]));
terminal.Objects.Temple.minigame.gods = Object.fromEntries(r.gods.map(({ key }) => [key, {}]));
const base = 'var Game=' + JSON.stringify(terminal) + ';Game;';
const cases = [];
const add = (name, changes = '', options = {}) => cases.push({
  name, steps: (Array.isArray(changes) ? changes : [changes]).map(change => change + ';Game;'), ...options,
});
const quote = JSON.stringify;
add('synthetic source-heap terminal witness');
for (const { name } of [r.requiredAchievements[0],r.requiredAchievements.at(-1)] ) {
  for (const flag of ['0','false','2','"1"','undefined','true'])
    add('achievement flag '+name+'='+flag,`Game.Achievements[${quote(name)}].won=${flag}`);
}
for (const { name } of [r.ownedUpgrades[0],r.ownedUpgrades.at(-1)]) {
  add('current ownership '+name,`Game.Upgrades[${quote(name)}].bought=0`);
}
const selector = quote(r.accessUpgrades[0].name);
add('missing selector access',`Game.Upgrades[${selector}].bought=0;Game.Upgrades[${selector}].unlocked=0`);
add('observed selector access survives locking',['',`Game.Upgrades[${selector}].bought=0;Game.Upgrades[${selector}].unlocked=0`]);
add('access history does not replace owned upgrade',['',`Game.Upgrades[${quote(r.ownedUpgrades[0].name)}].bought=0`]);
for (const { building } of r.minigames) {
  for (const field of ['minigameLoaded','minigameUrl','minigame','level'])
    add('minigame '+building+' '+field,`Game.Objects[${quote(building)}][${quote(field)}]=0`);
}
for (const { building,level } of r.buildingLevels)
  add('building level '+building,`Game.Objects[${quote(building)}].level=${level-1}`);
add('soil current farms','Game.Objects.Farm.amount=299');
add('market highest','Game.Objects.Mine.highest=0');
add('market office','Game.Objects.Bank.minigame.officeLevel=4');
add('removed seed',`delete Game.Objects.Farm.minigame.plants[${quote(r.seeds.at(-1).key)}]`);
add('locked seed',`Game.Objects.Farm.minigame.plants[${quote(r.seeds[0].key)}].unlocked=0`);
add('missing spell',`delete Game.Objects['Wizard tower'].minigame.spells[${quote(r.spells[0].key)}]`);
add('missing god',`delete Game.Objects.Temple.minigame.gods[${quote(r.gods[0].key)}]`);
for (const name of ['dragonLevel','santaLevel']) add(name,`Game.${name}--`);
for (const name of ['ascensionMode','OnAscend','AscendTimer','ReincarnateTimer']) add(name,`Game.${name}=1`);
add('all normal sugar exceptions off',r.excludedAchievements.map(({name})=>`Game.Achievements[${quote(name)}].won=0`).join(';'));
add('two retained normal flags satisfy milk',r.excludedAchievements.map(({name},i)=>`Game.Achievements[${quote(name)}].won=${i<2?1:0}`).join(';'));
add('won flags complete but native milk counter stale','Game.AchievementsOwned=599');
add('native milk threshold exact','Game.AchievementsOwned=600');
for (const value of [2 ** 53, 2 ** 53 + 2, 2 ** 90, 2 ** 1000, Number.MAX_VALUE]) {
  const literal = String(value);
  add('large represented native count '+literal,`Game.AchievementsOwned=${literal}`);
  add('large represented building counts '+literal,`Game.Objects.Farm.level=${literal};Game.Objects.Farm.amount=${literal};Game.Objects.Mine.highest=${literal}`);
}

for(const value of ['undefined','null','-1','599.5','Infinity','NaN','"600"'])
  add('invalid native count '+value,`Game.AchievementsOwned=${value}`,{projectionError:true});
add('missing native counter','delete Game.AchievementsOwned',{projectionError:true});
add('native counter accessor is unresolved',`Object.defineProperty(Game,'AchievementsOwned',{get:function(){throw 'not a data count';}})`,{projectionError:true});
add('web edition remains incomplete' ,'',{edition:'web'});
for(const value of ['-1','27.5','Infinity','NaN','"27"'])
  add('invalid count '+value,`Game.dragonLevel=${value}`,{projectionError:true});
add('unknown version','Game.version=2.052',{projectionError:true});
add('getter is unresolved, not evaluated',`Object.defineProperty(Game.Achievements['Wake and bake'],'won',{get:function(){throw 'not a data property';}})`,{projectionError:true});
add('nonenumerable catalogue entry is unresolved',`Object.defineProperty(Game.Achievements,'Wake and bake',{enumerable:false})`,{projectionError:true});
add('inherited catalogue entry is unresolved',`var a=Game.Achievements['Wake and bake'];delete Game.Achievements['Wake and bake'];Object.prototype['Wake and bake']=a`,{projectionError:true});
// These cases mark an explicitly partial interpreter descriptor. They do not
// claim that native JavaScript can set this model metadata.
for (const [label,path,name] of [
  ['achievement',['Achievements'],r.normalAchievements[0].name],
  ['owned upgrade',['Upgrades'],r.ownedUpgrades[0].name],
  ['seed',['Objects','Farm','minigame','plants'],r.seeds[0].key],
  ['spell',['Objects','Wizard tower','minigame','spells'],r.spells[0].key],
  ['god',['Objects','Temple','minigame','gods'],r.gods[0].key],
]) add('unknown catalogue descriptor '+label,'',{unknownOwn:{path,name},projectionError:true});
add('absent but unresolved spell descriptor',`delete Game.Objects['Wizard tower'].minigame.spells[${quote(r.spells[0].key)}]`,{
  unknownOwn:{path:['Objects','Wizard tower','minigame','spells'],name:r.spells[0].key},projectionError:true,
});


function expected(baseSource,test) {
  if(test.projectionError)return {projected:false};
  const context=vm.createContext({});vm.runInContext(baseSource,context);
  let history={};let snapshot;
  for(const source of test.steps){
    vm.runInContext(source,context);
    snapshot=captureCompletionSnapshot(context.Game,history,{edition:test.edition||'steam'});
    history=snapshot.history;
  }
  const assessment=assessCompletion(snapshot,r);
  assert.equal(assessment.valid,snapshot.edition==='steam',test.name+': '+assessment.issues);
  // The Lean goal list also includes five schema/version/edition/history goals.
  const identityFailures=snapshot.edition==='steam'?0:2;
  return {projected:true,complete:assessment.complete,missingGoals:assessment.missing.length+identityFailures,
    accessed:r.accessUpgrades.filter(({name})=>history.accessedUpgrades.includes(name)).map(({name})=>name)};
}
function compare(baseSource,tests) {
  const input={base:compileJavaScript(baseSource),cases:tests.map(test=>({...test,
    steps:test.steps.map(source=>compileJavaScript(source))}))};
  const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscompletioncheck',import.meta.url)),[],{
    input:JSON.stringify(input),encoding:'utf8',maxBuffer:32*1024*1024,timeout:180000,
  });
  if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);
  const actual=JSON.parse(child.stdout);assert.equal(actual.length,tests.length);
  for(let i=0;i<tests.length;i++){
    const want=expected(baseSource,tests[i]);
    if(!want.projected)assert.equal(actual[i].projected,false,tests[i].name);
    else assert.deepEqual(actual[i],want,tests[i].name);
  }
}
compare(base,cases);
let nativeCases=0;
if(process.argv.includes('--engine')){
  const {createRuntime}=await import('../model/runtime.mjs');
  const runtime=createRuntime();const G=runtime.Game;
  const sourceGame={};
  for(const name of ['version','AchievementsOwned','dragonLevel','santaLevel','ascensionMode','OnAscend','AscendTimer','ReincarnateTimer'])sourceGame[name]=G[name];
  sourceGame.Achievements=Object.fromEntries(Object.values(G.Achievements).map(x=>[x.name,{name:x.name,won:x.won}]));
  sourceGame.Upgrades=Object.fromEntries(Object.values(G.Upgrades).map(x=>[x.name,{name:x.name,id:x.id,bought:x.bought,unlocked:x.unlocked}]));
  sourceGame.Objects=Object.fromEntries(Object.values(G.Objects).map(x=>[x.name,{
    name:x.name,level:x.level,amount:x.amount,highest:x.highest,minigameUrl:x.minigameUrl,
    minigameLoaded:x.minigameLoaded,minigame:0,
  }]));
  const nativeBase='var Game='+JSON.stringify(sourceGame)+';Game;';
  compare(nativeBase,[{name:'actual new-save source data',steps:['Game;']}]);nativeCases++;
}
console.log(JSON.stringify({sourceHeapCases:cases.length,nativeSourceDataCases:nativeCases,sourceRefinementProved:false}));
