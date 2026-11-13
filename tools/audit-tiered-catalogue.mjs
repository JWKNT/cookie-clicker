import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { loadGameSource } from '../model/game-source.mjs';
import { createRuntime } from '../model/runtime.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn=require('acorn');
const sha=text=>createHash('sha256').update(text).digest('hex');
const source=loadGameSource(), main=source.sources['main.js'];
const syntax=acorn.parse(main,{ecmaVersion:5,locations:true});
const target=node=>node?.type==='Identifier'?node.name:node?.type==='ThisExpression'?'this':node?.type==='MemberExpression'
  ? `${target(node.object)}.${node.computed?'*':target(node.property)}`:'<expression>';
const functions=new Map(), calls=[], writes=[];
function visit(node) {
  if(!node||typeof node!=='object') return;
  if(node.type==='AssignmentExpression'&&node.right.type==='FunctionExpression') functions.set(target(node.left),node.right);
  if(['CallExpression','NewExpression'].includes(node.type)&&['Game.Object','Game.TieredUpgrade','Game.SynergyUpgrade','Game.GrandmaSynergy'].includes(target(node.callee))) calls.push(node);
  if(node.type==='AssignmentExpression'&&node.left.type==='MemberExpression') {
    const text=main.slice(node.left.start,node.left.end);
    if(/(?:tieredUpgrades|\.synergies|\.fortune|\.grandma|Game\.Tiers)/.test(text)) writes.push({line:node.loc.start.line,target:text,expression:main.slice(node.start,node.end)});
  }
  for(const [key,value]of Object.entries(node)) {
    if(['start','end','loc'].includes(key))continue;
    if(Array.isArray(value))value.forEach(visit);else if(value&&typeof value==='object')visit(value);
  }
}
visit(syntax);
const literal=(node,label)=>{assert.equal(node.type,'Literal',`${label}: source argument must be literal`);return node.value;};
const where=node=>({line:node.loc.start.line,sha256:sha(main.slice(node.start,node.end))});
const buildings=calls.filter(node=>target(node.callee)==='Game.Object').map((node,id)=>({
  id,name:literal(node.arguments[0],'building name'),source:where(node),tiers:[],synergies:[],fortune:null,grandma:null,
  callbackSource:where(node.arguments[7]),callbackBodySha256:sha(main.slice(node.arguments[7].start,node.arguments[7].end))}));
assert.equal(buildings.length,20);
const byName=new Map(buildings.map(b=>[b.name,b]));
for(const call of calls) {
  const kind=target(call.callee);
  if(kind==='Game.Object')continue;
  const name=literal(call.arguments[0],`${kind} name`), a=literal(call.arguments[2],`${kind} building`), b=byName.get(a);
  assert(b,`${kind}: unknown building ${a}`);
  if(kind==='Game.TieredUpgrade') {
    const tier=literal(call.arguments[3],'tier'), key=String(tier);
    assert(!b.tiers.some(row=>row.key===key),`duplicate tier ${a}/${key}`);
    b.tiers.push({key,name,tier,source:where(call)});
    if(tier==='fortune'){assert.equal(b.fortune,null);b.fortune={name,source:where(call)};}
  } else if(kind==='Game.SynergyUpgrade') {
    const other=literal(call.arguments[3],'second synergy building'), c=byName.get(other), tier=literal(call.arguments[4],'synergy tier');
    assert(c&&c!==b);
    for(const entry of [b,c])entry.synergies.push({key:String(entry.synergies.length),name,tier,buildings:[a,other],source:where(call)});
  } else {assert.equal(b.grandma,null);b.grandma={name,source:where(call)};}
}
// Integer-key order is the same order used by the implemented native enumeration.
for(const building of buildings)building.tiers.sort((a,b)=>typeof a.tier==='number'?(typeof b.tier==='number'?a.tier-b.tier:-1):typeof b.tier==='number'?1:0);
const runtime=createRuntime({recordAudit:false}), G=runtime.Game;
const descriptor=(object,key,value)=>{const d=Object.getOwnPropertyDescriptor(object,key);assert(d&&'value'in d,`missing own data ${key}`);assert.equal(d.value,value);assert.equal(d.writable,true);assert.equal(d.enumerable,true);assert.equal(d.configurable,true);return {writable:true,enumerable:true,configurable:true};};
const absent=(object,key)=>{for(let p=object;p;p=Object.getPrototypeOf(p))assert.equal(Object.getOwnPropertyDescriptor(p,key),undefined,`inherited ${key}`);};
const enumNames=object=>{const names=[];for(const key in object)names.push(key);return names;};
const tableShape=object=>{
  const keys=Object.getOwnPropertyNames(object).map(key=>{const d=Object.getOwnPropertyDescriptor(object,key);assert('value'in d);return {key,enumerable:d.enumerable};});
  let inheritedLevels=0;
  for(let p=Object.getPrototypeOf(object);p;p=Object.getPrototypeOf(p)){inheritedLevels++;for(const d of Object.values(Object.getOwnPropertyDescriptors(p)))assert.equal(d.enumerable,false);}
  return {kind:Array.isArray(object)?'array':'ordinary',ownKeys:keys,inheritedEnumerable:[],inheritedLevels,enumerated:enumNames(object)};
};
assert.equal(G.ascensionMode,0);assert.equal(G.UpgradesOwned,0);
for(const name of ['Has','GetTieredCpsMult','TieredUpgrade','SynergyUpgrade','GrandmaSynergy','SetTier']) {
  const node=functions.get(`Game.${name}`);assert(node);assert.equal(sha(String(G[name])),sha(main.slice(node.start,node.end)),`native function ${name}`);
}
const upgradedNames=new Set();
for(const building of buildings) {
  const b=G.Objects[building.name];assert.equal(b,G.ObjectsById[building.id]);
  descriptor(b,'name',building.name);descriptor(b,'tieredUpgrades',b.tieredUpgrades);descriptor(b,'synergies',b.synergies);
  assert.deepEqual(enumNames(b.tieredUpgrades),building.tiers.map(row=>row.key));
  assert.deepEqual(enumNames(b.synergies),building.synergies.map(row=>row.key));
  building.native={tierTable:tableShape(b.tieredUpgrades),synergyTable:tableShape(b.synergies),baseCps:typeof b.baseCps==='number'?{kind:'number',value:b.baseCps}:{kind:typeof b.baseCps,sourceSha256:sha(String(b.baseCps))}};
  const upgrade=(name,object)=>{assert.equal(object,G.Upgrades[name]);descriptor(G.Upgrades,name,object);descriptor(object,'name',name);descriptor(object,'bought',0);upgradedNames.add(name);return object.id;};
  for(const row of building.tiers){const u=b.tieredUpgrades[row.key];descriptor(b.tieredUpgrades,row.key,u);row.nativeUpgradeId=upgrade(row.name,u);descriptor(u,'tier',row.tier);descriptor(G.Tiers,row.key,G.Tiers[row.key]);if(row.tier==='fortune'){descriptor(G.Tiers[row.key],'special',1);row.special=1;}else{absent(G.Tiers[row.key],'special');row.special='absent';}}
  for(const row of building.synergies){const u=b.synergies[row.key];descriptor(b.synergies,row.key,u);row.nativeUpgradeId=upgrade(row.name,u);descriptor(u,'tier',row.tier);}
  for(const field of ['fortune','grandma']){const expected=building[field];if(expected){descriptor(b,field,G.Upgrades[expected.name]);expected.nativeUpgradeId=upgrade(expected.name,b[field]);expected.nativeDescriptor={state:'own-data',writable:true,enumerable:true,configurable:true};}else{absent(b,field);building.native[`${field}Absent`]=true;}}
  building.native.cpsMultiplier=G.GetTieredCpsMult(b);assert.equal(building.native.cpsMultiplier,1);
  building.leanBodySteps=building.tiers.reduce((n,r)=>n+(r.special===1?47:145),0)+113*building.synergies.length+(building.fortune?101:11)+(building.grandma?101:11)+37;
}
const total=(key)=>buildings.reduce((n,b)=>n+b[key].length,0);
const report={schemaVersion:1,status:'source-catalogue-and-diagnostic-descriptor-check-with-open-initialization-proof',
  sourceHashes:source.hashes,diagnosticRuntimeSha256:sha(readFileSync(new URL('../model/runtime.mjs', import.meta.url))),
  reproduction:'node tools/audit-tiered-catalogue.mjs',
  scope:'Source literal constructor sites determine the complete 20-building tier/synergy/fortune/grandma map. A fresh isolated diagnostic JavaScript runtime checks all selected own descriptors, identity links, lookup absence, enumeration order and zero bought fields. This is not a theorem that source initialization establishes the Lean frame, a browser refinement, or an optimality result.',
  sourceFunctions:Object.fromEntries(['Object','Upgrade','SetTier','TieredUpgrade','SynergyUpgrade','GrandmaSynergy','GetTieredCpsMult','Has'].map(name=>{const n=functions.get(`Game.${name}`);assert(n);return[name,where(n)];})),
  sourceSelectedWrites:writes,
  totals:{buildings:20,tierEntries:total('tiers'),normalTierEntries:total('tiers')-20,synergyEntries:total('synergies'),synergyConstructors:total('synergies')/2,fortuneGuards:20,grandmaGuards:18,distinctSelectedUpgrades:upgradedNames.size,bodyInterpreterSteps:buildings.reduce((n,b)=>n+b.leanBodySteps,0)},
  leanContracts:{World:['Window.Game own data and actual Has closure identities/lexical chain','Game.Tiers and Game.Has ordinary data properties','building tieredUpgrades own ordinary data property'],normalRows:['table[key] is the exact source-selected upgrade','upgrade.name and upgrade.tier own data fields','Game.Tiers[ToString(tier)] own ordinary descriptor','special absent through the full prototype chain','Game.Upgrades[name] names the actual zero-bought upgrade under normal ascension mode'],specialRows:['same selected table/name/tier edges','special native binary64 one'],synergies:['building.synergies array and full native enumeration','each selected upgrade name and zero-bought Has frame'],suffix:['fortune present for all 20','grandma absent for Cursor/Grandma and present for the other 18','all present selected upgrades have bought 0']},
  semanticOpenObligations:[
    'Prove source initialization and constructor execution establish this graph on the actual Lean source heap, including the actual native prototypes, data descriptors and lexical identities; diagnostic startup evidence alone does not supply that theorem.',
    'Link all catalogue IDs/names to the actual initialized heap rather than a copied sparse fixture or external JSON oracle.',
    'Prove the catalogue descriptors and zero ownership survive each permitted bootstrap purchase and every reachable Logic/Draw/timer callback; unlock writes may change other upgrade fields.',
    'Compose the completed GetTieredCpsMult source theorem with the 20 actual building callbacks, CalculateGains and the paired counter/scheduler route.',
    'Cursor.baseCps is its source function, not a finite number; the Cursor callback uses literal native 0.1. Only the other 19 baseCps fields are finite numeric constants.'
  ],buildings};
const out=new URL('../model/tiered-catalogue.json',import.meta.url);
if(process.argv.includes('--check'))assert.deepEqual(JSON.parse(readFileSync(out,'utf8')),report);else writeFileSync(out,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({checked:process.argv.includes('--check'),status:report.status,...report.totals}));
