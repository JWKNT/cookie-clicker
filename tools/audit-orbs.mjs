import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import assert from 'node:assert/strict';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine,EXPECTED_NATIVE_ENGINE} from '../model/native-engine.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),source=loadGameSource(),main=source.sources['main.js'];
const hash=s=>createHash('sha256').update(s).digest('hex');
const text=n=>main.slice(n.start,n.end);
const ast=acorn.parse(main,{ecmaVersion:5,locations:true});
const walk=(n,fn)=>{if(!n||typeof n!=='object')return;fn(n);for(const [k,v] of Object.entries(n)){if(['loc','start','end'].includes(k))continue;if(Array.isArray(v))v.forEach(x=>walk(x,fn));else if(v&&typeof v==='object')walk(v,fn)}};
const functions=[];walk(ast,n=>{if(n.type==='FunctionExpression'||n.type==='FunctionDeclaration')functions.push(n)});
const pop=functions.find(n=>text(n).startsWith('function(me)')&&text(n).includes('//select an effect')&&text(n).includes("if (choice=='chain cookie')"));
assert(pop,'source golden pop');
const body=pop.body.body;
const first=body.findIndex(n=>n.type==='VariableDeclaration'&&n.declarations[0].id.name==='list');
const removal=body.findIndex(n=>text(n).includes("list.splice(list.indexOf(this.last),1)"));
assert(first>=0&&removal>first);
assert.equal(text(body[first]),'var list=[];');
const calls=[];
// Every branch is allowed nondeterministically. Actual predicates are retained
// in the source certificate, but never replaced in an executable game callback.
const step=(n,lists)=>{
 if(!n)return lists;
 if(n.type==='BlockStatement')return n.body.reduce((s,x)=>step(x,s),lists);
 if(n.type==='IfStatement')return [...step(n.consequent,lists),...step(n.alternate,lists)];
 assert.equal(n.type,'ExpressionStatement');const c=n.expression;
 assert.equal(c.type,'CallExpression');assert.equal(c.callee.type,'MemberExpression');
 assert.equal(text(c.callee),'list.push');assert(c.arguments.every(x=>x.type==='Literal'&&typeof x.value==='string'));
 calls.push({line:n.loc.start.line,values:c.arguments.map(x=>x.value)});
 return lists.map(l=>[...l,...c.arguments.map(x=>x.value)]);
};
let lists=[[]];for(const n of body.slice(first+1,removal))lists=step(n,lists);
assert.equal(text(body[removal]),"if (this.last!='' && Math.random()<0.8 && list.indexOf(this.last)!=-1) list.splice(list.indexOf(this.last),1);");
const blab=body[removal+1];assert.equal(text(blab),"if (Math.random()<0.0001) list.push('blab');");
lists=step(blab,lists);
const unique=[...new Map(lists.map(l=>[JSON.stringify(l),l])).values()];
assert(unique.every(l=>l.length>=2&&l.length<=18&&['frenzy','clot'].includes(l[0])));
assert.equal(text(body[removal+2]),'var choice=choose(list);');
assert.equal(text(body[removal+3]),"if (this.chain>0) choice='chain cookie';");
assert.equal(text(body[removal+4]),"if (me.force!='') {this.chain=0;choice=me.force;me.force='';}");
assert.equal(text(body[removal+5]),"if (choice!='chain cookie') this.chain=0;");
const choose=functions.find(n=>n.type==='FunctionDeclaration'&&n.id.name==='choose');
const aura=functions.find(n=>n.type==='FunctionExpression'&&main.slice(n.start-14,n.start)==='Game.auraMult=');
assert(aura);const chainTest=[];walk(pop,n=>{if(n.type==='IfStatement'&&text(n.test)==='Math.random()<0.01 || nextMoni>=maxPayout')chainTest.push(n)});assert.equal(chainTest.length,1);
const sourceFragments={choose:text(choose),aura:text(aura),selection:main.slice(body[first].start,body[removal+6].end),chainBreak:text(chainTest[0])};
const worker=String.raw`
const fs=require('fs'),vm=require('vm');const input=JSON.parse(fs.readFileSync(0,'utf8'));
const c=vm.createContext({Game:{dragonAuras:[{name:'No aura'},{name:'Dragon Orbs'},{name:'Reality Bending'}],dragonAurasBN:{'Dragon Orbs':{id:0}},dragonLevel:100}});
vm.runInContext(input.fragments.choose+';Game.auraMult=('+input.fragments.aura+');Math.random=function(){return 0;};',c);
const selections=[];for(const list of input.lists){c.list=list;const result=vm.runInContext('choose(list)',c);if(result!==list[0])throw Error('choice zero failed');selections.push(result);}
const aura=[];for(let a=0;a<3;a++)for(let b=0;b<3;b++){c.Game.dragonAura=a;c.Game.dragonAura2=b;const value=vm.runInContext("Game.auraMult('Dragon Orbs')",c);aura.push({slots:[a,b],value,eligible:value>0,zeroPasses:0<value*0.1});}
const D=Math.pow(2,53),high=(D-1)/D;
function bits(x){const a=new ArrayBuffer(8),v=new DataView(a);v.setFloat64(0,x);return v.getBigUint64(0).toString();}
const intervalLengths=[];for(let n=2;n<=18;n++)intervalLengths.push({n,indexAtLower:Math.floor(0*n),indexAtUpper:Math.floor(((Math.pow(2,48)-1)/D)*n)});
process.stdout.write(JSON.stringify({versions:process.versions,listsChecked:selections.length,zeroChoices:new Set(selections).size,highBits:bits(high),antiRepeatBypassed:!(high<0.8),chainZeroBreaks:0<0.01,aura,intervalLengths,gameEntryPointExecuted:false}));
`;
const native=runNativeEngine(worker,{fragments:sourceFragments,lists:unique},{timeout:30000});
for(const[k,v]of Object.entries(EXPECTED_NATIVE_ENGINE))assert.equal(native.versions[k],v);
assert(native.antiRepeatBypassed&&native.chainZeroBreaks);assert(native.aura.every(x=>!x.eligible||x.zeroPasses));assert(native.intervalLengths.every(x=>x.indexAtLower===0&&x.indexAtUpper===0));
const report={schema:'cookie-orbs-source-closure-audit-v1',sourceHashes:source.hashes,sourceFragments:Object.fromEntries(Object.entries(sourceFragments).map(([k,v])=>[k,{sha256:hash(v),text:v}])),listProjection:{kind:'all syntactic conditional branches, no predicate assumptions',branchPaths:lists.length,uniqueLists:unique.length,minLength:Math.min(...unique.map(x=>x.length)),maxLength:Math.max(...unique.map(x=>x.length)),firstEntries:[...new Set(unique.map(x=>x[0]))],pushSites:[...new Map(calls.map(x=>[JSON.stringify(x),x])).values()],allListsSha256:hash(JSON.stringify(unique))},native,workerSha256:hash(worker),scope:{fullCallbackExecuted:false,newSaveReachabilityProved:false,sourcePhaseInvariantProved:false,universalAllPolicyClosureProved:false,wholeGameAttainmentProved:false},conditionalArgument:{episode:'Consecutive eligible highest-building sale/rebuy and unforced Orbs-pop cycles at fixed elapsed time. Leaving this control episode is an exit. No reload, Reset, intervening automatic task, forced shimmer, or mutation of the buff/chain table is silently erased.',event:'At a qualified sale, draw0 passes the positive aura test. If a chain is active, a pop draw0 at its break test clears it. For the next unchained pop, the largest IID53 draw bypasses anti-repeat removal if that test is evaluated; draw0 in native choose selects index0, Frenzy or Clot. Native gainBuff writes the entry before DOM work. Every further Orbs spawn requires an empty buff table.',designatedDrawsAtMost:5,probabilityLowerBound:'2^(-265)',tailBound:'If each eligible cycle returns through these source branches in free-IID phase, P(at least 2k further cycles without exit or a blocking buff) <= (1-2^(-265))^k. This is a mathematical argument over the source projection, not yet a Lean source-refinement theorem.',open:['Public hit-test reachability of opacity-zero newly created shimmer','Full free-RNG phase and exception/callee preservation','All-policy interleavings, especially save-current reload/initial Logic and resource-funded spells','Native retained heap/UI quotient']}};
const path=new URL('../model/orbs-source-closure.json',import.meta.url);
if(process.argv.includes('--check'))assert.deepEqual(JSON.parse(readFileSync(path,'utf8')),report);
else writeFileSync(path,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({paths:lists.length,unique:unique.length,min:report.listProjection.minLength,max:report.listProjection.maxLength,native:EXPECTED_NATIVE_ENGINE,conditionalTwoCycleExit:'2^-265'}));
