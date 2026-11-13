/** Intact clickLump/canLumps source comparisons with diagnostic DOM and award callbacks.
 * The callback fixtures expose order; they do not assert native DOM/Win refinement. */
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine} from '../model/native-engine.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),source=loadGameSource().sources['main.js'];
const extract=name=>{const start=source.indexOf(`Game.${name}=function`);assert(start>=0);const fn=acorn.parseExpressionAt(source,start+`Game.${name}=`.length,{ecmaVersion:5});return source.slice(fn.start,fn.end);};
const click=extract('clickLump'),can=extract('canLumps');
const sha=s=>createHash('sha256').update(s).digest('hex');
assert.equal(sha(can),'1c878d34a28f25680878430c755ca1e06a1401492f16e6047f7c7939e50e5dfc');
assert.equal(sha(click),'3fa4b86338646fdc1bf16f5407d696788dce003fb39304d693587b32d1b822e3');
const cases=[];
function add(name,{epoch=1793275200000n,age=100,total=0,ascension=0,earned=0,reset=0,choice=1,extra='',native=true}={}){
 const source=`var trace='',l=function(id){trace+='L'+id+';';return id;},triggerAnim=function(el,anim){trace+='A'+el+':'+anim+';';},choose=function(values){trace+='C'+values.join(',')+';';return ${choice};};var Game={lumpsTotal:${total},ascensionMode:${ascension},cookiesEarned:${earned},cookiesReset:${reset},lumpT:Date.now()-(${age}),lumpMatureAge:100,lumpRipeAge:200,lumpOverripeAge:300,Win:function(s){trace+='W'+s+';';},harvestLumps:function(n){trace+='H'+n+';';},computeLumpType:function(){trace+='T;';}};Game.canLumps=${can};Game.clickLump=${click};${extra}try{Game.clickLump();}catch(e){trace+='E'+e+';';}trace+'|'+(Date.now()-Game.lumpT);`;
 cases.push({name,epochMilliseconds:String(epoch),source,native});
}
for(const age of [-1,0,99,100,101,199,200,201,299,300,301])for(const choice of [0,1])add('native age boundary '+age+'/'+choice,{age,choice});
for(const [total,ascension,earned,reset] of [[-1,0,0,0],[-1,0,999999999,0],[-1,0,999999999,1],[-1,1,1e20,0],[0,1,0,0],[-0.5,1,0,0],[1e100,1,0,0]])add('actual canLumps short circuit '+[total,ascension,earned,reset].join('/'),{total,ascension,earned,reset});
add('first animation throws before eligibility',{extra:`triggerAnim=function(){throw 'first';};`});
add('second animation throws before eligibility',{extra:`var animations=0;triggerAnim=function(){trace+='A'+(++animations)+';';if(animations===2)throw 'second';};`});
add('source age getter throws after eligibility',{extra:`Object.defineProperty(Game,'lumpT',{get:function(){throw 'age';}});`,native:false});
// This throwing getter also affects the diagnostic result expression, so compare its
// ordering using a separate source that removes only that final read.
cases.at(-1).source=cases.at(-1).source.replace("trace+'|'+(Date.now()-Game.lumpT);","trace;");cases.at(-1).native=true;
add('eligibility property getter order',{total:-1,earned:1e9,extra:`Object.defineProperty(Game,'lumpsTotal',{get:function(){trace+='total;';return -1;}});Object.defineProperty(Game,'ascensionMode',{get:function(){trace+='mode;';return 0;}});Object.defineProperty(Game,'cookiesEarned',{get:function(){trace+='earned;';return 1e9;}});Object.defineProperty(Game,'cookiesReset',{get:function(){trace+='reset;';return 0;}});`});
add('existing lump skips later eligibility getters',{extra:`Object.defineProperty(Game,'ascensionMode',{get:function(){throw 'mode';}});`});
add('native award callback failure preserves ordering',{extra:`Game.Win=function(s){trace+='W'+s+';';throw 'win';};`});
add('native chosen zero still harvests and computes type',{choice:0});
const nativeCases=cases.filter(c=>c.native);
const expectedNative=runNativeEngine(`const fs=require('fs'),vm=require('vm');process.stdout.write(JSON.stringify(JSON.parse(fs.readFileSync(0,'utf8')).map(c=>{const code='Date.now=function(){return '+c.epochMilliseconds+';};'+c.source;const s=vm.runInNewContext(code);return Array.from({length:s.length},(_,i)=>s.charCodeAt(i));})));`,nativeCases);
for(let i=0;i<nativeCases.length;i++)nativeCases[i].expected=expectedNative[i];
for(const epoch of [2n**100n,2n**1200n])for(const age of [99,100,199,200,299,300]){
 add('unbounded selected clock source age '+epoch+'/'+age,{epoch,age,native:false});
 const same=nativeCases.find(c=>c.name==='native age boundary '+age+'/1');assert(same);cases.at(-1).expected=same.expected;
}
const request=cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),epochMilliseconds:c.epochMilliseconds,standardLibrary:true,fuel:200000}));
const p=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(request),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const actual=JSON.parse(p.stdout);assert.equal(actual.length,cases.length);
for(let i=0;i<cases.length;i++){assert.equal(actual[i].status,'complete',cases[i].name+':'+JSON.stringify(actual[i]));assert.deepEqual(actual[i].value,{type:'string',units:cases[i].expected},cases[i].name);}
console.log(JSON.stringify({sourcePrefixCases:cases.length,nativeComparisons:nativeCases.length,unboundedClockCases:cases.length-nativeCases.length,canLumpsSha256:sha(can),clickLumpSha256:sha(click),callbackFixtures:'Diagnostic DOM/choose/award callbacks preserve test order; not native callback refinement',provedCanLumpsBranch:'existing lumpsTotal > -1',fullClickLumpProved:false}));
