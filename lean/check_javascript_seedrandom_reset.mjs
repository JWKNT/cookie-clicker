/** Source-generator integration under the explicitly selected zero-argument law.
 * Native comparisons replace only seedrandom() with the same selected restore rule.
 * They are not claims that vanilla seedrandom restores its old function identity. */
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine} from '../model/native-engine.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),source=loadGameSource().sources['main.js'],ast=acorn.parse(source,{ecmaVersion:5});
const extract=name=>{const start=source.indexOf(`Game.${name}=function`);assert(start>=0);const fn=acorn.parseExpressionAt(source,start+`Game.${name}=`.length,{ecmaVersion:5});return source.slice(fn.start,fn.end);};
const libraryNodes=ast.body.filter(n=>n.type==='ExpressionStatement'&&source.slice(n.start,n.end).includes('c.seedrandom=function'));
assert.equal(libraryNodes.length,1);const library=source.slice(libraryNodes[0].start,libraryNodes[0].end);
assert.equal(createHash('sha256').update(library).digest('hex'),'a6c6d6219add3214812ad4d6dd8311ddb2b5d9551090344ce047a6226045b7be');
const type=extract('computeLumpType'),aura=extract('auraMult'),has=extract('Has');
const sha=s=>createHash('sha256').update(s).digest('hex');assert.equal(sha(type),'98909e66832224eab0e9b2e39ebdb5f0eaa2c426c4df8529520e2b86b668afdb');
const helper=name=>{const node=ast.body.find(n=>n.type==='FunctionDeclaration'&&n.id.name===name);assert(node);return source.slice(node.start,node.end);};
const bootstrap='var originalFree=Math.random;'+library+helper('choose')+helper('randomFloor');
const cases=[];
for(const seed of ['aaodk','ubyju'])for(const dragon of [0,1,2])for(const bought of [0,1]){
 const name='intact computeLumpType '+seed+'/'+dragon+'/'+bought;
 const setup=`var Game={seed:'${seed}',lumpT:Date.now(),elderWrath:3,ascensionMode:0,dragonAura:${dragon},dragonAura2:0,dragonLevel:100,dragonAuras:[{name:'none'},{name:"Dragon's Curve"},{name:'Reality Bending'}],dragonAurasBN:{"Dragon's Curve":{id:1}},Upgrades:{'Sucralosia Inutilis':{bought:${bought},pool:'',tier:0}}};Game.auraMult=${aura};Game.Has=${has};Game.computeLumpType=${type};`;
 cases.push({name,setup,action:`Game.computeLumpType();(Math.random===originalFree)+':'+Game.lumpCurrentType+':'+Math.random();`,native:true});
}
cases.push({name:'captured source call with detached receiver',setup:'',action:`Math.seedrandom('hello');var reset=Math.seedrandom;reset();(Math.random===originalFree)+':'+Math.random();`,native:true});
cases.push({name:'different source function identity is executed normally',setup:'',action:`Math.seedrandom('hello');Math.seedrandom=function(){return 7;};Math.seedrandom();(Math.random===originalFree)+':'+Math.seedrandom();`,native:false,expected:'false:7'});
cases.push({name:'used zeroarg return stays explicit',setup:'',action:`var used=Math.seedrandom();String(used);`,native:false,status:'unresolved'});
const nativeCases=cases.filter(c=>c.native);
const expected=runNativeEngine(`const fs=require('fs'),vm=require('vm');const input=JSON.parse(fs.readFileSync(0,'utf8'));process.stdout.write(JSON.stringify(input.cases.map(c=>{const context={};vm.createContext(context);vm.runInContext('var freeValues=[0.5,17/Math.pow(2,53)];Math.random=function(){return freeValues.shift();};Date.now=function(){return 1793275200000;};'+input.bootstrap+c.setup,context);vm.runInContext('var capturedSeedrandom=Math.seedrandom;Math.seedrandom=function(){if(arguments.length===0){Math.random=originalFree;return;}return capturedSeedrandom.apply(this,arguments);};',context);return vm.runInContext(c.action,context);})));`,{bootstrap,cases:nativeCases});
for(let i=0;i<nativeCases.length;i++)nativeCases[i].expected=expected[i];
const requests=cases.map(c=>({ast:compileJavaScript(bootstrap+c.setup,{name:c.name+' bootstrap'}),followupPrograms:[compileJavaScript(c.action,{name:c.name})],captureSeedrandomAfter:0,browserLibrary:true,epochMilliseconds:'1793275200000',randomInputs:[4503599627370496,17],fuel:3000000}));
const p=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const out=JSON.parse(p.stdout);
for(let i=0;i<cases.length;i++){const c=cases[i],a=out[i];assert.equal(a.status,c.status??'complete',c.name+':'+JSON.stringify(a));if(!c.status)assert.deepEqual(a.value,{type:'string',units:Array.from(c.expected,x=>x.charCodeAt(0))},c.name);assert.equal(a.randomInputsRemaining,c.native?0:1,c.name+' selected free-draw consumption');}
console.log(JSON.stringify({sourceResetCases:cases.length,selectedLawNativeComparisons:nativeCases.length,actualComputeLumpTypeCases:12,seedrandomLibrarySha256:sha(library),computeLumpTypeSha256:sha(type),nativeZeroargIdentityRefinement:false,fullPhaseInvariantProved:false}));
