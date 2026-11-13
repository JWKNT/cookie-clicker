/** Source seed construction and exact native seeded/flatten execution fixtures.
 * These checks do not establish the general ARC4 source refinement. */
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
const libraryNode=ast.body.find(n=>n.type==='ExpressionStatement'&&source.slice(n.start,n.end).includes('c.seedrandom=function'));assert(libraryNode);
const library=source.slice(libraryNode.start,libraryNode.end),functions=[];
function walk(n){if(!n||typeof n.type!=='string')return;if(n.type==='FunctionDeclaration'&&n.id.name==='l')functions.push(n);for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(walk);else if(v&&typeof v==='object')walk(v);}}
walk(libraryNode);assert.equal(functions.length,1);const flatten=source.slice(functions[0].start,functions[0].end);
const start=source.indexOf('Game.computeLumpType=function'),fn=acorn.parseExpressionAt(source,start+'Game.computeLumpType='.length,{ecmaVersion:5});
const first=source.slice(fn.body.body[0].start,fn.body.body[0].end);
const hash=s=>createHash('sha256').update(s).digest('hex');
assert.equal(hash(library),'a6c6d6219add3214812ad4d6dd8311ddb2b5d9551090344ce047a6226045b7be');
assert.equal(hash(flatten),'410f60344cdef052df9b2cdc5d36951dd8cf72ac47482569db1f083cf0eada86');
const cases=[],seeds=['','abc','aaodk/0','ubyju/1793275200000','\0','a\0b','é','😀','\ud800','\udfff','x'.repeat(256),'x'.repeat(257),String(2n**1200n)];
for(const seed of seeds){
 const encoded=JSON.stringify(seed);
 cases.push({name:'actual flatten string '+JSON.stringify(seed.slice(0,20)),source:flatten+`;var seed=${encoded};l(seed,3);`,standardLibrary:true});
 const code=library+`;var seed=${encoded},result=Math.seedrandom(seed);result+'|'+Math.random()+'|'+Math.random();`;
 cases.push({name:'actual seeded setup '+JSON.stringify(seed.slice(0,20)),source:code,nativeSource:'Math.random=function(){return 0.5;};'+code,browserLibrary:true,randomInputs:[4503599627370496]});
}
for(const epoch of [1793275200000n,2n**100n,2n**1200n]){
 const code=library+`;var Game={seed:'ubyju',lumpT:Date.now()};${first}Math.random()+':'+Math.random();`;
 const native=library+`;var Game={seed:'ubyju',lumpT:${JSON.stringify(String(epoch))}};${first}Math.random()+':'+Math.random();`;
 cases.push({name:'actual clock seed argument '+epoch,source:code,nativeSource:'Math.random=function(){return 0.5;};'+native,browserLibrary:true,randomInputs:[4503599627370496],epochMilliseconds:String(epoch),selectedClock:epoch>8640000000000000n});
}
const expected=runNativeEngine(`const fs=require('fs'),vm=require('vm');process.stdout.write(JSON.stringify(JSON.parse(fs.readFileSync(0,'utf8')).map(c=>{const s=vm.runInNewContext(c.nativeSource||c.source);if(typeof s!=='string')throw Error(c.name);return Array.from({length:s.length},(_,i)=>s.charCodeAt(i));})));`,cases);
const requests=cases.map(c=>({...c,ast:compileJavaScript(c.source,{name:c.name}),fuel:3000000}));
const p=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const out=JSON.parse(p.stdout);
for(let i=0;i<cases.length;i++){const c=cases[i],a=out[i];assert.equal(a.status,'complete',c.name+':'+JSON.stringify(a));assert.deepEqual(a.value,{type:'string',units:expected[i]},c.name);if(c.browserLibrary)assert.equal(a.randomInputsRemaining,0,c.name+' bootstrap only consumes free draw');}
console.log(JSON.stringify({seedEntryCases:cases.length,ordinaryNativeComparisons:cases.filter(c=>!c.selectedClock).length,selectedClockArgumentComparisons:cases.filter(c=>c.selectedClock).length,flattenSourceCases:seeds.length,nativeSeededSetupCases:seeds.length,wholeArc4SourceRefinementProved:false}));
