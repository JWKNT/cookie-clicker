/** Finite pinned-helper comparisons, separate from universal source refinement. */
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { pathToFileURL } from 'node:url';
import { resolve } from 'node:path';
import vm from 'node:vm';
const arg=(name,fallback)=>{const i=process.argv.indexOf(name);return i<0?fallback:process.argv[i+1];};
const repo=resolve(arg('--repo',new URL('..',import.meta.url).pathname));
const {spawnSyncWithFileInput:spawnSync}=await import(pathToFileURL(resolve(repo,'lean/process-input.mjs')));
const {compileJavaScript}=await import(pathToFileURL(resolve(repo,'model/javascript-ast.mjs')));
const {loadGameSource}=await import(pathToFileURL(resolve(repo,'model/game-source.mjs')));
const {runNativeEngine,inspectNativeEngine}=await import(pathToFileURL(resolve(repo,'model/native-engine.mjs')));
const acorn=createRequire(pathToFileURL(resolve(repo,'source/cookie-monster-plus/package.json')))('acorn');
const source=loadGameSource(),main=source.sources['main.js'],ast=acorn.parse(main,{ecmaVersion:5});
const names=['loc','parseLoc','escapeRegExp','replaceAll'];
const functions=Object.fromEntries(names.map(name=>{
 const n=ast.body.find(n=>n.type==='FunctionDeclaration'&&n.id.name===name)??ast.body.flatMap(n=>n.declarations||[]).find(n=>n.id.name===name)?.init;
 assert(n,name);return [name,n.type==='FunctionDeclaration'?main.slice(n.start,n.end):`var ${name}=(${main.slice(n.start,n.end)});`];
}));
const addLanguage=ast.body.flatMap(n=>n.declarations||[]).find(n=>n.id.name==='AddLanguage').init;
const normalizers=[];
const walk=n=>{if(!n||typeof n!=='object')return;if(n.type==='ForInStatement'&&n.body.type==='BlockStatement'&&n.body.body.length===1){const b=n.body.body[0];if(b.type==='IfStatement'&&b.test.type==='BinaryExpression'&&b.test.right.value==='/')normalizers.push(n);}for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(walk);else if(v&&typeof v==='object')walk(v);}};
walk(addLanguage);assert.equal(normalizers.length,1);
const normalization=main.slice(normalizers[0].start,normalizers[0].end);
assert.match(source.sources['loc/EN.js'],/"Achievement unlocked":\s*"\/"/);
const setup=Object.values(functions).join('\n')+'\nvar locStrings={"Achievement unlocked":"/"},locStringsFallback={},locBlink=false;\n'+normalization+'\n';
const cases=[];const add=(name,body)=>cases.push({name,source:setup+body});
add('actual default EN achievement label','loc("Achievement unlocked");');
add('nested source parseLoc with explicit undefined','parseLoc("Achievement unlocked",undefined);');
add('parseLoc with omitted parameter','parseLoc("Achievement unlocked");');
add('repeat calls retain catalogue entry','loc("Achievement unlocked")+":"+loc("Achievement unlocked")+":"+locStrings["Achievement unlocked"];');
add('native source fallback catalogue','locStrings={};locStringsFallback["Achievement unlocked"]="fallback";loc("Achievement unlocked");');
add('native source missing key and baseline','loc("missing")+":"+loc("missing",undefined,"baseline");');
add('native locBlink branch remains present','locBlink=true;loc("Achievement unlocked");');
add('falsy fallback suppresses blink','locBlink=true;locStrings={};locStringsFallback["Achievement unlocked"]="fallback";loc("Achievement unlocked");');
add('source string constructor getter remains observable','var log="";Object.defineProperty(String.prototype,"constructor",{get:function(){log+="c";return String;}});var result=loc("Achievement unlocked");log+":"+result;');
add('source constructor getter throw propagates','Object.defineProperty(String.prototype,"constructor",{get:function(){throw "constructor";}});try{loc("Achievement unlocked");}catch(e){e;}');
add('actual close-note marker replacement','replaceAll("==CLOSETHIS()==","Game.CloseNote(0);","a==CLOSETHIS()==b");');
add('all close-note occurrences are replaced','replaceAll("==CLOSETHIS()==","Game.CloseNote(18);","==CLOSETHIS()== ==CLOSETHIS()==");');
add('no marker retains original description',String.raw`replaceAll("==CLOSETHIS()==","Game.CloseNote(2);","<div class=\"title\">Wake and bake</div>");`);
add('empty description','replaceAll("==CLOSETHIS()==","Game.CloseNote(2);","");');
add('literal parentheses and metacharacters are escaped','replaceAll("a.b[0](x)","!","a.b[0](x)axb0x a.b[0](x)");');
add('native replacement dollar handling is retained','replaceAll("==CLOSETHIS()==","[$&]","a==CLOSETHIS()==b");');
add('escapeRegExp actual marker','escapeRegExp("==CLOSETHIS()==");');
const result=spawnSync(arg('--driver',resolve(repo,'lean/.lake/build/bin/jsastcheck')),['--execute'],{
 input:JSON.stringify(cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),fuel:1000000,standardLibrary:true}))),
 encoding:'utf8',timeout:120000,maxBuffer:16*1024*1024});
if(result.error)throw result.error;assert.equal(result.status,0,result.stderr);
const actual=JSON.parse(result.stdout);
const nativeScript=`const fs=require('fs'),vm=require('vm'),input=JSON.parse(fs.readFileSync(0,'utf8'));process.stdout.write(JSON.stringify(input.map(c=>{const value=vm.runInNewContext(c.source);if(typeof value!=='string')throw Error(c.name);return Array.from({length:value.length},(_,i)=>value.charCodeAt(i));})));`;
const engine=process.argv.includes('--engine');
const expected=engine?runNativeEngine(nativeScript,cases):cases.map(c=>{const v=vm.runInNewContext(c.source);assert.equal(typeof v,'string');return Array.from({length:v.length},(_,i)=>v.charCodeAt(i));});
for(let i=0;i<cases.length;i++){assert.equal(actual[i].status,'complete',cases[i].name+': '+JSON.stringify(actual[i]));assert.deepEqual(actual[i].value,{type:'string',units:expected[i]},cases[i].name);}
console.log(JSON.stringify({localizationCases:cases.length,comparisons:cases.length,engine:engine?inspectNativeEngine():{node:process.version},sourceHashes:source.hashes,formalScope:'loc Achievement unlocked initialized EN entry; other comparisons are finite regression cases',wholeStartupRefinement:false}));
