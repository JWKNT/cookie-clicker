/** Finite native comparisons for the explicit V8 sort translation and Lean runner. */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import vm from 'node:vm';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';

const useEngine = process.argv.includes('--engine');
const translation = readFileSync(new URL('../model/semantics/v8-timsort.js', import.meta.url), 'utf8');
const scheduleWorker = `
const fs=require('fs'),vm=require('vm'),assert=require('assert');
const sort=vm.runInNewContext(JSON.parse(fs.readFileSync(0,'utf8')));
let seed=1,count=0,comparisons=0;
const random=()=>{seed=(Math.imul(1664525,seed)+1013904223)>>>0;return seed;};
for(let n=0;n<=500;n++)for(let k=0;k<5;k++){
 const a=Array.from({length:n},()=>random()%31),b=a.slice(),la=[],lb=[];
 const cmp=(x,y)=>k===0?x-y:k===1?+(x<y):k===2?0:k===3?(x%7)-(y%7):NaN;
 a.sort((x,y)=>{la.push([x,y]);return cmp(x,y);});
 sort(b,(x,y)=>{lb.push([x,y]);return cmp(x,y);},String,Object.create,n);
 assert.deepStrictEqual(b,a);assert.deepStrictEqual(lb,la);
 count++;comparisons+=la.length;
}
process.stdout.write(JSON.stringify({cases:count,comparisons}));`;
const runWorker = (script,input) => {
  if (useEngine) return runNativeEngine(script,input,{timeout:300000});
  const result=spawnSync(process.execPath,['-e',script],{input:JSON.stringify(input),encoding:'utf8',timeout:300000,maxBuffer:32*1024*1024});
  if(result.error) throw result.error;
  assert.equal(result.status,0,result.stderr);return JSON.parse(result.stdout);
};
const schedules = runWorker(scheduleWorker,translation);

const cases=[];
const add=(name,source)=>cases.push({name,source,fuel:10000000,standardLibrary:true});
add('dense and stable numeric order','var a=[4,1,3,1,2],s="";a.sort(function(x,y){s+=x+","+y+";";return x-y;});s+"/"+a.join(":");');
add('boolean comparator preserves pinned call order','var a=[7,2,3,1,2,9,4,5],s="";a.sort(function(x,y){s+=x+","+y+";";return x<y;});s+"/"+a.join(":");');
add('undefined and holes are not compared','var a=[,3,void 0,1,,2,void 0],s="";a.sort(function(x,y){s+=x+","+y+";";return x-y;});s+"/"+a.join(":")+"/"+Object.keys(a).join(":");');
add('default comparator calls string conversion in order','var s="",a=[{toString:function(){s+="a";return "2";}},{toString:function(){s+="b";return "10";}},{toString:function(){s+="c";return "1";}}];a.sort();s;');
add('comparator ToNumber invokes valueOf','var s="",a=[3,1,2];a.sort(function(x,y){return {valueOf:function(){s+=x+","+y+";";return x-y;}};});s+"/"+a.join(":");');
add('NaN comparator preserves order','var a=[3,1,2];a.sort(function(){return NaN;});a.join(":");');
add('comparator throw leaves receiver uncommitted','var a=[4,3,2,1],s="",n=0;try{a.sort(function(x,y){s+=x+","+y+";";if(++n===2)throw 7;return x-y;});}catch(e){s+="e"+e;}s+"/"+a.join(":");');
add('comparator receiver shrink does not erase work copy','var a=[3,1,2],n=0;a.sort(function(x,y){if(!n++)a.length=0;return x-y;});a.length+"/"+a.join(":");');
add('comparator receiver growth retains new tail','var a=[3,1,2];a.sort(function(x,y){a[5]=8;return x-y;});a.length+"/"+a.join(":")+"/"+Object.keys(a).join(":");');
add('getter preprocessing precedes comparisons and writes','var s="",o={length:3,get 0(){s+="g";this[1]=8;return 3;},set 0(v){s+="s"+v;},1:1,2:2};Array.prototype.sort.call(o,function(x,y){s+="c"+x+","+y+";";return x-y;});s+"/"+o[1]+":"+o[2];');
add('readonly output fails after comparisons','var s="",a=[3,1,2];Object.defineProperty(a,"0",{writable:false});try{a.sort(function(x,y){s+=x+","+y+";";return x-y;});}catch(e){s+=e.name;}s+"/"+a.join(":");');
add('nonconfigurable trailing entry fails after sorted prefix','var a=[,3,1];Object.defineProperty(a,"2",{configurable:false});var s="";try{a.sort();}catch(e){s=e.name;}s+"/"+a.join(":");');
add('private scratch ignores indexed prototype setters','var a=[5,1,4,2,3],s="",set=false;a.sort(function(x,y){if(!set){set=true;Object.defineProperty(Array.prototype,"0",{set:function(){s+="array";},configurable:true});Object.defineProperty(Object.prototype,"minGallop",{set:function(){s+="object";},configurable:true});}return x-y;});delete Array.prototype[0];delete Object.prototype.minGallop;s+"/"+a.join(":");');
add('comparator validation precedes receiver conversion','var s="",o={get length(){s+="l";return 1;}};try{Array.prototype.sort.call(o,3);}catch(e){s+=e.name;}s;');
add('native primitive return for short receiver','typeof Array.prototype.sort.call(1)+":"+Array.prototype.sort.call("x");');
add('null receiver throws after valid comparator','try{Array.prototype.sort.call(null);}catch(e){e.name;}');
add('length conversion invokes source callback','var s="",o={0:3,1:1,2:2,length:{valueOf:function(){s+="v";return 3;}}};Array.prototype.sort.call(o);s+"/"+o[0]+o[1]+o[2];');
for(const n of [63,64,65,100,128]) for(const mode of ['numeric','boolean','default']){
 let source=`var a=[],s="";for(var i=0;i<${n};i++)a.push((i*73+19)%41);`;
 source+=mode==='default'?'a.sort();':`a.sort(function(x,y){s+=x+","+y+";";return ${mode==='numeric'?'x-y':'x<y'};});`;
 add(`TimSort merges at length ${n}, ${mode}`,source+'s+"/"+a.join(":");');
}
const referenceScript=`const fs=require('fs'),vm=require('vm');const cases=JSON.parse(fs.readFileSync(0,'utf8'));process.stdout.write(JSON.stringify(cases.map(c=>{const s=vm.runInNewContext(c.source,{}, {timeout:10000});if(typeof s!=='string')throw Error(c.name+' not string');return Array.from({length:s.length},(_,i)=>s.charCodeAt(i));})));`;
const expected=runWorker(referenceScript,cases);
const input=cases.map(c=>({...c,ast:compileJavaScript(c.source,{name:c.name})}));
const result=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{
 input:JSON.stringify(input),encoding:'utf8',timeout:300000,maxBuffer:64*1024*1024,
});
if(result.error)throw result.error;
assert.equal(result.status,0,result.stderr);
const actual=JSON.parse(result.stdout);
assert.equal(actual.length,cases.length);
for(let i=0;i<cases.length;i++){
 assert.equal(actual[i].status,'complete',`${cases[i].name}: ${JSON.stringify(actual[i])}`);
 assert.deepEqual(actual[i].value,{type:'string',units:expected[i]},cases[i].name);
}
console.log(JSON.stringify({scheduleCases:schedules.cases,comparisonCalls:schedules.comparisons,leanCases:cases.length,
 comparisonEngine:useEngine?inspectNativeEngine():{node:process.version,v8:process.versions.v8},sourceRefinementProved:false}));
