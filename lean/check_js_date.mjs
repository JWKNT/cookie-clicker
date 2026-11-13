import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
import { inspectNativeEngine,runNativeEngine } from '../model/native-engine.mjs';

const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,standardLibrary:true,fuel:1000000,...extra});
add('clock reads integer epoch in deterministic fixture','Date.now()+":"+new Date().getTime()+":"+Date();');
add('native epoch fields and UTC formatting','var d=new Date(0);d.getFullYear()+":"+d.getMonth()+":"+d.getDate()+":"+d.getDay()+":"+d.toISOString()+":"+d.toUTCString();');
add('negative timestamp and millisecond residue','var d=new Date(-1);d.getUTCFullYear()+":"+d.getUTCHours()+":"+d.getUTCMinutes()+":"+d.getUTCSeconds()+":"+d.getUTCMilliseconds()+":"+d.getTimezoneOffset();');
add('constructor normalizes components and short year','new Date(99,-13,0,25,-1,60,1001).toISOString();');
add('constructor supports year zero via setter','var d=new Date(0);d.setFullYear(0,1,29);d.toISOString();');
add('constructor and UTC truncate fractional components','new Date(2000.9,1.9,29.9,0.9,0.9,0.9,0.9).getTime()+":"+Date.UTC(2000.9,1.9,29.9);');
add('UTC defaults missing month and returns NaN without year','Date.UTC(2000)+":"+Date.UTC();');
add('Date clone bypasses overridden conversion methods','var d=new Date(17);d.valueOf=function(){throw 3;};d.toString=function(){throw 4;};new Date(d).getTime()+"";');
add('one numeric object argument uses default primitive order','var s="",d=new Date({valueOf:function(){s+="v";return 18;},toString:function(){s+="s";return "bad";}});s+":"+d.getTime();');
add('Date default hint is string, numeric subtraction is number','var d=new Date(0);(d+1)+":"+(d-1)+":"+(+d);');
add('Date string conversion honors source method override','var d=new Date(0),s="";d.toString=function(){s+="s";return "date";};d.valueOf=function(){s+="v";return 2;};var a=d+1,b=d-1;s+":"+a+":"+b;');
add('all provided constructor conversions run despite early NaN','var s="";function v(x){return {valueOf:function(){s+=x;return x==="a"?NaN:1;}};}new Date(v("a"),v("b"),v("c"));s;');
add('constructor conversion throw stops following conversions','var s="";try{new Date({valueOf:function(){s+="a";throw 3;}},{valueOf:function(){s+="b";return 1;}});}catch(e){s+=e;}s;');
// Beyond-native finite values are tested by the selected-clock suite, not this native-prefix comparison.
add('Date finite endpoint and nonfinite input','new Date(8640000000000000).toISOString()+":"+new Date(Infinity).toString();');
add('TimeClip normalizes negative zero','1/new Date(-0).getTime()+":"+new Date(-1.9).getTime();');
add('setTime mutates internal slot and returns clipped time','var d=new Date(0),r=d.setTime({valueOf:function(){return 2.9;}});r+":"+d.getTime();');
add('setFullYear normalizes leap day and keeps time','var d=new Date(2000,1,29,12,34,56,789),r=d.setFullYear(2001);r+":"+d.toISOString();');
add('setFullYear revives invalid Date from epoch fields','var d=new Date(NaN);d.setUTCFullYear(2000);d.toISOString();');
add('setFullYear checks brand before argument conversion','var s="";try{Date.prototype.setFullYear.call({}, {valueOf:function(){s+="v";return 2000;}});}catch(e){s+=e.name;}s;');
add('invalid Date formatting and ISO error','var d=new Date(NaN),s=d.toUTCString()+":"+d.getFullYear();try{d.toISOString();}catch(e){s+=":"+e.name;}s;');
add('Date prototype lacks a Date internal slot','try{Date.prototype.getTime();}catch(e){e.name;}');
add('setTime changes frozen Date internal slot','var d=new Date(0);Object.preventExtensions(d);d.setTime(12);d.getTime()+"";');
add('string Date parser is explicit model boundary','new Date("2026-10-29");',{expectedStatus:'unresolved'});
const source=loadGameSource().sources['main.js'];
// The season code contains exactly the source Date constructor and Easter algorithm.
const start=source.indexOf("Game.baseSeason='';//halloween");
const finish=source.indexOf('\n\tGame.updateLog=',start);
assert(start>=0&&finish>start);
add('pinned native automatic season calculation','var Game={};'+source.slice(start,finish)+'Game.baseSeason;');

const worker=`const fs=require('fs'),vm=require('vm');process.env.TZ='UTC';const cases=JSON.parse(fs.readFileSync(0,'utf8'));const output=cases.map(c=>{if(c.expectedStatus)return null;const context=vm.createContext({});const NativeDate=vm.runInContext('Date',context);function FixtureDate(...args){if(new.target)return args.length?new NativeDate(...args):new NativeDate(0);return new NativeDate(0).toString();}FixtureDate.prototype=NativeDate.prototype;FixtureDate.now=()=>0;FixtureDate.UTC=NativeDate.UTC;FixtureDate.parse=NativeDate.parse;context.Date=FixtureDate;const result=vm.runInContext(c.source,context,{timeout:10000});if(typeof result!=='string')throw Error(c.name+' must return string');return Array.from({length:result.length},(_,i)=>result.charCodeAt(i));});process.stdout.write(JSON.stringify(output));`;
const native=process.argv.includes('--engine');
let expected;
if(native)expected=runNativeEngine(worker,cases);
else{const p=spawnSync(process.execPath,['-e',worker],{input:JSON.stringify(cases),encoding:'utf8'});assert.equal(p.status,0,p.stderr);expected=JSON.parse(p.stdout);}
const input=cases.map(c=>({...c,ast:compileJavaScript(c.source,{name:c.name})}));
const p=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{
 input:JSON.stringify(input),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024,
});
if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const actual=JSON.parse(p.stdout);
assert.equal(actual.length,cases.length);
for(let i=0;i<cases.length;i++){
 if(cases[i].expectedStatus)assert.equal(actual[i].status,cases[i].expectedStatus,cases[i].name);
 else{assert.equal(actual[i].status,'complete',cases[i].name+':'+JSON.stringify(actual[i]));assert.deepEqual(actual[i].value,{type:'string',units:expected[i]},cases[i].name);}
}
console.log(JSON.stringify({cases:cases.length,clockFixture:{epochMilliseconds:0,timeZone:'UTC'},
 comparisonEngine:native?inspectNativeEngine():{node:process.version,v8:process.versions.v8},
 fullUnboundedClockSourceBridge:false}));
