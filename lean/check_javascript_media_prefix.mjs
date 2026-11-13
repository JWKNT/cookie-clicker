/** Script MouseEvent dispatch fragment; this is not a physical input refinement. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';
const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,...extra});
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
add('new Audio()', 'var a=new Audio();a.paused;');
add('new Audio("")', 'var a=new Audio("");a.paused;');
add('new Audio("data:audio/mpeg;base64,")', 'var a=new Audio("data:audio/mpeg;base64,");a.paused;');
add('document.createElement("audio")', 'var a=document.createElement("audio");a.paused;');

add('paused is readonly under ordinary assignment', 'var a=new Audio();a.paused=false;a.paused;');
add('paused source getter is borrowed by actual interface', 'var g=Object.getOwnPropertyDescriptor(HTMLMediaElement.prototype,"paused").get;g.call(new Audio());');
add('paused receiver is checked before result', 'try{Object.getOwnPropertyDescriptor(HTMLMediaElement.prototype,"paused").get.call(document.createElement("div"));}catch(e){e.name;}');
add('paused getter constructor rejects', 'try{new (Object.getOwnPropertyDescriptor(HTMLMediaElement.prototype,"paused").get)();}catch(e){e.name;}');
add('paused after src assignment before a resource task', 'var a=new Audio();a.src="snd/clickb1.mp3";a.paused;');
add('pending source removal stays explicit', 'var a=new Audio();a.setAttribute("src","snd/clickb1.mp3");a.removeAttribute("src");a.paused;',{expectedStatus:'unresolved'});
add('removing absent source keeps paused', 'var a=new Audio();a.removeAttribute("src");a.paused;');
add('autoplay admission remains explicit', 'var a=new Audio();a.setAttribute("autoplay","");a.paused;',{expectedStatus:'unresolved'});
add('autoplay removal cannot restore never-played evidence', 'var a=new Audio();a.setAttribute("autoplay","");a.removeAttribute("autoplay");a.paused;',{expectedStatus:'unresolved'});
add('parsed autoplay removal cannot restore never-played evidence', 'var d=document.createElement("div");d.innerHTML="<audio autoplay></audio>";var a=d.firstChild;a.removeAttribute("autoplay");a.paused;',{expectedStatus:'unresolved'});
add('connected parsed autoplay removal cannot restore never-played evidence', 'var d=document.createElement("div");d.innerHTML="<audio autoplay></audio>";document.body.appendChild(d);var a=d.firstChild;a.removeAttribute("autoplay");a.paused;',{expectedStatus:'unresolved'});
add('native play remains an explicit state transition', 'new Audio().play();',{expectedStatus:'unresolved'});
const initialHtml='<!doctype html><html><head></head><body></body></html>';
const requests=cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),browserLibrary:true,fuel:500000,initialHtmlUnits:units(initialHtml)}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:60000,maxBuffer:16*1024*1024});
if(child.error)throw child.error;
assert.equal(child.status,0,child.stderr);
const observed=JSON.parse(child.stdout);
const worker=function(cases){
  function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='number'){var a=new DataView(new ArrayBuffer(8));a.setFloat64(0,v,false);return{type:'number',bits:a.getBigUint64(0,false).toString()};}throw Error('Expected primitive fixture result');}
  return cases.map(function(c){if(c.expectedStatus)return{status:c.expectedStatus};try{return{status:'complete',value:encode((function(){return eval(c.source);})())};}catch(e){return{status:'throw',name:e.name,message:e.message};}});
};
const native=runNativeBrowser(worker.toString(),cases,{allowEval:true});
const failures=[];
for(let i=0;i<cases.length;i++){try{if(cases[i].expectedStatus)assert.equal(observed[i].status,cases[i].expectedStatus);else assert.deepEqual({status:observed[i].status,value:observed[i].value},native.result[i]);}catch(error){failures.push({name:cases[i].name,observed:observed[i],expected:native.result[i],error:error.message});}}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,javascriptSemanticsVerified:false}));
