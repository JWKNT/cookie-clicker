import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

const useEngine=process.argv.includes('--engine');
const cases=[];
const add=(name,text)=>cases.push({name,units:Array.from({length:text.length},(_,i)=>text.charCodeAt(i))});
const corpus=['','abc xyz',';/?:@&=+$,#-_.!~*\'()','\u0000\t\n\r\u000c','éßΩ中😀𐐀',
 '\ud800','\udc00','x\ud800y','\ud800\ud800','\uffff','%','%0','%gg','%uD800','%u123','%U1234',
 '%2f%3A%23%20%00','%C3%A9','%C0%80','%E0%80%80','%ED%A0%80','%F0%80%80%80','%F4%90%80%80',
 '%F4%8F%BF%BF','%E2%82','%E2x%AC','%80','%FF','%u00e9%2f%uD83D%uDE00'];
for(const text of corpus)for(const name of ['encodeURI','encodeURIComponent','decodeURI','decodeURIComponent','escape','unescape'])add(name,text);
for(let i=0;i<65536;i++){
 const s=String.fromCharCode(i);
 add('encodeURIComponent',s);add('escape',s);
 add('unescape','%u'+i.toString(16).padStart(4,'0'));
 if(i<0xd800||i>0xdfff)add('decodeURIComponent',encodeURIComponent(s));
}
let seed=19;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;};
for(let i=0;i<500;i++){
 const n=random()%100,s=Array.from({length:n},()=>String.fromCharCode(random()%65536)).join('');
 for(const name of ['encodeURI','decodeURI','escape','unescape'])add(name,s);
 const b=Array.from({length:n},()=>String.fromCharCode(random()%256)).join('');
 add('btoa',b);add('atob',btoa(b));
}
for(const s of ['','a','ab','abc','abcd','a=','ab=','ab==','abc=','abcd=','abcd====','====','ab===',
 'a b\tc\nd\rf\f','YQ==','YQ','Y R==','YWJ','AA==','AB==','/+//','_-','é','😀','\ud800','\u000b','\u00a0'])add('atob',s);
for(const s of corpus)add('btoa',s);
const worker=`const fs=require('fs');const cases=JSON.parse(fs.readFileSync(0,'utf8'));const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));process.stdout.write(JSON.stringify(cases.map(c=>{try{return{units:units(global[c.name](String.fromCharCode(...c.units)))}}catch(e){return{error:e.name}}})));`;
const nativeIndices=cases.map((c,i)=>i).filter(i=>!['btoa','atob'].includes(cases[i].name));
const expected=cases.map(c=>{
 try{const s=globalThis[c.name](String.fromCharCode(...c.units));return{units:Array.from({length:s.length},(_,i)=>s.charCodeAt(i))};}
 catch(e){return{error:e.name};}
});
let browserIdentity=null;
if(useEngine){
 const native=runNativeEngine(worker,nativeIndices.map(i=>cases[i]),{timeout:300000});
 for(let j=0;j<nativeIndices.length;j++)expected[nativeIndices[j]]=native[j];
 const browserIndices=cases.map((c,i)=>i).filter(i=>['btoa','atob'].includes(cases[i].name));
 const browser=runNativeBrowser(`cases=>cases.map(c=>{try{const s=globalThis[c.name](String.fromCharCode(...c.units));return{units:Array.from({length:s.length},(_,i)=>s.charCodeAt(i))};}catch(e){return{error:e.name};}})`,browserIndices.map(i=>cases[i]));
 for(let j=0;j<browserIndices.length;j++)expected[browserIndices[j]]=browser.result[j];
 browserIdentity={renderer:browser.renderer,versions:browser.versions,executableHash:browser.executableHash,
  gameEntryPointExecuted:browser.gameEntryPointExecuted,externalNetworking:browser.externalNetworking};
}
const result=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsencodingcheck',import.meta.url)),[],{
 input:JSON.stringify(cases),encoding:'utf8',timeout:300000,maxBuffer:128*1024*1024,
});
if(result.error)throw result.error;
assert.equal(result.status,0,result.stderr);
const actual=JSON.parse(result.stdout);assert.equal(actual.length,cases.length);
for(let i=0;i<cases.length;i++)assert.deepEqual(actual[i],expected[i],JSON.stringify(cases[i]));
console.log(JSON.stringify({checks:cases.length,pinnedEngineCases:useEngine?nativeIndices.length:0,
 base64ComparisonEngine:browserIdentity??{node:process.version,v8:process.versions.v8},
 uriComparisonEngine:useEngine?inspectNativeEngine():{node:process.version,v8:process.versions.v8},
 sourceRefinementProved:false}));
