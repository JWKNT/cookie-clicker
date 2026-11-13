/** Raw console-event and return-value comparisons; no display-formatting oracle. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript, numberLiteralBits } from '../model/javascript-ast.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

if (!process.argv.includes('--engine')) throw new Error('Console comparisons require --engine and the isolated native Chromium worker');
const cases = [
  ['empty log emits no console event', 'console.log();'],
  ['language log retains its exact string', 'console.log(\'Loaded language "english".\');'],
  ['null and undefined remain distinct arguments', 'console.log(null,undefined);'],
  ['number arguments retain signed zero and nonfinite values', 'console.log(-0,NaN,Infinity,-Infinity,0.1);'],
  ['multiple primitive arguments retain order', 'console.log("x",2,false,null,undefined);'],
  ['single format marker is a literal argument', 'console.log("%s");'],
  ['primitive format arguments retain raw inspector values', 'console.log("%s:%i:%f:%c",3,1.2,4.5,"color:red");'],
  ['detached log callable ignores receiver', 'var f=console.log;f("detached");'],
  ['borrowed log accepts arbitrary receiver', 'console.log.call({},"borrowed");'],
  ['borrowed log accepts null receiver', 'console.log.call(null,"null receiver");'],
  ['apply uses the exact native callable alias', 'console.log.apply(null,["applied",2]);'],
  ['log construction throws before any console event', 'try{new console.log("never logged");}catch(error){error.name;}'],
  ['source argument evaluation precedes the native call', 'var s="";function f(x){s+=x;return x;}console.log(f(1),f(2));s;'],
  ['argument throw prevents the console call', 'try{console.log("before",(function(){throw 7;})());}catch(error){error;}'],
  ['multiple calls retain event ordering', 'console.log("first");console.log();console.log("second");'],
  ['known console property absence is undefined', 'typeof console.cookieClickerAuditAbsent;'],
  ['object preview remains explicit', 'console.log({toString:function(){throw 99;}});', 'unresolved'],
  ['other console operations remain explicit', 'console.warn("unimplemented warning");', 'unresolved'],
].map(([name,source,expectedStatus]) => ({name,source,expectedStatus}));

const request = cases.map(entry => ({ast:compileJavaScript(entry.source,{name:entry.name}),browserLibrary:true,fuel:200000}));
const child = spawnSync(fileURLToPath(new URL('./.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{
  input:JSON.stringify(request),encoding:'utf8',timeout:60000,maxBuffer:1024*1024,
});
if (child.error) throw child.error;
assert.equal(child.status,0,child.stderr);
const actual = JSON.parse(child.stdout);
const marker = 'cookie-clicker-console-fixture-boundary';
const native = runNativeBrowser(function (input) {
  const encode = value => {
    if (value===undefined) return {type:'undefined'};
    if (value===null) return {type:'null'};
    if (typeof value==='boolean') return {type:'boolean',value};
    if (typeof value==='string') return {type:'string',units:Array.from({length:value.length},(_,i)=>value.charCodeAt(i))};
    if (typeof value==='number') {const view=new DataView(new ArrayBuffer(8));view.setFloat64(0,value,false);return {type:'number',bits:view.getBigUint64(0,false).toString()};}
    throw Error('Console comparison must return a primitive');
  };
  const run = function (source) {return eval(source);};
  return input.cases.map(entry=>{
    console.log(input.marker,entry.index);
    if (entry.skip) return null;
    try {return {status:'complete',value:encode(run(entry.source))};}
    catch (error) {return {status:'throw',value:encode(error)};}
  });
}.toString(),{marker,cases:cases.map((entry,index)=>({source:entry.source,index,skip:!!entry.expectedStatus}))},
{allowEval:true,captureConsoleEvents:true});

const encodeRemote = value => {
  if (value.type==='undefined') return {type:'undefined'};
  if (value.type==='object' && value.subtype==='null') return {type:'null'};
  if (value.type==='boolean') return {type:'boolean',value:value.value};
  if (value.type==='string') return {type:'string',units:Array.from({length:value.value.length},(_,i)=>value.value.charCodeAt(i))};
  if (value.type==='number') return {type:'number',bits:numberLiteralBits(value.unserializableValue===undefined?value.value:Number(value.unserializableValue))};
  throw Error(`Unexpected native console argument ${JSON.stringify(value)}`);
};
const expectedEvents = cases.map(()=>[]);
let activeIndex = -1;
for (const event of native.consoleEvents) {
  if (event.type==='log' && event.args.length===2 && event.args[0].value===marker) {
    activeIndex=event.args[1].value;
    assert(Number.isInteger(activeIndex) && activeIndex>=0 && activeIndex<cases.length);
  } else {
    assert(activeIndex>=0,'Unexpected console event before fixture marker');
    expectedEvents[activeIndex].push({type:event.type,arguments:event.args.map(encodeRemote)});
  }
}
const failures=[];
for (let index=0;index<cases.length;index++) {
  try {
    if(cases[index].expectedStatus) assert.equal(actual[index].status,cases[index].expectedStatus);
    else {
      assert.deepEqual({status:actual[index].status,value:actual[index].value},native.result[index]);
      assert.deepEqual(actual[index].consoleEvents,expectedEvents[index]);
    }
    assert.equal(actual[index].javascriptSemanticsVerified,false);
  } catch(error) {failures.push({name:cases[index].name,actual:actual[index],message:error.message});}
}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,
  nativeCompared:cases.filter(entry=>!entry.expectedStatus).length,versions:native.versions,
  executableHash:native.executableHash,gameEntryPointExecuted:native.gameEntryPointExecuted,
  rawConsoleEventsOnly:true,javascriptSemanticsVerified:false}));
