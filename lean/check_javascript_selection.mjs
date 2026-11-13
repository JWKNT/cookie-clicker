/** Pinned textarea cache operations and explicit animation-event dispatch stages.
 * No refresh rate, rendering/task race, frame-selection or scrolling claim. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw Error('Selection checks require pinned isolated Chromium');
const cases=[],add=(name,source,options={})=>cases.push({name,source,...options});
const prefix='var c=document.createElement("textarea"),log=[];c.value="abcdef";';
const fingerprint='[c.value,c.selectionStart,c.selectionEnd,c.selectionDirection].join("|")';
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
for(const start of [0,1,6,9,-1,4294967296,4294967297,NaN,Infinity])
  for(const finish of [0,3,9])add(`range ${start} ${finish}`,`c.setSelectionRange(${start},${finish});${fingerprint};`);
for(const direction of ['undefined','null','"none"','"forward"','"backward"','"other"','7'])
  add(`direction ${direction}`,`c.setSelectionRange(1,4,${direction});${fingerprint};`);
for(const name of ['selectionStart','selectionEnd','selectionDirection']){
  for(const value of ['undefined','null','-1','2','4294967297','"backward"','"forward"'])
    add(`${name} setter ${value}`,`c.setSelectionRange(1,4,'backward');c.${name}=${value};${fingerprint};`);
  add(`${name} omitted setter argument`,`Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype,'${name}').set.call(c);${fingerprint};`);
  add(`${name} receiver before argument coercion`,`try{Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype,'${name}').set.call({}, {valueOf:function(){log.push('bad');return 1;},toString:function(){log.push('bad');return 'forward';}});}catch(e){log.push(e.name);}log.join(',');`);
}
for(const args of ['','1'])add(`range missing ${args}`,`try{c.setSelectionRange(${args});}catch(e){log.push(e.name);}log.join(',')+':'+${fingerprint};`);
add('range conversion order and nested value writes',`c.setSelectionRange({valueOf:function(){log.push('a');c.value='x';return 1;}},{valueOf:function(){log.push('b');c.value='wxyz';return 3;}},{toString:function(){log.push('d');return 'backward';}});log.join(',')+':'+${fingerprint};`);
add('range conversion throw preserves prior callback writes',`try{c.setSelectionRange({valueOf:function(){c.value='nested';return 1;}},{valueOf:function(){throw 7;}},{toString:function(){log.push('bad');return 'none';}});}catch(e){log.push(e);}log.join(',')+':'+${fingerprint};`);
add('select ignores arguments',`c.select({toString:function(){throw 7;}});${fingerprint};`);
add('select on detached textarea does not focus',`c.select();(document.activeElement===document.body)+':'+${fingerprint};`);
add('select on disabled connected textarea does not focus',`c.disabled=true;document.body.appendChild(c);c.select();(document.activeElement===document.body)+':'+${fingerprint};`);
add('select constructor throws',`try{new c.select();}catch(e){e.name;}`);
add('select wrong receiver throws',`try{HTMLTextAreaElement.prototype.select.call({});}catch(e){e.name;}`);
const record=`c.addEventListener('select',function(e){log.push([e.type,e.bubbles,e.cancelable,e.composed,e.isTrusted,e.target===c,e.currentTarget===c,e.eventPhase,c.selectionStart,c.selectionEnd,c.selectionDirection].join(':'));});`;
add('select callback is deferred',record+`c.select();log.push('sync');log.join('|');`,{pending:1});
add('explicit event stage dispatches detached target',record+`c.select();log.push('sync');`,{stages:1,after:`log.join('|');`,pending:0});
add('range changes enqueue distinct events without coalescing',record+`c.setSelectionRange(1,2);c.setSelectionRange(2,4);c.setSelectionRange(2,4);`,{stages:1,after:`log.join('|');`,pending:0});
add('unchanged range enqueues nothing',record+`c.setSelectionRange(6,6);`,{stages:1,after:`log.join('|');`,pending:0});
add('direction-only change enqueues event',record+`c.setSelectionRange(6,6,'backward');`,{stages:1,after:`log.join('|');`,pending:0});
for(const stages of [1,2])add(`events added by callback wait until later stage ${stages}`,
  `c.addEventListener('select',function(){log.push(c.selectionStart);if(log.length===1)c.setSelectionRange(2,3);});c.setSelectionRange(1,3);`,
  {stages,after:`log.join('|');`,pending:stages===1?1:0});
add('listeners are observed at dispatch time',`c.select();c.addEventListener('select',function(){log.push('late');});`,{stages:1,after:`log.join('|');`,pending:0});
add('event listener exceptions do not discard subsequent events',`c.addEventListener('select',function(){log.push('first');throw 7;});c.addEventListener('select',function(){log.push('second');});c.select();c.setSelectionRange(1,3);`,{stages:1,after:`log.join('|');`,pending:0});
add('detachment preserves queued select event',`c.disabled=true;document.body.appendChild(c);c.addEventListener('select',function(){log.push('selected');});c.select();document.body.removeChild(c);`,{stages:1,after:`log.join('|');`,pending:0});
add('task order cannot bypass pending animation events',`c.select();setTimeout(function(){log.push('timer');},0);`,{taskBudget:1,expectedStatus:'unresolved',pending:1});
add('connected focus requiring layout remains explicit',`document.body.appendChild(c);c.select();`,{expectedStatus:'unresolved',pending:1});
const native=runNativeBrowser(async function(input){
  function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}throw Error('primitive result required');}
  const values=[];
  for(const test of input.cases){
    if(test.expectedStatus){values.push({status:test.expectedStatus});continue;}
    document.body.textContent='';
    const context=(function(){var result=eval(input.prefix+test.source);return{result:result,read:function(){return eval(test.after);}};})();
    for(let i=0;i<(test.stages||0);i++)await new Promise(resolve=>requestAnimationFrame(resolve));
    values.push({status:'complete',value:encode(test.after?context.read():context.result)});
  }
  return values;
}.toString(),{cases,prefix},{allowEval:true});
const requests=cases.map(c=>({ast:compileJavaScript(prefix+c.source,{name:c.name}),browserLibrary:true,fuel:500000,
  initialHtmlUnits:units('<!doctype html><html><head></head><body></body></html>'),fixturePageFocused:true,
  animationEventStages:c.stages||0,taskBudget:c.taskBudget||0,
  ...(c.after?{afterAnimationProgram:compileJavaScript(c.after,{name:c.name+' result'})}:{})}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{
  if(cases[i].expectedStatus)assert.equal(actual[i].status,cases[i].expectedStatus);
  else assert.deepEqual({status:actual[i].status,value:actual[i].value},native.result[i]);
  if(cases[i].pending!==undefined)assert.equal(actual[i].pendingAnimationEvents,cases[i].pending);
}catch(error){failures.push({name:cases[i].name,observed:actual[i],expected:native.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,
  versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,fullSelectionRefinementVerified:false,renderingCadenceSpecified:false}));
