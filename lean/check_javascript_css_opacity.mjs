/** Numeric opacity source/DOM checks. Finite comparisons do not prove renderer refinement. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw Error('Opacity comparisons require the pinned isolated Chromium worker');
const cases=[];const add=(name,source,expectedStatus)=>cases.push({name,source,expectedStatus});
const inputs=['0','1','0.5','.5','0.8','-0','-0.2','2','1.00000001','0.3333333333333333','0.000000123456789','+2e-5','1e40','-1e40','50%','-20%','250%','NaN','Infinity','1.','1e',' .5 ','0x1','1px','+','--1','1e+','1 2','0.5!important','1e-400','-1e-400','-0.0000001','1e308','-1e308','1e400','-1e400'];
for(let n=0;n<32;n++){inputs.push(String((n*1759%10007)/10007),`${n-16}.123456789123%`);}
for(const input of inputs){
 add('numeric opacity '+JSON.stringify(input),`var e=document.createElement('div'),s=e.style;s.opacity='.5';s.opacity=${JSON.stringify(input)};s.opacity+':'+s.cssText+':'+e.getAttribute('style');`);
 add('parsed opacity '+JSON.stringify(input),`var e=document.createElement('div');e.setAttribute('style',${JSON.stringify('opacity:'+input)});var s=e.style;s.opacity+':'+s.cssText+':'+e.getAttribute('style');`);
}
for(const input of ['0.12345678912345678','0.0000000123456789123','1.0000000001','-0.000000000123456789']){
 add('opacity cache survives another declaration '+input,`var e=document.createElement('div'),s=e.style;s.opacity=${JSON.stringify(input)};var a=s.opacity;s.left='2px';a+':'+s.opacity+':'+e.getAttribute('style');`);
 add('opacity reparses CSSOM assignment '+input,`var e=document.createElement('div'),s=e.style;s.opacity=${JSON.stringify(input)};var a=s.opacity;e.setAttribute('style',e.getAttribute('style'));a+':'+s.opacity+':'+s.cssText;`);
}
for(const value of ['null','undefined','false','true','{toString:function(){return null;}}','{toString:function(){return "0.123456789";}}'])add('opacity conversion '+value,`var e=document.createElement('div');e.style.opacity='.8';e.style.opacity=${value};e.style.opacity+':'+e.getAttribute('style');`);
add('opacity source conversion throw preserves declaration',`var e=document.createElement('div'),log='';e.style.opacity='.8';try{e.style.opacity={toString:function(){log+='s';throw 3;}};}catch(x){log+=x;}log+':'+e.style.opacity;`);
add('opacity native alias and priority',`var e=document.createElement('div'),s=e.style;s.setProperty('opacity','0.123456789','important');s.webkitOpacity+':'+s.getPropertyValue('opacity')+':'+s.getPropertyPriority('opacity')+':'+s.cssText;`);
const main=loadGameSource().sources['main.js'];
const formula=main.split('\n').find(s=>s.includes('var opacity=Math.min(6,(age/Game.lumpOverripeAge)*7)%1;'));
const assignment=main.split('\n').find(s=>s.includes("l('lumpsIcon2').style.opacity=opacity;"));
assert(formula&&assignment);
for(const age of [0,1,34,1000,100000,3600000,43200000,86399999,86400000,-1])for(const phase of [0,6])add('actual lump icon source '+age+':'+phase,`var icon=document.createElement('div');function l(id){if(id!=='lumpsIcon2')throw 'target';return icon;}var Game={lumpOverripeAge:86400000},age=${age},phase=${phase};${formula}if(phase>=6){opacity=1;}${assignment}icon.style.opacity+':'+icon.getAttribute('style');`);
for(const input of ['calc(1 / 2)','1e9999','0.5/*comment*/','\\30 .5'])add('explicit remaining opacity grammar '+input,`document.createElement('div').style.opacity=${JSON.stringify(input)};`,'unresolved');
const requests=cases.map(c=>({browserLibrary:true,ast:compileJavaScript(c.source,{name:c.name}),fuel:100000}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:24*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const observed=JSON.parse(child.stdout);
const native=runNativeBrowser(function(input){const values=input.cases.map(c=>{if(c.expectedStatus)return{status:c.expectedStatus};try{var value=(function(){return eval(c.source)})();return{status:'complete',value:{type:'string',units:Array.from(value,x=>x.charCodeAt(0))}}}catch(e){return{status:'throw',name:e.name}}});const precision=input.inputs.map(value=>{const e=document.createElement('div');e.style.opacity=value;const typed=e.attributeStyleMap.get('opacity');return typed?{status:'complete',internal:String(typed.value),text:e.style.opacity}:{status:'invalid'};});return{values,precision};}.toString(),{cases,inputs},{allowEval:true,allowInlineStyles:true});
const failures=[];for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(observed[i].status,cases[i].expectedStatus);else assert.deepEqual({status:observed[i].status,value:observed[i].value},native.result.values[i]);}catch(e){failures.push({name:cases[i].name,observed:observed[i],expected:native.result.values[i],message:e.message});}
const numeric=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(inputs.map(source=>({operation:'opacity',source}))),encoding:'utf8',timeout:60000,maxBuffer:16*1024*1024});
if(numeric.error)throw numeric.error;assert.equal(numeric.status,0,numeric.stderr);const numericObserved=JSON.parse(numeric.stdout);
for(let i=0;i<inputs.length;i++)try{assert.deepEqual(numericObserved[i],native.result.precision[i]);}catch(e){failures.push({name:'numeric backing '+inputs[i],observed:numericObserved[i],expected:native.result.precision[i],message:e.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length+inputs.length,passed:cases.length+inputs.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length+inputs.length,numericBackingCases:inputs.length,sourceCases:20,versions:native.versions,executableHash:native.executableHash,rendererRefinementVerified:false,computedStyleImplemented:false}));
