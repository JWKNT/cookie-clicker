/** Actual textarea focus/range callbacks and separate deferred event classes.
 * General scrolling, editing/range mutation and task interleavings remain explicit. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {compileCss} from '../model/css-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw Error('Focused selection comparisons require pinned Chromium');
const cases=[],add=(name,source,extra={})=>cases.push({name,source,...extra});
const prefix='var c=document.getElementById("c"),d=document.getElementById("d"),log=[];c.value="abcdef";d.value="12345";';
const css='html,body{margin:0;padding:0;border:0}body{overflow:hidden}textarea{position:absolute;left:10px;top:10px;width:200px;height:100px}';
const markup='<textarea id="c" readonly></textarea><textarea id="d" readonly></textarea>';
const fp='[c.selectionStart,c.selectionEnd,c.selectionDirection,d.selectionStart,d.selectionEnd,d.selectionDirection,document.activeElement.id].join(":")';
const listen=`[c,d].forEach(function(t){['focus','focusin','DOMFocusIn','blur','focusout','DOMFocusOut','select'].forEach(function(type){t.addEventListener(type,function(e){log.push(type+':'+t.id+':'+t.selectionStart+':'+t.selectionEnd+':'+t.selectionDirection+':'+document.activeElement.id+':'+e.bubbles+':'+e.isTrusted);});});});document.addEventListener('selectionchange',selectionListener=function(e){log.push('selectionchange:'+c.selectionStart+':'+c.selectionEnd+':'+c.selectionDirection+':'+d.selectionStart+':'+d.selectionEnd+':'+d.selectionDirection+':'+document.activeElement.id+':'+e.bubbles+':'+e.isTrusted);});`;
add('focus restore before callbacks',listen+`c.focus({preventScroll:true});log.join('|')+'#'+${fp};`);
add('direct select callbacks precede restoration',listen+`c.select();log.join('|')+'#'+${fp};`);
add('focus then select',listen+`c.focus({preventScroll:true});c.select();log.join('|')+'#'+${fp};`);
add('select nested focus changes final target',listen+`c.addEventListener('focus',function(){d.focus({preventScroll:true});});c.select();log.join('|')+'#'+${fp};`);
add('focus nested selection uses current cache',listen+`c.addEventListener('focus',function(){c.setSelectionRange(1,3,'backward');});c.select();log.join('|')+'#'+${fp};`);
add('focus nested blur',listen+`c.addEventListener('focus',function(){c.blur();});c.select();log.join('|')+'#'+${fp};`);
add('switch selected controls',listen+`c.focus({preventScroll:true});c.setSelectionRange(1,4,'backward');d.select();log.join('|')+'#'+${fp};`);
add('restore selected control after blur',listen+`c.focus({preventScroll:true});c.setSelectionRange(1,4,'backward');c.blur();c.setSelectionRange(2,3);c.focus({preventScroll:true});log.join('|')+'#'+${fp};`);
for(const first of ['none','forward','backward'])for(const next of ['none','forward','backward'])for(const collapsed of [false,true])
 add(`directions ${first} ${next} ${collapsed}`,`c.focus({preventScroll:true});c.setSelectionRange(2,${collapsed?2:4},'${first}');c.setSelectionRange(2,${collapsed?2:4},'${next}');${fp};`);
for(const property of ['selectionStart','selectionEnd','selectionDirection'])for(const value of ['0','3','99','-1','"backward"','undefined'])
 add(`focused setter ${property} ${value}`,`c.focus({preventScroll:true});c.setSelectionRange(1,4,'backward');c.${property}=${value};${fp};`);
for(const stages of [0,1])for(const script of [`c.focus({preventScroll:true});`,`c.select();`,`c.focus({preventScroll:true});c.select();`,`c.focus({preventScroll:true});c.setSelectionRange(1,2);c.setSelectionRange(2,3);`,`c.focus({preventScroll:true});c.select();c.select();`])
 add(`events ${stages} ${script}`,listen+script,{tasks:100,stages,after:`log.filter(function(x){return x.indexOf('selectionchange:')===0;}).join('|')+'#'+log.filter(function(x){return x.indexOf('selectionchange:')!==0&&x.indexOf('select:')!==0;}).join('|')+${stages?"'!'+log.filter(function(x){return x.indexOf('select:')===0;}).join('|')":"''"}+'#'+${fp};`});
for(const style of ['','textarea{width:0;height:0}','textarea{display:none}','textarea{visibility:hidden}','body{visibility:hidden}textarea{visibility:visible}','body{display:none}','textarea{opacity:0}','textarea{display:block}','textarea{display:inline}','textarea{position:absolute;left:-10000px}'])
 add('focus style '+style,`c.focus({preventScroll:true});${fp};`,{cssExtra:style});
for(const style of ['textarea{content-visibility:auto}','textarea{contain:paint}','textarea{display:contents}','textarea{user-select:none}','textarea{-webkit-user-select:none}','textarea{float:left}','textarea{clear:both}','textarea{content:"x"}','textarea{all:initial}','textarea{transition:all 1s}'])
 add('closed style '+style,`c.focus({preventScroll:true});`,{cssExtra:style,expectedStatus:'unresolved'});
for(const attr of ['-webkit-user-select:none','user-select:none','content:"x"','contain:paint'])
 add('closed inline '+attr,`c.setAttribute('style',${JSON.stringify(attr)});c.focus({preventScroll:true});`,{expectedStatus:'unresolved'});
add('selected value mutation remains explicit',`c.focus({preventScroll:true});c.value='changed';`,{expectedStatus:'unresolved'});
add('selected equal value allowed',`c.focus({preventScroll:true});c.value='abcdef';${fp};`);
add('default focus scrolling remains explicit',`c.focus();`,{expectedStatus:'unresolved'});
const native=runNativeBrowser(async function(input){
 function enc(v){if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(v===undefined)return{type:'undefined'};if(typeof v==='boolean')return{type:'boolean',value:v};throw Error('result');}
 const result=[];
 for(const test of input.cases){
  if(test.expectedStatus){result.push({status:test.expectedStatus});continue;}
  document.documentElement.innerHTML='<head><style>'+input.css+(test.cssExtra||'')+'</style></head><body>'+input.markup+'</body>';
  getSelection().removeAllRanges();await new Promise(r=>setTimeout(r,0));await new Promise(r=>requestAnimationFrame(r));
  const context=(function(){var selectionListener;var value=eval(input.prefix+test.source);return{value,read:function(){return eval(test.after);},remove:function(){if(selectionListener)document.removeEventListener('selectionchange',selectionListener);}};})();
  if(test.tasks)await new Promise(r=>setTimeout(r,0));
  for(let i=0;i<(test.stages||0);i++)await new Promise(r=>requestAnimationFrame(r));
  result.push({status:'complete',value:enc(test.after?context.read():context.value)});context.remove();
 }
 return result;
}.toString(),{cases,prefix,css,markup},{allowEval:true,allowInlineStyles:true});
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const requests=cases.map(c=>({ast:compileJavaScript(prefix+c.source,{name:c.name}),browserLibrary:true,fuel:500000,
 initialHtmlUnits:units('<!doctype html><html><head><link rel="stylesheet" href="selection.css"></head><body>'+markup+'</body></html>'),
 loadedStylesheets:[compileCss(css+(c.cssExtra||''),{name:'selection.css'})],fixturePageFocused:true,
 selectionEventTasks:c.tasks||0,animationEventStages:c.stages||0,
 ...(c.after?{afterAnimationProgram:compileJavaScript(c.after,{name:c.name+' result'})}:{})}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:64*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(actual[i].status,cases[i].expectedStatus);else assert.deepEqual({status:actual[i].status,value:actual[i].value},native.result[i]);}catch(e){failures.push({name:cases[i].name,actual:actual[i],expected:native.result[i],error:e.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,fullSelectionRefinementVerified:false,renderingCadenceSpecified:false}));
