/** Native focus callbacks on the explicitly supported layout fragment.
 * This is not a trusted pointer/keyboard or full-renderer refinement proof. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript,numberLiteralBits} from '../model/javascript-ast.mjs';
import {compileCss} from '../model/css-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw Error('Focus comparisons require pinned isolated Chromium');
const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,...extra});
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const css='html,body,div{margin:0;padding:0;border:0}html,body{width:100%;height:100%}body{overflow:hidden}div{position:absolute;left:0;top:0;width:40px;height:40px}';
const markup='<div id="a" tabindex="0"></div><div id="b" tabindex="0"></div><div id="c" tabindex="0"></div><div id="plain"></div>';
const prefix='var a=document.getElementById("a"),b=document.getElementById("b"),c=document.getElementById("c"),log=[];';
const listen=`[a,b,c].forEach(function(n){['blur','focusout','DOMFocusOut','focus','focusin','DOMFocusIn'].forEach(function(t){n.addEventListener(t,function(e){log.push(t+':'+e.target.id+':'+(e.relatedTarget?e.relatedTarget.id:'null')+':'+document.activeElement.id);});});});`;
add('initial active element and page focus',`document.activeElement===document.body&&document.hasFocus();`);
add('focus source callbacks and blur order',listen+`a.focus({preventScroll:true});b.focus({preventScroll:true});b.blur();log.join('|');`);
add('same focused target does not redispatch or require scrolling',listen+`a.focus({preventScroll:true});a.focus();a.focus({preventScroll:false});log.join('|');`);
add('blur of a nonfocused target is a no-op',listen+`a.focus({preventScroll:true});b.blur();log.join('|')+':'+document.activeElement.id;`);
add('native focus flags and representation',`a.addEventListener('focus',function(e){log.push([e instanceof FocusEvent,e instanceof UIEvent,e instanceof Event,e.bubbles,e.cancelable,e.composed,e.isTrusted,e.detail,e.which,e.view===window,e.sourceCapabilities,e.relatedTarget].join(','));});a.focus({preventScroll:true});log.join('|');`);
add('focus events capture and bubble in native order',`[document,a].forEach(function(n){['focus','focusin','DOMFocusIn'].forEach(function(t){n.addEventListener(t,function(e){log.push((n===document?'d':'a')+':'+t+':'+e.eventPhase);},true);n.addEventListener(t,function(e){log.push((n===document?'d':'a')+':'+t+':'+e.eventPhase);});});});a.focus({preventScroll:true});log.join('|');`);
add('nested focus from focus stops later old focus-in events',listen+`a.addEventListener('focus',function(){b.focus({preventScroll:true});});a.focus({preventScroll:true});log.join('|');`);
add('nested focus from focus-in stops old DOMFocusIn',listen+`a.addEventListener('focusin',function(){b.focus({preventScroll:true});});a.focus({preventScroll:true});log.join('|');`);
add('nested focus from blur replaces the requested target',listen+`a.focus({preventScroll:true});log=[];a.addEventListener('blur',function(){c.focus({preventScroll:true});});b.focus({preventScroll:true});log.join('|')+':'+document.activeElement.id;`);
add('nested focus from focusout preserves remaining old event',listen+`a.focus({preventScroll:true});log=[];a.addEventListener('focusout',function(){c.focus({preventScroll:true});});b.focus({preventScroll:true});log.join('|')+':'+document.activeElement.id;`);
add('blur inside focus callback terminates focus sequence',listen+`a.addEventListener('focus',function(){a.blur();});a.focus({preventScroll:true});log.join('|')+':'+(document.activeElement===document.body);`);
add('focus callback exception is reported and procedure continues',listen+`a.addEventListener('focus',function(){throw 7;});a.focus({preventScroll:true});log.join('|');`);
add('preventDefault cannot cancel native focus',`a.addEventListener('focus',function(e){e.preventDefault();log.push(e.defaultPrevented);});a.focus({preventScroll:true});log.join(',')+':'+(document.activeElement===a);`);
add('stopImmediatePropagation affects one event only',`a.addEventListener('focus',function(e){log.push('first');e.stopImmediatePropagation();});a.addEventListener('focus',function(){log.push('wrong');});a.addEventListener('focusin',function(){log.push('in');});a.focus({preventScroll:true});log.join(',');`);
add('detached target ignores focus after converting options',`var d=document.createElement('div');d.tabIndex=0;d.focus({get preventScroll(){log.push('read');return false;}});log.join(',')+':'+(document.activeElement===document.body);`);
add('unfocusable target is a no-op',`document.getElementById('plain').focus({preventScroll:true});document.activeElement===document.body;`);
for(const extra of ['#plain{border:4px ridge #663311;height:auto}',
  '#plain:hover{width:81px}',
  'body{-webkit-user-modify:read-only}#plain{width:auto;height:auto;padding:24px}',
  'body{-webkit-user-modify:read-write}#plain{-webkit-user-modify:read-only}'])
  add(`ordinary no-focus conjunction ${extra}`,`document.getElementById('plain').focus();document.activeElement===document.body;`,{cssExtra:extra});
for(const index of ['', 'bad', '2147483648'])add(`invalid tabindex does not require geometry ${JSON.stringify(index)}`,
  `var p=document.getElementById('plain');p.setAttribute('tabindex',${JSON.stringify(index)});p.focus();document.activeElement===document.body;`,
  {cssExtra:'#plain{border:4px ridge #663311;height:auto}'});
add('ordinary inherited editing cannot be omitted',`document.getElementById('plain').focus();`,
  {cssExtra:'body{-webkit-user-modify:read-write}',expectedStatus:'unresolved'});
add('options read only preventScroll and do not coerce boolean object',`a.focus({get preventScroll(){log.push('scroll');return {valueOf:function(){log.push('wrong');}};},get focusVisible(){log.push('wrong');}});log.join(',')+':'+document.activeElement.id;`);
add('source options exception occurs before focus',`try{a.focus({get preventScroll(){throw 17;}});}catch(e){log.push(e);}log.join(',')+':'+(document.activeElement===document.body);`);
for(const option of ['null','undefined','false','7','"x"'])add(`unfocusable target options ${option}`,`try{document.getElementById('plain').focus(${option});'ok';}catch(e){e.name;}`);
add('focus options reentry uses current focus state',listen+`a.focus({get preventScroll(){b.focus({preventScroll:true});return true;}});log.join('|');`);
add('wrong focus receiver rejects before dictionary getter',`try{HTMLElement.prototype.focus.call({},{get preventScroll(){log.push('wrong');return true;}});}catch(e){log.push(e.name);}log.join(',');`);
add('blur wrong receiver throws',`try{HTMLElement.prototype.blur.call({});}catch(e){e.name;}`);
add('saved focus method retains captured interface behavior',`var saved=HTMLElement.prototype.focus,old=HTMLElement;HTMLElement=function(){};saved.call(a,{preventScroll:true});HTMLElement=old;document.activeElement===a;`);
for(const v of ['0','-1','1.9','4294967297','NaN','Infinity','null','undefined','{valueOf:function(){log.push("n");return 3;}}'])add(`tabIndex setter ${v}`,`a.tabIndex=${v};log.join(',')+':'+a.tabIndex+':'+a.getAttribute('tabindex');`);
for(const v of ['',' ','+1x','-2.9','01','2147483647','2147483648','-2147483648','-2147483649','1e2','\t+12!','no'])add(`tabIndex HTML integer ${JSON.stringify(v)}`,`a.setAttribute('tabindex',${JSON.stringify(v)});a.tabIndex;`);
for(const tag of ['div','span','a','button','input','select','textarea'])add(`${tag} default tabIndex`,`document.createElement('${tag}').tabIndex;`);
for(const extra of ['#a{display:none}','#a{visibility:hidden}','#a{visibility:collapse}','#a{width:0;height:0}'])add(`focus CSS ${extra}`,`a.focus({preventScroll:true});document.activeElement===a;`,{cssExtra:extra});
add('native activeElement is null without body',`document.documentElement.removeChild(document.body);document.activeElement===null;`);
add('tabIndex setter omitted argument converts undefined to zero',`Object.getOwnPropertyDescriptor(HTMLElement.prototype,'tabIndex').set.call(a);a.tabIndex+':'+a.getAttribute('tabindex');`);
for(const tag of ['iframe','object'])add(`${tag} uncatalogued interface remains explicit`,`document.createElement('${tag}').tabIndex;`,{expectedStatus:'unresolved'});
add('activeElement fallback ignores a nested body under head',`var old=document.body;document.documentElement.removeChild(old);document.head.appendChild(document.createElement('body'));document.activeElement===null;`);
add('activeElement uses replacement direct body',`var old=document.body,replacement=document.createElement('body');document.documentElement.removeChild(old);document.documentElement.appendChild(replacement);document.activeElement===replacement;`);
add('activeElement receiver brand is required',`try{Object.getOwnPropertyDescriptor(Document.prototype,'activeElement').get.call({});}catch(e){e.name;}`);
add('hasFocus receiver brand is required',`try{Document.prototype.hasFocus.call({});}catch(e){e.name;}`);
add('focus constructor is rejected',`try{new HTMLElement.prototype.focus();}catch(e){e.name;}`);
add('tabIndex conversion throw preserves attribute',`try{a.tabIndex={valueOf:function(){throw 7;}};}catch(e){log.push(e);}log.join(',')+':'+a.getAttribute('tabindex');`);
add('unconfigured page focus remains explicit',`document.hasFocus();`,{pageFocused:null,expectedStatus:'unresolved'});
add('default scroll-into-view remains explicit',`a.focus();`,{expectedStatus:'unresolved'});
add('editable focus selection remains explicit',`a.setAttribute('contenteditable','true');a.focus({preventScroll:true});`,{expectedStatus:'unresolved'});
add('focused subtree removal lifecycle remains explicit',`a.focus({preventScroll:true});a.parentNode.removeChild(a);`,{expectedStatus:'unresolved'});
add('focused class/style lifecycle remains explicit',`a.focus({preventScroll:true});a.style.display='none';`,{expectedStatus:'unresolved'});
add('focused text mutation lifecycle remains explicit',`a.focus({preventScroll:true});a.textContent='changed';`,{expectedStatus:'unresolved'});
// Constructor and synthetic event paths use exactly the same concrete FocusEvent data.
for(const value of ['undefined','null','a','window','{}','7'])add(`FocusEvent relatedTarget ${value}`,`try{var e=new FocusEvent('focus',{relatedTarget:${value}});(e.relatedTarget===${value})+':'+e.type;}catch(e){e.name;}`);
add('FocusEvent ordered source dictionary reads',`var names=['bubbles','cancelable','composed','detail','sourceCapabilities','view','relatedTarget'],options={};names.forEach(function(n){Object.defineProperty(options,n,{get:function(){log.push(n);}});});new FocusEvent('focus',options);log.join(',');`);
add('FocusEvent brand and native fields',`var e=new FocusEvent('focus',{bubbles:true,detail:4294967297,view:window,relatedTarget:a});[e instanceof FocusEvent,e instanceof UIEvent,e instanceof Event,e.detail,e.view===window,e.relatedTarget===a,e.which,e.isTrusted].join(',');`);
add('FocusEvent saved constructor identity',`var Saved=FocusEvent;FocusEvent=function(){};var e=new Saved('focus'),r=e instanceof Saved;FocusEvent=Saved;r;`);
for(const connected of [false,true])for(const same of [false,true])add(`synthetic related target connected=${connected} same=${same}`,`var d=${connected?'a':"document.createElement('div')"},r=${same?'d':connected?'b':"document.createElement('div')"};var e=new FocusEvent('focus',{relatedTarget:r});d.addEventListener('focus',function(e){log.push((e.target===d)+':'+(e.relatedTarget===r));});d.dispatchEvent(e);log.join(',')+':'+(e.target===d)+':'+(e.target===null)+':'+(e.relatedTarget===r)+':'+(e.relatedTarget===null);`);
const worker=function(input){
  function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}throw Error('Fixture result must be primitive');}
  var values=input.cases.map(function(c){
    if(c.expectedStatus)return{status:c.expectedStatus};
    if(document.activeElement&&document.activeElement.blur)document.activeElement.blur();
    document.documentElement.innerHTML='<head><style>'+input.css+(c.cssExtra||'')+'</style></head><body>'+input.markup+'</body>';
    try{return{status:'complete',value:encode((function(){return eval(input.prefix+c.source);})())};}
    catch(e){return{status:'throw',name:e.name,message:e.message};}
  });return{values:values,viewport:[innerWidth,innerHeight],pageFocused:document.hasFocus()};
};
const native=runNativeBrowser(worker.toString(),{cases,css,markup,prefix},{allowEval:true,allowInlineStyles:true});
assert.equal(native.result.pageFocused,true,'Pinned fixture must have page focus');
const requests=cases.map(c=>({ast:compileJavaScript(prefix+c.source,{name:c.name}),browserLibrary:true,fuel:500000,
  initialHtmlUnits:units('<!doctype html><html><head><link rel="stylesheet" href="focus.css"></head><body>'+markup+'</body></html>'),
  loadedStylesheets:[compileCss(css+(c.cssExtra??''),{name:'focus.css'})],
  ...(c.pageFocused===null?{}:{fixturePageFocused:true}),
  fixtureWindowData:['innerWidth','innerHeight'].map((name,i)=>({name,value:{kind:'number',bits:numberLiteralBits(native.result.viewport[i])}}))}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(actual[i].status,cases[i].expectedStatus);else assert.deepEqual({status:actual[i].status,value:actual[i].value},native.result.values[i]);}catch(error){failures.push({name:cases[i].name,observed:actual[i],expected:native.result.values[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,fullFocusRefinementVerified:false,trustedInputRefinementVerified:false}));
