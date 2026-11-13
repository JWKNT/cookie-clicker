/** Native content-handler comparisons; no claim of general parser/browser refinement. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import {fileURLToPath} from 'node:url';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';

if(!process.argv.includes('--engine')) throw Error('Inline comparisons require the pinned isolated Chromium worker');
const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,...extra});
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const setup='var d=document.createElement("div");';
add('compile actual attribute and cancel dispatch',setup+String.raw`d.setAttribute("onclick","return false;");var e=new Event("click",{cancelable:true});d.dispatchEvent(e)+":"+e.defaultPrevented;`);
add('parameter is actual dispatched event',setup+String.raw`d.setAttribute("onclick","this.auditType=event.type;");d.dispatchEvent(new Event("click"));d.auditType;`);
add('exact name length and UTF16 source text',setup+String.raw`d.setAttribute("onclick","/* α */ return id;\n");var f=d.onclick;f.name+":"+f.length+":"+Function.prototype.toString.call(f);`);
add('compiled getter is cached',setup+String.raw`d.setAttribute("onclick","return id;");d.onclick===d.onclick;`);
add('same source attribute mutation creates new closure',setup+String.raw`d.setAttribute("onclick","return id;");var f=d.onclick;d.setAttribute("onclick","return id;");f===d.onclick;`);
add('lexical element survives different call receiver',setup+String.raw`d.id="original";d.setAttribute("onclick","return id;");var f=d.onclick;Function.prototype.call.call(f,{id:"different"});`);
add('live captured element value',setup+String.raw`d.id="before";d.setAttribute("onclick","return id;");var f=d.onclick;d.id="after";f();`);
add('this value differs from captured element',setup+String.raw`d.id="original";d.setAttribute("onclick","return id+\":\"+this.id;");Function.prototype.call.call(d.onclick,{id:"different"});`);
add('native method implicit receiver is element',setup+String.raw`d.id="native-method";d.setAttribute("onclick","return getAttribute(\"id\");");d.onclick();`);
add('global identifier crosses both native object scopes',setup+String.raw`var auditGlobal=17;d.setAttribute("onclick","return auditGlobal+1;");d.onclick();`);
add('element own binding shadows document and global',setup+String.raw`var auditScope="global";Object.defineProperty(Document.prototype,"auditScope",{value:"document",configurable:true});d.auditScope="element";d.setAttribute("onclick","return auditScope;");var r=d.onclick();delete Document.prototype.auditScope;r;`);
add('document prototype binding shadows global',setup+String.raw`var auditScope="global";Object.defineProperty(Document.prototype,"auditScope",{value:"document",configurable:true});d.setAttribute("onclick","return auditScope;");var r=d.onclick();delete Document.prototype.auditScope;r;`);
add('missing document binding reaches global after deletion',setup+String.raw`var auditScope="global";Object.defineProperty(Document.prototype,"auditScope",{value:"document",configurable:true});d.setAttribute("onclick","return auditScope;");var f=d.onclick;delete Document.prototype.auditScope;f();`);
add('source getter executes after HasBinding and once per read',setup+String.raw`var auditReads=0;Object.defineProperty(HTMLElement.prototype,"auditScope",{get:function(){auditReads++;return 9;},configurable:true});d.setAttribute("onclick","return auditScope+auditScope;");var result=d.onclick()+":"+auditReads;delete HTMLElement.prototype.auditScope;result;`);
add('source getter exception propagates on direct handler call',setup+String.raw`Object.defineProperty(HTMLElement.prototype,"auditScope",{get:function(){throw 73;},configurable:true});d.setAttribute("onclick","return auditScope;");var result;try{d.onclick();}catch(e){result=e;}delete HTMLElement.prototype.auditScope;result;`);
add('global assignment remains a reference through native scopes',setup+String.raw`var auditCount=5;d.setAttribute("onclick","auditCount+=3;return auditCount;");d.onclick()+":"+auditCount;`);
add('element assignment updates actual element',setup+String.raw`d.id="before";d.setAttribute("onclick","id=\"after\";return id;");d.onclick()+":"+d.id;`);
add('function locals shadow object environments',setup+String.raw`d.id="element";d.setAttribute("onclick","var id=\"local\";return id;");d.onclick()+":"+d.id;`);
add('function declarations close over handler locals',setup+String.raw`d.setAttribute("onclick","var n=7;function f(){return n+1;}return f();");d.onclick();`);
add('event argument shadows element expando',setup+String.raw`d.event="element";d.setAttribute("onclick","return event;");Function.prototype.call.call(d.onclick,d,"parameter");`);
add('initial Element unscopables skips append',setup+String.raw`var append="global";d.setAttribute("onclick","return append;");d.onclick();`);
add('initial Document unscopables skips fullscreen',setup+String.raw`var fullscreen="global";d.setAttribute("onclick","return fullscreen;");d.onclick();`);
add('strict body retains explicit receiver',setup+String.raw`d.setAttribute("onclick","\"use strict\";return this;");Function.prototype.call.call(d.onclick,7);`);
add('attribute handler serial survives replacement',setup+String.raw`var auditOrder="";d.addEventListener("click",function(){auditOrder+="a";});d.setAttribute("onclick","auditOrder+=\"old\";");d.addEventListener("click",function(){auditOrder+="b";});d.setAttribute("onclick","auditOrder+=\"new\";");d.dispatchEvent(new Event("click"));auditOrder;`);
add('replacement before pending attribute listener compiles current text',setup+String.raw`var auditOrder="";d.addEventListener("click",function(){d.setAttribute("onclick","auditOrder+=\"new\";");});d.setAttribute("onclick","auditOrder+=\"old\";");d.dispatchEvent(new Event("click"));auditOrder;`);
add('source exceptions preserve later dispatch listeners',setup+String.raw`var auditOrder="";d.setAttribute("onclick","throw 7;");d.addEventListener("click",function(){auditOrder+="next";});d.dispatchEvent(new Event("click"));auditOrder;`);
add('property assignment preserves raw attribute text',setup+String.raw`d.setAttribute("onclick","return 7;");d.onclick=function(){return 8;};d.getAttribute("onclick")+":"+d.onclick();`);
add('removing attribute clears handler',setup+String.raw`d.setAttribute("onclick","return 7;");var f=d.onclick;d.removeAttribute("onclick");(d.onclick===null)+":"+f();`);
add('unrecognized on-prefixed attribute is inert',setup+String.raw`var auditCount=0;d.setAttribute("onauditunknown","auditCount++;");d.dispatchEvent(new Event("auditunknown"));auditCount+":"+typeof d.onauditunknown;`);
add('HTML parsed content handler uses actual assembled source',setup+String.raw`d.innerHTML="<button id=\"inside\" onclick=\"return id;\"></button>";d.firstChild.onclick();`);
add('empty handler compiles ordinary undefined result',setup+String.raw`d.setAttribute("onclick","");d.onclick();`);
for(const [property,eventType] of [['onwebkitanimationend','webkitAnimationEnd'],['onwebkitanimationstart','webkitAnimationStart'],['onwebkitanimationiteration','webkitAnimationIteration'],['onwebkittransitionend','webkitTransitionEnd']]) {
  add(`${property} attribute uses native case-sensitive event type`,setup+`d.setAttribute('${property}','this.audit=(this.audit||0)+1;');d.dispatchEvent(new Event('${property.slice(2)}'));var before=d.audit||0;d.dispatchEvent(new Event('${eventType}'));before+':'+d.audit+':'+d.${property}.name;`);
  add(`${property} property handler uses same native alias`,setup+`d.${property}=function(){this.audit=(this.audit||0)+1;};d.dispatchEvent(new Event('${property.slice(2)}'));var before=d.audit||0;d.dispatchEvent(new Event('${eventType}'));before+':'+d.audit;`);
}
add('removing native alias attribute clears corresponding event listener',setup+String.raw`d.setAttribute("onwebkittransitionend","this.audit=1;");d.removeAttribute("onwebkittransitionend");d.dispatchEvent(new Event("webkitTransitionEnd"));typeof d.audit+":"+(d.onwebkittransitionend===null);`);
add('unsupported modern handler grammar remains explicit',setup+String.raw`d.setAttribute("onclick","let x=1;return x;");d.onclick;`,{expectedStatus:'unresolved'});
add('invalid handler native error reporting remains explicit',setup+String.raw`d.setAttribute("onclick","return );");d.onclick;`,{expectedStatus:'unresolved'});
add('form owner scope remains explicit',String.raw`var d=document.createElement("button");d.setAttribute("form","unknown-form");d.setAttribute("onclick","return 1;");d.onclick;`,{expectedStatus:'unresolved'});
add('native named document binding remains explicit',String.raw`var d=document.createElement("div"),candidate=document.createElement("img");candidate.setAttribute("name","auditCandidate");document.body.appendChild(candidate);d.setAttribute("onclick","return auditCandidate;");d.onclick();`,{expectedStatus:'unresolved'});
add('Symbol unscopables mutation remains explicit',setup+String.raw`Object.defineProperty(d,Symbol.unscopables,{value:{id:true}});`,{expectedStatus:'unresolved'});

const initialHtml='<!doctype html><html><head></head><body></body></html>';
const requests=cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),browserLibrary:true,fuel:500000,initialHtmlUnits:units(initialHtml)}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:60000,maxBuffer:16*1024*1024});
if(child.error)throw child.error;
assert.equal(child.status,0,child.stderr);
const observed=JSON.parse(child.stdout);
const worker=function(cases){
  function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='number'){var a=new DataView(new ArrayBuffer(8));a.setFloat64(0,v,false);return{type:'number',bits:a.getBigUint64(0,false).toString()};}throw Error('Expected primitive fixture result');}
  return cases.map(function(c){if(c.expectedStatus)return{status:c.expectedStatus};try{return{status:'complete',value:encode((0,eval)(c.source))};}catch(e){return{status:'throw',name:e.name,message:e.message};}});
};
const native=runNativeBrowser(worker.toString(),cases,{allowEval:true,allowInlineScripts:true});
const failures=[];
for(let i=0;i<cases.length;i++){try{if(cases[i].expectedStatus)assert.equal(observed[i].status,cases[i].expectedStatus);else assert.deepEqual({status:observed[i].status,value:observed[i].value},native.result[i]);}catch(error){failures.push({name:cases[i].name,observed:observed[i],expected:native.result[i],error:error.message});}}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,inlineHandlerRefinementVerified:false}));
