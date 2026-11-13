/** Exact native rectangle values, without a renderer-layout oracle. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import {fileURLToPath} from 'node:url';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw new Error('Geometry checks require the pinned isolated native Chromium worker');
const cases=[];const add=(name,source,extra={})=>cases.push({name,source,...extra});
const fields=['x','y','width','height','top','right','bottom','left'];
for(const kind of ['DOMRect','DOMRectReadOnly']){
  for(const args of ['','undefined,undefined,undefined,undefined','-0,-0,0,0','0,0,-0,-0','1,2,-3,-4','Infinity,-Infinity,1,-1','1,1,NaN,NaN','NaN,1,1,1','Infinity,0,-Infinity,0','9007199254740992,1,1,-1']){
    for(const field of fields)add(`${kind}(${args}).${field}`,`new ${kind}(${args}).${field};`);
  }
  add(`${kind} native instance and own JSON property order`, `var r=new ${kind}(1,2,3,4),j=r.toJSON();(r instanceof ${kind})+":"+Object.keys(j).join(",");`);
  add(`${kind} constructor converts source arguments in order`, `var s="";function n(k,v){return {valueOf:function(){s+=k;return v;}};}new ${kind}(n("x",1),n("y",2),n("w",3),n("h",4));s;`);
  add(`${kind} object undefined differs from default undefined`, `new ${kind}({valueOf:function(){return undefined;}}).x;`);
  add(`${kind} constructor conversion throw prevents later conversion`, `var s="";try{new ${kind}({valueOf:function(){s+="x";throw 7;}},{valueOf:function(){s+="wrong";return 2;}});}catch(e){s+=e;}s;`);
  add(`${kind} rejects call without new before argument conversion`, `var s="";try{${kind}({valueOf:function(){s+="wrong";return 1;}});}catch(e){s+=e.name;}s;`);
  for(const options of ['undefined','null','true','7','"x"'])add(`${kind}.fromRect dictionary ${options}`, `try{${kind}.fromRect(${options}).width;}catch(e){e.name;}`);
  add(`${kind}.fromRect getter then conversion order`, `var s="",o={};["x","y","width","height"].forEach(function(n){Object.defineProperty(o,n,{get:function(){s+=n+":";return {valueOf:function(){s+="v:";return 1;}};}});});${kind}.fromRect(o);s;`);
  add(`${kind}.fromRect conversion throw stops later getter`, `var s="";try{${kind}.fromRect({get height(){s+="h";return {valueOf:function(){s+="v";throw 7;}};},get width(){s+="wrong";return 1;}});}catch(e){s+=e;}s;`);
  add(`${kind}.fromRect defaults missing and undefined fields to zero`, `var r=${kind}.fromRect({x:undefined,y:null,width:false,height:true});r.x+":"+r.y+":"+r.width+":"+r.height;`);
  add(`${kind}.fromRect source undefined conversion becomes NaN`, `${kind}.fromRect({height:{valueOf:function(){return undefined;}}}).height;`);
  add(`${kind}.fromRect ignores borrowed this constructor`, `${kind}.fromRect.call(function(){}, {x:2}) instanceof ${kind};`);
  add(`${kind}.toJSON is a fresh ordinary mutable dictionary`, `var r=new ${kind}(1),a=r.toJSON(),b=r.toJSON();a.x=9;var d=Object.getOwnPropertyDescriptor(b,"x");(a!==b)+":"+(Object.getPrototypeOf(a)===Object.prototype)+":"+r.x+":"+b.x+":"+d.writable+":"+d.enumerable+":"+d.configurable;`);
  add(`${kind} captured prototype survives global constructor replacement`, `var Saved=${kind};${kind}=function(){};var r=new Saved(1),same=r instanceof Saved;${kind}=Saved;same;`);
}
for(const field of ['x','y','width','height']){
  add(`DOMRect setter ${field} converts source number and updates edges`, `var r=new DOMRect(1,2,3,4),s="",o={valueOf:function(){s+="v";return -8;}};var same=(r.${field}=o)===o;s+":"+same+":"+r.${field}+":"+r.left+":"+r.right+":"+r.top+":"+r.bottom;`);
  add(`DOMRect setter ${field} with omitted argument becomes NaN`, `var r=new DOMRect();Object.getOwnPropertyDescriptor(DOMRect.prototype,${JSON.stringify(field)}).set.call(r);r.${field};`);
  add(`DOMRect setter ${field} rejects readonly receiver before conversion`, `var s="";try{Object.getOwnPropertyDescriptor(DOMRect.prototype,${JSON.stringify(field)}).set.call(new DOMRectReadOnly(),{valueOf:function(){s+="wrong";return 1;}});}catch(e){s+=e.name;}s;`);
}
add('readonly coordinate assignment is ignored in sloppy source', 'var r=new DOMRectReadOnly(1);r.x=9;r.x;');
add('readonly coordinate assignment throws in strict source', '"use strict";var r=new DOMRectReadOnly(1);try{r.x=9;}catch(e){e.name;}');
add('readonly edge assignment does not change mutable rectangle', 'var r=new DOMRect(1,2,3,4);r.left=9;r.top=10;r.left+":"+r.top;');
add('DOMRect own getter brands readonly receivers', 'try{Object.getOwnPropertyDescriptor(DOMRect.prototype,"x").get.call(new DOMRectReadOnly(3));}catch(e){e.name;}');
add('DOMRectReadOnly getter accepts mutable receiver', 'Object.getOwnPropertyDescriptor(DOMRectReadOnly.prototype,"x").get.call(new DOMRect(3));');
add('rectangle method rejects unrelated receiver', 'try{DOMRectReadOnly.prototype.toJSON.call({x:1});}catch(e){e.name;}');
add('native source getBounds mutates coordinates and retains derived readonly edges', 'var r=new DOMRect(10,20,30,40),s=2;r.x/=s;r.y/=s;r.width/=s;r.height/=s;r.top/=s;r.bottom/=s;r.left/=s;r.right/=s;r.x+":"+r.y+":"+r.width+":"+r.height+":"+r.top+":"+r.bottom+":"+r.left+":"+r.right;');
add('renderer geometry remains explicit', 'document.createElement("div").getBoundingClientRect();',{expectedStatus:'unresolved'});
add('native rectangle prototype reflection retains the explicit host boundary', 'Object.getPrototypeOf(new DOMRect());',{expectedStatus:'unresolved'});
const requests=cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),browserLibrary:true,fuel:100000}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:60000,maxBuffer:16*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const observed=JSON.parse(child.stdout);
const worker=function(cases){function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}throw Error('Geometry fixture must return primitive');}return cases.map(c=>{if(c.expectedStatus)return{status:c.expectedStatus};try{return{status:'complete',value:encode((function(){return eval(c.source);})())};}catch(e){return{status:'throw',name:e.name,message:e.message};}});};
const native=runNativeBrowser(worker.toString(),cases,{allowEval:true}),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(observed[i].status,cases[i].expectedStatus);else assert.deepEqual({status:observed[i].status,value:observed[i].value},native.result[i]);}catch(error){failures.push({name:cases[i].name,observed:observed[i],expected:native.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,rendererLayoutVerified:false,javascriptSemanticsVerified:false}));
