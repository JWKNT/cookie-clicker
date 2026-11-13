import assert from 'node:assert/strict';
import {runNativeBrowser} from './native-escape-input-worker.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {createRequire} from 'node:module';
import {writeFileSync,readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),main=loadGameSource().sources['main.js'];
const marker="AddEvent(window,'keyup',";
const start=main.indexOf(marker)+marker.length;
const fn=acorn.parseExpressionAt(main,start,{ecmaVersion:5});
const callback=main.slice(fn.start,fn.end);
const downMarker="AddEvent(window,'keydown',";
const downStart=main.indexOf(downMarker)+downMarker.length;
const downFn=acorn.parseExpressionAt(main,downStart,{ecmaVersion:5});
const downCallback=main.slice(downFn.start,downFn.end);
const setup=`() => {
 document.body.innerHTML='<div id="ordinary">Ordinary page</div>';
 globalThis.Game={lastActivity:0,time:1234,promptOn:false,promptNoClose:false,AscendTimer:1,AscendDuration:150,OnAscend:false,keys:[]};
 globalThis.events=[];
 const describe=e=>({type:e.type,target:e.target===document.body?'body':e.target.nodeName,currentTarget:e.currentTarget===window?'window':e.currentTarget.nodeName,key:e.key,code:e.code,keyCode:e.keyCode,charCode:e.charCode,detail:e.detail,location:e.location,repeat:e.repeat,isComposing:e.isComposing,isTrusted:e.isTrusted,bubbles:e.bubbles,cancelable:e.cancelable,composed:e.composed,defaultPrevented:e.defaultPrevented,viewWindow:e.view===window,sourceCapabilities:e.sourceCapabilities===null?null:{firesTouchEvents:e.sourceCapabilities.firesTouchEvents},ctrlKey:e.ctrlKey,altKey:e.altKey,shiftKey:e.shiftKey,metaKey:e.metaKey});
 for (const type of ['keydown','keypress','keyup']) {document.body.addEventListener(type,e=>events.push(describe(e)));window.addEventListener(type,e=>events.push(describe(e)));}
 window.addEventListener('keydown',${downCallback});
 window.addEventListener('keyup',()=>{globalThis.beforeRelease={key27:Game.keys[27],AscendTimer:Game.AscendTimer,lastActivity:Game.lastActivity};});
 window.addEventListener('keyup',${callback});
 globalThis.initial={focus:document.hasFocus(),activeElement:document.activeElement.tagName};
 return initial;
}`;
const result=runNativeBrowser(setup,null,{inputSequence:[{type:'keyDown',keyCode:'ESCAPE'},{type:'keyUp',keyCode:'ESCAPE'}],afterInputFunctionSource:`()=>({initial,beforeRelease,events,final:{lastActivity:Game.lastActivity,AscendTimer:Game.AscendTimer,key27:Game.keys[27],focus:document.hasFocus(),activeElement:document.activeElement.tagName}})`});
assert.equal(result.versions.chrome,'87.0.4280.141');
assert.deepEqual(result.result.beforeRelease,{key27:1,AscendTimer:1,lastActivity:0});
assert.deepEqual(result.result.final,{lastActivity:1234,AscendTimer:150,key27:0,focus:true,activeElement:'BODY'});
assert.equal(result.result.events.length,4);
for(const event of result.result.events){
 assert.equal(event.target,'body'); assert.equal(event.key,'Escape'); assert.equal(event.code,'Escape');
 assert.equal(event.keyCode,27); assert.equal(event.charCode,0); assert.equal(event.isTrusted,true);
 assert.equal(event.bubbles,true); assert.equal(event.cancelable,true); assert.equal(event.composed,true);
 assert.equal(event.defaultPrevented,false); assert.equal(event.viewWindow,true);
 assert.deepEqual(event.sourceCapabilities,{firesTouchEvents:false});
}
const output={...result,sourceCallbackSha256:createHash('sha256').update(callback).digest('hex'),sourceCallback:callback,keydownCallbackSha256:createHash('sha256').update(downCallback).digest('hex'),keydownCallback:downCallback,scope:'Isolated native key-down then key-up delivery, with both intact pinned source callbacks and a synthetic Game fixture. The down callback establishes keys[27]=1 before release. This is not a fresh-save reachability or complete OS physical-input refinement.'};
const path=new URL('../model/escape-input-witness.json',import.meta.url);
const retained={result:output.result,versions:output.versions,identity:output.identity,executableHash:output.executableHash,sourceCallbackSha256:output.sourceCallbackSha256,keydownCallbackSha256:output.keydownCallbackSha256,scope:output.scope};
if(process.argv.includes('--check'))assert.deepEqual(retained,JSON.parse(readFileSync(path,'utf8')));
else writeFileSync(path,JSON.stringify(retained,null,2)+'\n');
console.log(JSON.stringify({versions:result.versions,result:result.result,callbackSha:output.sourceCallbackSha256}));
