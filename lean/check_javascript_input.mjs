/** Native input-event records and source-handler comparisons, not trusted input refinement. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
import {loadGameSource} from '../model/game-source.mjs';

if(!process.argv.includes('--engine')) throw Error('Input-event comparisons require pinned isolated Chromium');
const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,...extra});
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const ui=['bubbles','cancelable','composed','detail','sourceCapabilities','view'];
const modifiers=['altKey','ctrlKey','metaKey','modifierAltGraph','modifierCapsLock','modifierFn','modifierNumLock','modifierScrollLock','modifierSymbol','shiftKey'];
const mouse=['button','buttons','clientX','clientY','movementX','movementY','region','relatedTarget','screenX','screenY'];
const keyboard=['charCode','code','isComposing','key','keyCode','location','repeat'];
for(const type of ['UIEvent','MouseEvent','KeyboardEvent']) {
  add(`${type} defaults and native prototype`, `var e=new ${type}('audit');e.type+':'+e.bubbles+':'+e.cancelable+':'+e.composed+':'+e.detail+':'+e.view+':'+e.sourceCapabilities+':'+e.which+':'+e.isTrusted+':'+(e instanceof ${type})+':'+(e instanceof UIEvent)+':'+(e instanceof Event);`);
  add(`${type} immutable captured prototype`, `var Saved=${type};${type}=function(){};var e=new Saved('audit'),r=e instanceof Saved;${type}=Saved;r;`);
  const fields=ui.concat(type==='UIEvent'?[]:modifiers,type==='MouseEvent'?mouse:type==='KeyboardEvent'?keyboard:[]);
  const getters=fields.map(n=>`get ${n}(){log.push('${n}');return undefined;}`).join(',');
  add(`${type} exact inherited dictionary getter order`, `var log=[];new ${type}({toString:function(){log.push('type');return 'audit';}},{${getters}});log.join(',');`);
  for(const option of ['null','undefined','false','7','"x"']) add(`${type} options ${option}`,`try{new ${type}('audit',${option}).type;}catch(e){e.name;}`);
  add(`${type} type coercion precedes invalid dictionary`, `var log='';try{new ${type}({toString:function(){log+='type';return 'audit';}},7);}catch(e){log+=':'+e.name;}log;`);
  add(`${type} call and missing type reject`, `var log='';try{${type}('x');}catch(e){log=e.name;}try{new ${type}();}catch(e){log+=':'+e.name;}log;`);
  add(`${type} source numeric conversion before later getter`, `var log='';new ${type}('audit',{get detail(){log+='d';return {valueOf:function(){log+='v';return 4294967297;}};},get sourceCapabilities(){log+='s';return null;},get view(){log+='w';return null;}});log;`);
  add(`${type} failed capability brand stops view getter`, `var log='';try{new ${type}('audit',{get sourceCapabilities(){log+='s';return {};},get view(){log+='wrong';}});}catch(e){log+=':'+e.name;}log;`);
  add(`${type} invalid view rejects before modifier getter`, `var log='';try{new ${type}('audit',{get view(){log+='v';return {};},get altKey(){log+='wrong';}});}catch(e){log+=':'+e.name;}log;`);
  add(`${type} window view identity`, `new ${type}('audit',{view:window}).view===window;`);
}
for(const n of ['0','-0','1.9','-1.9','2147483647','-2147483648','4294967297','NaN','Infinity']) {
  add(`UI detail long conversion ${n}`,`new UIEvent('x',{detail:${n}}).detail;`);
  add(`Keyboard legacy code conversion ${n}`,`var e=new KeyboardEvent('keypress',{charCode:${n},keyCode:${n},location:${n}});e.charCode+':'+e.keyCode+':'+e.which+':'+e.location;`);
  add(`Mouse button conversion ${n}`,`var e=new MouseEvent('click',{button:${n},buttons:${n},movementX:${n}});e.button+':'+e.buttons+':'+e.which+':'+e.movementX;`);
}
for(const n of ['0','-0','0.25','-0.25','0.5','-0.5','1.5','-1.5','1.9','-1.9','2147483647','-2147483648']) {
  add(`Mouse initial coordinate projections ${n}`,`var e=new MouseEvent('x',{clientX:${n},clientY:${n},screenX:${n},screenY:${n}});e.clientX+':'+e.x+':'+e.clientY+':'+e.screenX+':'+e.screenY+':'+e.pageX+':'+e.pageY+':'+e.layerX+':'+e.layerY+':'+e.offsetX+':'+e.offsetY;`);
  add(`Mouse offset negative zero bits ${n}`,`new MouseEvent('x',{clientX:${n}}).offsetX;`);
}
for(const coordinate of ['clientX','clientY','screenX','screenY']) for(const n of ['NaN','Infinity','-Infinity']) add(`${coordinate} finite double rejection ${n}`,`try{new MouseEvent('x',{${coordinate}:${n}});}catch(e){e.name;}`);
for(const type of ['mousemove','mouseover','mouseout','mouseenter','mouseleave','mousedown','mouseup','click','audit']) add(`Mouse button special type ${type}`,`var e=new MouseEvent('${type}',{button:2});e.button+':'+e.which;`);
for(const n of [-2,-1,0,1,2,32767,-32768]) add(`Mouse which raw button ${n}`,`var e=new MouseEvent('click',{button:${n}});e.button+':'+e.which;`);
for(const type of ['MouseEvent','KeyboardEvent']) {
  add(`${type} modifiers and macOS Accel`, `var e=new ${type}('x',{ctrlKey:true,metaKey:true,altKey:true,shiftKey:true,modifierAltGraph:true,modifierCapsLock:true,modifierFn:true,modifierNumLock:true,modifierScrollLock:true,modifierSymbol:true});['Alt','Control','Meta','Shift','AltGraph','CapsLock','Fn','NumLock','ScrollLock','Symbol','Accel','FnLock','Hyper','Super','SymbolLock','unknown'].map(function(n){return n+':'+e.getModifierState(n);}).join(',');`);
  add(`${type} Accel uses meta not control`, `var e=new ${type}('x',{ctrlKey:true});e.ctrlKey+':'+e.metaKey+':'+e.getModifierState('Accel');`);
  add(`${type} modifier name source conversion`, `var log='';var e=new ${type}('x',{shiftKey:true});e.getModifierState({toString:function(){log+='s';return 'Shift';}})+':'+log;`);
  add(`${type} boolean object options do not coerce`, `var log='';var e=new ${type}('x',{altKey:{valueOf:function(){log+='wrong';return 0;},toString:function(){log+='wrong';return '';}}});e.altKey+':'+log;`);
  add(`${type} modifier receiver and required argument`, `var log='';try{${type}.prototype.getModifierState.call({},'Shift');}catch(e){log=e.name;}try{new ${type}('x').getModifierState();}catch(e){log+=':'+e.name;}log;`);
}
add('Keyboard source strings and composing flags',String.raw`var log='';var e=new KeyboardEvent('keydown',{get code(){log+='c';return {toString:function(){log+='C';return 'KeyA';}};},get key(){log+='k';return {toString:function(){log+='K';return 'α';}};},isComposing:true,repeat:true});log+':'+e.code+':'+e.key+':'+e.isComposing+':'+e.repeat;`);
add('Keyboard nullable string fields use ordinary ToString',`var e=new KeyboardEvent('x',{key:null,code:false});e.key+':'+e.code;`);
add('Mouse region conversion occurs although getter is disabled',`var log='';new MouseEvent('x',{region:{toString:function(){log+='r';return 'zone';}},get relatedTarget(){log+='t';return null;}});log;`);
add('Mouse related target retains native identity',`var d=document.createElement('div'),e=new MouseEvent('mouseover',{relatedTarget:d});(e.relatedTarget===d)+':'+(e.fromElement===d)+':'+e.toElement;`);
add('Mouse from/to element distinction on mouseout',`var d=document.createElement('div'),e=new MouseEvent('mouseout',{relatedTarget:d});(e.relatedTarget===d)+':'+e.fromElement+':'+(e.toElement===d);`);
add('Mouse Window related target is not a Node',`var e=new MouseEvent('mouseout',{relatedTarget:window});(e.relatedTarget===window)+':'+e.fromElement+':'+e.toElement;`);
for(const value of ['{}','7','false']) add(`Mouse invalid related target ${value}`,`try{new MouseEvent('x',{relatedTarget:${value}});}catch(e){e.name;}`);
add('Mouse source numeric throw stops later dictionary getter',`var log='';try{new MouseEvent('x',{get clientX(){log+='x';return {valueOf:function(){log+='v';throw 7;}};},get clientY(){log+='wrong';}});}catch(e){log+=':'+e;}log;`);
add('UIEvent which getter dynamically dispatches mouse representation',`Object.getOwnPropertyDescriptor(UIEvent.prototype,'which').get.call(new MouseEvent('mousemove',{button:2}));`);
add('UIEvent which getter dynamically dispatches keyboard representation',`Object.getOwnPropertyDescriptor(UIEvent.prototype,'which').get.call(new KeyboardEvent('keypress',{keyCode:4294967295}));`);
add('Mouse getter rejects a KeyboardEvent',`try{Object.getOwnPropertyDescriptor(MouseEvent.prototype,'ctrlKey').get.call(new KeyboardEvent('x'));}catch(e){e.name;}`);
add('Keyboard getter rejects a MouseEvent',`try{Object.getOwnPropertyDescriptor(KeyboardEvent.prototype,'ctrlKey').get.call(new MouseEvent('x'));}catch(e){e.name;}`);
add('UIEvent getter rejects base Event',`try{Object.getOwnPropertyDescriptor(UIEvent.prototype,'detail').get.call(new Event('x'));}catch(e){e.name;}`);

const main=loadGameSource().sources['main.js'];
const mouseStart=main.indexOf('Game.GetMouseCoords=function(e)');
const mouseEnd=main.indexOf('\r\n\t\t}',mouseStart)+6;
assert(mouseStart>0&&mouseEnd>mouseStart);
const actualMouse=main.slice(mouseStart,mouseEnd);
for(const [x,y] of [[10,20],[1.5,-1.5],[-17,28],[0,42],[42,0]]) add(`actual source Game.GetMouseCoords ${x},${y}`,`var TopBarOffset=7,Game={mouseX:3,mouseY:4,scale:2,time:99};${actualMouse};Game.GetMouseCoords(new MouseEvent('mousemove',{clientX:${x},clientY:${y}}));Game.mouseX+':'+Game.mouseY+':'+Game.mouseX2+':'+Game.mouseY2+':'+Game.mouseMoved+':'+Game.lastActivity;`,{sourceFixture:true});
const keyStart=main.indexOf("AddEvent(window,'keydown',function(e){")+"AddEvent(window,'keydown',".length;
const keyEnd=main.indexOf('\r\n\t\t});',keyStart)+5;
assert(keyStart>0&&keyEnd>keyStart);
const actualKey=main.slice(keyStart,keyEnd);
for(const keyCode of [9,16,17,65,83]) add(`actual source keydown ${keyCode}`,`var Game={promptOn:false,OnAscend:false,AscendTimer:0,tooltip:{dynamic:false},keys:[],toSave:false};var handler=${actualKey};var e=new KeyboardEvent('keydown',{keyCode:${keyCode},ctrlKey:true,cancelable:true});handler(e);Game.toSave+':'+(Game.keys[${keyCode}]||0)+':'+e.defaultPrevented;`,{sourceFixture:true});
add('coordinate cast beyond native defined int range stays explicit',`new MouseEvent('x',{clientX:1e30}).clientX;`,{expectedStatus:'unresolved'});
add('window scroll snapshot stays explicit',`new MouseEvent('x',{view:window}).pageX;`,{expectedStatus:'unresolved'});
add('mouse native activation dispatch stays explicit',`document.createElement('div').dispatchEvent(new MouseEvent('click'));`,{expectedStatus:'unresolved'});
add('keyboard native focus/default action stays explicit',`document.createElement('div').dispatchEvent(new KeyboardEvent('keydown'));`,{expectedStatus:'unresolved'});

const initialHtml='<!doctype html><html><head></head><body></body></html>';
const requests=cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),browserLibrary:true,fuel:500000,initialHtmlUnits:units(initialHtml)}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:60000,maxBuffer:16*1024*1024});
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
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,sourceFixtures:cases.filter(c=>c.sourceFixture).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,trustedInputRefinementVerified:false}));
