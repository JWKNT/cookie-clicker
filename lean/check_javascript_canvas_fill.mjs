/** Native source effects and deferred-command checks; no pixel refinement claim. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
import {loadGameSource} from '../model/game-source.mjs';

if(!process.argv.includes('--engine'))throw Error('Canvas fill comparisons require isolated pinned Chromium');
const cases=[],add=(name,source,extra={})=>cases.push({name,source,...extra});
const prefix='var c=document.createElement("canvas"),x=c.getContext("2d");';
const fields=['globalAlpha','globalCompositeOperation','lineWidth','lineCap','lineJoin','miterLimit',
 'lineDashOffset','shadowOffsetX','shadowOffsetY','shadowBlur','imageSmoothingEnabled',
 'imageSmoothingQuality','textAlign','textBaseline','fillStyle','strokeStyle','shadowColor','filter','font'];
const fingerprint=`[${fields.map(n=>`x.${n}`).join(',')}].join('|')`;
for(const args of ['','0','0,1','0,1,2'])add('fillRect missing arguments '+args,
 `try{x.fillRect(${args});}catch(e){e.name;}`,{commands:0});
add('fillRect receiver check precedes conversion',`var log='';try{CanvasRenderingContext2D.prototype.fillRect.call({}, {valueOf:function(){log+='wrong';return 0;}},0,1,1);}catch(e){log+=e.name;}log;`,{commands:0});
add('fillRect required argument count precedes conversion',`var log='';try{x.fillRect({valueOf:function(){log+='wrong';return 0;}},0,1);}catch(e){log+=e.name;}log;`,{commands:0});
add('fillRect is not a constructor',`var fill=x.fillRect;try{new fill(0,0,1,1);}catch(e){e.name;}`,{commands:0});
add('fillRect ignores trailing arguments',`var log='';x.fillRect(0,0,1,1,{valueOf:function(){log+='wrong';return 0;}});log;`,{commands:1});
add('fillRect converts all four arguments after NaN',`var log='';function n(mark,value){return {valueOf:function(){log+=mark;return value;}};}x.fillRect(n('a',NaN),n('b',0),n('c',1),n('d',1));log;`,{commands:0});
add('fillRect conversion throws before later source callbacks',`var log='';try{x.fillRect({valueOf:function(){log+='a';return 0;}},{valueOf:function(){log+='b';throw 'stop';}},{valueOf:function(){log+='wrong';return 1;}},1);}catch(e){log+=e;}log;`,{commands:0});
add('fillRect object conversion uses numeric hint',`var log='';x.fillRect({valueOf:function(){log+='v';return {};},toString:function(){log+='s';return '1.5';}},0,2,3);log;`,{commands:1});
add('fillRect conversion reset keeps new allocation and color',`x.fillStyle='red';x.save();x.fillRect({valueOf:function(){c.width=17;x.fillStyle='#12345680';return 0;}},0,1,2);x.restore();c.width+':'+x.fillStyle;`,{commands:1,fill:[18,52,86,128],width:17});
add('fillRect conversion changes composite before recording',`x.fillRect({valueOf:function(){x.globalCompositeOperation='copy';return 0;}},0,1,0);x.globalCompositeOperation;`,{commands:1,composite:'copy'});
add('fillRect conversion invokes a nested native draw first',`x.fillRect({valueOf:function(){x.fillStyle='red';x.fillRect(1,2,3,4);x.fillStyle='blue';return 10;}},20,30,40);x.fillStyle;`,{commands:2,fill:[0,0,255,255]});
add('fillRect has no implicit drawing-state mutation',`x.fillStyle='#12345680';x.strokeStyle='#345678ff';x.shadowColor='#abcdef07';x.globalAlpha=0.3;x.shadowBlur=5;x.save();x.fillRect(1,2,3,4);x.restore();${fingerprint};`,{commands:1,fill:[18,52,86,128],shadow:[171,205,239,7]});
add('saved colors are restored as bytes before the draw',`x.fillStyle='#12345680';x.shadowColor='#abcdef07';x.save();x.fillStyle='red';x.shadowColor='blue';x.restore();x.fillRect(1,2,3,4);x.fillStyle+':'+x.shadowColor;`,{commands:1,fill:[18,52,86,128],shadow:[171,205,239,7]});
add('later color writes do not mutate retained command',`x.fillStyle='#12345680';x.fillRect(1,2,3,4);x.fillStyle='red';x.fillStyle;`,{commands:1,fill:[18,52,86,128]});
add('dimension reset clears commands and restores color bytes',`x.fillStyle='red';x.fillRect(1,2,3,4);c.width=17;x.fillRect(0,0,1,1);x.fillStyle;`,{commands:1,fill:[0,0,0,255],width:17});
add('restoring drawing state preserves already issued commands',`x.save();x.fillStyle='red';x.fillRect(1,2,3,4);x.restore();x.fillStyle;`,{commands:1,fill:[255,0,0,255]});
add('command keeps its matrix after later reset',`x.translate(3,4);x.fillRect(1,2,3,4);x.resetTransform();x.fillStyle;`,{commands:1,matrix:[1,0,0,1,3,4]});
add('command keeps font before later setter',`x.font='20px Merriweather';x.fillRect(1,2,3,4);x.font='9px serif';x.font;`,{commands:1,font:'20px Merriweather'});
add('command retains opaque target creation mode',`c=document.createElement('canvas');x=c.getContext('2d',{alpha:false});x.fillRect(1,2,3,4);x.getContextAttributes().alpha;`,{commands:1,alpha:false});
add('singular matrix prevents copy drawing',`x.globalCompositeOperation='copy';x.scale(0,1);x.fillRect(1,2,3,4);x.globalCompositeOperation;`,{commands:0});
add('zero width canvas has no paint allocation',`c.width=0;x.fillRect(1,2,3,4);c.width;`,{commands:0});
add('zero height canvas has no paint allocation',`c.height=0;x.fillRect(1,2,3,4);c.height;`,{commands:0});
add('nonfinite input is rejected before large allocation',`c.width=100000;x.fillRect(NaN,0,1,1);c.width;`,{commands:0});
add('unknown large canvas resource allocation remains explicit',`c.width=100000;x.fillRect(0,0,1,1);`,{expectedStatus:'unresolved'});
add('paint readback remains an explicit boundary',`x.fillRect(0,0,1,1);x.getImageData(0,0,1,1);`,{expectedStatus:'unresolved'});
add('clip changes remain explicit',`x.rect(0,0,1,1);x.clip();x.fillRect(0,0,1,1);`,{expectedStatus:'unresolved'});

const rectangles=[[0,0,0,0],[0,0,1,0],[0,0,0,1],[0,0,1,1],[10,20,-3,-4],
 [-0,-0,-0,1],[1.25,-2.5,3.75,-4.25],[NaN,0,1,1],[0,Infinity,1,1],
 [0,0,-Infinity,1],[0,0,1,NaN],[1e300,-1e300,1e200,-1e200],
 [-1e308,1e308,-1e308,1e308],[1+2**-24,1+3*2**-24,2**-149,2**-150],
 [0,0,2**-150,2**-150],[0,0,-(2**-150),-(2**-150)]];
const literal=n=>Number.isNaN(n)?'NaN':Object.is(n,-0)?'-0':String(n);
const bits=n=>{const d=new DataView(new ArrayBuffer(8));d.setFloat64(0,n,false);return d.getBigUint64(0,false).toString();};
const floatMaximum=(2**24-1)*2**104;
const adjusted=([x,y,w,h])=>{if(w<0){w=-w;x-=w;}if(h<0){h=-h;y-=h;}return[x,y,w,h].map(n=>bits(Math.fround(Math.max(-floatMaximum,Math.min(floatMaximum,n)))));};
for(const [i,r]of rectangles.entries())for(const composite of ['source-over','copy','source-in']){
 const valid=r.every(Number.isFinite)&&(r[2]!==0||r[3]!==0);
 add(`rectangle ${i} ${composite}`,`x.globalCompositeOperation='${composite}';var result=x.fillRect(${r.map(literal).join(',')});typeof result;`,
  {commands:valid?1:0,rectangle:valid?adjusted(r):null,composite});
}
const main=loadGameSource().sources['main.js'];
const milk=main.split('\n').find(line=>line.includes('ctx.fillRect(0,height-y+480,width,Math.max(0,(y-480)))'));
assert.ok(milk,'Expected exact source milk fillRect');
for(const y of [0,20,480,481,600])add('actual milk rectangle source y='+y,
 `var ctx=x,height=572,width=240,y=${y};${milk}x.fillStyle;`,{commands:1,rectangle:adjusted([0,572-y+480,240,Math.max(0,y-480)])});

const worker=function(input){function encode(v){if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};throw Error('Expected primitive result');}
 const results=input.cases.map(function(c){if(c.expectedStatus)return{status:c.expectedStatus};try{return{status:'complete',value:encode((function(){return eval(input.prefix+c.source);})())};}catch(e){return{status:'throw',name:e.name,message:e.message};}});
 // Native evidence for the zero-area composite trap; not supplied to the model.
 const zeroArea=[];for(const composite of ['source-over','copy','source-in']){const c=document.createElement('canvas');c.width=c.height=2;const x=c.getContext('2d');x.fillStyle='red';x.fillRect(0,0,2,2);x.globalCompositeOperation=composite;x.fillRect(0,0,1,0);zeroArea.push({composite,pixel:Array.from(x.getImageData(0,0,1,1).data)});}
 return{results,zeroArea};};
const native=runNativeBrowser(worker.toString(),{cases,prefix},{allowEval:true});
const requests=cases.map(c=>({browserLibrary:true,diagnosticCanvas:true,fuel:300000,ast:compileJavaScript(prefix+c.source,{name:c.name})}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{const test=cases[i],observed=actual[i];if(test.expectedStatus){assert.equal(observed.status,test.expectedStatus);continue;}assert.deepEqual({status:observed.status,value:observed.value},native.result.results[i]);
 const records=observed.diagnosticCanvas?.at(-1)?.commandRecords;assert.equal(records?.length,test.commands,'retained command count');
 const fill=records?.at(-1);if(test.rectangle)assert.deepEqual(fill.rectangle,test.rectangle,'native normalization and float clamp');
 if(test.fill)assert.deepEqual(fill.fill,test.fill,'retained RGBA fill');if(test.shadow)assert.deepEqual(fill.shadow,test.shadow,'retained RGBA shadow');
 if(test.width!==undefined)assert.equal(fill.canvasWidth,test.width,'post-conversion allocation');
 if(test.matrix)assert.deepEqual(fill.matrix,test.matrix.map(bits),'retained matrix snapshot');
 if(test.alpha!==undefined)assert.equal(fill.alpha,test.alpha,'target creation alpha');
 if(test.font)assert.deepEqual(fill.fields.font,{type:'string',units:Array.from(test.font,c=>c.charCodeAt(0))});
 if(test.composite&&fill)assert.deepEqual(fill.fields.globalCompositeOperation,{type:'string',units:Array.from(test.composite,c=>c.charCodeAt(0))});
 }catch(error){failures.push({name:cases[i].name,observed:actual[i],expected:native.result.results[i],error:error.message});}
assert.deepEqual(native.result.zeroArea,[{composite:'source-over',pixel:[255,0,0,255]},{composite:'copy',pixel:[0,0,0,0]},{composite:'source-in',pixel:[0,0,0,0]}]);
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeSourceEffectComparisons:cases.filter(c=>!c.expectedStatus).length,
 zeroAreaNativeWitness:native.result.zeroArea,versions:native.versions,executableHash:native.executableHash,
 deferredCommandStateChecked:true,pixelInterpretationProvided:false,rendererRefinementVerified:false}));
