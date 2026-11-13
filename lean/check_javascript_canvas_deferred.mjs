/** Isolated integration checks. No numerical rotation or pixel-refinement claim. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
const nativeRequested=process.argv.includes('--engine');
const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,...extra});
const prefix='var c=document.createElement("canvas"),x=c.getContext("2d");';
const bits=n=>{const d=new DataView(new ArrayBuffer(8));d.setFloat64(0,n,false);return d.getBigUint64(0,false).toString();};
const literal=n=>Number.isNaN(n)?'NaN':Object.is(n,-0)?'-0':String(n);
for(const angle of [0,-0,0.1,-0.1,Math.PI,0.017453292519943295,1e-300,1e300,Number.MAX_VALUE,NaN,Infinity,-Infinity])
 add('rotation normal return '+literal(angle),`x.globalAlpha=0.25;typeof x.rotate(${literal(angle)})+':'+x.globalAlpha;`,
 {unknown:Number.isFinite(angle)&&angle!==0,history:['rotate']});
add('translation after rotation keeps cache absent',`x.rotate(0.1);x.translate(3,4);x.scale(2,3);x.transform(1,0,0,1,8,9);x.fillStyle;`,{unknown:true,history:['rotate','translate','scale','transform']});
add('reset after rotation restores known logical matrix',`x.rotate(0.1);x.resetTransform();x.translate(3,4);x.fillStyle;`,{unknown:false,history:['rotate','resetTransform','translate']});
add('finite setTransform restores known logical matrix',`x.rotate(0.1);x.setTransform(2,0,0,3,4,5);x.fillStyle;`,{unknown:false,history:['rotate','setTransform']});
add('invalid setTransform preserves unknown cache',`x.rotate(0.1);x.setTransform(NaN,0,0,1,0,0);x.fillStyle;`,{unknown:true,history:['rotate']});
add('setTransform no arguments resets',`x.rotate(0.1);x.setTransform();x.fillStyle;`,{unknown:false,history:['rotate','resetTransform']});
add('restore known state restores history',`x.translate(3,4);x.save();x.rotate(0.1);x.restore();x.fillStyle;`,{unknown:false,history:['translate']});
add('restore unknown state restores history',`x.rotate(0.1);x.save();x.resetTransform();x.restore();x.fillStyle;`,{unknown:true,history:['rotate']});
add('nested saves preserve independent histories',`x.rotate(0.1);x.save();x.rotate(0.2);x.save();x.resetTransform();x.restore();x.restore();x.fillStyle;`,{unknown:true,history:['rotate']});
add('dimension reset clears history',`x.rotate(0.1);x.save();c.width=c.width;x.restore();x.fillStyle;`,{unknown:false,history:[]});
add('empty canvas rotation has no transform effect',`c.width=0;typeof x.rotate(0.1);`,{unknown:false,history:[]});
add('invalid setTransform precedes unavailable allocation',`c.width=100000;x.setTransform(NaN,0,0,1,0,0);c.width;`,{unknown:false,history:[]});
add('missing required rotate argument',`try{x.rotate();}catch(e){e.name;}`,{unknown:false,history:[]});
add('receiver validation before numeric callback',`var log='';try{CanvasRenderingContext2D.prototype.rotate.call({}, {valueOf:function(){log+='wrong';return 1;}});}catch(e){log+=e.name;}log;`,{unknown:false,history:[]});
add('constructor validation before numeric callback',`var log='',rotate=x.rotate;try{new rotate({valueOf:function(){log+='wrong';return 1;}});}catch(e){log+=e.name;}log;`,{unknown:false,history:[]});
add('numeric callback and later return',`var log='';var result=x.rotate({valueOf:function(){log+='v';return 0.1;},toString:function(){log+='wrong';return '1';}});log+':'+typeof result;`,{unknown:true,history:['rotate']});
add('numeric callback can reset prior state',`x.rotate(0.1);x.save();x.rotate({valueOf:function(){c.width=17;return 0.2;}});x.restore();c.width;`,{unknown:true,history:['rotate']});
add('numeric callback nested rotation order',`var log='';x.rotate({valueOf:function(){x.rotate(0.2);log+='v';return 0.1;}});log;`,{unknown:true,history:['rotate','rotate'],angles:[0.2,0.1]});
add('numeric exception leaves prior history',`x.rotate(0.1);try{x.rotate({valueOf:function(){throw 'stop';}});}catch(e){}x.fillStyle;`,{unknown:true,history:['rotate']});
add('rotate ignores trailing argument conversion',`var log='';x.rotate(0.1,{valueOf:function(){log+='wrong';return 1;}});log;`,{unknown:true,history:['rotate']});
add('fill retains unknown matrix and call-time history',`x.rotate(0.1);x.fillStyle='red';x.fillRect(1,2,3,4);x.resetTransform();x.fillStyle='blue';x.fillStyle;`,{unknown:false,history:['rotate','resetTransform'],command:{kind:'fillRect',unknown:true,history:['rotate']}});
add('clear retains unknown matrix and call-time history',`x.rotate(0.1);x.clearRect(1,2,3,4);x.resetTransform();x.fillStyle;`,{unknown:false,history:['rotate','resetTransform'],command:{kind:'clearRect',unknown:true,history:['rotate']}});
add('restore preserves retained painting',`x.rotate(0.1);x.save();x.rotate(0.2);x.fillRect(1,2,3,4);x.restore();x.fillStyle;`,{unknown:true,history:['rotate'],command:{kind:'fillRect',unknown:true,history:['rotate','rotate']}});
add('numeric observation still explicit',`x.rotate(0.1);x.getTransform();`,{expectedStatus:'unresolved'});
add('pixel observation still explicit',`x.rotate(0.1);x.fillRect(1,2,3,4);x.getImageData(0,0,1,1);`,{expectedStatus:'unresolved'});
add('nonempty path still explicit',`x.rotate(0.1);x.rect(0,0,1,1);`,{expectedStatus:'unresolved'});
add('large native allocation remains explicit',`c.width=100000;x.rotate(0.1);`,{expectedStatus:'unresolved'});
add('DOMMatrix overload still explicit',`x.setTransform({a:1,b:0,c:0,d:1,e:0,f:0});`,{expectedStatus:'unresolved'});
const worker=function(input){function encode(v){if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='undefined')return{type:'undefined'};throw Error('Unsupported primitive');}return input.cases.map(function(test){if(test.expectedStatus)return {status:test.expectedStatus};return(function(){var value=eval(input.prefix+test.source);var matrix=x.getTransform();return{status:'complete',value:encode(value),matrix:['a','b','c','d','e','f'].map(k=>encode(matrix[k]).bits)};})();});};
const native=nativeRequested?runNativeBrowser(worker.toString(),{cases,prefix},{allowEval:true}):null;
const requests=cases.map(test=>({browserLibrary:true,diagnosticCanvas:true,fuel:300000,ast:compileJavaScript(prefix+test.source,{name:test.name})}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{const test=cases[i],observed=actual[i];if(test.expectedStatus){assert.equal(observed.status,test.expectedStatus);continue;}assert.equal(observed.status,'complete');if(native)assert.deepEqual(observed.value,native.result[i].value);const drawing=observed.diagnosticCanvas[0];assert.equal(drawing.matrix===null,test.unknown,'known cache admission');assert.deepEqual(drawing.transformHistory.map(o=>o.name),test.history);if(!test.unknown&&native)assert.deepEqual(drawing.matrix,native.result[i].matrix,'known logical matrix');if(test.angles)assert.deepEqual(drawing.transformHistory.map(o=>o.bits[0]),test.angles.map(bits));if(test.command){const command=drawing.commandRecords.at(-1);assert.equal(command.kind,test.command.kind);assert.equal(command.matrix===null,test.command.unknown);assert.deepEqual(command.transformHistory.map(o=>o.name),test.command.history);}}catch(error){failures.push({name:cases[i].name,error:error.message,observed:actual[i],expected:native?.result[i]});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:native?cases.filter(c=>!c.expectedStatus).length:0,versions:native?.versions,retainedHistoryVerified:true,nativeRotationNumericsVerified:false,rendererRefinementVerified:false}));
