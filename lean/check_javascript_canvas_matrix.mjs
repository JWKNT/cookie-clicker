/** Pinned native affine arithmetic; nonzero C-library rotations remain explicit. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import{runNativeBrowser}from'../model/native-browser.mjs';
import{spawnSyncWithFileInput}from'./process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
if (!process.argv.includes('--engine')) throw Error('Canvas matrix checks require isolated pinned Chromium');
const v=new DataView(new ArrayBuffer(8));const bits=x=>{v.setFloat64(0,x,false);return v.getBigUint64(0,false).toString();};
const op=(op,args)=>({op,args:args.map(bits)}),cases=[];
const vals=[0,-0,1,-1,0.1,1.5,-2.25,1e-100,1e100,Infinity,-Infinity,NaN,2**-149,2**-150,2**24+1,2**128];
for(const type of ['translate','scale'])for(const x of vals)for(const y of vals)cases.push([op(type,[x,y])]);
for(const angle of [0,-0,Infinity,-Infinity,NaN])cases.push([op('translate',[2,3]),op('rotate',[angle])]);
const matrices=[[1,0,0,1,0,0],[1,-0,-0,1,-0,-0],[0,0,0,0,2,3],[1,2,3,4,5,6],[1e100,1e100,1e100,1e100,1e100,1e100],[1,0,0,1,Infinity,0]];
for(const m of matrices)for(const type of ['transform','setTransform']){
 cases.push([op(type,m)]);
 for(const tail of [op('translate',[2,3]),op('scale',[2,3]),op('transform',[0.1,0.2,0.3,0.4,0.5,0.6]),op('setTransform',[1,0,0,1,4,5]),op('resetTransform',[])])cases.push([op(type,m),tail]);
}
let state=912345678;const random=()=>{state=(Math.imul(state,1664525)+1013904223)>>>0;return state/2**32;};
for(let i=0;i<900;i++){const seq=[];for(let j=0;j<1+i%8;j++){
 const type=['translate','scale','transform','setTransform'][Math.floor(random()*4)];
 const args=Array.from({length:['translate','scale'].includes(type)?2:6},()=>i%9===0?vals[Math.floor(random()*vals.length)]:Math.floor(random()*2000-1000)/17);
 seq.push(op(type,args));}cases.push(seq);}
const worker=function(cases){const v=new DataView(new ArrayBuffer(8));const number=b=>{v.setBigUint64(0,BigInt(b),false);return v.getFloat64(0,false);};const bits=x=>{v.setFloat64(0,Number.isNaN(x)?NaN:x,false);return v.getBigUint64(0,false).toString();};return cases.map(seq=>{const c=document.createElement('canvas'),ctx=c.getContext('2d');for(const {op,args}of seq)ctx[op](...args.map(number));const m=ctx.getTransform();return ['a','b','c','d','e','f'].map(k=>bits(m[k]));});};
const native=runNativeBrowser(worker.toString(),cases,{});
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jscanvasmatrixcheck',import.meta.url)),[],{input:JSON.stringify(cases),encoding:'utf8',timeout:120000,maxBuffer:64*1024*1024});if(child.error)throw child.error;assert.equal(child.status,0,child.stderr||child.stdout);
const actual=JSON.parse(child.stdout),failures=[];for(let i=0;i<cases.length;i++)if(JSON.stringify(actual[i])!==JSON.stringify(native.result[i]))failures.push({i,case:cases[i],actual:actual[i],expected:native.result[i]});
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,failures:failures.slice(0,5),versions:native.versions,executableHash:native.executableHash,rendererRefinementVerified:false}));if(failures.length)process.exitCode=1;

// Compare the actual source-call path as well as its pure arithmetic. The
// diagnostic matrix is test output only; it is not a policy observation.
const sourceCases=[];
const add=(name,source,expectedStatus)=>sourceCases.push({name,source,expectedStatus});
const prefix='var c=document.createElement("canvas"),x=c.getContext("2d");';
const asCode=b=>{v.setBigUint64(0,BigInt(b),false);const n=v.getFloat64(0,false);return Object.is(n,-0)?'-0':String(n);};
for(let i=0;i<cases.length;i+=7){
  const source=cases[i].map(({op,args})=>`x.${op}(${args.map(asCode).join(',')});`).join('');
  add(`native source matrix sequence ${i}`,source+'"ok";');
}
for(const op of ['translate','scale','rotate','transform']){
  const count=op==='rotate'?1:op==='transform'?6:2;
  const args=Array.from({length:count},(_,i)=>i===0?'{valueOf:function(){log+="a";return 0;}}':`{valueOf:function(){log+="${i}";return 1;}}`);
  add(`${op} ordered source conversion`,`var log='';x.${op}(${args});log;`);
  for(let n=0;n<count;n++)add(`${op} missing ${count-n} arguments`,
    `var log='';try{x.${op}(${args.slice(0,n)});}catch(e){log+=e.name;}log;`);
  add(`${op} receiver checked before conversion`,
    `var log='';try{CanvasRenderingContext2D.prototype.${op}.call({},${args});}catch(e){log+=e.name;}log;`);
  add(`${op} nonconstructor`,
    `var log='';try{new x.${op}(${Array(count).fill(0)});}catch(e){log+=e.name;}log;`);
}
add('convert every transform argument after nonfinite input',
  'var log="";function n(mark,value){return {valueOf:function(){log+=mark;return value;}};}x.transform(n("a",NaN),n("b",0),n("c",0),n("d",1),n("e",2),n("f",3));log;');
add('conversion exception stops remaining conversions',
  'var log="";try{x.translate({valueOf:function(){log+="a";throw "stop";}},{valueOf:function(){log+="wrong";return 2;}});}catch(e){log+=e;}log;');
add('conversion reset changes transform base and saved stack',
  'x.translate(4,5);x.save();x.translate({valueOf:function(){c.width=50;return 6;}},7);x.restore();"ok";');
add('conversion can change matrix before outer operation',
  'x.translate({valueOf:function(){x.scale(2,3);return 4;}},5);"ok";');
add('native save restore matrix and fields',
  'x.translate(4,5);x.globalAlpha=0.5;x.save();x.scale(2,3);x.globalAlpha=0.25;x.restore();String(x.globalAlpha);');
add('nested save restore order',
  'x.translate(4,5);x.save();x.scale(2,3);x.save();x.transform(1,2,3,4,5,6);x.restore();x.restore();"ok";');
add('empty restore leaves transform', 'x.translate(4,5);x.restore();"ok";');
add('resetTransform keeps saved transform',
  'x.translate(4,5);x.save();x.resetTransform();x.restore();"ok";');
add('setTransform without arguments resets', 'x.translate(4,5);x.setTransform();"ok";');
add('reset ignores uncoerced extra arguments',
  'var log="";x.translate(4,5);x.resetTransform({valueOf:function(){log+="wrong";return 1;}});log;');
add('singular transform followed by save restore and translation',
  'x.scale(0,0);x.save();x.translate(4,5);x.restore();x.translate(6,7);"ok";');
add('reset repairs singular transform', 'x.scale(0,0);x.resetTransform();x.translate(4,5);"ok";');
add('clear preserves transform', 'x.translate(4,5);x.clearRect(0,0,20,20);"ok";');
for(const dimension of ['width','height'])for(const value of [0,1,17,300])add(`dimension ${dimension}=${value} resets transform`,
  `x.translate(4,5);x.save();c.${dimension}=${value};x.restore();x.translate(6,7);x.scale(2,3);"ok";`);
add('general rotation numeric observation remains explicit','x.rotate(0.1);x.getTransform();','unresolved');
add('matrix dictionary overload remains explicit','x.setTransform({e:5});"ok";','unresolved');
add('DOMMatrix result remains explicit','x.getTransform();"ok";','unresolved');
add('large native allocation remains explicit','c.width=4097;x.translate(1,1);"ok";','unresolved');
const nativeSource=runNativeBrowser(function(input){
  const bytes=new DataView(new ArrayBuffer(8));
  const bits=x=>{bytes.setFloat64(0,Number.isNaN(x)?NaN:x,false);return bytes.getBigUint64(0,false).toString();};
  return input.cases.map(item=>{
    if(item.expectedStatus)return {status:item.expectedStatus};
    // Keep c and x local to this invocation and retain the completion value.
    return (function(){
      const result=eval(input.prefix+item.source);
      const m=x.getTransform();
      return {status:'complete',value:{type:'string',units:Array.from(result,ch=>ch.charCodeAt(0))},
        matrix:['a','b','c','d','e','f'].map(k=>bits(m[k]))};
    })();
  });
}.toString(),{prefix,cases:sourceCases},{allowEval:true});
const sourceRequests=sourceCases.map(c=>({browserLibrary:true,diagnosticCanvas:true,fuel:500000,
  ast:compileJavaScript(prefix+c.source,{name:c.name})}));
const sourceChild=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{
  input:JSON.stringify(sourceRequests),encoding:'utf8',timeout:120000,maxBuffer:64*1024*1024});
if(sourceChild.error)throw sourceChild.error;
assert.equal(sourceChild.status,0,sourceChild.stderr||sourceChild.stdout);
const sourceActual=JSON.parse(sourceChild.stdout),sourceFailures=[];
for(let i=0;i<sourceCases.length;i++)try{
  if(sourceCases[i].expectedStatus)assert.equal(sourceActual[i].status,sourceCases[i].expectedStatus);
  else assert.deepEqual({status:sourceActual[i].status,value:sourceActual[i].value,matrix:sourceActual[i].diagnosticCanvas?.[0]?.matrix},nativeSource.result[i]);
}catch(error){sourceFailures.push({name:sourceCases[i].name,observed:sourceActual[i],expected:nativeSource.result[i],error:error.message});}
if(sourceFailures.length){console.error(JSON.stringify(sourceFailures.slice(0,10),null,2));process.exitCode=1;}
console.log(JSON.stringify({browserCases:sourceCases.length,browserPassed:sourceCases.length-sourceFailures.length,
  nativeComparisons:sourceCases.filter(c=>!c.expectedStatus).length,rendererRefinementVerified:false}));
