import assert from 'node:assert/strict';
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {compileJavaScript,compilePinnedGameAst} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
mkdirSync('/tmp/cookie-audit',{recursive:true});
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));const acorn=require('acorn'),game=loadGameSource(),manifest=JSON.parse(readFileSync(new URL('../model/clock-source-sites.json',import.meta.url))),cases=[];
function func(file,name){const text=game.sources[file];let found;function walk(n){if(!n||typeof n.type!=='string')return;if(n.type==='AssignmentExpression'&&text.slice(n.left.start,n.left.end)===name&&n.right.type==='FunctionExpression'){assert(!found);found={file,sourceStart:n.start,text:text.slice(n.start,n.end)};}for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(walk);else if(v&&typeof v==='object')walk(v);}}walk(acorn.parse(text,{ecmaVersion:5}));assert(found);return found;}
function add(name,epoch,parts,expected,status='complete'){let source='',clockFragments=[];for(const p of parts){if(typeof p==='string')source+=p;else{clockFragments.push({file:p.file,sourceStart:p.sourceStart??p.start,generatedStart:source.length,length:p.text.length});source+=p.text+';';}}cases.push({name,epochMilliseconds:String(epoch),source,ast:compileJavaScript(source,{name,unboundedClock:true,clockFragments}),expected,expectedStatus:status,standardLibrary:true,fuel:1000000});}
const save=func('minigamePantheon.js','M.save'),load=func('minigamePantheon.js','M.load');
for(const epoch of [0n,1793275200000n,2n**100n,2n**1200n])for(const fraction of ['0','0.125','0.1']){
 add('full pinned Pantheon save/load '+epoch+'/'+fraction,epoch,[
  'var M={slot:[-1,-1,-1],swaps:2,swapT:Date.now()+'+fraction+',parent:{onMinigame:false}};',save,load,
  'var before=M.swapT,saved=M.save();M.swapT=Date.now()+12345;M.load(saved);(M.swapT===before)+":"+((M.swapT+1)-M.swapT)+":"+M.swaps+":"+(typeof saved);'],
  'true:1:2:string');
}
for(const epoch of [0n,1793275200000n,2n**100n,2n**1200n])for(const field of manifest.savedFields){
 let setup,write,reset,read,expected;
 if(field.field.startsWith('Game.')){
  setup='var Game={startDate:Date.now(),fullDate:Date.now(),lastDate:Date.now(),lumpT:Date.now()+0.125};var spl=[];';
  const slot=Number(field.slot.match(/\[(\d+)\]$/)[1]);write='var before='+field.field+';spl['+slot+']=String('+field.writer.text+');';reset=field.field+'=Date.now()+12345;';
  expected=field.field==='Game.lumpT'?'0.125:1':'0:1';
 }else if(field.slot.startsWith('garden.')){
  const slot=Number(field.slot.match(/colon\[(\d+)\]/)[1]);setup='var M={nextStep:Date.now()+0.125,nextSoil:Date.now()+0.125,nextFreeze:Date.now()+0.125};var spl2=[],i2='+slot+';';write='var before='+field.field+';spl2['+slot+']=String('+field.writer.text+');';reset=field.field+'=Date.now()+12345;';expected='0:1';
 }else{setup='var M={swapT:Date.now()+0.125};var spl=[],i=2;';write='var before=M.swapT;spl[2]=String('+field.writer.text+');';reset='M.swapT=Date.now()+12345;';expected='0:1';}
 add('exact pinned writer/reader '+field.field+' '+epoch,epoch,[setup,write,reset,field.reader,'(before-'+field.field+')+":"+(('+field.field+'+1)-'+field.field+');'],expected);
}
for(const entry of manifest.extraTypedSites.filter(row=>row.role.startsWith('zero timestamp'))){
 const field=entry.site.text.split('=')[0];
 add('zero clock initializer keeps duration domain '+field,2n**1200n,['var Game={},M={};',entry.site,'typeof '+field+'+":"+isFinite(Date.now()-'+field+');'],'number:false');
}
const reader=manifest.savedFields[0].reader;
add('clock intrinsic identity checked after argument evaluation',2n**100n,['var log="",Game={},spl={get 0(){log+="a";return "1";}};parseInt=function(x){log+="call";return 1;};',reader],null,'unresolved');
add('clock reader source ToString callback preserved',2n**100n,['var log="",Game={},spl=[{toString:function(){log+="s";return "1267650600228229401496703205377";}}];',reader,'log+":"+(Game.startDate-Date.now());'],'s:1');
add('clock reader source coercion throw preserved',2n**100n,['var Game={},spl=[{toString:function(){throw 7;}}];',reader],null,'throw');
add('current-save field syntax boundary stays explicit',2n**100n,['var Game={},spl=["not a current timestamp"];',reader],null,'unresolved');
const plain=compileJavaScript('var Game={};Game.startDate=parseInt("1267650600228229401496703205377");');assert.equal(plain.nodes.some(n=>n.tag==='clockRead'),false);
assert.throws(()=>compileJavaScript('Game.startDate=parseInt("1");',{unboundedClock:true,clockFragments:[{file:'main.js',sourceStart:reader.start,generatedStart:0,length:reader.text.length}]}),/does not match pinned source/);
const original=compilePinnedGameAst(),annotated=compilePinnedGameAst({unboundedClock:true});let erased=0;for(const n of annotated.nodes){if(n.tag==='clockRead'){erased++;n.tag='call';n.arguments=[n.argument];delete n.argument;delete n.integer;}else if(n.tag==='clockZero'){erased++;n.tag='literal';n.literalKind='number';n.bits='0';n.raw='0';}}delete annotated.clockModel;assert.deepEqual(annotated,original);assert.equal(erased,15);
const p=spawnSync(new URL('./.lake/build/bin/jsastcheck',import.meta.url).pathname,['--execute'],{input:JSON.stringify(cases),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const out=JSON.parse(p.stdout);assert.equal(out.length,cases.length);for(let i=0;i<cases.length;i++){const c=cases[i],a=out[i];assert.equal(a.status,c.expectedStatus,c.name+':'+JSON.stringify(a));if(c.expectedStatus==='complete')assert.deepEqual(a.value,{type:'string',units:Array.from(c.expected,x=>x.charCodeAt(0))},c.name);}
const binary=new URL('./.lake/build/bin/jsastcheck',import.meta.url).pathname;
function reject(request,message){const result=spawnSync(binary,['--execute'],{input:JSON.stringify([request]),encoding:'utf8',timeout:120000,maxBuffer:1024*1024});if(result.error)throw result.error;assert.equal(result.status,1);assert.match(result.stderr,message);}
reject({ast:compileJavaScript('void 0;'),fuel:100,requireClockAnnotations:true},/requires annotated clock artifacts/);
const missingMarker=structuredClone(cases[0]);delete missingMarker.ast.clockModel;
reject(missingMarker,/requires the selected unbounded-clock artifact marker/);
const wrongMarker=structuredClone(cases[0]);wrongMarker.ast.clockModel='unknown-clock';
reject(wrongMarker,/Unknown source clock model/);
writeFileSync('/tmp/cookie-audit/loader-clock-results.json',JSON.stringify({passed:cases.length,annotationErasureExact:true,sourceRefinementProved:false,cases:cases.map(({ast,...c})=>c),results:out},null,2));console.log(JSON.stringify({passed:cases.length,fullPantheonSaveLoadCases:12,exactEightWriterReaderCases:32,annotationErasure:erased,artifactRejections:3,sourceRefinementProved:false}));
