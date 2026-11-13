/** Differential checks for the explicitly selected timestamp-text extension.
 * Native Date-prefix construction and native explicit-string seed processing are
 * different claims. The latter does not assert native arbitrary Date support.
 * Actual pinned seedrandom source executes; no seeded-output oracle is installed
 * in the Lean interpreter. The zero-argument restore rule is the selected law. */
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine} from '../model/native-engine.mjs';
import {spawnSyncWithFileInput} from './process-input.mjs';

const option=name=>{const at=process.argv.indexOf(name);return at<0?undefined:process.argv[at+1];};
const driver=option('--driver')??fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url));
const maximumDigits=Number(option('--max-digits')??65536);
assert(Number.isSafeInteger(maximumDigits)&&maximumDigits>=1&&maximumDigits<=65536);
const selected=option('--case');
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const main=loadGameSource().sources['main.js'];
const parsed=require('acorn').parse(main,{ecmaVersion:5});
const libraryNode=parsed.body.find(n=>n.type==='ExpressionStatement'&&main.slice(n.start,n.end).includes('c.seedrandom=function'));
assert(libraryNode);
const library=main.slice(libraryNode.start,libraryNode.end);
const libraryHash=createHash('sha256').update(library).digest('hex');
assert.equal(libraryHash,'a6c6d6219add3214812ad4d6dd8311ddb2b5d9551090344ce047a6226045b7be');
const bootstrap='var originalFree=Math.random;'+library;
const cases=[];
const push=(name,kind,epoch,plain=false,offset='')=>{
 let timestamp=epoch;
 if(offset){
  if(kind==='native-date-prefix')timestamp=String(Number(epoch)+Number(offset));
  else {assert.equal(offset,'+0.5');timestamp=epoch+'.5';}
 }
 const text='ubyju/'+timestamp;
 const lumpExpression=plain?JSON.stringify(epoch):'Date.now()'+offset;
 const action=`var Game={seed:'ubyju',lumpT:${lumpExpression}};var seedText=Game.seed+'/'+Game.lumpT;var returned=Math.seedrandom(seedText);console.log(returned);for(var i=0;i<20;i++)console.log(Math.random());Math.seedrandom();console.log(Math.random());(typeof seedText)+':'+(seedText===${JSON.stringify(text)})+':'+(Math.random===originalFree);`;
 cases.push({name,kind,epoch,plain,text,action,nativeAction:kind==='extended-decimal-argument'?action.replace('lumpT:'+lumpExpression,'lumpT:'+JSON.stringify(timestamp)):action});
};
for(const epoch of ['0','1','-1','1793275200000','8640000000000000','8639999999999999','-8640000000000000'])
 push('native-date-'+epoch,'native-date-prefix',epoch);
for(const [epoch,offset] of [['1793275200000','+0.125'],['1','-0.125'],['0','+0.1']])
 push('native-fraction-'+epoch+offset,'native-date-prefix',epoch,false,offset);
for(const epoch of ['8640000000000001','9007199254740991','9007199254740992','9007199254740993','1000000000000000000000'])
 push('extended-boundary-'+epoch,'extended-decimal-argument',epoch);
push('extended-fraction','extended-decimal-argument','9007199254740993',false,'+0.5');
for(const digits of [249,250,251,255,256,257,1024,4096,65536])if(digits<=maximumDigits){
 const epoch='1'+Array.from({length:digits-1},(_,i)=>String((i*7+3)%10)).join('');
 push('extended-digits-'+digits,'extended-decimal-argument',epoch);
 if(digits<=257)push('ordinary-string-digits-'+digits,'ordinary-string-control',epoch,true);
}
const chosen=cases.filter(c=>!selected||c.name===selected);assert(chosen.length,'No selected case');
const native=runNativeEngine(`const fs=require('fs'),vm=require('vm');const input=JSON.parse(fs.readFileSync(0,'utf8'));const bits=n=>{const b=Buffer.alloc(8);b.writeDoubleBE(n);return b.readBigUInt64BE().toString()};const encode=v=>typeof v==='number'?{type:'number',bits:bits(v)}:typeof v==='string'?{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))}:(()=>{throw Error('Unsupported result')})();process.stdout.write(JSON.stringify(input.cases.map(c=>{let freeCalls=0;const tape=[0.5,17/Math.pow(2,53)],events=[];const context={console:{log:(...args)=>events.push({type:'log',arguments:args.map(encode)})},fixtureFree:()=>{if(freeCalls>=tape.length)throw Error('Extra free draw');return tape[freeCalls++]}};vm.createContext(context);vm.runInContext('Math.random=fixtureFree;'+input.bootstrap,context);vm.runInContext('var capturedSeedrandom=Math.seedrandom;Math.seedrandom=function(){if(arguments.length===0){Math.random=originalFree;return;}return capturedSeedrandom.apply(this,arguments);};',context);let action=c.nativeAction;if(c.kind==='native-date-prefix'){vm.runInContext('Date.now=function(){return new Date(Number('+JSON.stringify(c.epoch)+')).getTime();};',context);}const value=vm.runInContext(action,context);return {name:c.name,value:encode(value),events,freeCalls};})));`,{bootstrap,cases:chosen});
for(const row of native){assert.equal(row.freeCalls,2,row.name);assert.equal(row.events.length,22,row.name);}
if(process.argv.includes('--native-only')){
 console.log(JSON.stringify({nativeReferenceOnly:true,cases:chosen.map((c,i)=>({name:c.name,kind:c.kind,digits:c.epoch.length,seedLength:c.text.length,reference:native[i]})),libraryHash}));
 process.exit(0);
}
const results=[];
for(let i=0;i<chosen.length;i++){
 const c=chosen[i],start=performance.now();
 const request={ast:compileJavaScript(bootstrap,{name:c.name+' bootstrap',unboundedClock:true}),captureSeedrandomAfter:0,browserLibrary:true,epochMilliseconds:c.epoch,randomInputs:[4503599627370496,17],fuel:3000000,taskFuel:50000000,postTaskStages:[{ast:compileJavaScript(c.action,{name:c.name,unboundedClock:true}),taskBudget:0}]};
 const p=spawnSyncWithFileInput(driver,['--execute'],{input:JSON.stringify([request]),encoding:'utf8',timeout:600000,maxBuffer:16*1024*1024});
 if(p.error)throw p.error;assert.equal(p.status,0,c.name+':'+p.stderr);
 const actual=JSON.parse(p.stdout)[0];
 assert.equal(actual.status,'complete',c.name+':'+JSON.stringify(actual));
 assert.deepEqual(actual.value,native[i].value,c.name+' typeof/equality/restored identity');
 assert.deepEqual(actual.consoleEvents,native[i].events,c.name+' returned seed and20 draw bits plus restored free draw');
 assert.equal(actual.randomInputsRemaining,0,c.name+' consumes one bootstrap draw and one restored draw');
 assert.equal(actual.timestampMixkeyActivations,c.plain?0:1,c.name+' uses only the captured typed timestamp mixing activation');
 assert.equal(actual.postTaskStagesCompleted,1,c.name+' source action completes');
 results.push({name:c.name,kind:c.kind,digits:c.epoch.length,seedLength:c.text.length,milliseconds:Math.round(performance.now()-start)});
 console.log(JSON.stringify({passed:results.at(-1)}));
}
console.log(JSON.stringify({timestampTextCases:results.length,nativeDatePrefixCases:results.filter(x=>x.kind==='native-date-prefix').length,extendedArgumentCases:results.filter(x=>x.kind==='extended-decimal-argument').length,ordinaryStringControls:results.filter(x=>x.kind==='ordinary-string-control').length,maximumDigits,selectedCase:selected??null,drawsComparedPerCase:20,freeDrawsPerCase:2,seedrandomLibrarySha256:libraryHash,arbitraryLengthProvedByTheseTests:false}));
