/** Native source save-codec transport followed by selected timestamp reader and
 * captured source seed mixing. Extended text cases use native explicit strings;
 * they do not assert that native parseInt or Date represents huge integers. */
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
import {spawnSyncWithFileInput} from './process-input.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const main=loadGameSource().sources['main.js'],tree=require('acorn').parse(main,{ecmaVersion:5});
const libraryNode=tree.body.find(n=>n.type==='ExpressionStatement'&&main.slice(n.start,n.end).includes('c.seedrandom=function'));
assert(libraryNode);const library=main.slice(libraryNode.start,libraryNode.end);
const helpers=tree.body.filter(n=>n.type==='FunctionDeclaration'&&['utf8_to_b64','b64_to_utf8'].includes(n.id.name));assert.equal(helpers.length,2);
const helperText=helpers.map(n=>main.slice(n.start,n.end)).join('\n');
const reader=JSON.parse(readFileSync(new URL('../model/clock-source-sites.json',import.meta.url))).savedFields.find(x=>x.field==='Game.lumpT').reader;
assert.equal(main.slice(reader.start,reader.end),reader.text);
const bootstrap='var originalFree=Math.random;'+library+helperText;
const cases=[13,249,250,251,255,256,257,1024].map(digits=>{
 const epoch=digits===13?'1793275200000':'1'+Array.from({length:digits-1},(_,i)=>String((i*7+3)%10)).join('');
 const prefix=`var Game={seed:'ubyju',lumpT:Date.now()},spl=[];spl[0]=12345.625;spl[44]=Game.lumpT;var saved=escape(utf8_to_b64(spl.join(';'))+'!END!');var decoded=b64_to_utf8(unescape(saved).slice(0,-5));spl=decoded.split(';');Game.cookies=parseFloat(spl[0]);`;
 const suffix=`;var seedText=Game.seed+'/'+Game.lumpT;var returned=Math.seedrandom(seedText);console.log(saved);console.log(decoded);console.log(returned);for(var i=0;i<20;i++)console.log(Math.random());Math.seedrandom();console.log(Math.random());(typeof seedText)+':'+(seedText===${JSON.stringify('ubyju/'+epoch)})+':'+(Math.random===originalFree)+':'+(typeof Game.cookies)+':'+(Game.cookies===12345.625);`;
 const action=prefix+reader.text+suffix;
 return {name:'source-save-codec-'+digits,digits,epoch,action,nativeAction:prefix.replace('lumpT:Date.now()','lumpT:'+JSON.stringify(epoch))+(digits===13?reader.text:"Game.lumpT=spl[44]")+suffix,fragments:[{file:'main.js',sourceStart:reader.start,generatedStart:prefix.length,length:reader.end-reader.start}]};
});
const native=runNativeBrowser(`input=>{const numberBits=n=>{const b=new ArrayBuffer(8),d=new DataView(b);d.setFloat64(0,n);return d.getBigUint64(0).toString()};const encode=v=>typeof v==='number'?{type:'number',bits:numberBits(v)}:{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};return input.cases.map(c=>{let calls=0;const values=[0.5,17/Math.pow(2,53)],events=[],original=Math.random,originalSeedrandom=Math.seedrandom;Math.random=()=>{if(calls>=2)throw Error('Extra free draw');return values[calls++]};try{const result=Function('console',input.bootstrap+'var capturedSeedrandom=Math.seedrandom;Math.seedrandom=function(){if(arguments.length===0){Math.random=originalFree;return;}return capturedSeedrandom.apply(this,arguments);};return(function(){'+c.nativeAction+'})()')({log:(...args)=>events.push({type:'log',arguments:args.map(encode)})});return {name:c.name,events,calls,result:encode(result)}}finally{Math.random=original;Math.seedrandom=originalSeedrandom}})}`,{bootstrap,cases:cases.map(c=>({...c,nativeAction:c.nativeAction.replace(/\(typeof seedText\)\+/, 'return (typeof seedText)+')}))},{allowEval:true});
const driver=process.argv.includes('--driver')?process.argv[process.argv.indexOf('--driver')+1]:new URL('.lake/build/bin/jsastcheck',import.meta.url).pathname;
for(let i=0;i<cases.length;i++){
 const c=cases[i],start=performance.now();
 const request={ast:compileJavaScript(bootstrap,{unboundedClock:true}),captureSeedrandomAfter:0,browserLibrary:true,epochMilliseconds:c.epoch,randomInputs:[4503599627370496,17],fuel:3000000,taskFuel:50000000,postTaskStages:[{ast:compileJavaScript(c.action,{unboundedClock:true,clockFragments:c.fragments}),taskBudget:0}]};
 const p=spawnSyncWithFileInput(driver,['--execute'],{input:JSON.stringify([request]),encoding:'utf8',timeout:600000,maxBuffer:16*1024*1024});if(p.error)throw p.error;assert.equal(p.status,0,c.name+':'+p.stderr);
 const actual=JSON.parse(p.stdout)[0],reference=native.result[i];
 assert.equal(actual.status,'complete',c.name+':'+JSON.stringify(actual));assert.deepEqual(actual.value,reference.result,c.name+' final types/economic field');assert.deepEqual(actual.consoleEvents,reference.events,c.name+' exact save text, decoded text, seed and20 draw bits');assert.equal(reference.calls,2);assert.equal(actual.randomInputsRemaining,0);assert.equal(actual.timestampMixkeyActivations,1);assert.equal(actual.postTaskStagesCompleted,1);
 console.log(JSON.stringify({passed:c.name,digits:c.digits,milliseconds:Math.round(performance.now()-start),nativeReference:c.digits===13?'ordinary timestamp reader':'explicit decoded timestamp string'}));
}
console.log(JSON.stringify({saveCodecCases:cases.length,sourceHelpers:helpers.map(n=>({name:n.id.name,sha256:createHash('sha256').update(main.slice(n.start,n.end)).digest('hex')})),readerSha256:reader.sha256,engine:native.identity,arbitraryLengthRoundtripProved:false}));
