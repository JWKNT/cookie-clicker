/** Compare intact PlaySound calls which return before accessing audio or RNG. */
import assert from 'node:assert/strict';
import vm from 'node:vm';
import {createRequire} from 'node:module';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine} from '../model/native-engine.mjs';
import {spawnSyncWithFileInput} from './process-input.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const main=loadGameSource().sources['main.js'];
const node=require('acorn').parse(main,{ecmaVersion:5}).body.flatMap(n=>n.type==='VariableDeclaration'?n.declarations:[]).find(n=>n.id.name==='PlaySound').init;
const fn=main.slice(node.start,node.end);
const cases=[];
for(const value of ['undefined','0','-0','1','0.5','-5','-4.999999999999999','Infinity','NaN','1e300']){
 const source=`var Game={volume:0};var effects='';var guarded=['Audio','Sounds','SoundI','SoundInsts','pitchSupport'];for(var i=0;i<guarded.length;i++)Object.defineProperty(this,guarded[i],{get:function(){effects+='host';throw 'unexpected host read';}});var url={toString:function(){effects+='url';throw 'url conversion';}},pitch={valueOf:function(){effects+='pitch';throw 'pitch conversion';}};var PlaySound=${fn};var result=PlaySound(url,${value},pitch);result+':'+effects+':'+Game.volume;`;
 cases.push({name:'muted '+value,source});
}
// A real source getter must run, while unrelated audio accesses remain absent.
cases.push({name:'setting getter is not erased',source:`var effects='';var Game={get volume(){effects+='volume';return 0;}};var PlaySound=${fn};PlaySound('url')+':'+effects;`});
cases.push({name:'setting getter throw is retained',source:`var Game={get volume(){throw 'setting';}};var PlaySound=${fn};try{PlaySound('url');}catch(e){e;}`});
// Outside the theorem's non-music premise, the music setting really is read.
cases.push({name:'negative music branch is retained',source:`var effects='';var Game={volume:0,get volumeMusic(){effects+='music';return 0;}};var PlaySound=${fn};PlaySound('url',-9)+':'+effects;`});
const request=cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),standardLibrary:true,fuel:100000}));
const executed=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(request),encoding:'utf8',timeout:60000,maxBuffer:8*1024*1024});
assert.equal(executed.status,0,executed.stderr||executed.error?.message);
const actual=JSON.parse(executed.stdout),engine=process.argv.includes('--engine');
const expected=engine?runNativeEngine('const fs=require("fs"),vm=require("vm");const input=JSON.parse(fs.readFileSync(0,"utf8"));process.stdout.write(JSON.stringify(input.map(c=>vm.runInNewContext(c.source))));',cases):cases.map(c=>vm.runInNewContext(c.source));
for(let i=0;i<cases.length;i++){
 assert.equal(actual[i].status,'complete',cases[i].name+':'+JSON.stringify(actual[i]));
 assert.deepEqual(actual[i].value,{type:'string',units:Array.from(expected[i],c=>c.charCodeAt(0))},cases[i].name);
}
console.log(JSON.stringify({audioMutedSourceCases:cases.length,engine:engine?'installed Electron11.5.0':'current Node',functionSha256:createHash('sha256').update(fn).digest('hex'),allSourceBranchesRetained:true}));
