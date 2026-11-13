import assert from 'node:assert/strict';
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
mkdirSync('/tmp/cookie-audit',{recursive:true});
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),game=loadGameSource(),cases=[];
function extract(file,name){const text=game.sources[file],ast=acorn.parse(text,{ecmaVersion:5});let found=[];function walk(n){if(!n||typeof n.type!=='string')return;if(n.type==='AssignmentExpression'&&text.slice(n.left.start,n.left.end)===name&&n.right.type==='FunctionExpression')found.push(text.slice(n.start,n.end));for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(walk);else if(v&&typeof v==='object')walk(v);}}walk(ast);assert.equal(found.length,1);return found[0]+';';}
const pantheon=extract('minigamePantheon.js','M.logic'),garden=extract('minigameGarden.js','M.save'),earn=extract('main.js','Game.Earn');
const add=(name,epoch,source,expected,status='complete')=>cases.push({name,epochMilliseconds:String(epoch),source,expected,expectedStatus:status,standardLibrary:true,fuel:500000});
for(const epoch of [1793275200000n,2n**100n,2n**1200n]){
 for(const swaps of [0,1,2,3])for(const delta of [-1,0,1]){
  const duration=swaps===0?16*3600000:swaps===1?4*3600000:3600000;
  const passed=duration+delta,increment=delta>=0&&swaps<3;
  add('actual Pantheon.logic '+epoch+' '+swaps+'/'+delta,epoch,
   'var M={swaps:'+swaps+',swapT:Date.now()-'+passed+',lastSwapT:9007199254740992};'+pantheon+'M.logic();M.swaps+":"+(Date.now()-M.swapT)+":"+M.lastSwapT;',
   (swaps+(increment?1:0))+':'+(increment?0:passed)+':9007199254740992');
 }
 add('actual Garden.save clocks '+epoch,epoch,
  'var M={nextStep:Date.now()+120000,nextSoil:Date.now()+600000,nextFreeze:Date.now(),soil:0,freeze:0,harvests:0,harvestsTotal:0,parent:{onMinigame:false},convertTimes:0,plants:{},plot:[]};for(var y=0;y<6;y++){M.plot[y]=[];for(var x=0;x<6;x++)M.plot[y][x]=[0,0];}'+garden+'M.save().split(" ")[0];',
  `${epoch+120000n}:0:${epoch+600000n}:0:0:0:0:0:${epoch}:`);
 add('source Earn stays binary64 '+epoch,epoch,'var Game={cookies:Math.pow(2,100),cookiesEarned:Math.pow(2,100)};'+earn+'var before=Game.cookies;Game.Earn(1);(Game.cookies===before)+":"+((Date.now()+1)-Date.now())+":"+(0.1+0.2);','true:1:0.30000000000000004');
 add('clock coercion and exact differences '+epoch,epoch,'var a=Date.now();typeof a+":"+(a+1>a)+":"+((a+1)-a)+":"+isFinite(a)+":"+isNaN(a)+":"+(parseInt(a)===a)+":"+(parseFloat(a)===a);','number:true:1:true:false:true:true');
 add('exact Date object clone and setter '+epoch,epoch,'var d=new Date(),e=new Date(d);d.setTime(d.getTime()+1);(d-e)+":"+(e.getTime()===Date.now())+":"+d.getUTCMilliseconds();','1:true:'+String((epoch+1n)%1000n));
}
add('ordinary clock division projects binary64',2n**100n,'String(Date.now()/1000);',String(Number(2n**100n)/1000));
add('civil calendar arithmetic remains exact beyond prefix',2n**100n,'var year=new Date().getFullYear();typeof year+":"+((year+5)-year);','number:5');
for(const epoch of [8640000000000000n,8640000000000001n,-8640000000000001n]){
 add('native-prefix boundary advances '+epoch,epoch,'var a=Date.now(),b=new Date(a+1);String(a)+":"+(b.getTime()-a)+":"+(b.getTime()>a);',epoch+':1:true');
}
for(const epoch of [1793275200000n,2n**100n,2n**1200n])for(const fits of [true,false]){
 const quota=(String(epoch).length+1)*2-(fits?0:1);
 add('clock save text retains actual byte quota '+epoch+'/'+quota,epoch,'var out="";try{localStorage.setItem("t",String(Date.now()));out="stored";}catch(e){out=e.name;}out+":"+localStorage.getItem("t");',(fits?'stored:'+epoch:'QuotaExceededError:null'));
 Object.assign(cases.at(-1),{browserLibrary:true,fixtureStorage:{origin:'enabled',quotaBytes:quota}});
}
const input=cases.map(c=>({...c,ast:compileJavaScript(c.source,{name:c.name})}));
writeFileSync('/tmp/cookie-audit/source-clock-cases.json',JSON.stringify(input));
const binary=new URL('./.lake/build/bin/jsastcheck',import.meta.url).pathname;
const p=spawnSync(binary,['--execute'],{input:JSON.stringify(input),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const out=JSON.parse(p.stdout);assert.equal(out.length,cases.length);
for(let i=0;i<cases.length;i++){const c=cases[i],a=out[i];assert.equal(a.status,c.expectedStatus,c.name+':'+JSON.stringify(a));if(c.expectedStatus==='complete')assert.deepEqual(a.value,{type:'string',units:Array.from(c.expected,x=>x.charCodeAt(0))},c.name);}
const report={passed:cases.length,pinnedSourceCases:42,sourceHashes:game.hashes,executableSha256:createHash('sha256').update(readFileSync(binary)).digest('hex'),sourceIntegrationComplete:false,sourceLoaderAnnotations:false,ordinaryEconomicArithmeticUnchangedInFixtures:true};
writeFileSync('/tmp/cookie-audit/source-clock-results.json',JSON.stringify({report,results:out},null,2));console.log(JSON.stringify(report));
