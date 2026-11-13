import assert from 'node:assert/strict';
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
mkdirSync('/tmp/cookie-audit',{recursive:true});
const game=loadGameSource(),source=game.sources['main.js'];
const start=source.indexOf("Game.baseSeason='';//halloween"),finish=source.indexOf('\n\tGame.updateLog=',start);
assert(start>=0&&finish>start);
const season=source.slice(start,finish);
const expiry='now.setFullYear(now.getFullYear()+5);';
assert(source.includes(expiry));
const floor=(a,b)=>{let q=a/b;return a%b<0n?q-1n:q;};
const mod=(a,b)=>a-floor(a,b)*b;
const yearStart=y=>365n*(y-1970n)+floor(y-1969n,4n)-floor(y-1901n,100n)+floor(y-1601n,400n);
const leap=y=>mod(y,4n)===0n&&(mod(y,100n)!==0n||mod(y,400n)===0n);
const monthDays=y=>[31n,leap(y)?29n:28n,31n,30n,31n,30n,31n,31n,30n,31n,30n,31n];
const dayOf=(y,m,d)=>monthDays(y).slice(0,m-1).reduce((a,b)=>a+b,0n)+BigInt(d);
const epoch=(y,m,d,ms=0n)=>(yearStart(y)+dayOf(y,m,d)-1n)*86400000n+ms;
function easter(y){
 const c=floor(y,100n),n=mod(y,19n),k=floor(c-17n,25n);
 let i=mod(c-floor(c,4n)-floor(c-k,3n)+19n*n+15n,30n);
 i-=floor(i,28n)*(1n-floor(i,28n)*floor(29n,i+1n)*floor(21n-n,11n));
 const j=mod(y+floor(y,4n)+i+2n-c+floor(c,4n),7n),l=i-j;
 const m=3n+floor(l+40n,44n),d=l+28n-31n*floor(m,4n);
 return dayOf(y,Number(m),d);
}
function baseSeason(y,day){const l=leap(y)?1n:0n;
 if(day>=41n&&day<=46n)return 'valentines';
 if(day+l>=90n&&day<=92n+l)return 'fools';
 if(day>=304n-7n+l&&day<=304n+l)return 'halloween';
 if(day>=349n+l&&day<=365n+l)return 'christmas';
 const e=easter(y);return day>=e-7n&&day<=e?'easter':'';
}
const cases=[];
function add(name,epochMilliseconds,code,expected){cases.push({name,epochMilliseconds:String(epochMilliseconds),source:code,expected,standardLibrary:true,fuel:1000000});}
for(const y of [2026n,2n**100n,2n**100n+1n,2n**1200n,-(2n**100n)]){
 const e=easter(y),l=leap(y)?1n:0n;
 for(const day of new Set([1n,40n,41n,46n,47n,89n,90n,92n+l,93n+l,297n+l,304n+l,305n+l,349n+l,365n+l,e-8n,e-7n,e,e+1n])){
  add('actual season year '+y+' day '+day,(yearStart(y)+day-1n)*86400000n+43200000n,
   'var Game={};'+season+'Game.baseSeason+":"+year+":"+day;',baseSeason(y,day)+':'+y+':'+day);
 }
 add('actual cookie expiry +5 year '+y,epoch(y,2,28,45296789n),
  'var now=new Date();'+expiry+'now.getFullYear()+":"+now.getMonth()+":"+now.getDate()+":"+now.getHours()+":"+now.getMinutes()+":"+now.getSeconds()+":"+now.getMilliseconds()+":"+now.getTime();',
  `${y+5n}:1:28:12:34:56:789:${epoch(y+5n,2,28,45296789n)}`);
 add('exact calendar Date.UTC components '+y,epoch(y,1,1),
  'var y=new Date().getFullYear(),d=new Date(Date.UTC(y,1,29));d.getFullYear()+":"+d.getMonth()+":"+d.getDate()+":"+d.getTime();',
  `${y}:${leap(y)?1:2}:${leap(y)?29:1}:${epoch(y,2,29)}`);
 add('exact calendar negative truncating remainder '+y,epoch(y,1,1),
  'var y=new Date().getFullYear();(y%19)+":"+Math.floor(y/19)+":"+Math.ceil(y/19)+":"+Math.trunc(y/19);',
  `${y%19n}:${floor(y,19n)}:${-floor(-y,19n)}:${y/19n}`);
}
const input=cases.map(c=>({...c,ast:compileJavaScript(c.source,{name:c.name})}));
const binary=new URL('./.lake/build/bin/jsastcheck',import.meta.url).pathname;
const p=spawnSync(binary,['--execute'],{input:JSON.stringify(input),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const out=JSON.parse(p.stdout);assert.equal(out.length,cases.length);
for(let i=0;i<cases.length;i++){assert.equal(out[i].status,'complete',cases[i].name+':'+JSON.stringify(out[i]));assert.deepEqual(out[i].value,{type:'string',units:Array.from(cases[i].expected,x=>x.charCodeAt(0))},cases[i].name);}
const report={passed:cases.length,pinnedSeasonSourceSha256:createHash('sha256').update(season).digest('hex'),sourceHashes:game.hashes,executableSha256:createHash('sha256').update(readFileSync(binary)).digest('hex'),expected:'independent exact BigInt Gregorian/computus formulas; no native Date beyond finite range',fullSourceClockRefinement:false};
writeFileSync('/tmp/cookie-audit/calendar-clock-results.json',JSON.stringify({report,results:out},null,2));console.log(JSON.stringify(report));
