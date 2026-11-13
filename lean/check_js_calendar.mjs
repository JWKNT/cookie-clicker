/** Calendar tests preserve UTC as the documented simulation environment. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';

const cases=[];
const add=t=>cases.push({op:'time',time:String(t)});
for(const n of [-8640000000000000n,-8639999999999999n,-2208988800000n,-1n,0n,1n,951782400000n,8640000000000000n])add(n);
for(const year of [-100000,-400,-100,-4,-1,0,1,4,99,100,400,1600,1900,1969,1970,2000,2024,2100,10000,100000]){
 for(const month of [-25,-13,-1,0,1,2,3,11,12,25])for(const day of [0,1,28,29,30,31,32]){
  cases.push({op:'components',values:[year,month,day,25,-1,60,-1].map(String)});
 }
}
let seed=67;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;};
for(let i=0;i<4000;i++){
 const n=(BigInt(random())*4294967296n+BigInt(random()))%17280000000000001n-8640000000000000n;add(n);
}
const worker=`const fs=require('fs');process.env.TZ='UTC';if(new Date(0).getTimezoneOffset()!==0)throw Error('UTC fixture unavailable');const cases=JSON.parse(fs.readFileSync(0,'utf8'));process.stdout.write(JSON.stringify(cases.map(c=>{let d;if(c.op==='components'){const v=c.values.map(Number);d=new Date(0);d.setUTCFullYear(v[0],v[1],v[2]);d.setUTCHours(v[3],v[4],v[5],v[6]);}else d=new Date(Number(c.time));return{time:String(d.getTime()),year:String(d.getUTCFullYear()),month:d.getUTCMonth(),day:d.getUTCDate(),weekday:d.getUTCDay(),hour:d.getUTCHours(),minute:d.getUTCMinutes(),second:d.getUTCSeconds(),millisecond:d.getUTCMilliseconds(),utc:d.toUTCString(),date:d.toDateString(),clock:d.toTimeString(),iso:d.toISOString()};})));`;
const native=process.argv.includes('--engine');
let expected;
if(native)expected=runNativeEngine(worker,cases);
else{
 const child=spawnSync(process.execPath,['-e',worker],{input:JSON.stringify(cases),encoding:'utf8',maxBuffer:32*1024*1024});
 assert.equal(child.status,0,child.stderr);expected=JSON.parse(child.stdout);
}
const finiteCases=cases.length;
const period=146097n*86400000n;
for(const cycle of [-(2n**100n),-1000000000000n,-1n,1n,1000000000000n,2n**100n])for(const base of [0,1,2,3,4,5,6,7]){
 const e=expected[base],time=BigInt(e.time)+cycle*period,year=BigInt(e.year)+400n*cycle;
 const yearText=(year<0n?'-':'')+(year<0n?-year:year).toString().padStart(4,'0');
 const isoYear=year>=0n&&year<=9999n?year.toString().padStart(4,'0'):(year<0n?'-':'+')+(year<0n?-year:year).toString().padStart(6,'0');
 const utc=e.utc.replace(/ [+-]?\d+ (\d\d:)/,' '+yearText+' $1');
 const date=e.date.replace(/[+-]?\d+$/,yearText);
 const iso=e.iso.replace(/^[+-]?\d+-/,isoYear+'-');
 add(time);expected.push({...e,time:String(time),year:String(year),utc,date,iso});
}
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscalendarcheck',import.meta.url)),[],{
 input:JSON.stringify(cases),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024,
});
if(child.error)throw child.error;
assert.equal(child.status,0,child.stderr);
const actual=JSON.parse(child.stdout);assert.equal(actual.length,cases.length);
for(let i=0;i<cases.length;i++)assert.deepEqual(actual[i],expected[i],JSON.stringify(cases[i]));
console.log(JSON.stringify({nativeRangeCases:finiteCases,unboundedPeriodCases:cases.length-finiteCases,
 comparisonEngine:native?inspectNativeEngine():{node:process.version,v8:process.versions.v8},
 clockSourceRefinementProved:false}));
