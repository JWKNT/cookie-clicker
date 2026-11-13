/** Source and native checks of the fully partitioned startup-letter projection. */
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import {fileURLToPath} from 'node:url';
import {loadGameSource} from '../model/game-source.mjs';
import {LETTER_BUCKETS,IID53_SIZE,STARTUP_SEED_PRIOR_DENOMINATOR,startupSeedPriorNumerator} from '../model/seed-inference.mjs';

const root=fileURLToPath(new URL('./',import.meta.url));
const source=loadGameSource();
const compact=source.sources['main.js'].replace(/\s/g,'');
assert(compact.includes("functionchoose(arr){returnarr[Math.floor(Math.random()*arr.length)];}"));
assert(compact.includes("Game.makeSeed=function(){varchars='abcdefghijklmnopqrstuvwxyz'.split('');varstr='';for(vari=0;i<5;i++){str+=choose(chars);}returnstr;}"));
assert.equal(IID53_SIZE,2n**53n);
assert.equal(STARTUP_SEED_PRIOR_DENOMINATOR,2n**265n);
assert.equal(LETTER_BUCKETS.length,26);
assert.equal(LETTER_BUCKETS.reduce((sum,x)=>sum+x.count,0n),IID53_SIZE);
const proofs=[];
let boundaryCases=0;
for(const [j,bucket] of LETTER_BUCKETS.entries()) {
  proofs.push(`example : boundary ${j} = ${bucket.lower} := by decide +kernel`);
  proofs.push(`example : boundary ${j+1} = ${bucket.upperExclusive} := by decide +kernel`);
  proofs.push(`example : bucketCount ${j} = ${bucket.count} := by decide +kernel`);
  for(const k of new Set([bucket.lower,bucket.lower+1n,(bucket.lower+bucket.upperExclusive)/2n,bucket.upperExclusive-1n])) {
    const actual=Math.floor(Number(k)/Number(IID53_SIZE)*26);
    assert.equal(actual,j);
    proofs.push(`example : letter ${k} = ${actual} := by decide +kernel`);
    boundaryCases++;
  }
}
for(const seed of ['aaaaa','zzzzz','aaaao','aaodk','abeby']) {
  const ids=[...seed].map(x=>x.charCodeAt(0)-97);
  const product=ids.map(x=>`bucketCount ${x}`).join(' * ');
  proofs.push(`example : ${product} = ${startupSeedPriorNumerator(seed)} := by decide +kernel`);
}
let nativeSeeds=0;
if(process.argv.includes('--engine')) {
  const {createRuntime}=await import('../model/runtime.mjs');
  const runtime=createRuntime({recordAudit:false});
  const original=runtime.context.Math.random;
  try {
    for(const seed of ['aaaaa','zzzzz','aaaao','aaodk','abeby']) {
      const indices=[...seed].map(x=>LETTER_BUCKETS[x.charCodeAt(0)-97].lower);
      let used=0;
      runtime.context.Math.random=()=>{
        assert(used<5,'makeSeed consumed an unexpected extra free draw');
        return Number(indices[used++])/Number(IID53_SIZE);
      };
      assert.equal(runtime.Game.makeSeed(),seed);
      assert.equal(used,5);
      nativeSeeds++;
    }
  }finally{runtime.context.Math.random=original;}
}
const directory=mkdtempSync(join(tmpdir(),'cookie-startup-seed-'));
try {
  const file=join(directory,'Probes.lean');
  writeFileSync(file,`import CookieClicker.StartupSeed
set_option maxHeartbeats 0
open CookieClicker.FullGame.StartupSeed
${proofs.join('\n')}
`);
  const checked=spawnSync('lake',['env','lean',file],{cwd:root,encoding:'utf8',maxBuffer:8*1024*1024});
  assert.equal(checked.status,0,checked.stdout+'\n'+checked.stderr);
}finally{rmSync(directory,{recursive:true,force:true});}
console.log(`Startup seed prior passed all26 bucket/count comparisons,${boundaryCases} native numeric probes,5 seed-weight checks,and${nativeSeeds} native five-draw seed calls. The universal interval proof is in StartupSeed.lean; complete source refinement remains separate.`);
