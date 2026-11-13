/** Finite native binary64 comparisons; no universal engine-refinement claim. */
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';

const root=fileURLToPath(new URL('./',import.meta.url));
const proofs=[];
const result=x=>Number.isFinite(x)?`some ${BigInt(x)}`:'none';
const probe=(exact,native)=>{
  assert(exact>=0n);
  proofs.push(`example : roundBinary64Integer ${exact} = ${result(native)} := by decide +kernel`);
};
const integers=new Set([0n,1n,2n]);
for(const exponent of [52,53,54,89,90,91,1022,1023,1024]) {
  const base=2n**BigInt(exponent),spacing=2n**BigInt(Math.max(0,exponent-52));
  for(const displacement of [-spacing-1n,-spacing,-spacing/2n-1n,-spacing/2n,-1n,0n,1n,spacing/2n,spacing/2n+1n,spacing,spacing+1n]) {
    if(base+displacement>=0n)integers.add(base+displacement);
  }
}
for(const value of integers)probe(value,Number(value));
const bank=2**90,unitCap=2**53;
assert.equal(0.01,5764607523034235/2**59);
assert.equal(100*0.01,1);
probe(5764607523034235n*100n,100*0.01*2**59);
for(const amount of [0,1,2**36-1,2**36,2**36+1,2**37-1,2**37,2**37+1]) {
  probe(BigInt(bank)+BigInt(amount),bank+amount);
  probe(BigInt(bank)-BigInt(amount),bank-amount);
}
for(const value of [unitCap-2,unitCap-1,unitCap,unitCap+2])probe(BigInt(value)+1n,value+1);
const numericCases=proofs.length;
let nativePriceCases=0;
if(process.argv.includes('--engine')) {
  const {createRuntime}=await import('../model/runtime.mjs');
  const runtime=createRuntime({recordAudit:false});
  const mine=runtime.Game.Objects.Mine;
  let maxDebit=0,maxRefund=0;
  for(let amount=1;amount<=100;amount++) {
    mine.amount=amount;
    const debit=mine.getPrice();
    assert(Number.isSafeInteger(debit)&&debit<=2**36);
    assert.equal(bank-debit,bank);
    probe(BigInt(bank)-BigInt(debit),bank-debit);
    proofs.push(`example : Transaction.small (.debit ${debit}) := by unfold Transaction.small; decide +kernel`);
    maxDebit=Math.max(maxDebit,debit);
    mine.amount=amount+1;
    const refund=Math.floor(mine.getPrice()*mine.getSellMultiplier());
    assert(Number.isSafeInteger(refund)&&refund<=2**37);
    assert.equal(bank+refund,bank);
    probe(BigInt(bank)+BigInt(refund),bank+refund);
    proofs.push(`example : Transaction.small (.refund ${refund}) := by unfold Transaction.small; decide +kernel`);
    maxRefund=Math.max(maxRefund,refund);
    nativePriceCases+=2;
  }
  console.log(`Native Mine1..101 fixture bounds: max per-copy debit ${maxDebit}, max refund ${maxRefund}; bank2^90 rounds every transfer away.`);
}
const directory=mkdtempSync(join(tmpdir(),'cookie-godzamok-rounding-'));
try {
  const file=join(directory,'Probes.lean');
  writeFileSync(file,`import CookieClicker.GodzamokRounding
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option exponentiation.threshold 2048
open CookieClicker.FullGame.GodzamokRounding
${proofs.join('\n')}
`);
  const checked=spawnSync('lake',['env','lean',file],{cwd:root,encoding:'utf8',maxBuffer:8*1024*1024});
  assert.equal(checked.status,0,checked.stdout+'\n'+checked.stderr);
}finally{rmSync(directory,{recursive:true,force:true});}
console.log(`Binary64 integer rounding passed ${numericCases} native boundary comparisons and ${nativePriceCases} source-price projections. Finite tests do not prove full numeric or callback refinement.`);
