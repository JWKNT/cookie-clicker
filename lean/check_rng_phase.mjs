import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';
import { extractPhase } from './generate_rng_phase.mjs';
const {parse}=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url))('acorn');
const extract=text=>extractPhase(parse(text,{ecmaVersion:'latest',locations:true}).body[0],text);

const safe=extract('function f(){ Math.seedrandom("s"); randomFloor(1.1); Math.seedrandom(); }');
assert.deepEqual(safe.unresolved,[]);
assert.deepEqual(safe.helpers,['randomFloor']);
const unknown=extract('function f(){ Math.seedrandom(); arbitraryCallback(); }');
assert.deepEqual(unknown.unresolved,['arbitraryCallback']);
assert.deepEqual(unknown.code,['seq',['effect','reset'],['effect','unknown']]);
assert.throws(()=>extract('function f(){ Math.random=other; }'),/Unreviewed Math write/);
assert.throws(()=>extract('function f(){ try { Math.seedrandom("x"); } finally { Math.seedrandom(); } }'),/Unsupported phase statement/);
assert.throws(()=>extract('function f(){ while (x) { break; } }'),/Unsupported phase statement/);
assert.deepEqual(extract('function f(){ var a=[]; a.push(1); }').unresolved,[]);
assert.deepEqual(extract('function f(){ var a=[]; a=other; a.push(1); }').unresolved,['a.push']);
assert.deepEqual(extract('function f(){ var a=[]; a.push=other; a.push(1); }').unresolved,['a.push']);
const report=JSON.parse(readFileSync(new URL('./rng-phase-programs.json',import.meta.url),'utf8'));
const callbacks=report.records.filter(x=>x.mode==='conservative-calls');
assert.equal(callbacks.length,8);
assert.deepEqual(callbacks.filter(x=>x.unresolved.length===0).map(x=>[x.name,x.line]),[
  ['Game.computeLumpType',4522],['Game.last.descFunc',11205],['Game.last.descFunc',11393],
]);
assert(callbacks.find(x=>x.name==='M.castSpell').unresolved.includes('spell.win'));
assert(callbacks.find(x=>x.name==='this.draw').unresolved.includes('pic'));
console.log('Source phase extraction checks passed: 7 closed helpers, 3 conservatively closed callbacks, 5 explicit unresolved callback closures, and negative mutation cases.');
