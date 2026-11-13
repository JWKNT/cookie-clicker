import assert from 'node:assert/strict';
import {createRequire}from'node:module';
import{readFileSync,writeFileSync}from'node:fs';
import{execFileSync}from'node:child_process';
import{createHash}from'node:crypto';
import{loadGameSource}from'../../game-source.mjs';
import{runNativeEngine}from'../../native-engine.mjs';
import{shortAsciiSeededRandom}from'../../seed-inference.mjs';
const dir='/tmp/cookie-audit/veil-seed-cover/';
const require=createRequire(new URL('../../../source/cookie-monster-plus/package.json',import.meta.url));
const source=loadGameSource(),text=source.sources['main.js'],parsed=require('acorn').parse(text,{ecmaVersion:5});
const roots=parsed.body.filter(n=>n.type==='ExpressionStatement'&&text.slice(n.start,n.end).includes('c.seedrandom=function'));assert.equal(roots.length,1);
const library=text.slice(roots[0].start,roots[0].end),sha=x=>createHash('sha256').update(x).digest('hex');
const seed=n=>{let s='';for(let i=0;i<5;i++){s=String.fromCharCode(97+n%26)+s;n=Math.floor(n/26);}return s;};
const samples=[];let state=1;for(let n=0;n<1000;n++){state=(Math.imul(state,1664525)+1013904223)>>>0;for(const counter of[0,1,9,10,31,63])samples.push({seed:seed(state%11881376),counter});}
for(const x of['aaaaa','aaaab','zzzzz'])for(let counter=0;counter<64;counter++)samples.push({seed:x,counter});
const sampleText=samples.map(x=>x.seed+' '+x.counter).join('\n')+'\n';writeFileSync(dir+'samples.txt',sampleText);
const cpp=execFileSync(dir+'scan',['--samples',dir+'samples.txt'],{encoding:'utf8'}).trim().split('\n');
const script=`const fs=require('fs'),vm=require('vm');const input=JSON.parse(fs.readFileSync(0,'utf8')),context=vm.createContext({});vm.runInContext(input.library,context);const rows=input.samples.map(x=>{context.seed=x.seed+'/'+x.counter;const value=vm.runInContext('Math.seedrandom(seed);Math.random()',context);const buffer=Buffer.alloc(8);buffer.writeDoubleBE(value);return buffer.toString('hex');});process.stdout.write(JSON.stringify({versions:process.versions,rows}));`;
const native=runNativeEngine(script,{library,samples});
const bits=x=>{const b=Buffer.alloc(8);b.writeDoubleBE(x);return b.toString('hex');};
for(let i=0;i<samples.length;i++){const [s,c,word,b]=cpp[i].split(' ');assert.equal(s,samples[i].seed);assert.equal(+c,samples[i].counter);assert.equal(b,native.rows[i]);assert.equal(b,bits(shortAsciiSeededRandom(s+'/'+c)()));assert(BigInt(word)>0n);}
writeFileSync(dir+'preflight.json',JSON.stringify({scope:'Actual pinned seedrandom library in installed Electron Node mode; game startup/player saves not used',samples:samples.length,bitExact:true,sourceHashes:source.hashes,seedrandomLibrarySha256:sha(library),sampleInputSha256:sha(sampleText),sampleOutputSha256:sha(cpp.join('\n')),engine:native.versions,compilerSourceSha256:sha(readFileSync(dir+'scan.cpp')),arc4HeaderSha256:sha(readFileSync(dir+'arc4-short.hpp'))},null,2)+'\n');
console.log('Exact pinned-engine/independent JS/C++ agreement on '+samples.length+' first outputs.');
