import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { resolve, join } from 'node:path';
import { pathToFileURL, fileURLToPath } from 'node:url';
const argv=process.argv.slice(2);
const repo=resolve(argv.includes('--repo')?argv[argv.indexOf('--repo')+1]:fileURLToPath(new URL('../',import.meta.url)));
const witnessPath=resolve(argv.includes('--witness')?argv[argv.indexOf('--witness')+1]:join(repo,'model/building-cps-witness.json'));
const {loadGameSource}=await import(pathToFileURL(join(repo,'model/game-source.mjs')));
const {inspectNativeEngine,runNativeEngine}=await import(pathToFileURL(join(repo,'model/native-engine.mjs')));
const require=createRequire(pathToFileURL(join(repo,'source/cookie-monster-plus/package.json'))),acorn=require('acorn');
const source=loadGameSource(),main=source.sources['main.js'];
const start=main.indexOf('Game.Object=function');
const fn=acorn.parseExpressionAt(main,start+'Game.Object='.length,{ecmaVersion:5});
const branch=fn.body.body.find(n=>n.type==='IfStatement'&&n.test.type==='BinaryExpression'&&
 n.test.left.type==='MemberExpression'&&n.test.left.object.type==='ThisExpression'&&n.test.left.property.name==='n');
assert.equal(branch.test.operator,'!=');assert.equal(branch.test.right.value,0);
const statements=branch.consequent.body.slice(0,3);
const prefixSource=main.slice(statements[0].start,statements[2].end);
const sha256=value=>createHash('sha256').update(value).digest('hex');
const native=inspectNativeEngine();
const result=runNativeEngine(String.raw`const fs=require('fs');const input=JSON.parse(fs.readFileSync(0,'utf8'));
const bits=value=>{const b=Buffer.alloc(8);b.writeDoubleBE(value);return BigInt('0x'+b.toString('hex')).toString();};
const run=new Function(input.prefixSource+'\nreturn {value:this.baseCps,digits:digits};');
const rows=[];for(let id=1;id<20;id++){const result=run.call({n:id,baseCps:function actualCallback(){}});
rows.push({id,nBits:bits(id),baseCps:result.value,baseCpsBits:bits(result.value),digits:result.digits,digitsBits:bits(result.digits)});}
process.stdout.write(JSON.stringify({ln10Bits:bits(Math.LN10),rows}));`,{prefixSource});
const witness={schemaVersion:1,status:'finite-native-source-prefix-comparison',
 identity:{versions:native.versions,arch:native.arch,platform:native.platform,gameEntryPointExecuted:false},
 sourceSha256:source.hashes['main.js'],constructorSha256:sha256(main.slice(fn.start,fn.end)),
 cpsPrefixSha256:sha256(prefixSource),
 scope:'The exact contiguous three-statement CpS prefix in the numeric Game.Object branch, for all nineteen numeric building indices. The remaining nine price statements are excluded from this finite check. No save or game entry point is loaded; full constructor reachability and compiled-engine refinement remain separate proof obligations.',
 ...result};
if(argv.includes('--check')){
 const leanRoot=resolve(argv.includes('--lean-root')?argv[argv.indexOf('--lean-root')+1]:join(repo,'lean'));
 const cases=readFileSync(join(leanRoot,'CookieClicker/JavaScriptBuildingCpsCases.lean'),'utf8');
 const arithmetic=readFileSync(join(leanRoot,'CookieClicker/JavaScriptBuildingCpsArithmetic.lean'),'utf8');
 for(const row of result.rows){
  const pattern=new RegExp(`def row${row.id} : Row := \\{\\s*id:=${row.id},n:=${row.nBits},cps:=${row.baseCpsBits},scale:=${row.digitsBits}`);
  assert(pattern.test(cases),`Lean row${row.id} differs from native source result`);
  assert(arithmetic.includes(`theorem source_${row.id} : output ${row.nBits}=(${row.baseCpsBits},${row.digitsBits})`),`Lean arithmetic row${row.id} differs`);
 }
 assert.deepEqual(JSON.parse(readFileSync(witnessPath,'utf8')),witness,'Building CpS native witness differs');
}else writeFileSync(witnessPath,JSON.stringify(witness,null,2)+'\n');
console.log(JSON.stringify({check:argv.includes('--check'),cases:result.rows.length,sourceSha256:witness.sourceSha256,cpsPrefixSha256:witness.cpsPrefixSha256,nativeEngine:native.versions.electron,v8:native.versions.v8}));
