/** Exact pinned ARC4 constructor and generator fixtures.
 * The finite comparisons do not replace the remaining source-composition proofs. */
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeEngine} from '../model/native-engine.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),source=loadGameSource().sources['main.js'],ast=acorn.parse(source,{ecmaVersion:5});
const library=ast.body.find(n=>n.type==='ExpressionStatement'&&source.slice(n.start,n.end).includes('c.seedrandom=function'));
assert(library);const found=[];
function walk(n){if(!n||typeof n.type!=='string')return;if(n.type==='FunctionDeclaration'&&n.id.name==='k')found.push(n);for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(walk);else if(v&&typeof v==='object')walk(v);}}
walk(library);assert.equal(found.length,1);const constructor=source.slice(found[0].start,found[0].end);
assert.equal(createHash('sha256').update(constructor).digest('hex'),'d00db4ed15c1bd645b4ac34b38e508046814ab0124db34b44fef340fd012d838');
const keys=[[],[0],[1],[255],[1,2],[1,2,3],[255,0,127,128],Array(255).fill(0),Array(256).fill(0),Array(256).fill(255),Array.from({length:255},(_,i)=>i),Array.from({length:256},(_,i)=>i),Array.from({length:256},(_,i)=>255-i)];
const cases=keys.map((key,index)=>({name:'native ARC4 key '+index+' length '+key.length,source:`var d=256,j=255;${constructor};var key=${JSON.stringify(key)},q=new k(key),out=[key.join(','),q.i,q.j,q.S.join(',')];var lengths=[0,1,6,1,6,256,1,6];for(var r=0;r<lengths.length;r++){out.push(q.g(lengths[r]),q.i,q.j,q.S.join(','));}out.join('|');`,standardLibrary:true,fuel:3000000}));
const expected=runNativeEngine(`const fs=require('fs'),vm=require('vm');process.stdout.write(JSON.stringify(JSON.parse(fs.readFileSync(0,'utf8')).map(c=>{const s=vm.runInNewContext(c.source);return Array.from({length:s.length},(_,i)=>s.charCodeAt(i));})));`,cases);
const requests=cases.map(c=>({...c,ast:compileJavaScript(c.source,{name:c.name})}));
const p=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const actual=JSON.parse(p.stdout);
for(let n=0;n<cases.length;n++){assert.equal(actual[n].status,'complete',cases[n].name+':'+JSON.stringify(actual[n]));assert.deepEqual(actual[n].value,{type:'string',units:expected[n]},cases[n].name);}
console.log(JSON.stringify({arc4SourceCases:cases.length,nativeConstructorComparisons:cases.length,nativeGeneratorCalls:cases.length*8,sourceCoreConstructorProofComplete:true,fullRuntimeRefinementComplete:false}));
