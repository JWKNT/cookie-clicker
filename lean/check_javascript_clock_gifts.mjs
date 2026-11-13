import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {mkdirSync,writeFileSync} from 'node:fs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
mkdirSync('/tmp/cookie-audit',{recursive:true});
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),text=loadGameSource().sources['main.js'],ast=acorn.parse(text,{ecmaVersion:5});
const helpers=[],decoders=[];
function walk(n){if(!n||typeof n.type!=='string')return;
 if(n.type==='FunctionDeclaration'&&['utf8_to_b64','b64_to_utf8'].includes(n.id.name))decoders.push(n);
 if(n.type==='VariableDeclarator'&&n.id.name==='checkCode'&&n.init?.type==='FunctionExpression'&&text.slice(n.start,n.end).includes("str[0]!=='MAIL'"))helpers.push(n);
 for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(walk);else if(v&&typeof v==='object')walk(v);}}
walk(ast);assert.equal(decoders.length,2);assert.equal(helpers.length,1);
const helper=helpers[0],prefix=decoders.map(n=>text.slice(n.start,n.end)).join('\n')+'\nvar Game={giftBoxDesigns:[[34,6]]};var ';
const suffix=';var code=utf8_to_b64("MAIL|"+(Date.now()+DELTA)+"|999|-|hello"),r=checkCode(code);r===-1?"expired":r.cookies+":"+r.message+":"+r.icon[0]+":"+r.icon[1];';
const cases=[];
for(const epoch of [1793275200000n,2n**100n,2n**1200n])for(const delta of [-172800001,-172800000,-1,0,1,172800000,172800001]){
 const source=prefix+text.slice(helper.start,helper.end)+suffix.replace('DELTA',String(delta));
 cases.push({name:'actual MAIL checkCode '+epoch+'/'+delta,epochMilliseconds:String(epoch),source,ast:compileJavaScript(source,{unboundedClock:true,clockFragments:[{file:'main.js',sourceStart:helper.start,generatedStart:prefix.length,length:helper.end-helper.start}]}),standardLibrary:true,fuel:3000000,expected:Math.abs(delta)>172800000?'expired':'999:hello:34:6'});
}
const p=spawnSync(new URL('./.lake/build/bin/jsastcheck',import.meta.url).pathname,['--execute'],{input:JSON.stringify(cases),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});if(p.error)throw p.error;assert.equal(p.status,0,p.stderr);const out=JSON.parse(p.stdout);assert.equal(out.length,cases.length);for(let i=0;i<cases.length;i++){assert.equal(out[i].status,'complete',cases[i].name+':'+JSON.stringify(out[i]));assert.deepEqual(out[i].value,{type:'string',units:Array.from(cases[i].expected,x=>x.charCodeAt(0))},cases[i].name);}
const report={passed:cases.length,actualSourceHelpers:3,sourceRefinementProved:false};writeFileSync('/tmp/cookie-audit/gift-clock-results.json',JSON.stringify({report,results:out},null,2));console.log(JSON.stringify(report));
