/** Selected-clock source annotations. This is not a proof of the JS frontend. */
import {createRequire} from 'node:module';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {loadGameSource} from './game-source.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn');
const inventory=JSON.parse(readFileSync(new URL('./clock-source-sites.json',import.meta.url)));
let cached;
const hash=text=>createHash('sha256').update(text).digest('hex');
function registry(){
 if(cached)return cached;
 const source=loadGameSource(),rows=[];
 for(const field of inventory.savedFields){
  const site=field.reader,text=source.sources[site.file];
  if(source.hashes[site.file]!==inventory.sourceHashes[site.file]||text.slice(site.start,site.end)!==site.text||hash(site.text)!==site.sha256)throw Error('Pinned clock reader changed');
  const ast=acorn.parse(site.text,{ecmaVersion:5}),calls=[];
  function visit(n){if(!n||typeof n.type!=='string')return;if(n.type==='CallExpression'&&n.callee.type==='Identifier'&&['parseInt','parseFloat'].includes(n.callee.name))calls.push(n);for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(visit);else if(v&&typeof v==='object')visit(v);}}
  visit(ast);if(calls.length!==1||calls[0].arguments.length!==1)throw Error('Clock reader is not a single one-argument native parse call');
  const call=calls[0];rows.push({file:site.file,start:site.start+call.start,end:site.start+call.end,kind:'read',integer:call.callee.name==='parseInt',field:field.field,text:text.slice(site.start+call.start,site.start+call.end)});
 }
 for(const extra of inventory.extraTypedSites.filter(row=>row.role.startsWith('MAIL gift timestamp'))){
  const site=extra.site,text=source.sources[site.file];
  if(source.hashes[site.file]!==inventory.sourceHashes[site.file]||text.slice(site.start,site.end)!==site.text||hash(site.text)!==site.sha256)throw Error('Pinned gift clock reader changed');
  const call=acorn.parse(site.text,{ecmaVersion:5}).body[0].expression;
  if(call.type!=='CallExpression'||call.callee.name!=='parseInt'||call.arguments.length!==1)throw Error('Expected one-argument gift clock parser');
  rows.push({file:site.file,start:site.start,end:site.end,kind:'read',integer:true,field:'MAIL.timestamp',text:site.text});
 }
 for(const extra of inventory.extraTypedSites.filter(row=>row.role.startsWith('zero timestamp'))){
  const site=extra.site,text=source.sources[site.file];if(text.slice(site.start,site.end)!==site.text)throw Error('Pinned zero timestamp initializer changed');
  const node=acorn.parse(site.text,{ecmaVersion:5}).body[0].expression.right;
  if(node.type!=='Literal'||node.value!==0)throw Error('Expected literal zero timestamp initializer');
  rows.push({file:site.file,start:site.start+node.start,end:site.start+node.end,kind:'zero',text:'0'});
 }
 return cached={source,rows};
}
export function clockAnnotations(text,{unboundedClock=false,clockFragments=[]}={}){
 const result=new Map();if(!unboundedClock)return result;
 const {source,rows}=registry();
 const fragments=[...clockFragments];
 for(const [file,pinned]of Object.entries(source.sources))if(file.endsWith('.js')&&hash(text)===source.hashes[file]&&text===pinned)fragments.push({file,sourceStart:0,generatedStart:0,length:text.length});
 for(const f of fragments){
  if(!Number.isSafeInteger(f.sourceStart)||!Number.isSafeInteger(f.generatedStart)||!Number.isSafeInteger(f.length)||Math.min(f.sourceStart,f.generatedStart,f.length)<0)throw Error('Invalid clock fragment bounds');
  const pinned=source.sources[f.file];if(typeof pinned!=='string'||f.sourceStart+f.length>pinned.length||f.generatedStart+f.length>text.length||pinned.slice(f.sourceStart,f.sourceStart+f.length)!==text.slice(f.generatedStart,f.generatedStart+f.length))throw Error('Clock fragment does not match pinned source');
  for(const row of rows)if(row.file===f.file&&row.start>=f.sourceStart&&row.end<=f.sourceStart+f.length){
   const start=f.generatedStart+row.start-f.sourceStart,end=f.generatedStart+row.end-f.sourceStart;
   result.set(start+':'+end,{...row,generatedStart:start,generatedEnd:end});
  }
 }
 return result;
}
