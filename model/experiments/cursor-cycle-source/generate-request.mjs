/** Rebuild the archived diagnostic input from pinned installed source. No game execution. */
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { gunzipSync } from 'node:zlib';
const here=dirname(fileURLToPath(import.meta.url));
const [repository,output=resolve(here,'request.json')]=process.argv.slice(2);
if(!repository) throw new Error('Usage: node generate-request.mjs REPOSITORY [OUTPUT]');
const root=resolve(repository);
const {loadGameSource}=await import(pathToFileURL(resolve(root,'model/game-source.mjs')));
const {compileJavaScript}=await import(pathToFileURL(resolve(root,'model/javascript-ast.mjs')));
const game=loadGameSource();
const specs=JSON.parse(readFileSync(resolve(here,'source-units.json'),'utf8'));
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const compiled=new Map();
for(const spec of specs){
 const whole=spec.file ? game.sources[spec.file] : spec.text;
 if(typeof whole!=='string') throw new Error(`Missing source ${spec.name}`);
 const text=spec.start===undefined?whole:whole.slice(spec.start,spec.end);
 if(text.length!==spec.lengthUtf16||sha(text)!==spec.sha256) throw new Error(`Source differs: ${spec.name}`);
 compiled.set(spec.name,compileJavaScript(text,{name:spec.name,unboundedClock:true}));
}
const request=JSON.parse(readFileSync(resolve(here,'request-template.json'),'utf8'));
for(const r of request){
 r.ast=compiled.get(r.ast.compile);
 r.followupPrograms=r.followupPrograms.map(a=>compiled.get(a.compile));
 for(const s of r.sourceScripts)s.ast=compiled.get(s.ast.compile);
 for(const s of r.postTaskStages)s.ast=compiled.get(s.ast.compile);
}
// The accepted request was serialized with Python ensure_ascii=True.
const bytes=Buffer.from(JSON.stringify(request).replace(/[\u007f-\uffff]/g,character=>'\\u'+character.charCodeAt(0).toString(16).padStart(4,'0')));
const archived=gunzipSync(readFileSync(resolve(here,'request.json.gz')));
if(!bytes.equals(archived)){
 const firstDifference=(a,b,path='$')=>{
  if(JSON.stringify(a)===JSON.stringify(b))return null;
  if(a&&b&&typeof a==='object'&&typeof b==='object'){
   for(const k of new Set([...Object.keys(a),...Object.keys(b)])){
    const diff=firstDifference(a[k],b[k],`${path}.${k}`);if(diff)return diff;
   }
   return {path,reason:'object-key ordering differs'};
  }
  return {path,generated:a,archived:b};
 };
 throw new Error(`Generated AST input differs from archive: ${sha(bytes)} versus ${sha(archived)}. ${JSON.stringify(firstDifference(request,JSON.parse(archived)))}. Do not relabel this as the accepted run.`);
}
writeFileSync(output,bytes);
console.log(JSON.stringify({status:'exact-request-match',sha256:sha(bytes),bytes:bytes.length,output,gameHashes:game.hashes}));
