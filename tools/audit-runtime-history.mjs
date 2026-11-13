import {createRequire} from 'node:module';
import {readFileSync,writeFileSync} from 'node:fs';
import assert from 'node:assert/strict';
import {loadGameSource} from '../model/game-source.mjs';
const {parse}=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url))('acorn');
const game=loadGameSource(),writes=[],aliases=[];
const path=n=>n?.type==='Identifier'?[n.name]:n?.type==='MemberExpression'?[...(path(n.object)||[]),n.computed?(n.property.type==='Literal'?n.property.value:'*'):n.property.name]:null;
function match(p){return p?.[0]==='Game'&&['Upgrades','UpgradesById','UpgradesN'].includes(p[1]);}
for(const [file,source]of Object.entries(game.sources)){
 if(!file.endsWith('.js'))continue;
 function walk(n){
  if(!n||typeof n.type!=='string')return;
  const lhs=n.type==='AssignmentExpression'?n.left:n.type==='UpdateExpression'?n.argument:n.type==='UnaryExpression'&&n.operator==='delete'?n.argument:null;
  const p=path(lhs);
  if(match(p)&&(p.length<=3||['name','id'].includes(p.at(-1))))writes.push({file,line:n.loc.start.line,path:p,source:source.slice(n.start,n.end)});
  if(n.type==='VariableDeclarator'&&match(path(n.init))&&path(n.init).length===2)aliases.push({file,line:n.loc.start.line,source:source.slice(n.start,n.end)});
  for(const v of Object.values(n)){if(Array.isArray(v))v.forEach(walk);else if(v&&typeof v==='object')walk(v);}
 }
 walk(parse(source,{ecmaVersion:5,locations:true}));
}
const report={sourceHashes:game.hashes,writes,aliases,scope:'Direct source write and table-alias audit, not a whole-program alias or dynamic-code proof. The optimization relies on the pinned vanilla catalogue-entry/name identity contract; custom injected replacement of one entry without the native constructor is outside this contract.'};
const target=new URL('../model/runtime-history-catalogue-audit.json',import.meta.url);
if(process.argv.includes('--check'))assert.deepEqual(JSON.parse(readFileSync(target,'utf8')),report);
else writeFileSync(target,JSON.stringify(report,null,2)+'\n');
console.log(`Runtime history catalogue audit: ${writes.length} direct writes, ${aliases.length} direct table aliases.`);
