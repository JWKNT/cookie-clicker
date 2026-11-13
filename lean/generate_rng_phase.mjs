/** Source-to-control-flow projection. This is an audited extractor, not a
 * verified JavaScript parser or compiler. Unknown calls have BOTH phase outputs.
 * The checked Lean analyzer, rather than this file, supplies the flow theorem.
 */
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { loadGameSource } from '../model/game-source.mjs';
import { buildRngPhaseInventory } from './rng-phase-audit.mjs';
const { parse } = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url))('acorn');
const functionNode = n => /^(FunctionExpression|FunctionDeclaration|ArrowFunctionExpression)$/.test(n?.type);
const children = n => Object.entries(n).filter(([k]) => k !== 'loc').flatMap(([,v]) =>
  Array.isArray(v) ? v.filter(x => x?.type) : v?.type ? [v] : []);
const symbol = n => !n ? '' : n.type === 'Identifier' ? n.name : n.type === 'ThisExpression' ? 'this' :
  n.type === 'Literal' ? String(n.value) : n.type === 'MemberExpression' ? `${symbol(n.object)}.${symbol(n.property)}` : '';
const skip = ['effect', 'identity'];
const seq = list => {
  const useful = list.filter(x => JSON.stringify(x) !== JSON.stringify(skip));
  return useful.length ? useful.reduce((a,b) => ['seq',a,b]) : skip;
};
const branch = (a,b) => JSON.stringify(a) === JSON.stringify(b) ? a : ['branch',a,b];
const source = loadGameSource();
const inventory = buildRngPhaseInventory();
const functions = new Map();
for (const [file,text] of Object.entries(source.sources)) {
  if (!file.endsWith('.js')) continue;
  const ast = parse(text,{ecmaVersion:'latest',locations:true});
  const walk = (n,parent) => {
    if (functionNode(n)) {
      const name = parent?.type === 'AssignmentExpression' ? symbol(parent.left) :
        parent?.type === 'VariableDeclarator' ? symbol(parent.id) : n.id?.name || '<anonymous>';
      functions.set(`${file}:${n.loc.start.line}`, {name,node:n,text,file});
    }
    for(const child of children(n)) walk(child,n);
  };
  walk(ast,null);
}

// These source helper bodies contain no dynamic callback dispatch. They are
// inlined as invocations, so their returns do not return from the caller.
const helpers = {
  choose: ['main.js',17],
  randomFloor: ['main.js',54],
  shuffle: ['main.js',56],
  'Game.Has': ['main.js',9697],
  'Game.HasUnlocked': ['main.js',9703],
  'Game.auraMult': ['main.js',14873],
  'Game.getVeilDefense': ['main.js',11351],
};
const helperNames = new Map(Object.keys(helpers).map((name,i) => [name,`helper${i}`]));
const nativeLeaves = new Set(['Math.random','Math.floor','Math.ceil','Math.min','Math.max','Date.now']);
const records = [];

export function extractPhase(fn, text, {local=false, excludeYouTooltip=true, helperMap=helperNames}={}) {
  const unresolved = new Set(), usedHelpers = new Set(), leaves = new Set();
  // A fresh array literal establishes the local `types.push` receiver used by
  // computeLumpType. No suffix-wide method-name assumption is made.
  const freshArrays = new Set();
  const collectArrays = n => {
    if (functionNode(n)) return;
    if (n.type==='VariableDeclarator' && n.id.type==='Identifier' && n.init?.type==='ArrayExpression') freshArrays.add(n.id.name);
    for(const child of children(n)) collectArrays(child);
  };
  collectArrays(fn.body);
  const invalidateArrays = n => {
    if (functionNode(n)) return;
    if (n.type==='AssignmentExpression' || n.type==='UpdateExpression') {
      const target=n.type==='AssignmentExpression'?n.left:n.argument;
      if (target.type==='Identifier') freshArrays.delete(target.name);
      if (target.type==='MemberExpression' && (target.computed || symbol(target.property)==='push')) freshArrays.delete(symbol(target.object));
    }
    for(const child of children(n)) invalidateArrays(child);
  };
  invalidateArrays(fn.body);
  const callEffect = n => {
    const name=symbol(n.callee);
    if (helperMap.has(name)) { usedHelpers.add(name); return ['invoke',helperMap.get(name)]; }
    if (nativeLeaves.has(name) || n.type==='NewExpression' && name==='Date'
        || n.callee?.type==='MemberExpression' && !n.callee.computed
          && symbol(n.callee.property)==='push' && freshArrays.has(symbol(n.callee.object))) {
      leaves.add(name); return skip;
    }
    unresolved.add(name || '<dynamic>');
    return ['effect',local?'identity':'unknown'];
  };
  const expression = n => {
    if (!n || functionNode(n)) return skip;
    if ((n.type==='AssignmentExpression' || n.type==='UpdateExpression')
        && /^Math(?:\.|$)/.test(symbol(n.left || n.argument))) {
      throw new Error(`Unreviewed Math write at ${n.loc?.start.line}`);
    }
    if(n.type==='ConditionalExpression') return seq([expression(n.test),branch(expression(n.consequent),expression(n.alternate))]);
    if(n.type==='LogicalExpression') return seq([expression(n.left),branch(skip,expression(n.right))]);
    if(n.type==='CallExpression' && symbol(n.callee)==='Math.seedrandom') return seq([
      ...n.arguments.map(expression),['effect',n.arguments.length?'seed':'reset']]);
    if(n.type==='CallExpression' || n.type==='NewExpression') return seq([
      expression(n.callee),...n.arguments.map(expression),callEffect(n)]);
    return seq(children(n).map(expression));
  };
  const statement = n => {
    if(!n)return skip;
    switch(n.type) {
      case 'BlockStatement':return seq(n.body.map(statement));
      case 'ExpressionStatement':return expression(n.expression);
      case 'VariableDeclaration':return seq(n.declarations.map(d=>expression(d.init)));
      case 'ReturnStatement':return seq([expression(n.argument),['ret']]);
      case 'IfStatement': {
        const excluded=excludeYouTooltip && text.slice(n.test.start,n.test.end).replace(/\s/g,'')==="selected==i&&this.name=='You'";
        return seq([expression(n.test), excluded?statement(n.alternate):branch(statement(n.consequent),statement(n.alternate))]);
      }
      case 'WhileStatement':return seq([expression(n.test),['loop',seq([statement(n.body),expression(n.test)])]]);
      case 'ForStatement':return seq([
        n.init?.type==='VariableDeclaration'?statement(n.init):expression(n.init),expression(n.test),
        ['loop',seq([statement(n.body),expression(n.update),expression(n.test)])]]);
      case 'ForInStatement':case 'ForOfStatement':return seq([expression(n.right),['loop',statement(n.body)]]);
      case 'FunctionDeclaration':case 'EmptyStatement':return skip;
      default:throw new Error(`Unsupported phase statement ${n.type} at ${n.loc?.start.line}`);
    }
  };
  const code=statement(fn.body);
  return {code,unresolved:[...unresolved].sort(),helpers:[...usedHelpers].sort(),nativeLeaves:[...leaves].sort()};
}

const print = code => {
  const [kind,a,b]=code;
  if(kind==='ret')return '.ret';
  if(kind==='effect')return `(.effect ${a})`;
  if(kind==='invoke')return `(.invoke ${a})`;
  if(kind==='loop')return `(.loop ${print(a)})`;
  return `(.${kind} ${print(a)} ${print(b)})`;
};
const chunks=[`import CookieClicker.RngPhase

/-! Generated from the pinned source by generate_rng_phase.mjs.
The extractor and host-leaf classifications are separate trust obligations.
Unknown callees remain arbitrary phase effects in the conservative programs.
No theorem below asserts whole JavaScript semantics or exception safety.
-/
namespace CookieClicker.FullGame.NativeRngPhase
open RngPhase
`];
const record=(entry,projected,mode)=>records.push({name:entry.name,file:entry.file,line:entry.node.loc.start.line,
  sourceSha256:createHash('sha256').update(entry.text.slice(entry.node.start,entry.node.end)).digest('hex'),mode,...projected});
for(const [name,[file,line]] of Object.entries(helpers)) {
  const entry=functions.get(`${file}:${line}`);assert.equal(entry?.name,name);
  const projected=extractPhase(entry.node,entry.text);
  assert.deepEqual(projected.unresolved,[],`Helper ${name} gained an unresolved call`);
  assert(!projected.helpers.includes(name),'Recursive helper needs a separate proof');
  const id=helperNames.get(name);
  chunks.push(`def ${id} : Code := ${print(projected.code)}\n`);
  chunks.push(`theorem ${id}_preserves : analyze (.invoke ${id}) = ⟨identity, zero⟩ := by decide +kernel\n`);
  record(entry,projected,'source-helper');
}
for(const [i,callback] of inventory.callbacks.entries()) {
  const entry=functions.get(`${callback.file}:${callback.line}`);assert.equal(entry?.name,callback.name);
  for(const local of [true,false]) {
    const projected=extractPhase(entry.node,entry.text,{local});
    const id=`${local?'local':'conservative'}Callback${i}`;
    chunks.push(`def ${id} : Code := ${print(projected.code)}\n`);
    record(entry,projected,local?'local-call-premises':'conservative-calls');
    if(local || projected.unresolved.length===0) {
      chunks.push(`theorem ${id}_checked : restoresFree ${id} = true := by decide +kernel\n`);
      chunks.push(`theorem ${id}_restores (exit : Exit) (phase : Phase)
    (execution : Executes ${id} free exit phase) : phase = free :=
  restores_free_sound ${id} ${id}_checked exit phase execution\n`);
    }
  }
  if(callback.name==='this.draw') {
    const unrestricted=extractPhase(entry.node,entry.text,{local:true,excludeYouTooltip:false});
    chunks.push(`def unrestrictedTooltip : Code := ${print(unrestricted.code)}\n`);
    chunks.push('theorem unrestricted_tooltip_not_certified : restoresFree unrestrictedTooltip = false := by decide +kernel\n');
    record(entry,unrestricted,'forbidden-tooltip-countercase');
  }
}
chunks.push('end CookieClicker.FullGame.NativeRngPhase\n');
const generated=chunks.join('\n');
const report=JSON.stringify({schemaVersion:1,sourceHashes:source.hashes,
  scope:'Source-derived phase control flow. Lean checks the analyzer and emitted programs; Acorn extraction, host operations, native object integrity, exceptions and unexpanded dynamic calls remain explicit boundaries.',
  records},null,2)+'\n';
for(const [relative,bytes] of [['CookieClicker/NativeRngPhase.lean',generated],['rng-phase-programs.json',report]]) {
  const path=new URL(relative,import.meta.url);
  if(process.argv.includes('--write'))writeFileSync(path,bytes);
  else assert.equal(readFileSync(path,'utf8'),bytes,`${relative} is stale; review before --write`);
}
console.log(`Checked ${Object.keys(helpers).length} source helpers and ${inventory.callbacks.length} callback projections.`);
