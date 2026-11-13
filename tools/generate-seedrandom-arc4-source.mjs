import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url));
const acorn=require('acorn'),source=loadGameSource(),text=source.sources['main.js'];
const parsed=acorn.parse(text,{ecmaVersion:5});
const library=parsed.body.filter(n=>n.type==='ExpressionStatement'&&text.slice(n.start,n.end).includes('c.seedrandom=function'));
assert.equal(library.length,1);
const root=library[0],functions=[];
function walk(node){
  if(!node||typeof node.type!=='string')return;
  if(node.type==='FunctionDeclaration'&&node.id.name==='k')functions.push(['constructor',node]);
  if(node.type==='AssignmentExpression'&&text.slice(node.left.start,node.left.end)==='e.g')functions.push(['generator',node.right]);
  for(const value of Object.values(node)){if(Array.isArray(value))value.forEach(walk);else if(value&&typeof value==='object')walk(value);}
}
walk(root);assert.equal(functions.length,2);
const sha=s=>createHash('sha256').update(s).digest('hex'),definitions=[],rows=[];
for(const [name,node] of functions){
  const fnText=text.slice(node.start,node.end);
  const ast=compileJavaScript(`(${fnText});`,{name:`seedrandom.${name}`});
  const program=ast.nodes[ast.units[0].root],fn=ast.nodes[ast.nodes[program.body[0]].expression];
  const option = id => id === null ? 'none' : `(some ${render(id)})`;
  const declarations = ds => `[${ds.map(d => `(${JSON.stringify(d.name)}, ${option(d.value)})`).join(', ')}]`;
  const render = id => {
    const n = ast.nodes[id];
    const list = ids => `[${ids.map(render).join(', ')}]`;
    if (n.tag === 'identifier') return `(.identifier ${JSON.stringify(n.name)})`;
    if (n.tag === 'this') return '.this';
    if (n.tag === 'literal') {
      const literal = n.literalKind === 'number' ? `(.number ${n.bits})` : n.literalKind === 'boolean' ? `(.boolean ${n.value})`
        : n.literalKind === 'string' ? `(.string [${n.units.join(',')}])` : '.null';
      return `(.literal ${literal})`;
    }
    if (n.tag === 'member') return `(.member ${render(n.object)} ${render(n.property)} ${n.computed})`;
    if (['assignment', 'binary', 'logical'].includes(n.tag)) return `(.${n.tag} .${n.operator} ${render(n.left)} ${render(n.right)})`;
    if (n.tag === 'unary') return `(.unary .${n.operator} ${render(n.argument)})`;
    if (n.tag === 'update') return `(.update .${n.operator} ${render(n.argument)} ${n.isPrefix})`;
    if (n.tag === 'conditional') return `(.conditional ${render(n.test)} ${render(n.consequent)} ${render(n.alternate)})`;
    if (n.tag === 'function') return `(.function ${n.name===null?'none':`(some ${JSON.stringify(n.name)})`} [${n.parameters.map(JSON.stringify).join(',')}] ${list(n.body)} ${n.strict} ${n.sourceText===null?'none':`(some [${n.sourceText.join(',')}])`})`;
    if (n.tag === 'sequence') return `(.sequence ${list(n.expressions)})`;
    if (n.tag === 'construct') return `(.construct ${render(n.callee)} ${list(n.arguments)})`;
    if (n.tag === 'forIn') {
      const binding=n.binding.kind==='variable'?`(.variable ${JSON.stringify(n.binding.name)})`:`(.reference ${render(n.binding.value)})`;
      return `(.forIn ${binding} ${render(n.object)} ${render(n.body)})`;
    }
    if (n.tag === 'tryCatchFinally') return `(.tryCatchFinally ${render(n.body)} ${n.handler===null?'none':`(some (${JSON.stringify(n.handler.name)}, ${render(n.handler.body)}))`} ${option(n.finalizer)})`;
    if (n.tag === 'empty') return '.empty';
    if (n.tag === 'call') return `(.call ${render(n.callee)} ${list(n.arguments)})`;
    if (n.tag === 'array') return `(.array [${n.elements.map(option).join(', ')}])`;
    if (n.tag === 'expression') return `(.expression ${render(n.expression)})`;
    if (n.tag === 'block') return `(.block ${list(n.body)})`;
    if (n.tag === 'variable') return `(.variable ${declarations(n.declarations)})`;
    if (n.tag === 'return') return `(.return ${option(n.value)})`;
    if (n.tag === 'ifThenElse') return `(.ifThenElse ${render(n.test)} ${render(n.consequent)} ${option(n.alternate)})`;
    if (n.tag === 'forLoop') {
      const initial = n.initial === null ? 'none' : n.initial.kind === 'variables' ? `(some (.variables ${declarations(n.initial.declarations)}))` : `(some (.expression ${render(n.initial.value)}))`;
      return `(.forLoop ${initial} ${option(n.test)} ${option(n.update)} ${render(n.body)})`;
    }
    throw new Error(`Unsupported seedrandom source node ${n.tag}`);
  };

  definitions.push(`-- Source SHA-256: ${sha(fnText)}\ndef ${name}Body : Stmt := .block [\n  ${fn.body.map(render).join(',\n  ')}]\ndef ${name}Text : JSString := [${fn.sourceText.join(',')}]\n`);
  rows.push({name,parameters:fn.parameters,nodes:ast.nodes.length,sourceSha256:sha(fnText)});
}
const output=`import CookieClicker.JavaScriptSyntax

/- Generated by tools/generate-seedrandom-arc4-source.mjs from the pinned game.
main.js SHA-256: ${source.hashes['main.js']}
The frontend and source-byte correspondence remain separate proof obligations.
Every branch and nested source function in these helpers is retained. -/
namespace CookieClicker.JavaScript.SeedrandomArc4Syntax

${definitions.join('\n')}
end CookieClicker.JavaScript.SeedrandomArc4Syntax
`;
const path=new URL('../lean/CookieClicker/JavaScriptSeedrandomArc4Syntax.lean',import.meta.url);
if(process.argv.includes('--check'))assert.equal(readFileSync(path,'utf8'),output,'ARC4 source is stale');else writeFileSync(path,output);
console.log(JSON.stringify({check:process.argv.includes('--check'),functions:rows}));
