import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { resolve, join } from 'node:path';
import { pathToFileURL, fileURLToPath } from 'node:url';
const argv=process.argv.slice(2), repo=resolve(argv.includes('--repo')?argv[argv.indexOf('--repo')+1]:fileURLToPath(new URL('../',import.meta.url)));
const output=resolve(argv.includes('--output')?argv[argv.indexOf('--output')+1]:join(repo,'lean/CookieClicker/JavaScriptBuildingConstructorSyntax.lean'));
const {compileJavaScript}=await import(pathToFileURL(join(repo,'model/javascript-ast.mjs')));
const {loadGameSource}=await import(pathToFileURL(join(repo,'model/game-source.mjs')));
const require=createRequire(pathToFileURL(join(repo,'source/cookie-monster-plus/package.json'))),acorn=require('acorn');
const source=loadGameSource(),main=source.sources['main.js'];
const sha256=value=>createHash('sha256').update(value).digest('hex');
const start=main.indexOf('Game.Object=function');
const fn=acorn.parseExpressionAt(main,start+'Game.Object='.length,{ecmaVersion:5});
const assignment=(n,key)=>n.type==='ExpressionStatement'&&n.expression.type==='AssignmentExpression'&&
 n.expression.left.type==='MemberExpression'&&n.expression.left.object.type==='ThisExpression'&&n.expression.left.property.name===key;
const base=fn.body.body.find(n=>assignment(n,'baseCps'));
const nAssignment=fn.body.body.find(n=>assignment(n,'n'));
const branch=fn.body.body.find(n=>n.type==='IfStatement'&&n.test.type==='BinaryExpression'&&
 n.test.left.type==='MemberExpression'&&n.test.left.object.type==='ThisExpression'&&n.test.left.property.name==='n');
assert.equal(branch.test.operator,'!=');assert.equal(branch.test.right.value,0);
assert.equal(branch.alternate,null);assert.equal(branch.consequent.type,'BlockStatement');
const prefix=branch.consequent.body.slice(0,3);
assert(assignment(prefix[0],'baseCps'));assert.equal(prefix[1].type,'VariableDeclaration');
assert.equal(prefix[1].declarations[0].id.name,'digits');assert(assignment(prefix[2],'baseCps'));
const definitions=[];
for(const [name,node] of [['baseFromCallback',base],['idToN',nAssignment],['numericBranch',branch]]){
 const text=main.slice(node.start,node.end),ast=compileJavaScript(text,{name:'Game.Object.'+name});
 const root=ast.nodes[ast.units[0].root];
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
    if (n.tag === 'construct') return `(.construct ${render(n.callee)} ${list(n.arguments)})`;
    if (n.tag === 'forIn') {
      const binding = n.binding.kind === 'variable' ? `(.variable ${JSON.stringify(n.binding.name)})` : `(.reference ${render(n.binding.value)})`;
      return `(.forIn ${binding} ${render(n.object)} ${render(n.body)})`;
    }
    if (n.tag === 'call') return `(.call ${render(n.callee)} ${list(n.arguments)})`;
    if (n.tag === 'array') return `(.array [${n.elements.map(option).join(', ')}])`;
    if (n.tag === 'expression') return `(.expression ${render(n.expression)})`;
    if (n.tag === 'block') return `(.block ${list(n.body)})`;
    if (n.tag === 'variable') return `(.variable ${declarations(n.declarations)})`;
    if (n.tag === 'return') return `(.return ${option(n.value)})`;
    if (n.tag === 'ifThenElse') return `(.ifThenElse ${render(n.test)} ${render(n.consequent)} ${option(n.alternate)})`;
    if (n.tag === 'while') return `(.while ${render(n.test)} ${render(n.body)})`;
    if (n.tag === 'forLoop') {
      const initial = n.initial === null ? 'none' : n.initial.kind === 'variables' ? `(some (.variables ${declarations(n.initial.declarations)}))` : `(some (.expression ${render(n.initial.value)}))`;
      return `(.forLoop ${initial} ${option(n.test)} ${option(n.update)} ${render(n.body)})`;
    }
    throw new Error(`Unsupported production source node ${n.tag}`);
  };

 definitions.push(`-- source SHA-256: ${sha256(text)}
def ${name} : Stmt := ${render(root.body[0])}
`);
}
const result=`import CookieClicker.JavaScriptSyntax

/- Generated from the pinned complete Game.Object constructor.
main.js SHA-256: ${source.hashes['main.js']}
Constructor SHA-256: ${sha256(main.slice(fn.start,fn.end))}
The three CpS statements retain their exact source order. The price suffix is
retained in numericBranch; no assertion about constructor reachability follows
from this source extraction alone. -/
namespace CookieClicker.JavaScript.BuildingConstructorSyntax

${definitions.join('\n')}
def numericStatements : List Stmt := match numericBranch with
  | .ifThenElse _ (.block statements) _ => statements
  | _ => []
def cpsPrefix : List Stmt := numericStatements.take 3
def priceSuffix : List Stmt := numericStatements.drop 3

theorem numeric_partition : numericStatements=cpsPrefix++priceSuffix := by
  exact (List.take_append_drop 3 numericStatements).symm

end CookieClicker.JavaScript.BuildingConstructorSyntax
`;
if(argv.includes('--check'))assert.equal(readFileSync(output,'utf8'),result);else writeFileSync(output,result);
console.log(JSON.stringify({sourceSha256:source.hashes['main.js'],constructorSha256:sha256(main.slice(fn.start,fn.end)),numericStatements:branch.consequent.body.length,prefixStatements:3,prefixSource:main.slice(prefix[0].start,prefix[2].end),output,sha256:sha256(result)}));
