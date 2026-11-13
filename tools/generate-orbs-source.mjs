import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
const require=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url)),acorn=require('acorn');
const source=loadGameSource(),main=source.sources['main.js'],full=acorn.parse(main,{ecmaVersion:5});
let pop;const visit=n=>{if(!n||typeof n!=='object')return;if(n.type==='FunctionExpression'&&main.slice(n.start,n.end).includes('//select an effect')&&main.slice(n.start,n.end).startsWith('function(me)')&&main.slice(n.start,n.end).includes("if (choice=='chain cookie')"))pop=n;for(const v of Object.values(n))if(Array.isArray(v))v.forEach(visit);else if(v&&typeof v==='object')visit(v)};visit(full);assert(pop);
const body=pop.body.body,first=body.findIndex(n=>n.type==='VariableDeclaration'&&n.declarations[0].id.name==='list'),remove=body.findIndex(n=>main.slice(n.start,n.end).includes('list.splice(list.indexOf(this.last),1)'));
assert(first>=0&&remove>first);const a=body[first+1],bs=[...body.slice(first+2,remove),body[remove+1]];
const texts={initial:main.slice(a.start,a.end),appends:'{'+bs.map(n=>main.slice(n.start,n.end)).join('\n')+'}',antiRepeat:main.slice(body[remove].start,body[remove].end),selectionTail:main.slice(body[remove+2].start,body[remove+6].end)};
const definitions=[];for(const[name,text]of Object.entries(texts)){
 const ast=compileJavaScript(text,{name:'native-orbs-'+name});const render=id=>{const n=ast.nodes[id],r=render,opt=id=>id===null?'none':`(some ${r(id)})`,list=ids=>'['+ids.map(r).join(',')+']';
 if(n.tag==='identifier')return`(.identifier ${JSON.stringify(n.name)})`;if(n.tag==='this')return'.this';
 if(n.tag==='literal')return'(.literal '+(n.literalKind==='number'?`(.number ${n.bits})`:n.literalKind==='string'?`(.string [${n.units.join(',')}])`:n.literalKind==='boolean'?`(.boolean ${n.value})`:'.null')+')';
 if(n.tag==='member')return`(.member ${r(n.object)} ${r(n.property)} ${n.computed})`;
 if(['binary','logical','assignment'].includes(n.tag))return`(.${n.tag} .${n.operator} ${r(n.left)} ${r(n.right)})`;
 if(n.tag==='unary')return`(.unary .${n.operator} ${r(n.argument)})`;
 if(n.tag==='call')return`(.call ${r(n.callee)} ${list(n.arguments)})`;
 if(n.tag==='expression')return`(.expression ${r(n.expression)})`;
 if(n.tag==='block')return`(.block ${list(n.body)})`;
 if(n.tag==='ifThenElse')return`(.ifThenElse ${r(n.test)} ${r(n.consequent)} ${opt(n.alternate)})`;
 if(n.tag==='variable')return'(.variable ['+n.declarations.map(d=>`(${JSON.stringify(d.name)},${opt(d.value)})`).join(',')+'])';
 throw Error(n.tag);};
 const root=ast.nodes[ast.units[0].root];definitions.push(`-- Source fragment SHA-256: ${createHash('sha256').update(text).digest('hex')}\ndef ${name} : Stmt := .block [${root.body.map(render).join(',')}]`);
}
const result=`import CookieClicker.JavaScriptSyntax\n\n/- Generated from pinned main.js ${source.hashes['main.js']}.\nActual branch tests are retained. The list projection is separate from native\nexpression/array-operation execution; no native callback replacement is made. -/\nnamespace CookieClicker.JavaScript.OrbsSyntax\n${definitions.join('\n\n')}\nend CookieClicker.JavaScript.OrbsSyntax\n`;
const path=new URL('../lean/CookieClicker/JavaScriptOrbsSyntax.lean',import.meta.url);if(process.argv.includes('--check'))assert.equal(readFileSync(path,'utf8'),result);else writeFileSync(path,result);console.log(JSON.stringify({check:process.argv.includes('--check'),sha256:createHash('sha256').update(result).digest('hex')}));
