import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { compileJavaScript, compilePinnedGameAst, numberLiteralBits, AST_SCHEMA } from '../model/javascript-ast.mjs';
import { hasGameSource, loadGameSource, SOURCE_HASHES } from '../model/game-source.mjs';

const skip = !hasGameSource() && 'Set COOKIE_CLICKER_SOURCE to the pinned Steam 2.053 src directory';
const hash = text => createHash('sha256').update(text).digest('hex');
let compiled;
const gameAst = () => compiled ||= compilePinnedGameAst();

function childReferences(node) {
  const declarationRefs = ds => ds.flatMap(d => d.value === null ? [] : [d.value]);
  const optional = value => value === null ? [] : [value];
  if (node.kind === 'program') return node.body;
  if (node.kind === 'expr') switch (node.tag) {
    case 'identifier': case 'this': case 'literal': case 'regexp': return [];
    case 'array': return node.elements.filter(x => x !== null);
    case 'object': return node.properties.map(p => p.value);
    case 'function': return node.body;
    case 'sequence': return node.expressions;
    case 'unary': case 'update': return [node.argument];
    case 'binary': case 'logical': case 'assignment': return [node.left, node.right];
    case 'conditional': return [node.test, node.consequent, node.alternate];
    case 'member': return [node.object, node.property];
    case 'call': case 'construct': return [node.callee, ...node.arguments];
  }
  if (node.kind === 'stmt') switch (node.tag) {
    case 'empty': case 'break': case 'continue': return [];
    case 'expression': return [node.expression];
    case 'block': case 'functionDeclaration': return node.body;
    case 'variable': return declarationRefs(node.declarations);
    case 'ifThenElse': return [node.test, node.consequent, ...optional(node.alternate)];
    case 'while': case 'doWhile': return [node.test, node.body];
    case 'forLoop': return [...(node.initial === null ? [] : node.initial.kind === 'expression' ? [node.initial.value] : declarationRefs(node.initial.declarations)), ...optional(node.test), ...optional(node.update), node.body];
    case 'forIn': return [...(node.binding.kind === 'reference' ? [node.binding.value] : []), node.object, node.body];
    case 'return': return optional(node.value);
    case 'throw': return [node.value];
    case 'labeled': return [node.body];
    case 'tryCatchFinally': return [node.body, ...(node.handler ? [node.handler.body] : []), ...optional(node.finalizer)];
  }
  assert.fail(`Unexpected closed AST constructor ${node.kind}/${node.tag}`);
}

test('numeric literals retain source spelling and exact binary64 bits without JSON precision loss', () => {
  const ast = compileJavaScript('var a=0,b=1e309,c=0x10,d=9007199254740993,e=-0;');
  const numbers = ast.nodes.filter(n => n.literalKind === 'number');
  assert.deepEqual(numbers.map(n => n.raw), ['0', '1e309', '0x10', '9007199254740993', '0']);
  assert.deepEqual(numbers.map(n => n.bits), [0, Infinity, 16, 9007199254740992, 0].map(numberLiteralBits));
  assert(numbers.every(n => typeof n.bits === 'string' && BigInt(n.bits) <= 0xffffffffffffffffn));
  const minusZero = ast.nodes.find(n => n.tag === 'unary' && n.operator === 'minus');
  assert.equal(ast.nodes[minusZero.argument].bits, '0');
  assert.deepEqual(JSON.parse(JSON.stringify(ast)).nodes, ast.nodes);
});

test('UTF16 strings, property kinds/order, array holes and computed references remain explicit', () => {
  const ast = compileJavaScript('var x={a:1,a:2,get p(){return "\\ud800";},set p(v){this.q=v;},"😀":3,4:5};var holes=[,undefined,,];obj()[key()]+=rhs();');
  const object = ast.nodes.find(n => n.tag === 'object');
  assert.deepEqual(object.properties.map(p => p.kind), ['init', 'init', 'get', 'set', 'init', 'init']);
  assert.deepEqual(object.properties.slice(0, 2).map(p => p.key.name), ['a', 'a']);
  assert.deepEqual(object.properties[4].key.units, [0xd83d, 0xde00]);
  assert.equal(object.properties[5].key.bits, numberLiteralBits(4));
  assert.deepEqual(ast.nodes.find(n => n.literalKind === 'string').units, [0xd800]);
  const array = ast.nodes.find(n => n.tag === 'array');
  assert.equal(array.elements.length, 3);
  assert.equal(array.elements[0], null); assert.equal(array.elements[2], null);
  assert.equal(ast.nodes[array.elements[1]].name, 'undefined');
  const assign = ast.nodes.find(n => n.tag === 'assignment' && n.operator === 'add');
  const member = ast.nodes[assign.left];
  assert.equal(member.computed, true);
  assert.equal(ast.nodes[ast.nodes[member.object].callee].name, 'obj');
  assert.equal(ast.nodes[ast.nodes[member.property].callee].name, 'key');
  assert.equal(ast.nodes[ast.nodes[assign.right].callee].name, 'rhs');
  assert(member.object < member.property && member.property < assign.right);
});

test('function declarations, closure bodies and inherited strictness preserve directive prologues', () => {
  const text = 'function a(){"use strict";return function b(x){return x;};}function c(){"use\\x20strict";return 1;}';
  const ast = compileJavaScript(text);
  assert.deepEqual(Object.fromEntries(ast.functions.map(f => [f.name, f.strict])), { b: true, a: true, c: false });
  const a = ast.nodes.find(n => n.tag === 'functionDeclaration' && n.name === 'a');
  assert.equal(ast.nodes[a.body[0]].directive, 'use strict');
  for (const fn of ast.functions) assert.match(text.slice(fn.start, fn.end), /^function/);
  const inherited = compileJavaScript('function f(){return this;}', { inheritedStrict: true });
  assert.equal(inherited.functions[0].strict, true);
  assert.equal(inherited.nodes.at(-1).strict, true);
  assert.throws(() => compileJavaScript('var x=010;', { inheritedStrict: true }), /Unsupported JavaScript syntax/);
});

test('function source text preserves comments, whitespace and complete accessor spelling', () => {
  const declaration='function /*😀*/ named ( x ) { return x; }';
  const expression='function (y){\r\n/* c */return y;}';
  const getter='get /*before key*/ "x" () { return 1; }';
  const setter='set x(v){this.y=v;}';
  const ast=compileJavaScript(`${declaration}\nvar f=(${expression}),o={${getter},${setter}};`);
  assert.equal(ast.schemaVersion,2);
  const spelling=node=>String.fromCharCode(...node.sourceText);
  assert.equal(spelling(ast.nodes.find(node=>node.tag==='functionDeclaration')),declaration);
  const object=ast.nodes.find(node=>node.tag==='object');
  assert.deepEqual(object.properties.map(property=>spelling(ast.nodes[property.value])),[getter,setter]);
  assert(ast.nodes.some(node=>node.tag==='function' && spelling(node)===expression));
});

test('loop labels, abrupt control flow and try-finally stay typed rather than being replaced by callback results', () => {
  const ast = compileJavaScript('function f(o){outer:for(var k in o){try{if(o[k])continue outer;throw k;}catch(e){return e;}finally{o.done=1;}}for(var i=0;i<3;i++){if(i===2)break;}do{i--;}while(i>0);return (1,2);}');
  const tags = new Set(ast.nodes.map(n => n.tag));
  for (const tag of ['labeled', 'forIn', 'tryCatchFinally', 'continue', 'throw', 'return', 'forLoop', 'break', 'doWhile', 'sequence']) assert(tags.has(tag), tag);
  assert.equal(ast.nodes.find(n => n.tag === 'continue').label, 'outer');
  assert.equal(ast.nodes.find(n => n.tag === 'tryCatchFinally').handler.name, 'e');
  for (const node of ast.nodes) for (const ref of childReferences(node)) assert(ref < node.id);
});

test('unsupported syntax and operators fail explicitly instead of producing opaque interpreter nodes', () => {
  for (const source of ['let x=1;', 'var f=x=>x;', 'var x=2**3;', 'with(x){}', 'switch(x){case 1:break;}', 'debugger;', 'for(var k=0 in x){}']) {
    assert.throws(() => compileJavaScript(source), /Unsupported JavaScript syntax/);
  }
  assert.throws(() => compileJavaScript('return 1;'), /Unsupported JavaScript syntax/);
  assert.equal(compileJavaScript('return 1;', { kind: 'html-handler' }).nodes.at(-1).kind, 'program');
});

test('all eight pinned files compile to ordered typed ASTs with complete source function bodies', { skip }, () => {
  const ast = gameAst(); const source = loadGameSource();
  assert.equal(ast.schema, AST_SCHEMA); assert.deepEqual(ast.sourceHashes, SOURCE_HASHES);
  assert.equal(ast.coverage.pinnedFiles, 8); assert.equal(ast.coverage.sourceScripts, 7);
  assert.equal(ast.nodes.length, 153252); assert.equal(ast.functions.length, 1027);
  assert.equal(ast.units.length, 40);
  assert.equal(ast.inventory.nodeTypes.FunctionDeclaration, 37);
  assert.equal(ast.inventory.nodeTypes.FunctionExpression, 990);
  assert.equal(ast.sourceCorrespondenceVerified, false); assert.equal(ast.javascriptSemanticsVerified, false);
  for (const node of ast.nodes) {
    assert.equal(ast.nodes[node.id], node);
    for (const ref of childReferences(node)) {
      assert(Number.isSafeInteger(ref) && ref >= 0 && ref < node.id);
      assert.equal(ast.nodes[ref].source.unit, node.source.unit);
    }
    assert(node.source.start >= 0 && node.source.end <= ast.units[node.source.unit].lengthUtf16);
  }
  for (const unit of ast.units.filter(u => u.origin.kind === 'pinned-file')) {
    assert.equal(unit.textSha256, hash(source.sources[unit.name]));
    assert.equal(unit.lengthUtf16, source.sources[unit.name].length);
    for (const fn of ast.functions.filter(f => f.unit === unit.id)) {
      assert.match(source.sources[unit.name].slice(fn.start, fn.end), /^function/);
      assert.equal(ast.nodes[fn.node].strict, fn.strict);
      assert.deepEqual(ast.nodes[fn.node].sourceText,
        Array.from({length:fn.end-fn.start},(_,index)=>source.sources[unit.name].charCodeAt(fn.start+index)));
    }
  }
});

test('page script order and literal handlers are compiled while dynamic fragments stay explicit', { skip }, () => {
  const ast = gameAst(); const source = loadGameSource();
  assert.deepEqual(ast.pageScripts.map(s => s.kind), ['external-host-script', 'pinned-script', 'inline-script', 'pinned-script', 'inline-script', 'inline-script']);
  assert.equal(ast.pageScripts[0].src, '../steam/steam.js');
  assert.equal(ast.units[ast.pageScripts[1].unit].name, 'base64.js');
  assert.equal(ast.units[ast.pageScripts[3].unit].name, 'main.js');
  for (const script of ast.pageScripts.filter(s => s.kind === 'inline-script')) {
    const unit = ast.units[script.unit];
    assert.equal(unit.textSha256, hash(source.sources['index.html'].slice(unit.origin.start, unit.origin.end)));
  }
  assert.equal(ast.pageHandlers.length, 4);
  assert.equal(ast.generatedHandlers.filter(h => h.status === 'compiled').length, 26);
  assert.equal(ast.generatedHandlers.filter(h => h.status === 'fragment').length, 15);
  const template = ast.generatedHandlers.find(h => h.status === 'template');
  assert.equal(template.text, 'Game.prefs.showBackupWarning=0;==CLOSETHIS()==');
  assert.equal(template.unit, null); assert.match(template.parseError, /Unexpected token/);
  const commentedCandidate = ast.generatedHandlers.find(h => /pressMusicShuffle/.test(h.text));
  assert.equal(commentedCandidate.status, 'compiled');
  assert.match(commentedCandidate.activation, /Requires runtime HTML parsing/);
  assert.equal(ast.hostRequirements.dynamicCode.length, 1);
  assert.equal(ast.hostRequirements.dynamicCode[0].operation, 'Function');
  assert.equal(ast.hostRequirements.dynamicCode[0].source.line, 489);
  assert.equal(ast.hostRequirements.regexLiterals.length, 23);
});

test('compiler CLI writes the full source artifact without reading or producing a game save', { skip }, () => {
  const directory = mkdtempSync(join(tmpdir(), 'cookie-game-ast-'));
  try {
    const output = join(directory, 'ast.json');
    const run = spawnSync(process.execPath, ['tools/compile-game-ast.mjs', '--output', output], { cwd: new URL('..', import.meta.url), encoding: 'utf8', timeout: 60000 });
    assert.equal(run.status, 0, run.stderr || run.error?.message);
    const report = JSON.parse(run.stdout); const ast = JSON.parse(readFileSync(output, 'utf8'));
    assert.equal(report.nodes, ast.nodes.length); assert.equal(report.units, ast.units.length);
    assert.deepEqual(ast.sourceHashes, SOURCE_HASHES);
    assert.equal(report.javascriptSemanticsVerified, false);
    assert.equal(Object.hasOwn(ast, 'save'), false); assert.equal(Object.hasOwn(ast, 'randomTape'), false);
  } finally { rmSync(directory, { recursive: true, force: true }); }
});
