/** Finite matcher checks; --engine selects the pinned installed game engine. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compilePinnedGameAst } from '../model/javascript-ast.mjs';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';

const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index));
const cases = [];
const add = (pattern, flags, input, start = 0) => cases.push({ pattern: units(pattern), flags, input: units(input), start });
const texts = ['', 'abc', '123456789', '12,345,678', 'a\nb\r\nc', '<q>hello</q>\nend', 'abc-123_%20', 'éßΩ😀𐐀', 'x'.repeat(20), '1234567890'.repeat(10)];
const source = compilePinnedGameAst();
for (const { pattern, flags } of source.hostRequirements.regexLiterals) {
  for (const input of texts) cases.push({ pattern, flags, input: units(input), start: 0 });
}
for (const pattern of ['a*', 'a*?', '(a|ab)+', '(a(b)?)+', '(a*)*', '(a?){2}', '(a?)*', '(a)?b\\1', '(a+)\\1', '\\1(a)', '(?=(a+))a*b\\1', '(?!ab)a.', 'a{2,4}?', '^a$', '\\b\\w+\\b', '[^a-z]+', '[]', '[^]', '(a)|(b)', '(?:(a)|(b))*', '(a(b)?)+c']) {
  for (const input of ['', 'a', 'aa', 'ab', 'aba', 'aabaaa', 'ababc', ' abc ', 'é😀', 'a\n']) add(pattern, '', input);
}
for (const flags of ['', 'i', 'm', 'im', 'u', 'iu', 's', 'y', 'uy']) {
  for (const pattern of ['.', '^x$', '[a-z]+', '\\w+', '(.)\\1', '(?:😀|𐐀)+']) {
    for (const input of ['x\n', '\nx\n', 'KKkſs', 'éÉ', '😀😀', '𐐀𐐨', '\ud800x\udc00']) add(pattern, flags, input);
  }
}
for (const pattern of ["[^'\\-_0-9 \\p{L}]", '\\p{Letter}+', '\\u{1f600}+', '[\\u{10000}-\\u{10ffff}]', '\\uD83D\\uDE00']) {
  for (const input of ["Cookie's 123", 'éΩ中𐐀😀', '\ud800\udc00', '\ud800x', '😀😀']) add(pattern, 'u', input);
}
for (const [pattern, flags] of [['(', ''], ['a{3,2}', ''], ['*a', ''], ['{2}', ''], ['[z-a]', ''], ['a', 'gg'], ['\\2(a)', 'u'], ['\\z', 'u']]) add(pattern, flags, 'a');
for (const flags of ['g', 'y', 'ug', 'uy']) {
  for (let start = 0; start <= 5; start += 1) {
    for (const pattern of ['.', '(?:)', 'x', '\\udc00']) add(pattern, flags, '😀x', start);
  }
}

const nativeScript = `const fs=require('fs');const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));const out=JSON.parse(fs.readFileSync(0,'utf8')).map(c=>{try{let flags=c.flags.includes('y')?c.flags:c.flags.replace('g','')+'g';let r=new RegExp(String.fromCharCode(...c.pattern),flags);r.lastIndex=c.start;let m=r.exec(String.fromCharCode(...c.input));return m?{status:'match',index:m.index,end:m.index+m[0].length,captures:Array.from(m,x=>x===undefined?null:units(x))}:{status:'none'};}catch(e){return{status:'syntax'};}});process.stdout.write(JSON.stringify(out));`;
const nativeEngine = process.argv.includes('--engine');
const identity = nativeEngine ? inspectNativeEngine() : {
  engine: 'host-node', versions: process.versions, installedGameEngine: false,
};
const expected = nativeEngine ? runNativeEngine(nativeScript, cases) : (() => {
  const result = spawnSync(process.execPath, ['-e', nativeScript], {
    input: JSON.stringify(cases), encoding: 'utf8', timeout: 120000, maxBuffer: 64 * 1024 * 1024,
  });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
})();
const result = spawnSync(fileURLToPath(new URL('.lake/build/bin/jsregexpcheck', import.meta.url)), [], {
  input: JSON.stringify(cases), encoding: 'utf8', timeout: 120000, maxBuffer: 64 * 1024 * 1024,
});
if (result.error) throw result.error;
assert.equal(result.status, 0, result.stderr);
const actual = JSON.parse(result.stdout);
assert.equal(actual.length, cases.length);
for (let i = 0; i < cases.length; i += 1) {
  const observed = expected[i].status === 'syntax' ? { status: actual[i].status } : actual[i];
  assert.deepEqual(observed, expected[i], JSON.stringify({ index: i, case: cases[i] }));
}
console.log(JSON.stringify({ checks: cases.length, comparisonEngine: identity, javascriptSemanticsVerified: false }));
