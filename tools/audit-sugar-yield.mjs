import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
import vm from 'node:vm';
import { loadGameSource } from '../model/game-source.mjs';
import { IID53_SIZE, SUGAR_YIELD_TABLES, nativeYieldIndex, projectedYieldIndex,
  sugarYieldBuckets, sugarYieldDistribution, sugarYieldExpectation } from '../model/sugar-yield-kernel.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn'), source = loadGameSource(), text = source.sources['main.js'];
const ast = acorn.parse(text, { ecmaVersion: 5, locations: true });
const choose = ast.body.find(node => node.type === 'FunctionDeclaration' && node.id.name === 'choose');
let harvest;
function visit(node, callback) {
  if (!node || typeof node !== 'object') return;
  if (node.type) callback(node);
  for (const value of Object.values(node)) {
    if (Array.isArray(value)) value.forEach(item => visit(item, callback));
    else if (value && typeof value === 'object') visit(value, callback);
  }
}
visit(ast, node => {
  if (node.type === 'AssignmentExpression' && node.left.type === 'MemberExpression' &&
      node.left.object.name === 'Game' && node.left.property.name === 'harvestLumps') harvest = node.right;
});
assert(choose && harvest);
const sha256 = value => createHash('sha256').update(value).digest('hex');
const sourceArrays = {};
visit(harvest.body, node => {
  if (node.type !== 'AssignmentExpression' || node.operator !== '*=' || node.left.name !== 'total' ||
      node.right.type !== 'CallExpression' || node.right.callee.name !== 'choose') return;
  const array = node.right.arguments[0];
  if (array?.type !== 'ArrayExpression' || !array.elements.every(item => item?.type === 'Literal')) return;
  const values = array.elements.map(item => item.value);
  for (const [kind, table] of Object.entries(SUGAR_YIELD_TABLES)) {
    if (JSON.stringify(values) === JSON.stringify(table.values)) {
      assert(!sourceArrays[kind]);
      sourceArrays[kind] = { line: node.loc.start.line, values, callSha256: sha256(text.slice(node.start, node.end)) };
    }
  }
});
assert.deepEqual(Object.keys(sourceArrays).sort(), ['golden', 'meaty']);

const context = vm.createContext({ Math: Object.create(Math) });
vm.runInContext(text.slice(choose.start, choose.end), context);
let cases = 0;
const corrections = [];
for (const [kind, table] of Object.entries(SUGAR_YIELD_TABLES)) {
  const indices = new Set([0n, IID53_SIZE - 1n]);
  for (const boundary of table.boundaries)
    for (let delta = -2n; delta <= 2n; delta++)
      if (boundary + delta >= 0n && boundary + delta < IID53_SIZE) indices.add(boundary + delta);
  let state = 0x4d595df4d0f33173n;
  for (let index = 0; index < 1000; index++) {
    state = BigInt.asUintN(64, state * 6364136223846793005n + 1442695040888963407n);
    indices.add(state >> 11n);
  }
  for (const index of indices) {
    const nativeIndex = nativeYieldIndex(kind, index);
    assert.equal(projectedYieldIndex(kind, index), nativeIndex);
    context.Math.random = () => Number(index) / 2 ** 53;
    assert.equal(context.choose(table.values), table.values[nativeIndex]);
    const realIndex = Number(index * BigInt(table.values.length) / IID53_SIZE);
    if (realIndex !== nativeIndex) corrections.push({ kind, index, realIndex, nativeIndex });
    cases++;
  }
}

const output = {
  schemaVersion: 1,
  scope: 'Exact IID53 array-index kernel with native binary64 multiplication before floor.',
  doesNotProve: ['The active generator at every harvest', 'The initialized source call frame',
    'The full harvest callback transition', 'A full-game optimal strategy'],
  reproduction: 'node tools/audit-sugar-yield.mjs --check',
  mainSourceSha256: source.hashes['main.js'],
  chooseSourceSha256: sha256(text.slice(choose.start, choose.end)),
  harvestSourceSha256: sha256(text.slice(harvest.start, harvest.end)),
  sourceArrays,
  denominator: IID53_SIZE,
  tables: Object.fromEntries(Object.keys(SUGAR_YIELD_TABLES).map(kind => [kind, {
    buckets: sugarYieldBuckets(kind), distribution: sugarYieldDistribution(kind), expectation: sugarYieldExpectation(kind),
  }])),
  nativeSourceComparisonCases: cases,
  roundingCorrections: corrections,
  proofModule: 'lean/CookieClicker/JavaScriptRandomSmallChoiceBridge.lean',
  proofSha256: sha256(readFileSync(new URL('../lean/CookieClicker/JavaScriptRandomSmallChoiceBridge.lean', import.meta.url))),
  kernelSha256: sha256(readFileSync(new URL('../model/sugar-yield-kernel.mjs', import.meta.url))),
};
const encoded = JSON.stringify(output, (_, value) => typeof value === 'bigint' ? value.toString() : value, 2) + '\n';
const path = new URL('../model/sugar-yield-kernel.json', import.meta.url);
if (process.argv.includes('--check')) assert.equal(readFileSync(path, 'utf8'), encoded);
else writeFileSync(path, encoded);
console.log(JSON.stringify({ check: process.argv.includes('--check'), cases, roundingCorrections: corrections.length,
  goldenExpectation: '9/2', meatyExpectation: '1' }));
