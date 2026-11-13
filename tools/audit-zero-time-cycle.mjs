import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { loadGameSource } from '../model/game-source.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const source = loadGameSource();
const main = source.sources['main.js'];
const hash = text => createHash('sha256').update(text).digest('hex');
const nameOf = node => node?.type === 'Identifier' ? node.name
  : node?.type === 'ThisExpression' ? 'this'
  : node?.type === 'MemberExpression' && !node.computed ? `${nameOf(node.object)}.${node.property.name}` : null;
const walk = (node, visit) => {
  if (!node || typeof node !== 'object') return;
  if (typeof node.type === 'string') visit(node);
  for (const [name, value] of Object.entries(node)) {
    if (['start', 'end', 'loc'].includes(name)) continue;
    if (Array.isArray(value)) for (const item of value) walk(item, visit);
    else if (value && typeof value === 'object') walk(value, visit);
  }
};
const functions = [];
for (const [name, marker] of [
  ['buy', 'this.buy=function'], ['sell', 'this.sell=function'],
  ['getPrice', 'this.getPrice=function'], ['getSumPrice', 'this.getSumPrice=function'],
  ['getReverseSumPrice', 'this.getReverseSumPrice=function'], ['getSellMultiplier', 'this.getSellMultiplier=function'],
  ['refresh', 'this.refresh=function'], ['rebuild', 'this.rebuild=function'],
  ['modifyBuildingPrice', 'Game.modifyBuildingPrice=function'], ['storeBulkButton', 'Game.storeBulkButton=function'],
  ['PlaySound', 'var PlaySound=function'], ['tooltip.hide', 'Game.tooltip.hide=function'],
  ['tooltip.wobble', 'Game.tooltip.wobble=function'],
]) {
  const start = main.indexOf(marker);
  assert(start >= 0, marker);
  const node = acorn.parseExpressionAt(main, start + marker.indexOf('function'), { ecmaVersion: 5 });
  const text = main.slice(node.start, node.end);
  const calls = new Set(), constructors = new Set(), ownReads = new Set();
  walk(node, child => {
    if (child.type === 'CallExpression') calls.add(nameOf(child.callee) ?? '<computed or expression call>');
    if (child.type === 'NewExpression') constructors.add(nameOf(child.callee) ?? '<computed constructor>');
    if (child.type === 'MemberExpression' && child.object.type === 'ThisExpression' && !child.computed)
      ownReads.add(child.property.name);
  });
  const timers = [...calls].filter(call => /(?:^|\.)(?:setTimeout|setInterval|requestAnimationFrame)$/.test(call));
  assert.equal(timers.length, 0, `${name} introduced a direct timer`);
  if (name === 'getPrice') {
    assert(ownReads.has('amount') && ownReads.has('free') && ownReads.has('basePrice'));
    assert(!ownReads.has('bought'), 'price now depends on the saturated bought counter');
  }
  functions.push({ name, line: main.slice(0, node.start).split('\n').length,
    sha256: hash(text), directCalls: [...calls].sort(), constructors: [...constructors].sort(), directTimers: timers });
}
const audioPool = 'for (var i=0;i<12;i++){SoundInsts[i]=new Audio();}';
assert(main.includes(audioPool));
assert(main.includes('if (SoundI>=12) SoundI=0;'));
assert(main.includes("if (!volumeSetting || volume==0) return 0;"));
assert(main.includes("if (typeof Sounds[url]==='undefined')"));
const report = {
  schemaVersion: 1,
  scope: 'source audit of the proposed Cursor sale/rebuy route; not a whole-game transition or optimality theorem',
  sourceHashes: source.hashes,
  reproduction: 'node tools/audit-zero-time-cycle.mjs',
  functions,
  sourceFacts: {
    directTimerCallsInAuditedBodies: 0,
    audioPool: { instances: 12, initializerSha256: hash(audioPool), indexWrap: 12,
      cacheKey: 'native sound URL',
      silenceAlternative: 'The native volume control can set Game.volume=0. PlaySound then returns before allocation or playback.' },
    financialCycle: 'With one Cursor and no price modifiers, amount changes1→0→1. Fresh free0 gives refund4 and rebuy15; Starter kit free>=1 gives refund3 and rebuy15. getPrice depends on amount/free, not bought. The bought counter may saturate without changing this price rule.',
    hostUpdates: 'refresh/rebuild replace existing style/text/markup fields. storeBulkButton changes mode, bulk, classes and storeToRefresh. Tooltip mouseout/hide and disabled wobble do not schedule a timer.',
    bankArithmetic: 'JavaScriptBankCycleBridge proves every canonical bank with exponent6..970 absorbs each integer refund0..4 and debit0..15, and any finite sequence of these refund-then-debit pairs preserves its bits. This includes bank>=2^58 below2^1023; callback entry and preservation still need refinement.',
    existingDevastation: 'For success, sold1, Ruin in diamond and an existing Devastation object, the source branch adds the native cent to multClick and does not update time. Its actual helper composition is kernel checked in JavaScriptGodzamokSource.',
  },
  open: [
    'The direct-call inventory is not a complete transitive no-timer proof; native DOM/audio callbacks and helper frames need refinement.',
    'Prove the whole buy/sell source path and native visible input path, including price modifiers, affordability, amount and Game.BuildingsOwned invariants.',
    'Prove initialization and preservation of the entry heap, plus absence of a due Logic callback during the same-time sequence.',
    'This route-specific audit does not establish a finite zero-time quotient for all competitor policies.',
  ],
};
const file = new URL('../model/zero-time-cycle-source-audit.json', import.meta.url);
if (process.argv.includes('--check')) assert.deepEqual(JSON.parse(readFileSync(file, 'utf8')), report);
else writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify({ checked: process.argv.includes('--check'), functions: functions.length,
  directTimers: 0, audioPool: 12, scope: report.scope }));
