/** Source-code inventory only: never load a save, execute the game, or change its installation. */
import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { loadGameSource } from '../model/game-source.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const source = loadGameSource();
const sha256 = text => createHash('sha256').update(text).digest('hex');
const output = new URL('../model/clock-source-sites.json', import.meta.url);
const timestampProperties = new Set([
  'Timer.t', 'Game.time', 'Game.lastActivity', 'Game.fpsStartTime',
  'Game.startDate', 'Game.fullDate', 'Game.lastDate', 'Game.lumpT',
  'Game.lastClick', 'Game.lastClickedSpecialPic',
  'M.nextStep', 'M.nextSoil', 'M.nextFreeze', 'M.swapT', 'this.date',
]);
const propertyPath = node => node?.type === 'Identifier' ? node.name
  : node?.type === 'ThisExpression' ? 'this'
  : node?.type === 'MemberExpression' ? (() => {
    const base = propertyPath(node.object);
    const key = !node.computed && node.property.type === 'Identifier' ? node.property.name
      : node.computed && node.property.type === 'Literal' && typeof node.property.value === 'string' ? node.property.value : null;
    return base && key ? `${base}.${key}` : null;
  })() : null;
const expressions = new Map();
const sites = [];
const directNumericProjectionSites = [];
const stringCandidates = [];
for (const [file, text] of Object.entries(source.sources)) {
  if (!file.endsWith('.js')) continue;
  const ast = acorn.parse(text, { ecmaVersion: 5, locations: true });
  const nodes = [];
  function visit(node, ancestors = []) {
    if (!node || typeof node.type !== 'string') return;
    nodes.push(node);
    const path = propertyPath(node);
    const isDateCall = (node.type === 'CallExpression' || node.type === 'NewExpression') &&
      (propertyPath(node.callee) === 'Date' || propertyPath(node.callee) === 'Date.now');
    const isDateMethod = node.type === 'CallExpression' && node.callee.type === 'MemberExpression' &&
      !node.callee.computed && /^(?:getTime|getFullYear|getMinutes|setTime|setFullYear|toUTCString)$/.test(node.callee.property.name);
    const isTimestampProperty = node.type === 'MemberExpression' && timestampProperties.has(path);
    if (isDateCall || isDateMethod || isTimestampProperty) {
      const parent = ancestors.at(-1);
      const functionNode = [...ancestors].reverse().find(n => /Function/.test(n.type));
      const functionIndex = functionNode ? ancestors.indexOf(functionNode) : -1;
      const owner = functionIndex > 0 ? ancestors[functionIndex - 1] : null;
      const functionName = functionNode?.id?.name ||
        (owner?.type === 'AssignmentExpression' ? propertyPath(owner.left) : null) ||
        (owner?.type === 'VariableDeclarator' ? owner.id.name : null) || null;
      const code = text.slice(node.start, node.end);
      sites.push({ file, start: node.start, end: node.end, line: node.loc.start.line,
        column: node.loc.start.column, kind: isDateCall ? 'clock-or-Date-construction' : isDateMethod ? 'Date-method-candidate' : 'timestamp-property',
        name: path || propertyPath(node.callee), functionName,
        parentType: parent?.type || null, parentOperator: parent?.operator || null,
        text: code, sha256: sha256(code) });
      if (parent?.type === 'BinaryExpression' && ['*', '/', '%', '<<', '>>', '>>>', '&', '|', '^'].includes(parent.operator)) {
        const expression = text.slice(parent.start, parent.end);
        directNumericProjectionSites.push({ file, start: parent.start, end: parent.end,
          line: parent.loc.start.line, operator: parent.operator, functionName,
          operandDomain: node.callee?.type === 'MemberExpression' && !node.callee.computed && node.callee.property.name === 'getMinutes' ? 'bounded calendar Number; no timestamp projection' : 'timestamp or Date numeric value',
          clockOperand: code, text: expression, sha256: sha256(expression) });
      }
    }
    if (node.type === 'Literal' && typeof node.value === 'string' && /\bDate(?:\s*\(|\.now\s*\()/.test(node.value)) {
      stringCandidates.push({ file, start: node.start, end: node.end, line: node.loc.start.line,
        text: node.value, sha256: sha256(node.value), activeHandlerVerified: false });
    }
    for (const value of Object.values(node)) {
      if (Array.isArray(value)) for (const child of value) visit(child, [...ancestors, node]);
      else if (value && typeof value === 'object' && typeof value.type === 'string') visit(value, [...ancestors, node]);
    }
  }
  visit(ast);
  expressions.set(file, nodes);
}

function uniqueSite(file, exactText, nodeType) {
  const text = source.sources[file];
  const matches = expressions.get(file).filter(node => (!nodeType || node.type === nodeType) && text.slice(node.start, node.end) === exactText);
  if (matches.length !== 1) throw new Error(`Expected one ${nodeType || 'node'} in ${file}: ${exactText}; found ${matches.length}`);
  const node = matches[0];
  return { file, start: node.start, end: node.end, line: node.loc.start.line, column: node.loc.start.column,
    nodeType: node.type, text: exactText, sha256: sha256(exactText) };
}
const codecs = [
  ['Game.startDate', 'main.js', 'main.stats[0]', 'parseInt(Game.startDate)', 'Game.startDate=parseInt(spl[0])', 'truncate-integer'],
  ['Game.fullDate', 'main.js', 'main.stats[1]', 'parseInt(Game.fullDate)', 'Game.fullDate=parseInt(spl[1])', 'truncate-integer'],
  ['Game.lastDate', 'main.js', 'main.stats[2]', 'parseInt(Game.lastDate)', 'Game.lastDate=parseInt(spl[2])', 'truncate-integer'],
  ['Game.lumpT', 'main.js', 'main.general[44]', 'parseFloat(Math.floor(Game.lumpT))', 'Game.lumpT=spl[44]?parseInt(spl[44]):Date.now()', 'floor-integer'],
  ['M.nextStep', 'minigameGarden.js', 'garden.space[0].colon[0]', 'parseFloat(M.nextStep)', 'M.nextStep=parseFloat(spl2[i2++]||M.nextStep)', 'dyadic-decimal'],
  ['M.nextSoil', 'minigameGarden.js', 'garden.space[0].colon[2]', 'parseFloat(M.nextSoil)', 'M.nextSoil=parseFloat(spl2[i2++]||M.nextSoil)', 'dyadic-decimal'],
  ['M.nextFreeze', 'minigameGarden.js', 'garden.space[0].colon[8]', 'parseFloat(M.nextFreeze)', 'M.nextFreeze=parseFloat(spl2[i2++]||M.nextFreeze)', 'dyadic-decimal'],
  ['M.swapT', 'minigamePantheon.js', 'pantheon.space[2]', 'parseFloat(M.swapT)', 'M.swapT=parseFloat(spl[i++]||Date.now())', 'dyadic-decimal'],
].map(([field, file, slot, writer, reader, mode]) => ({ field, slot, mode,
  writer: uniqueSite(file, writer, 'CallExpression'), reader: uniqueSite(file, reader, 'AssignmentExpression'),
  annotationImplemented: true }));

const inventory = {
  schema: 'cookie-clicker-clock-source-sites-v1', gameVersion: source.version,
  sourceHashes: source.hashes, parser: { name: 'acorn', version: acorn.version, ecmaVersion: 5 },
  scope: 'AST inventory of all seven pinned JavaScript files; comments are excluded. Index script and dynamically compiled handler execution still require source propagation checks.',
  sourceRefinementVerified: false, sourceAnnotationsImplemented: true,
  semantics: {
    clock: 'Unbounded exact elapsed clock; Date.now floors to integer milliseconds.',
    nativePrefix: 'Absolute value at most 8640000000000000 milliseconds. Preserve existing binary64 result while the exact arithmetic result remains in this range.',
    extendedArithmetic: 'Timestamp plus/minus a finite binary64 duration uses its exact dyadic value outside the native prefix. Reentry rounds once to binary64.',
    difference: 'Timestamp minus timestamp projects the exact difference to ordinary binary64; two native-prefix operands use the existing Number.sub directly.',
    numericProjection: 'Timestamp multiply/divide/remainder/bitwise and explicit Number conversion leave the clock domain by binary64 projection. This does not make ordinary economic arithmetic exact.',
    calendar: 'Exact UTC Gregorian calendar. Outside the native Date prefix, civil years and Easter intermediate arithmetic use a separate exact rational carrier; date construction truncates components as native source does.',
    save: 'Eight listed current-save timestamp fields and the separate MAIL timestamp use source-checked typed readers. Main lumpT is intentionally floored. The user selected total processing of timestamp-derived UTF-16 text beyond native string/index limits; the retained mixkey activation and native save-codec operations now carry that text provenance. Complete source propagation and tagged-loop termination proofs remain open. Ordinary cookie/counter parsers are unchanged.',
    quota: 'The native 104857600-byte storage quota still applies. The selected timestamp-text extension does not remove storage quota or prove late reload success.',
  },
  unresolvedChoices: [
    'The unbounded-clock assumption alone does not select out-of-range arithmetic rules; exact dyadic duration arithmetic is the selected extension, not native JavaScript behavior.',
    'The implemented calendar scalar covers source Easter and expiry arithmetic. A general whole-source propagation invariant and any additional calendar crossings still require proof.',
    'Direct numeric-projection sites are listed below. Aliases and callback propagation require the executable typed-value rules and source invariants, not an inference from a finite direct-site inventory.',
    'Selected full-source execution requires the selected-unbounded-v1 artifact marker. Fifteen checked source annotations erase to the original AST; this validation is not a kernel proof of the frontend or source correspondence.',
    'Current pure ClockValue does not yet prove general binary64 packing/range validity or the complete rendered fractional decimal string round-trip.',
  ],
  savedFields: codecs,
  extraTypedSites: [
    { role: 'zero timestamp initializer, needed to distinguish elapsed subtraction from duration subtraction', site: uniqueSite('main.js', 'Game.fpsStartTime=0', 'AssignmentExpression') },
    { role: 'zero timestamp initializer, needed to distinguish elapsed subtraction from duration subtraction', site: uniqueSite('minigameGarden.js', 'M.nextStep=0', 'AssignmentExpression') },
    { role: 'zero timestamp initializer, needed to distinguish elapsed subtraction from duration subtraction', site: uniqueSite('minigameGarden.js', 'M.nextSoil=0', 'AssignmentExpression') },
    { role: 'zero timestamp initializer, needed to distinguish elapsed subtraction from duration subtraction', site: uniqueSite('minigameGarden.js', 'M.nextFreeze=0', 'AssignmentExpression') },
    { role: 'zero timestamp initializer, needed to distinguish elapsed subtraction from duration subtraction', site: uniqueSite('main.js', 'Game.lastClick=0', 'AssignmentExpression') },
    { role: 'zero timestamp initializer, needed to distinguish elapsed subtraction from duration subtraction', site: uniqueSite('main.js', 'Game.lastClickedSpecialPic=0', 'AssignmentExpression') },
    { role: 'MAIL gift timestamp reader, separate from current-save codec', site: uniqueSite('main.js', 'parseInt(str[1]||0)', 'CallExpression') },
    { role: 'Exact decimal timestamp contributes to seeded RNG input', site: uniqueSite('main.js', "Math.seedrandom(Game.seed+'/'+Game.lumpT)", 'CallExpression') },
  ],
  nonTimestamp: [
    { field: 'Game.lumpRefill', reason: 'Decreasing frame cooldown; the save label is historical. Its value remains ordinary binary64.' },
    { field: 'Game.accumulatedDelay', reason: 'Ordinary binary64 duration updated from timestamp differences; not an absolute timestamp.' },
    { field: 'Game.T and frame counters', reason: 'Ordinary native counters; the clock assumption does not remove their binary64 saturation.' },
  ],
  sites, directNumericProjectionSites, stringCandidates,
  summary: { sites: sites.length, byKind: Object.fromEntries([...new Set(sites.map(x => x.kind))].map(kind => [kind, sites.filter(x => x.kind === kind).length])), savedFields: codecs.length, directNumericProjections: directNumericProjectionSites.filter(x => x.operandDomain === 'timestamp or Date numeric value').length, boundedCalendarNumericSites: directNumericProjectionSites.filter(x => x.operandDomain !== 'timestamp or Date numeric value').length, dynamicStringCandidates: stringCandidates.length },
};
const rendered = `${JSON.stringify(inventory, null, 2)}\n`;
if (process.argv.includes('--check')) {
  if (readFileSync(output, 'utf8') !== rendered) throw new Error('Clock source-site inventory is stale');
} else writeFileSync(output, rendered);
console.log(JSON.stringify(inventory.summary));
