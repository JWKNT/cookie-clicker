import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
const { parse } = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url))('acorn');
import { loadGameSource } from '../model/game-source.mjs';
import { createRuntime } from '../model/runtime.mjs';
import { NATURAL_TAIL_ACHIEVEMENTS, NATURAL_TAIL_PREFIX_ACHIEVEMENTS, NATURAL_TAIL_OWNERSHIP_ACHIEVEMENTS, recoveryTailPolicySource } from '../model/recovery-tail-policy.mjs';
import { orderedNaturalPolicySource } from '../model/ordered-natural-policy.mjs';
const sha = text => createHash('sha256').update(text).digest('hex');
const source = loadGameSource();
const requirements = JSON.parse(readFileSync(new URL('../model/completion-requirements.json', import.meta.url)));
const catalogue = JSON.parse(readFileSync(new URL('../model/catalogue.json', import.meta.url)));
const text = source.sources['main.js'];
const ast = parse(text, { ecmaVersion: 2020, locations: true });
const sites = new Map();
// Keep the traversal independent of the report's required-name lists.
function walk(node, parents = []) {
  if (!node || typeof node !== 'object') return;
  if (node.type === 'CallExpression' && node.callee?.type === 'MemberExpression'
    && node.callee.object?.name === 'Game' && node.callee.property?.name === 'Win'
    && typeof node.arguments[0]?.value === 'string') {
    const name = node.arguments[0].value, gate = parents.findLast(p => p.type === 'IfStatement');
    sites.set(name, [...(sites.get(name) || []), { line: node.loc.start.line,
      call: text.slice(node.start, node.end), enclosingCondition: gate ? text.slice(gate.test.start, gate.test.end) : null }]);
  }
  for (const child of Object.values(node)) {
    if (Array.isArray(child)) { for (const value of child) if (value?.type) walk(value, [...parents, node]); }
    else if (child?.type) walk(child, [...parents, node]);
  }
}
walk(ast);
const runtime = createRuntime({ recordAudit: false });
const observation = runtime.snapshot();
const production = [...observation.production.bankAchievements, ...observation.production.cpsAchievements,
  ...observation.production.handmadeAchievements, ...observation.shop.buildings.flatMap(b => [...b.countAchievements, ...b.productionAchievements])].map(a => a.name);
const covered = new Set([...NATURAL_TAIL_ACHIEVEMENTS, ...production]);
const mandatory = new Set(NATURAL_TAIL_PREFIX_ACHIEVEMENTS);
const partition = requirements.requiredAchievements.map(a => ({ id: a.id, name: a.name,
  phase: a.name === 'Thick-skinned' ? 'direct-veil' : mandatory.has(a.name) || !covered.has(a.name) ? 'prefix' : 'tail' }));
const excluded = catalogue.achievements.filter(a => a.normal && !requirements.requiredAchievements.some(x => x.name === a.name)).map(a => ({ id: a.id, name: a.name }));
const ownership = NATURAL_TAIL_OWNERSHIP_ACHIEVEMENTS.map(name => {
  const native = (sites.get(name) || []).filter(s => s.line >= 16388 && s.line <= 16505);
  if (!native.length) throw new Error(`Missing intact Logic ownership award: ${name}`);
  return { name, native };
});
if (new Set(partition.map(a => a.name)).size !== partition.length) throw new Error('Duplicate required achievement');
const report = { schemaVersion: 1, status: 'source-linked-controller-partition-not-reachability-or-optimality',
  sourceHashes: source.hashes, policySha256: sha(orderedNaturalPolicySource()), tailPolicySha256: sha(recoveryTailPolicySource()),
  normalCatalogueCount: catalogue.achievements.filter(a => a.normal).length, requiredCount: partition.length,
  counts: Object.fromEntries(['prefix','direct-veil','tail'].map(phase => [phase, partition.filter(a => a.phase === phase).length])),
  ownership, partition, excludedNormalGoals: excluded,
  limitations: ['Static ownership guards are checked against pinned source; no source-loop preservation theorem is supplied.',
    'The partition covers every required normal achievement; current upgrades and finite access retain the full completion predicate.',
    'The new-save prefix, funding target, complete retry laws, calendar restoration and physical inputs remain unproved.'] };
const path = new URL('../model/ordered-natural-partition.json', import.meta.url);
const output = JSON.stringify(report, null, 2) + '\n';
if (process.argv.includes('--check')) { if (readFileSync(path, 'utf8') !== output) throw new Error('Stale ordered natural partition report'); }
else writeFileSync(path, output);
console.log(JSON.stringify({ status: 'pass', required: report.requiredCount, counts: report.counts, nativeOwnershipAwards: ownership.length }));
