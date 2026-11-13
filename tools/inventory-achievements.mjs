/**
 * Print the static achievement inventory from the audited Steam 2.053 source.
 * Usage: node tools/inventory-achievements.mjs /path/to/main.js > paper/achievements-2.053.json
 * Install the source/cookie-monster-plus dependencies first. The game is never executed.
 */
import fs from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const { parse } = require('acorn');
const sourcePath = process.argv[2];
if (!sourcePath || process.argv.length !== 3) {
  throw new Error('Usage: node tools/inventory-achievements.mjs /path/to/main.js');
}
const bytes = fs.readFileSync(sourcePath);
const sha256 = createHash('sha256').update(bytes).digest('hex');
const auditedHash = 'a8813ec2ee97edf5ebff6a3ce2037dcb65c08abd13c123bb92efda89b06ef4f7';
if (sha256 !== auditedHash) {
  throw new Error('The source does not match the audited Steam 2.053 hash. Review the new source before changing this inventory.');
}
const source = bytes.toString('utf8');
const start = source.indexOf('//define achievements');
const end = source.indexOf('//end of achievements', start);
if (start < 0 || end < start) throw new Error('Achievement declaration boundaries were not found.');
const methods = new Set(['Achievement', 'BankAchievement', 'CpsAchievement', 'TieredAchievement', 'ProductionAchievement']);
const events = [];
const ast = parse(source, { ecmaVersion: 'latest', locations: true });

function visit(node) {
  if (!node || typeof node !== 'object') return;
  if (node.start >= start && node.end <= end) {
    if (node.type === 'NewExpression' || node.type === 'CallExpression') {
      const callee = node.callee;
      if (callee.type === 'MemberExpression' && callee.object.name === 'Game' && methods.has(callee.property.name)) {
        const name = node.arguments[0];
        events.push({
          kind: 'achievement',
          ...(name?.type === 'Literal' && typeof name.value === 'string'
            ? { name: name.value }
            : { name_expression: source.slice(name.start, name.end) }),
          definition: callee.property.name,
          line: node.loc.start.line,
          start: node.start,
        });
      }
    }
    if (node.type === 'AssignmentExpression' && source.slice(node.left.start, node.left.end) === 'Game.last.pool' && node.right.type === 'Literal') {
      events.push({ kind: 'pool', pool: node.right.value, start: node.start });
    }
  }
  for (const [key, value] of Object.entries(node)) {
    if (key === 'loc') continue;
    if (Array.isArray(value)) value.forEach(visit);
    else if (value && typeof value === 'object') visit(value);
  }
}
visit(ast);
events.sort((a, b) => a.start - b.start);
const entries = [];
let previous;
for (const event of events) {
  if (event.kind === 'achievement') {
    previous = { ...event, pool: 'normal' };
    entries.push(previous);
  } else if (previous) previous.pool = event.pool;
}
const achievements = entries.filter((entry) => 'name' in entry).map(({ name, pool, definition, line }) => ({ name, pool, definition, line }));
if (new Set(achievements.map((entry) => entry.name)).size !== achievements.length) {
  throw new Error('Duplicate primary achievement names require review.');
}
const catalogue = {
  schema_version: 1,
  game_version: '2.053',
  status: 'static_inventory_not_runtime_validated',
  source: { file: 'main.js', sha256 },
  extraction: {
    method: 'Parse JavaScript with Acorn. Read literal achievement names and subsequent Game.last.pool assignments in declaration order. Normalize the default empty pool to normal. Do not execute the game.',
    literal_identifiers: achievements.length,
    normal_literal_identifiers: achievements.filter((entry) => entry.pool === 'normal').length,
    shadow_identifiers: achievements.filter((entry) => entry.pool === 'shadow').length,
    unused_dungeon_identifiers: achievements.filter((entry) => entry.pool === 'dungeon').length,
    numeric_game_ids_assigned: false,
    runtime_validated: false,
  },
  unresolved_dynamic_identifiers: entries.filter((entry) => 'name_expression' in entry).map((entry) => ({
    source_line: entry.line,
    definition: entry.definition,
    name_expression: entry.name_expression,
    pool: entry.pool,
    reason: 'The primary name depends on the runtime Beautify function. Capture it from the verified game initialization before asserting complete coverage.',
  })),
  achievements,
};
process.stdout.write(`${JSON.stringify(catalogue, null, 2)}\n`);
