import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { loadGameSource } from '../model/game-source.mjs';
import { buildRngPhaseInventory } from '../lean/rng-phase-audit.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const hash = text => createHash('sha256').update(text).digest('hex');
const nameOf = node => node?.type === 'Identifier' ? node.name
  : node?.type === 'ThisExpression' ? 'this'
  : node?.type === 'MemberExpression' ? `${nameOf(node.object)}.${node.computed
    ? node.property.type === 'Literal' ? node.property.value : '*' : node.property.name}` : '<expression>';
const union = (...sets) => new Set(sets.flatMap(set => [...set]));
const equal = (a, b) => a.size === b.size && [...a].every(value => b.has(value));

/**
 * Control-flow projection only. Non-seed calls are assumed to return normally
 * with the incoming generator, or the free generator. This assumption is
 * recorded, not established, by the report. Potential exceptional exits are
 * recorded separately; a lexical reset is not an exception-safety proof.
 */
export function projectRngFunction(fn, { forbiddenBranch = null } = {}) {
  const seedCalls = new Map(), callsWhileSeeded = new Map(), abruptWhileSeeded = new Map();
  const current = outcomes => new Set([...outcomes].filter(x => x.startsWith('normal:')).map(x => x.slice(7)));
  const abrupt = outcomes => new Set([...outcomes].filter(x => !x.startsWith('normal:')));
  const normals = phases => new Set([...phases].map(phase => `normal:${phase}`));
  const noteAbrupt = (node, phases, operation) => {
    if (phases.has('seeded')) abruptWhileSeeded.set(`${node.start}:${operation}`, {
      line: node.loc.start.line, operation,
    });
  };
  const expression = (node, phases) => {
    if (!node || phases.size === 0) return phases;
    switch (node.type) {
      case 'Literal': case 'Identifier': case 'ThisExpression':
      case 'FunctionExpression': return phases;
      case 'SequenceExpression': return node.expressions.reduce((s, n) => expression(n, s), phases);
      case 'ArrayExpression': return node.elements.reduce((s, n) => expression(n, s), phases);
      case 'ObjectExpression': return node.properties.reduce((s, n) => expression(n.value, s), phases);
      case 'MemberExpression': {
        const out = node.computed ? expression(node.property, expression(node.object, phases)) : expression(node.object, phases);
        noteAbrupt(node, out, 'property-read-or-reference'); return out;
      }
      case 'CallExpression': case 'NewExpression': {
        let out = expression(node.callee, phases);
        out = node.arguments.reduce((s, n) => expression(n, s), out);
        const name = nameOf(node.callee);
        if (name === 'Math.seedrandom' && node.type === 'CallExpression') {
          seedCalls.set(node.start, { line: node.loc.start.line, kind: node.arguments.length ? 'explicit-seed' : 'restore-free' });
          noteAbrupt(node, out, 'seedrandom-call');
          return out.size ? new Set([node.arguments.length ? 'seeded' : 'free']) : out;
        }
        noteAbrupt(node, out, `${node.type === 'NewExpression' ? 'construct' : 'call'}:${name}`);
        if (out.has('seeded')) callsWhileSeeded.set(node.start, { line: node.loc.start.line, target: name });
        // The report lists this as a required callee contract. A callee may
        // restore free randomness, but may not introduce a leaked seed.
        return out.size ? union(out, new Set(['free'])) : out;
      }
      case 'LogicalExpression': return union(expression(node.left, phases), expression(node.right, expression(node.left, phases)));
      case 'ConditionalExpression': {
        const input = expression(node.test, phases);
        return union(expression(node.consequent, input), expression(node.alternate, input));
      }
      case 'AssignmentExpression': {
        const out = expression(node.right, expression(node.left, phases));
        noteAbrupt(node, out, 'assignment-or-conversion'); return out;
      }
      case 'BinaryExpression': {
        const out = expression(node.right, expression(node.left, phases));
        noteAbrupt(node, out, 'binary-conversion'); return out;
      }
      case 'UnaryExpression': case 'UpdateExpression': {
        const out = expression(node.argument, phases); noteAbrupt(node, out, 'unary-or-update-conversion'); return out;
      }
      default: throw new Error(`Uncovered expression: ${node.type}`);
    }
  };
  const sequence = (nodes, phases) => nodes.reduce((out, node) => union(abrupt(out), statement(node, current(out))), normals(phases));
  const loop = (node, phases, init, test, update, body, atLeastOnce) => {
    let head = expression(init, phases), exits = new Set(), prev;
    if (atLeastOnce) {
      const first = statement(body, head); exits = union(exits, abrupt(first)); head = current(first);
    }
    do {
      prev = new Set(head);
      const tested = expression(test, head), next = statement(body, tested);
      exits = union(exits, normals(tested), new Set([...next].filter(x => x.startsWith('return:') || x.startsWith('throw:'))));
      const continued = new Set([...next].filter(x => x.startsWith('continue:')).map(x => x.split(':').at(-1)));
      const broken = new Set([...next].filter(x => x.startsWith('break:')).map(x => x.split(':').at(-1)));
      exits = union(exits, normals(broken));
      head = union(head, expression(update, union(current(next), continued)));
    } while (!equal(prev, head));
    return exits;
  };
  const statement = (node, phases) => {
    if (!node || phases.size === 0) return normals(phases);
    switch (node.type) {
      case 'BlockStatement': return sequence(node.body, phases);
      case 'EmptyStatement': case 'FunctionDeclaration': case 'DebuggerStatement': return normals(phases);
      case 'ExpressionStatement': return normals(expression(node.expression, phases));
      case 'VariableDeclaration': return normals(node.declarations.reduce((s, d) => expression(d.init, s), phases));
      case 'IfStatement': {
        const input = expression(node.test, phases);
        if (node === forbiddenBranch) return statement(node.alternate, input);
        return union(statement(node.consequent, input), statement(node.alternate, input));
      }
      case 'ReturnStatement': return new Set([...expression(node.argument, phases)].map(phase => `return:${phase}`));
      case 'ThrowStatement': return new Set([...expression(node.argument, phases)].map(phase => `throw:${phase}`));
      case 'BreakStatement': return new Set([...phases].map(phase => `break:${node.label?.name ?? ''}:${phase}`));
      case 'ContinueStatement': return new Set([...phases].map(phase => `continue:${node.label?.name ?? ''}:${phase}`));
      case 'ForStatement': {
        const input = node.init?.type === 'VariableDeclaration' ? current(statement(node.init, phases)) : expression(node.init, phases);
        return loop(node, input, null, node.test, node.update, node.body, false);
      }
      case 'WhileStatement': return loop(node, phases, null, node.test, null, node.body, false);
      case 'DoWhileStatement': return loop(node, phases, null, node.test, null, node.body, true);
      case 'ForInStatement': {
        const input = expression(node.right, phases);
        return loop(node, input, null, null, null, node.body, false);
      }
      case 'LabeledStatement': {
        const out = statement(node.body, phases);
        return new Set([...out].map(x => x.startsWith(`break:${node.label.name}:`) ? `normal:${x.split(':').at(-1)}` : x));
      }
      case 'SwitchStatement': {
        const input = expression(node.discriminant, phases);
        let out = normals(input);
        for (let index = 0; index < node.cases.length; index++) {
          const branch = sequence(node.cases.slice(index).flatMap(c => c.consequent), expression(node.cases[index].test, input));
          out = union(out, new Set([...branch].map(x => x.startsWith('break::') ? `normal:${x.split(':').at(-1)}` : x)));
        }
        return out;
      }
      case 'TryStatement': {
        let out = statement(node.block, phases);
        if (node.handler) out = union(new Set([...out].filter(x => !x.startsWith('throw:'))),
          statement(node.handler.body, new Set([...out].filter(x => x.startsWith('throw:')).map(x => x.slice(6)))));
        if (node.finalizer) {
          const restored = new Set();
          for (const completion of out) {
            const parts = completion.split(':'), phase = parts.pop(), kind = parts.join(':');
            for (const result of statement(node.finalizer, new Set([phase])))
              restored.add(result.startsWith('normal:') ? `${kind}:${result.slice(7)}` : result);
          }
          out = restored;
        }
        return out;
      }
      case 'WithStatement': return statement(node.body, expression(node.object, phases));
      default: throw new Error(`Uncovered statement: ${node.type}`);
    }
  };
  const outcomes = statement(fn.body, new Set(['free']));
  return {
    outcomes: [...outcomes].sort(), seedCalls: [...seedCalls.values()].sort((a, b) => a.line - b.line),
    callsWhileSeeded: [...callsWhileSeeded.values()].sort((a, b) => a.line - b.line),
    potentialExceptionalSitesWhileSeeded: [...abruptWhileSeeded.values()].sort((a, b) => a.line - b.line || a.operation.localeCompare(b.operation)),
  };
}

export function buildRngPhaseAudit() {
  const source = loadGameSource(), rows = [], everySeedCall = [];
  // Reuse the existing alias and generated-handler coverage checks.
  const inventory = buildRngPhaseInventory();
  for (const [name, text] of Object.entries(source.sources)) {
    if (!name.endsWith('.js')) continue;
    const ast = acorn.parse(text, { ecmaVersion: 5, locations: true });
    const functions = [], seedOwners = new Map();
    const walk = (node, owner = null, parent = null) => {
      if (!node || typeof node !== 'object') return;
      if (['FunctionExpression', 'FunctionDeclaration'].includes(node.type)) {
        owner = node; functions.push({ node, parent });
      }
      if (node.type === 'CallExpression' && nameOf(node.callee) === 'Math.seedrandom') {
        assert(owner, 'Every native seedrandom call must have an enclosing function');
        everySeedCall.push({ file: name, line: node.loc.start.line, kind: node.arguments.length ? 'explicit-seed' : 'restore-free' });
        if (!seedOwners.has(owner)) seedOwners.set(owner, []);
        seedOwners.get(owner).push(node);
      }
      for (const [key, value] of Object.entries(node)) {
        if (['loc', 'start', 'end'].includes(key)) continue;
        if (Array.isArray(value)) value.forEach(child => walk(child, owner, node));
        else if (value && typeof value === 'object') walk(value, owner, node);
      }
    };
    walk(ast);
    for (const { node, parent } of functions.filter(({ node }) => seedOwners.has(node))) {
      const functionName = parent?.type === 'AssignmentExpression' ? nameOf(parent.left) : node.id?.name ?? '<anonymous>';
      const raw = projectRngFunction(node);
      let forbiddenBranch = null;
      const find = child => {
        if (!child || typeof child !== 'object') return;
        if (child !== node && ['FunctionExpression', 'FunctionDeclaration'].includes(child.type)) return;
        if (name === 'main.js' && child.type === 'IfStatement' && child.loc.start.line === 8417) forbiddenBranch = child;
        for (const [key, value] of Object.entries(child)) {
          if (['loc', 'start', 'end'].includes(key)) continue;
          if (Array.isArray(value)) value.forEach(find); else if (value && typeof value === 'object') find(value);
        }
      };
      find(node);
      const restricted = forbiddenBranch ? projectRngFunction(node, { forbiddenBranch }) : raw;
      rows.push({ file: name, name: functionName, line: node.loc.start.line,
        sha256: hash(text.slice(node.start, node.end)),
        forbiddenBranch: forbiddenBranch ? { line: 8417, test: text.slice(forbiddenBranch.test.start, forbiddenBranch.test.end),
          meaning: 'The clone-hover branch leaks a seeded generator. Excluding this branch is a stated action-class premise, not a consequence of the syntax checker.' } : null,
        unrestricted: raw, excludingForbiddenCloneBranch: restricted });
    }
  }
  assert.equal(everySeedCall.length, inventory.sites.length);
  assert.equal(rows.filter(row => row.forbiddenBranch).length, 1);
  assert(rows.every(row => !row.excludingForbiddenCloneBranch.outcomes.some(x => /^(normal|return):seeded$/.test(x))));
  assert.equal(rows.filter(row => row.unrestricted.outcomes.some(x => /^(normal|return):seeded$/.test(x))).length, 1);
  return {
    schemaVersion: 1, status: 'normal-control-flow-certificate-with-open-exception-and-call-refinement',
    sourceHashes: source.hashes, reproduction: 'node tools/audit-rng-phase.mjs',
    existingKernelProjection: 'lean/CookieClicker/NativeRngPhase.lean already checks the local normal-return phase programs. This report adds operation-level exceptional-exit obligations; it does not replace or strengthen those programs into a source-refinement theorem.',
    scope: 'All explicit Math.seedrandom callsites in the pinned eight source files. The library implementation at main.js702 uses its local c.seedrandom alias and is separately the native generator implementation, not a game action.',
    assumptionsOfProjection: [
      'Ordinary calls and constructions terminate normally and return with their incoming generator or the free generator.',
      'Property reads, writes, conversion and host operations do not throw or synchronously invoke an unclassified generator-changing callback.',
      'The clone-hover branch at main.js8417 is not executed; all other branch choices and loop iteration counts are overapproximated.',
      'No imported/mod/injected code replaces native functions, properties or generator bindings.',
    ],
    conclusionsOfProjection: [
      'Starting free, all enumerated seed-owning functions have only free normal/return outcomes under the projection premises and clone-branch exclusion.',
      'Without that exclusion, the building draw callback has a seeded normal exit.',
    ],
    openForUniversalHandPickedBound: [
      'Connect the syntax projection and callee contracts to actual source execution, including indirect functions and aliases.',
      'Discharge every potentially exceptional operation reached while seeded. None of the paired reset sites is protected by finally.',
      'Show the initialized generator is free and preserve phase through every allowed event, timer and host callback, including a callback that reports an uncaught exception.',
      'Establish that the admissible policy definition excludes the clone leak; an intention-based prohibition alone is not a syntactic branch invariant.',
      'Connect the harvest choose([0,1]) draw to that free phase and combine conditional fairness with the actual source sugar-clock spacing theorem.',
    ],
    everySeedCall, functions: rows,
  };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const report = buildRngPhaseAudit(), file = new URL('../model/rng-phase-source-audit.json', import.meta.url);
  if (process.argv.includes('--check')) assert.deepEqual(JSON.parse(readFileSync(file, 'utf8')), report);
  else writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ status: report.status, seedCallsites: report.everySeedCall.length,
    seedOwningFunctions: report.functions.length,
    seededNormalExitFunctions: report.functions.filter(row => row.unrestricted.outcomes.includes('normal:seeded')).length,
    exceptionSites: report.functions.reduce((n, row) => n + row.excludingForbiddenCloneBranch.potentialExceptionalSitesWhileSeeded.length, 0) }));
}
