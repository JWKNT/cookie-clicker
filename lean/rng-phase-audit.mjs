/** Local reseed dataflow audit, not a JavaScript semantics verifier. */
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { loadGameSource } from '../model/game-source.mjs';
const { parse } = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url))('acorn');
const FREE = 1, SEEDED = 2;
const functionNode = node => /^(FunctionExpression|FunctionDeclaration|ArrowFunctionExpression)$/.test(node?.type);
const symbol = node => !node ? '' : node.type === 'Identifier' ? node.name : node.type === 'ThisExpression' ? 'this' :
  node.type === 'Literal' ? String(node.value) : node.type === 'MemberExpression' ? `${symbol(node.object)}.${symbol(node.property)}` : '';
const children = node => Object.entries(node).filter(([key]) => key !== 'loc').flatMap(([, value]) =>
  Array.isArray(value) ? value.filter(child => child?.type) : value?.type ? [value] : []);
const seedCall = node => node?.type === 'CallExpression' && symbol(node.callee) === 'Math.seedrandom';
const names = mask => [mask & FREE ? 'free' : null, mask & SEEDED ? 'seeded' : null].filter(Boolean);

/** Branch conditions are treated nondeterministically. Calls other than explicit
 * reseeds preserve phase in this local analysis; their effect is a separate obligation.
 * Implicit exceptions are not normal returns and are outside this analysis.
 */
export function localPhaseFlow(fn, text, { excludeYouTooltip = false } = {}) {
  const callsWhileSeeded = new Set();
  let excluded = 0;
  const expression = (node, phase) => {
    if (!node || functionNode(node) || !phase) return phase;
    if (node.type === 'ConditionalExpression') {
      const p = expression(node.test, phase);
      return expression(node.consequent, p) | expression(node.alternate, p);
    }
    if (node.type === 'LogicalExpression') {
      const p = expression(node.left, phase);
      return p | expression(node.right, p);
    }
    if (seedCall(node)) {
      for (const arg of node.arguments) phase = expression(arg, phase);
      return node.arguments.length ? SEEDED : FREE;
    }
    for (const child of children(node)) phase = expression(child, phase);
    if (node.type === 'CallExpression' && phase & SEEDED) callsWhileSeeded.add(symbol(node.callee) || '<dynamic>');
    return phase;
  };
  const branchExcluded = test => excludeYouTooltip &&
    text.slice(test.start, test.end).replace(/\s/g, '') === "selected==i&&this.name=='You'";
  const statement = (node, phase) => {
    if (!node || !phase) return { normal: phase, returns: 0 };
    switch (node.type) {
      case 'BlockStatement': {
        let returns = 0;
        for (const child of node.body) {
          const next = statement(child, phase); phase = next.normal; returns |= next.returns;
        }
        return { normal: phase, returns };
      }
      case 'ExpressionStatement': return { normal: expression(node.expression, phase), returns: 0 };
      case 'VariableDeclaration':
        for (const d of node.declarations) phase = expression(d.init, phase);
        return { normal: phase, returns: 0 };
      case 'ReturnStatement': return { normal: 0, returns: expression(node.argument, phase) };
      case 'IfStatement': {
        const p = expression(node.test, phase);
        if (branchExcluded(node.test)) { excluded++; return statement(node.alternate, p); }
        const yes = statement(node.consequent, p), no = statement(node.alternate, p);
        return { normal: yes.normal | no.normal, returns: yes.returns | no.returns };
      }
      case 'WhileStatement': case 'ForStatement': case 'ForInStatement': case 'ForOfStatement': {
        if (node.init) phase = node.init.type === 'VariableDeclaration' ? statement(node.init, phase).normal : expression(node.init, phase);
        if (node.right) phase = expression(node.right, phase);
        let head = phase, returns = 0;
        // Only two phase bits exist, so union iteration reaches its fixed point.
        for (let iteration = 0; iteration < 4; iteration++) {
          const test = expression(node.test, head), body = statement(node.body, test);
          returns |= body.returns;
          const next = head | expression(node.update, body.normal);
          if (next === head) return { normal: expression(node.test, head), returns };
          head = next;
        }
        throw new Error('Phase fixed point did not converge');
      }
      case 'FunctionDeclaration': case 'EmptyStatement': return { normal: phase, returns: 0 };
      default: throw new Error(`Unreviewed statement ${node.type} at line ${node.loc?.start.line}`);
    }
  };
  const result = statement(fn.body, FREE);
  return { normalExitPhases: names(result.normal | result.returns), callsWhileSeeded: [...callsWhileSeeded].sort(), excludedYouTooltipBranches: excluded };
}

export function analyzeFunctionText(text, options) {
  const ast = parse(text, { ecmaVersion: 'latest', locations: true });
  assert(functionNode(ast.body[0]));
  return localPhaseFlow(ast.body[0], text, options);
}

const expectedSites = {
  'main.js': [[4524,1],[4538,0],[7584,1],[7584,0],[8299,1],[8376,0],[8387,1],[8396,0],[8421,1],[8423,1],
    [11206,1],[11207,0],[11208,0],[11294,1],[11295,1],[11300,0],[11303,0],[11394,1],[11396,0],[14959,1],[14968,0]],
  'minigameGrimoire.js': [[312,1],[314,0]],
};

export function buildRngPhaseInventory() {
  const source = loadGameSource();
  const sites = [], callbacks = [], references = [];
  for (const [file, text] of Object.entries(source.sources)) {
    // index.html has no reseed tokens, including inline scripts and handlers.
    if (!file.endsWith('.js')) { assert(!text.includes('seedrandom')); continue; }
    const ast = parse(text, { ecmaVersion: 'latest', locations: true });
    const owners = new Map();
    const walk = (node, parents = []) => {
      if (!node?.type) return;
      if (node.type === 'Literal' && typeof node.value === 'string') assert(!node.value.includes('seedrandom'), 'Unreviewed generated reseed code');
      if (node.type === 'MemberExpression' && symbol(node.property) === 'seedrandom') {
        const parent = parents.at(-1);
        references.push({ file, line: node.loc.start.line, symbol: symbol(node), context: parent?.type });
        assert(seedCall(parent) || file === 'main.js' && node.loc.start.line === 702 && symbol(node) === 'c.seedrandom' && parent?.type === 'AssignmentExpression', 'Unreviewed reseed alias or property access');
      }
      if (seedCall(node)) {
        const owner = [...parents].reverse().find(functionNode);
        assert(owner, 'Top-level reseed needs review');
        const parent = parents[parents.indexOf(owner) - 1];
        const ownerName = parent?.type === 'AssignmentExpression' ? symbol(parent.left) : owner.id?.name || '<anonymous>';
        const site = { file, line: node.loc.start.line, column: node.loc.start.column, arguments: node.arguments.length,
          operation: node.arguments.length ? 'explicit-seed' : 'reset-to-free-assumption',
          source: text.slice(node.start, node.end), callback: `${ownerName}@${owner.loc.start.line}` };
        sites.push(site); owners.set(owner, ownerName);
      }
      for (const child of children(node)) walk(child, [...parents, node]);
    };
    walk(ast);
    assert.deepEqual(sites.filter(site => site.file === file).map(site => [site.line, site.arguments]), expectedSites[file] || [], `Reseed inventory changed in ${file}`);
    for (const [fn, name] of owners) callbacks.push({ file, name, line: fn.loc.start.line,
      unrestricted: localPhaseFlow(fn, text), permittedTooltipBranch: localPhaseFlow(fn, text, { excludeYouTooltip: true }) });
  }
  assert.equal(sites.length, 23);
  assert.equal(references.length, 24); // 23 calls and the one library definition.
  assert.equal(callbacks.length, 8);
  for (const callback of callbacks) {
    assert.deepEqual(callback.permittedTooltipBranch.normalExitPhases, ['free']);
    assert.deepEqual(callback.unrestricted.normalExitPhases, callback.name === 'this.draw' ? ['free', 'seeded'] : ['free']);
  }
  return { schemaVersion: 1, sourceHashes: source.hashes, fileCount: Object.keys(source.sources).length,
    resetAssumption: 'No-argument seedrandom returns to fresh independent uniform 53-bit draws; this intentionally differs from native entropy reseeding.',
    scope: 'Fail-closed inventory and intraprocedural normal-return phase analysis of explicit reseed call sites. Branches are nondeterministic; called helpers preserve phase in this local analysis. No whole-engine refinement or exception-safety claim.',
    sites, callbacks, references };
}
