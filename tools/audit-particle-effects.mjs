import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
import vm from 'node:vm';
import { loadGameSource } from '../model/game-source.mjs';
const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const { sources, hashes } = loadGameSource();
const hash = (s) => createHash('sha256').update(s).digest('hex');
const path = (n) =>
  n?.type === 'Identifier'
    ? n.name
    : n?.type === 'ThisExpression'
      ? 'this'
      : n?.type === 'MemberExpression'
        ? `${path(n.object)}.${n.computed ? (n.property.type === 'Literal' ? n.property.value : '*') : n.property.name}`
        : '<expression>';
const walk = (n, f, parent = null, owner = null) => {
  if (!n || typeof n !== 'object') return;
  const current = /Function/.test(n.type) ? n : owner;
  f(n, parent, current);
  for (const [k, v] of Object.entries(n)) {
    if (k === 'loc') continue;
    if (Array.isArray(v))
      for (const x of v)
        if (x?.type) walk(x, f, n, current);
        else {
        }
    else if (v?.type) walk(v, f, n, current);
  }
};
const ast = acorn.parse(sources['main.js'], { ecmaVersion: 2020, locations: true });
const parents = new WeakMap();
walk(ast, (n, p) => {
  if (p) parents.set(n, p);
});
const functions = new Map();
walk(ast, (n, p) => {
  if (n.type === 'FunctionDeclaration') functions.set(n.id.name, n);
  if (n.type === 'VariableDeclarator' && n.init?.type === 'FunctionExpression')
    functions.set(path(n.id), n.init);
  if (n.type === 'AssignmentExpression' && n.right.type === 'FunctionExpression')
    functions.set(path(n.left), n.right);
});
const text = (n) => sources['main.js'].slice(n.start, n.end);
const selected = [
  'Game.particleAdd',
  'Game.particlesUpdate',
  'Game.particlesDraw',
  'Pic',
  'Loader',
  'bind',
  'choose',
];
const expectedWrites = {
  'Game.particleAdd': [
    'me.dur',
    'me.life',
    'me.pic',
    'me.picId',
    'me.picPos',
    'me.r',
    'me.size',
    'me.text',
    'me.x',
    'me.xd',
    'me.y',
    'me.yd',
    'me.z',
  ],
  'Game.particlesUpdate': ['me.life', 'me.x', 'me.y', 'me.yd'],
  'Game.particlesDraw': ['ctx.fillStyle', 'ctx.font', 'ctx.globalAlpha', 'ctx.textAlign'],
  Pic: [],
  bind: [],
  choose: [],
};
const expectedCalls = {
  'Game.particleAdd': [
    'Game.bakeryName.toLowerCase',
    'Math.floor',
    'Math.random',
    'choose',
    'cookies.push',
  ],
  'Game.particlesUpdate': ['Math.random'],
  'Game.particlesDraw': [
    'Pic',
    'ctx.drawImage',
    'ctx.fillText',
    'ctx.restore',
    'ctx.rotate',
    'ctx.save',
    'ctx.translate',
  ],
  Pic: [
    'Game.Loader.Load',
    'Game.Loader.assetsLoaded.indexOf',
    'Game.Loader.assetsLoading.indexOf',
  ],
  bind: ['fn.apply'],
  choose: ['Math.floor', 'Math.random'],
};
const reports = selected.map((name) => {
  const fn = functions.get(name);
  assert(fn, name);
  const writes = [],
    calls = [],
    reads = [],
    returns = [];
  walk(fn, (n, p) => {
    if (
      (n.type === 'AssignmentExpression' && n.left.type === 'MemberExpression') ||
      (n.type === 'UpdateExpression' && n.argument.type === 'MemberExpression')
    )
      writes.push({
        line: n.loc.start.line,
        target: path(n.left || n.argument),
        operator: n.operator,
      });
    if (n.type === 'CallExpression' || n.type === 'NewExpression')
      calls.push({
        line: n.loc.start.line,
        target: path(n.callee),
        construct: n.type === 'NewExpression',
      });
    if (n.type === 'MemberExpression' && !(p?.type === 'AssignmentExpression' && p.left === n))
      reads.push({ line: n.loc.start.line, target: path(n) });
    if (n.type === 'ReturnStatement')
      returns.push({ line: n.loc.start.line, value: n.argument ? text(n.argument) : null });
  });
  if (expectedWrites[name])
    assert.deepEqual([...new Set(writes.map((x) => x.target))].sort(), expectedWrites[name]);
  if (expectedCalls[name])
    assert.deepEqual([...new Set(calls.map((x) => x.target))].sort(), expectedCalls[name]);
  const aliases = [];
  walk(fn, (n) => {
    if (n.type === 'VariableDeclarator' && n.init?.type === 'MemberExpression')
      aliases.push({ line: n.loc.start.line, local: path(n.id), value: path(n.init) });
  });
  if (
    name === 'Game.particleAdd' ||
    name === 'Game.particlesUpdate' ||
    name === 'Game.particlesDraw'
  ) {
    assert.deepEqual(
      aliases.filter((x) => x.local === 'me').map((x) => x.value),
      ['Game.particles.*'],
    );
    if (name === 'Game.particlesDraw')
      assert.deepEqual(
        aliases.filter((x) => x.local === 'ctx').map((x) => x.value),
        ['Game.LeftBackground'],
      );
  }
  return {
    name,
    line: fn.loc.start.line,
    sourceSha256: hash(text(fn)),
    writes,
    calls,
    returns,
    aliases,
    readRoots: [...new Set(reads.map((x) => x.target))].sort(),
  };
});
const storageUses = [],
  particleCalls = [],
  escaped = [],
  initialization = [],
  methodReferences = [];
const pictureNames = (n) =>
  !n
    ? ['icons.png', 'smallDollars.png']
    : n.type === 'Literal' && typeof n.value === 'string'
      ? n.value
        ? [n.value]
        : ['icons.png', 'smallDollars.png']
      : n.type === 'ArrayExpression'
        ? ['icons.png']
        : n.type === 'ConditionalExpression'
          ? [...pictureNames(n.consequent), ...pictureNames(n.alternate)]
          : (() => {
              throw Error(`unclassified picture expression ${text(n)}`);
            })();
walk(ast, (n, p, owner) => {
  if (n.type === 'MemberExpression' && path(n) === 'Game.particleAdd')
    methodReferences.push({
      line: n.loc.start.line,
      parent: p.type,
      callee: p.type === 'CallExpression' && p.callee === n,
    });
  if (n.type === 'MemberExpression' && ['Game.particles', 'Game.particlesN'].includes(path(n)))
    storageUses.push({
      line: n.loc.start.line,
      target: path(n),
      parent: p.type,
      owner: owner?.loc.start.line ?? null,
    });
  if (
    n.type === 'AssignmentExpression' &&
    ['Game.particles', 'Game.particlesN', 'Game.particles.*'].includes(path(n.left))
  )
    initialization.push({ line: n.loc.start.line, target: path(n.left), value: text(n.right) });
  if (n.type === 'CallExpression' && path(n.callee) === 'Game.particleAdd') {
    const call = {
      line: n.loc.start.line,
      arguments: n.arguments.map(text),
      possiblePictures: pictureNames(n.arguments[7]),
      owner: owner?.loc.start.line ?? null,
      discarded: p.type === 'ExpressionStatement',
    };
    particleCalls.push(call);
    if (!call.discarded) {
      assert.equal(p.type, 'VariableDeclarator');
      assert.equal(p.id.name, 'part');
      const refs = [];
      walk(owner, (z, parent) => {
        if (z.type === 'Identifier' && z.name === 'part')
          refs.push({
            line: z.loc.start.line,
            parent: parent.type,
            member: parent.type === 'MemberExpression' ? path(parent) : null,
            writeOnly:
              parent.type === 'MemberExpression' &&
              parents.get(parent)?.type === 'AssignmentExpression' &&
              parents.get(parent).left === parent &&
              parents.get(parent).operator === '=',
          });
      });
      for (const r of refs)
        assert(
          r.parent === 'VariableDeclarator' || (r.member === 'part.r' && r.writeOnly),
          JSON.stringify(r),
        );
      escaped.push({ ...call, alias: p.id.name, references: refs });
    }
  }
});
assert.deepEqual(
  initialization.map((x) => [x.line, x.target]),
  [
    [5914, 'Game.particles'],
    [5915, 'Game.particlesN'],
    [5918, 'Game.particles.*'],
  ],
);
assert.equal(initialization[1].value, '50');
assert.equal(particleCalls.length, 9);
assert.equal(escaped.length, 2);
assert.equal(methodReferences.length, 10);
assert.equal(methodReferences.filter((x) => x.callee).length, 9);
assert.equal(methodReferences.filter((x) => x.parent === 'AssignmentExpression').length, 1);
const particleImageNames = [
  ...new Set(['smallCookies.png', ...particleCalls.flatMap((x) => x.possiblePictures)]),
].sort();
assert.deepEqual(particleImageNames, [
  'icons.png',
  'shinyWrinklerBits.png',
  'smallCookies.png',
  'smallDollars.png',
  'wrinklerBits.png',
]);
// Execute intact source functions in an explicit ordinary-data/host-contract fixture.
// This regression guards the effect inventory; it is not a browser or new-save proof.
const cases = [];
const scenarios = [
  { name: 'empty-auto', args: [] },
  { name: 'explicit-position', args: [10, 20] },
  { name: 'fools', season: 'fools', args: [] },
  { name: 'ortiel', bakeryName: 'ortiel', args: [] },
  { name: 'string-picture', args: [10, 20, 0, 0, 1, 2, 0, 'wrinklerBits.png'] },
  { name: 'icon-picture', args: [10, 20, 0, 0, 1, 2, 0, [20, 3]] },
  { name: 'text', args: [10, 20, 0, 0, 1, 4, 2, '', '+1'] },
  { name: 'all-active', active: true, args: [10, 20] },
  { name: 'active-text', active: true, text: 'hello', args: [10, 20] },
  { name: 'expiry', active: true, life: 59, args: [10, 20] },
  { name: 'no-background', background: false, args: [] },
  { name: 'startup-callback-boundary', loaderStarted: false, args: [] },
];
for (const scenario of scenarios) {
  const writes = [],
    host = [],
    jobs = [];
  let draws = 0,
    startupCalls = 0;
  const allowed = (name, object) =>
    new Proxy(object, {
      set(o, k, v) {
        writes.push(`${name}.${String(k)}`);
        o[k] = v;
        return true;
      },
      deleteProperty() {
        throw Error('unexpected delete');
      },
    });
  const readonly = (name, object) =>
    new Proxy(object, {
      set() {
        throw Error(`economic write ${name}`);
      },
      deleteProperty() {
        throw Error(`economic delete ${name}`);
      },
    });
  const particles = Array.from({ length: 50 }, (_, i) =>
    allowed(`particle${i}`, {
      x: 0,
      y: 0,
      xd: 0,
      yd: 0,
      w: 64,
      h: 64,
      z: 0,
      size: 1,
      dur: 2,
      life: scenario.active ? (scenario.life ?? i) : -1,
      r: 0,
      pic: 'smallCookies.png',
      picId: 0,
      picPos: [0, 0],
      text: scenario.text || 0,
    }),
  );
  const ctx = allowed(
    'canvas',
    Object.assign(
      { canvas: { width: 800 } },
      Object.fromEntries(
        ['save', 'restore', 'translate', 'rotate', 'drawImage', 'fillText'].map((name) => [
          name,
          (...args) => {
            host.push({
              kind: name,
              args: args.map((x) => (typeof x === 'object' ? 'object' : x)),
            });
          },
        ]),
      ),
    ),
  );
  const math = Object.create(Math);
  math.random = () => {
    draws++;
    return ((draws * 3571) % 8192) / 8192;
  };
  const economics = {
    cookies: 123,
    cookiesEarned: 456,
    AchievementsOwned: 7,
    lumps: 8,
    lumpsTotal: 9,
    T: 10,
    drawT: 11,
  };
  const icon = readonly('upgrade-icon', [1, 2]);
  const gameData = {
    ...economics,
    particles: readonly('particle-array', particles),
    particlesN: 50,
    fps: 30,
    LeftBackground: scenario.background === false ? null : ctx,
    season: scenario.season || '',
    bakeryName: scenario.bakeryName || 'ordinary',
    Upgrades: readonly('upgrades', {
      a: readonly('upgrade-a', { bought: 1, pool: 'cookie', icon }),
      b: readonly('upgrade-b', { bought: 0, pool: 'cookie', icon }),
    }),
    local: true,
  };
  const game = readonly('Game', gameData);
  let ctxVM;
  class Image {
    set src(v) {
      this._src = v;
      jobs.push(() => this.onload?.({ target: this }));
    }
    get src() {
      return this._src;
    }
  }
  ctxVM = vm.createContext({
    Game: game,
    Math: math,
    Image,
    document: { createElement: (type) => allowed(`created-${type}`, {}) },
    setTimeout() {
      throw Error('unexpected timer');
    },
  });
  for (const name of ['choose', 'bind', 'Loader', 'Pic'])
    vm.runInContext(`${name}=${text(functions.get(name))}`, ctxVM);
  gameData.Loader = vm.runInContext('new Loader()', ctxVM);
  gameData.Loader.doneLoading = scenario.loaderStarted === false ? 0 : 1;
  gameData.Loader.loaded = () => {
    startupCalls++;
  };
  for (const name of ['Game.particleAdd', 'Game.particlesUpdate', 'Game.particlesDraw'])
    gameData[name.slice(5)] = vm.runInContext(`(${text(functions.get(name))})`, ctxVM);
  const before = JSON.stringify(economics);
  const start = draws;
  const part = game.particleAdd(...scenario.args);
  const addDraws = draws - start;
  assert(particles.includes(part));
  assert(addDraws >= 2 && addDraws <= 5);
  const beforeUpdate = draws;
  game.particlesUpdate();
  const updateDraws = draws - beforeUpdate;
  assert(updateDraws <= 50);
  if (game.LeftBackground) {
    game.particlesDraw(0);
    game.particlesDraw(2);
  }
  while (jobs.length) jobs.shift()();
  for (const [k, v] of Object.entries(economics)) assert.equal(game[k], v);
  assert.equal(JSON.stringify(economics), before);
  assert.equal(game.particles.length, 50);
  assert.equal(game.Loader.doneLoading, 1);
  assert.equal(startupCalls, scenario.loaderStarted === false ? 1 : 0);
  cases.push({
    name: scenario.name,
    startupCalls,
    addDraws,
    updateDraws,
    particleWrites: writes.filter((x) => x.startsWith('particle')).length,
    canvasWrites: writes.filter((x) => x.startsWith('canvas')).length,
    hostCalls: host.length,
    loadedAssets: [...game.Loader.assetsLoaded],
  });
}
const report = {
  schemaVersion: 1,
  generatorSha256: hash(readFileSync(new URL(import.meta.url), 'utf8')),
  status: 'source-effect-inventory-and-guarded-native-regression-not-yet-interpreter-refinement',
  sourceHashes: hashes,
  scope:
    'All pinned main.js particle storage definitions and uses, plus complete particleAdd/update/draw bodies and their Pic/Loader dependency.',
  initialization,
  functions: reports,
  storageUses,
  methodReferences,
  particleCalls,
  particleImageNames,
  escapedAliases: escaped,
  conclusions: [
    'The pinned source initializes exactly50 particle records and has no other assignment to Game.particles, Game.particlesN or Game.particles[index].',
    'All member writes in particleAdd/update are to the selected particle record; all particleDraw member writes are to the native canvas context.',
    'The only external aliases of the particleAdd return value are two local part variables; their only nondeclaration uses write part.r.',
    'particleAdd performs2 to5 source free/seeded random calls (including choose), while particlesUpdate performs at most50; random calls are retained in the inventory and cannot be dropped from a seeded generator.',
    'Native initialization and the9 audited live callsites restrict particle image names to5 fixed assets, as recorded; this does not classify other callers of Pic.',
    'The particleAdd cookie icon array may alias an upgrade icon; the particle code reads its coordinates and does not mutate that array.',
    'particleDraw calls Pic, whose cache-miss path schedules image-load effects through Loader.Load; this is not a pure canvas-only path. With Loader.doneLoading=1 the native onLoad branch cannot call Loader.loaded.',
  ],
  requiredContracts: [
    'Native initialized ordinary Game/particle/upgrade/data properties and unmodified native function/prototype identities; property operations must not invoke economic getters, setters or proxies.',
    'The50 particle records are pairwise distinct and disjoint from economic/control records; native initialization and every possible subsequent alias/write must refine the audited source inventory.',
    'All actual particle arguments are ordinary primitive values or readonly icon arrays; no user code or object conversion callbacks.',
    'Math.floor, native String.toLowerCase, Array.push and choose have their pinned semantics. Retain every random draw and its current generator unless a separate free-IID discarded-prefix theorem applies.',
    'Canvas calls preserve economic heap and generator phase but retain canvas state, possible exceptions and asset/task effects. Pic/Loader must use their native source identities.',
    'To exclude an asset-triggered startup callback, establish Loader.doneLoading=1. Preserve load jobs and loaded/loading/cache writes even under zero asset latency.',
    'Normal termination, native property/coercion/host exception behavior and public-control reachability are separate obligations; this inventory is not a whole-game simulation theorem.',
  ],
  nativeRegression: {
    kind: 'isolated Node VM with rejecting economic-write proxies and explicit host contract; no game save/browser',
    cases: cases.length,
    results: cases,
  },
};
const out = new URL('../model/particle-effects-source-audit.json', import.meta.url);
const rendered = JSON.stringify(report, null, 2) + '\n';
if (process.argv.includes('--check')) assert.equal(readFileSync(out, 'utf8'), rendered);
else writeFileSync(out, rendered);
console.log(
  JSON.stringify({
    output: out,
    check: process.argv.includes('--check'),
    functions: reports.length,
    callSites: particleCalls.length,
    escapedAliases: escaped.length,
    cases: cases.length,
    sourceSha256: hashes['main.js'],
    reportSha256: hash(rendered),
  }),
);
