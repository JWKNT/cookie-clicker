import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { loadGameSource } from '../model/game-source.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');
const hash = text => createHash('sha256').update(text).digest('hex');
const walk = (node, visit) => {
  if (!node || typeof node !== 'object') return;
  if (node.type) visit(node);
  for (const [key, value] of Object.entries(node)) {
    if (['start', 'end', 'loc'].includes(key)) continue;
    if (Array.isArray(value)) value.forEach(item => walk(item, visit));
    else if (value && typeof value === 'object') walk(value, visit);
  }
};
const nameOf = node => node?.type === 'Identifier' ? node.name
  : node?.type === 'ThisExpression' ? 'this'
  : node?.type === 'MemberExpression' ? `${nameOf(node.object)}.${node.computed
    ? node.property.type === 'Literal' ? node.property.value : '*' : node.property.name}` : '<expression>';

export function buildProductionFrameAudit() {
  const source = loadGameSource(), main = source.sources['main.js'];
  const syntax = acorn.parse(main, { ecmaVersion: 5 });
  const functions = new Map(), buildings = [], eachFrameWrites = [];
  walk(syntax, node => {
    if (node.type === 'AssignmentExpression' && node.right.type === 'FunctionExpression') {
      const name = nameOf(node.left);
      if (!functions.has(name)) functions.set(name, []);
      functions.get(name).push(node.right);
    }
    if (node.type === 'AssignmentExpression' && nameOf(node.left).endsWith('.eachFrame'))
      eachFrameWrites.push({ target: nameOf(node.left), value: main.slice(node.right.start, node.right.end) });
    if (node.type === 'NewExpression' && nameOf(node.callee) === 'Game.Object')
      buildings.push({ name: node.arguments[0].value, fn: node.arguments[7] });
  });
  const describe = (name, node) => {
    const text = main.slice(node.start, node.end);
    const calls = new Set(), memberWrites = new Set(), localWrites = new Set(), members = new Set();
    walk(node, child => {
      if (child.type === 'CallExpression') calls.add(nameOf(child.callee));
      if (child.type === 'MemberExpression') members.add(nameOf(child));
      const target = child.type === 'AssignmentExpression' ? child.left
        : child.type === 'UpdateExpression' ? child.argument : null;
      if (target) (target.type === 'Identifier' ? localWrites : memberWrites).add(nameOf(target));
    });
    return { name, line: main.slice(0, node.start).split('\n').length, sha256: hash(text),
      directCalls: [...calls].sort(), memberWrites: [...memberWrites].sort(),
      identifierWrites: [...localWrites].sort(), memberReferences: [...members].sort() };
  };
  const get = name => {
    assert.equal(functions.get(`Game.${name}`)?.length, 1, `${name} must have one source definition`);
    return functions.get(`Game.${name}`)[0];
  };
  const cps = buildings.map(({ name, fn }) => describe(name, fn));
  assert.equal(cps.length, 20);
  assert.equal(new Set(cps.slice(2).map(row => row.sha256)).size, 1,
    'The 18 Farm-through-You callbacks no longer share one body');
  assert(cps.every(row => row.memberWrites.length === 0), 'A CpS callback now writes an object field');
  assert.deepEqual(eachFrameWrites, [{ target: 'this.eachFrame', value: '0' }]);
  const productionHelpers = ['Has', 'GetTieredCpsMult', 'magicCpS', 'ComputeCps', 'eff',
    'auraMult', 'GetHeavenlyMultiplier', 'hasBuff', 'runModHookOnValue', 'mouseCps'];
  const helpers = productionHelpers.map(name => describe(name, get(name)));
  assert(helpers.every(row => row.memberWrites.length === 0),
    'A production helper now contains a direct object-field write');
  const frameNames = ['CalculateGains', 'Logic', 'Loop', 'Draw', 'UpdateSpecial',
    'ToggleSpecialMenu', 'UpdateGrandmapocalypse', 'UpdateWrinklers', 'Earn', 'Dissolve',
    'doLumps', 'computeLumpTimes', 'Win', 'Unlock', 'RebuildUpgrades', 'RefreshStore',
    'updateShimmers', 'updateBuffs', 'UpdateTicker', 'WriteSave', 'CheckUpdates', 'GrabData'];
  const frames = frameNames.map(name => describe(name, get(name)));
  const bodyText = name => main.slice(get(name).start, get(name).end);
  assert(bodyText('CalculateGains').includes('me.storedCps=me.cps(me);'));
  assert(bodyText('Logic').includes('Game.Earn(Game.cookiesPs/Game.fps)'));
  assert(bodyText('Logic').includes('if (Game.recalculateGains) Game.CalculateGains();'));
  assert(bodyText('Loop').includes('setTimeout(Game.Loop,1000/Game.fps);'));
  assert(main.includes('Game.prefs.timeout=0;//if true, game may show pause screen when timed out'));
  assert(bodyText('UpdateGrandmapocalypse').includes("Game.Objects['Grandma'].amount==0) Game.elderWrath=0;"));
  let loopLogicCalls = 0;
  walk(get('Loop'), node => {
    if (node.type === 'CallExpression' && nameOf(node.callee) === 'Game.Logic') loopLogicCalls++;
  });
  assert.equal(loopLogicCalls, 2);
  return {
    schemaVersion: 1,
    status: 'source-linked-frame-contract-with-open-semantic-preservation',
    sourceHashes: source.hashes,
    reproduction: 'node tools/audit-production-frame.mjs',
    scope: 'Historical slower one-Cursor frame contract. The current eight-stage candidate is in bootstrap-route-witness.json. These inventories are source syntax checks, not execution or a whole-game optimality proof.',
    buildingCallbacks: cps, productionHelpers: helpers, scheduledFrames: frames,
    checkedSourceFacts: {
      buildingCount: cps.length, commonFarmThroughYouBodies: cps.length - 2,
      directMemberWritesInCpsAndHelpers: 0,
      directLogicCallsInLoopBody: loopLogicCalls,
      eachFrameWrites,
      allBuildingCallbacksExecute: 'CalculateGains invokes me.cps(me) for every member of Game.Objects, including buildings with amount 0. Zero amount does not bypass a callback.',
      callbackEffectsBoundary: 'The absence of direct member writes does not establish purity. Property access, conversion, calls, prototypes, getters and caller environments still require semantic frame proofs.',
      automaticRecalculation: 'Logic can call CalculateGains before its passive Earn, and sets recalculateGains every 300 frames. Wins and shimmer creation/death can request additional recalculation.',
    },
    provedComponents: [
      'JavaScriptCounterLadder proves the current eight-stage native bank/earned recurrence and purchase guards within 6660050 credits. The historical single-Cursor envelope below is a separate slower contract.',
      'JavaScriptTieredCall composes the complete real Game.GetTieredCpsMult source call under zero-owned upgrade catalogue premises: lookup, argument, invocation, hoist, both full loops, both guards and return. Native allocations are retained. The premises still need initialized-state and automatic-callback preservation proofs.',
      'JavaScriptScaledArithmeticBridge: actual native passive additions from bank0 and earned15 reach the billion-cookie threshold within the stated credit bound.',
      'JavaScriptThresholdBridge: the actual native canLumps guard returns true at that threshold on its stated entry heap.',
      'JavaScriptLoopArithmeticBridge: actual native negative-delay addition and minimum preserve a nonpositive delay; every timer nesting converts 1000/30 to 33ms; native timestamp differences and the finite frame/calendar bounds are proved.',
      'JavaScriptLoopSource: the selected intact latency assignment and Math.min call execute the stated operations, and the native catch-up while skips with unchanged heap on the proved delay states. The source unconditional Logic call is identified; the complete surrounding Loop frame is not yet proved.',
    ],
    requiredFrameTheorem: {
      quantification: 'For every actual initialized heap satisfying the entry invariant, every free-IID branch and every native scheduled callback before the selected exit, the callback terminates, preserves the production inputs and satisfies the stated counter transition. The theorem must also preserve the actual function/prototype/data-property graph and caller continuation.',
      immutableInputs: [
        'The 20 native building identities, callbacks, baseCps values, upgrade ties and registries retain their initialized data-property meanings. Cursor.baseCps is the native Cursor function; its callback uses literal 0.1. The other 19 baseCps fields are finite numbers.',
        'The building amount vector is (1,0,...,0); all 20 levels are 0, eachFrame is 0, minigameLoaded is false, and onMinigame is false.',
        'Every upgrade bought field and UpgradesOwned are 0; no hidden earn/buy callback is invoked. Unlock and achievement fields may change.',
        'Prestige, cookiesReset, ascensionMode, OnAscend, AscendTimer and ReincarnateTimer are 0; fps is 30; dragonAura and dragonAura2 are 0; hasGod is absent; buffs is empty; native mod hook lists are empty.',
        'All wrinkler phases are 0. Grandma amount 0 makes UpdateGrandmapocalypse assign elderWrath 0, so the native spawn guard cannot activate a wrinkler.',
        'At entry immediately after the first Cursor purchase, bank is native 0, earned is native 15 and recalculateGains is 1. At every subsequent Logic entry, either recalculateGains is truthy or the production caches already satisfy the production postcondition.',
        'The generated bakery name is neither orteil nor ortiel after toLowerCase. No rename or other user action occurs during this waiting segment.',
        'The segment has no maintenance reload request, no pending save import, no timeout, no ascension/reincarnation, and no user or mod input. The native default prefs.timeout remains 0. Startup callbacks must finish or be proved harmless before entry.',
      ],
      permittedMutation: [
        'Achievements, unlocked upgrades, milk, prices, DOM/canvas/UI caches, natural unclicked shimmers, ticker state, random draw counts, notes, save metadata, season display state and the recalculateGains flag may change.',
        'CalculateGains may replace effs and CpS caches and write the native Window.name binding. Those outputs must satisfy the production postcondition and cannot alias its input fields.',
        'The passive Earn increases bank and earned by the same native credit; building totalCookies counters and frame/draw counters advance through their actual native operations.',
        'At the first billion-cookie crossing, doLumps may activate the initial lump and its clock. The next 150 frames cannot mature that lump under the proved native timing values.',
      ],
      productionPostcondition: {
        cookiesPsBits: '4591870180066957722', cookiesPs: 'native 0.1', globalCpsMult: 'native 1',
        cpsSucked: 'positiveZero', computedMouseCps: 'native 1', effs: 'empty object',
        buildingStoredTotal: 'Cursor: native 0.1; each of the other 19: positiveZero',
        callbackValues: 'Cursor: native 0.1; Grandma: its finite native baseCps; Farm through You: their finite native baseCps',
      },
      logicPostcondition: [
        'Exactly one unconditional passive Earn call receives Number.div(native 0.1,native 30). Dissolve is skipped because cpsSucked=0.',
        'No other Earn or direct bank/earned write occurs before exit. In particular, the NaN repair is unreachable and the 1e14 You-win-a-cookie reward threshold is above the proved 2^45 counter envelope.',
        'The earned counter follows the proved native recurrence from 15; the bank follows the same native credit recurrence from 0. The initialized/caller heap frame must connect these operations to those exact Game fields.',
        'When earned reaches 1e9, native canLumps returns true, and the next native 150-frame check grants Hardcore and Neverclick. The existing arithmetic/eligibility theorems do not yet prove that check callback.',
      ],
      schedulePostcondition: [
        'Under pinned Chromium87 conversion, setTimeout(Game.Loop,1000/30) requests 33ms. With zero host latency and the preceding Game.time, the latency increment is native 33−native(1000/30)<0.',
        'A nonpositive accumulatedDelay remains nonpositive, so the catch-up while loop is skipped. Each ordinary Loop supplies one Logic call and, if visible, one Draw call.',
        '512000000000 passive credits and 150 check frames fit within 16896000004950ms after entry. T, drawT and loopT remain below 2^40 when their entry values plus this count are below 2^40; the chosen 2026 epoch also stays inside the native Date range.',
      ],
    },
    semanticOpenObligations: [
      'Map this invariant to the initialized source heap and prove it after the actual 15-click/one-Cursor input sequence.',
      'Prove the complete CalculateGains helper/callback composition, including finite baseCps, native arithmetic, actual globals and caller frames.',
      'Prove preservation through all reachable Logic/Draw/Steam/timer callbacks and through DOM getter/default-action behavior; direct-write inventories alone are insufficient.',
      'Compose the proved native Loop latency arithmetic, selected source statements and finite clock bound with actual timer ownership/order and all pending startup and host callbacks.',
      'Compose the native challenge check and subsequent lump/Temple/income stages with the full 1558-condition route; no full finite-expectation bound or optimality result follows from this contract.',
    ],
  };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const report = buildProductionFrameAudit();
  const file = new URL('../model/production-frame-source-audit.json', import.meta.url);
  if (process.argv.includes('--check')) assert.deepEqual(JSON.parse(readFileSync(file, 'utf8')), report);
  else writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ checked: process.argv.includes('--check'), buildings: report.buildingCallbacks.length,
    helpers: report.productionHelpers.length, frames: report.scheduledFrames.length, status: report.status }));
}
