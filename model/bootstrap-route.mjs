import { createRuntime } from './runtime.mjs';
import { nextPositiveFloat } from './income-route.mjs';

/** A source-linked construction, with explicit unclosed refinement obligations. */
export const BOOTSTRAP_ROUTE = Object.freeze({
  status: 'finite-source-route-with-arithmetic-proofs-and-open-refinement',
  target: 'Hardcore, Neverclick, Temple level1, Godzamok and bank>=2^90 before unbounded random retries',
  steps: [
    'After native startup is ready, make15 accepted clicks20ms apart and buy one Cursor. With zero upgrades, buy one each Grandma, Farm, Mine, Factory, Bank, Temple and Wizard tower as soon as affordable. Keep the first15-click count and buy no upgrades until the five-second check after earned>=1e9.',
    'Keep elderWrath zero and buy no research. One Grandma does not activate the Grandmapocalypse. First lump activation starts a new clock; harvest at the observed ripe23h threshold, before24h. Do not search timestamps for seeded lump types.',
    'Keep the Temple and Wizard tower already bought by the ladder and buy ten total Cursors; buy Reinforced index finger, Carpal tunnel prevention cream and Ambidextrous. Earn1000 handmade cookies and buy Plastic mouse.',
    'Spend one ripe lump on Temple level1; wait for its native10ms loader; sell nine Cursors, then slot Godzamok in diamond.',
    'At bank B below2^58, run floor(B/32) one-Cursor sale/rebuy cycles and400 accepted clicks20ms apart after one gains-update frame. Repeat on an11s period after the old buff expires.',
    'At bank>=2^58, the Cursor debit15 and refund4 are absorbed. A finite2^56-cycle prefix reaches the cent-increment Godzamok cap2^47. Repeat400-click bursts until bank>=2^90.',
    'A later ordinary reset keeps Temple level1. Rebuild the three Cursor upgrades, Plastic mouse and one Temple before repeating the same income construction.',
  ],
  source: {
    challenge: ['main.js:16323-16332', 'main.js:16273-16278', 'main.js:8700-8704'],
    lump: ['main.js:14204', 'main.js:4533', 'main.js:4541-4544', 'main.js:4597-4604', 'main.js:4470-4514'],
    clicks: ['main.js:4671-4743', 'main.js:9931-9933', 'main.js:16426'],
    cycles: ['main.js:7830-7901'],
  },
  bounds: {
    passiveIncrement: { numerator: '7686143364045647', denominatorPowerOfTwo: 61 },
    passiveLowerGain: '1/1024', challengeFrames: '6660050', gainsUpdateFrames: 8, checkFrames: 150,
    schedulerFramesIncludingOverhead: '6660208', schedulerMsAfterReadyIncludingClicks: '219787164',
    diagnosticStartupWaitMs: 200,
    firstRipeWaitMs: 82800000, templePrice: 20000000, templeBaseCps: 7800,
    minimumBaseClick: 64, centMultiplierCap: 2 ** 47, centCyclesToCap: '72057594037927936',
    lowBankCycleMaximumLoss: 16, burstClicks: 400, burstPeriodMs: 11000,
    burstBankGainLower: '9*floor(B/32)', highBankClickGainLower: '2^52',
    highBankClicksUpper: '274877906944', proposedTotalFramesUpper: '2^40',
  },
  kernelArithmetic: ['CookieClicker/BootstrapArithmetic.lean', 'CookieClicker/JavaScriptBootstrapLadder.lean',
    'CookieClicker/JavaScriptRoundingOrder.lean', 'CookieClicker/JavaScriptScaledOrder.lean',
    'CookieClicker/JavaScriptCounterLadder.lean'],
  purchaseLadder: [
    { current: 'Cursor', next: 'Grandma', target: 100, gainQuanta: 1, frames: 102400 },
    { current: 'Grandma', next: 'Farm', target: 1100, gainQuanta: 16, frames: 70400 },
    { current: 'Farm', next: 'Mine', target: 12000, gainQuanta: 128, frames: 96000 },
    { current: 'Mine', next: 'Factory', target: 130000, gainQuanta: 512, frames: 260000 },
    { current: 'Factory', next: 'Bank', target: 1400000, gainQuanta: 4096, frames: 350000 },
    { current: 'Bank', next: 'Temple', target: 20000000, gainQuanta: 16384, frames: 1250000 },
    { current: 'Temple', next: 'Wizard tower', target: 330000000, gainQuanta: 131072, frames: 2578125 },
    { current: 'Wizard tower', next: null, target: 1000000000, gainQuanta: 524288, frames: 1953125 },
  ],
  open: [
    'Compose the proved joint bank/earned recurrence and source Earn/Spend bodies with initialized production and purchase callbacks; later sale/rebuy and click gain bounds remain separate',
    'Prove the full no-upgrade production invariant for the eight fixed boards, automatic-callback preservation, native startup and timer schedule',
    'Prove all256 low-bank bursts suffice, including native expiration/recalculation phases and bounded incidental host state',
    'Compose this entry route with every later income stage, helper setup and all1558 completion conditions',
  ],
});

/** Native short-prefix and boundary checks, not execution of the long route. */
export function probeBootstrapRoute() {
  const runtime = createRuntime({ recordAudit: false }), G = runtime.Game;
  const act = action => runtime.act(action, { observe: false });
  const wait = milliseconds => act({ type: 'wait', milliseconds });
  wait(200);
  for (let i = 0; i < 15; i++) { wait(20); act({ type: 'click' }); }
  act({ type: 'buy-building', id: G.Objects.Cursor.id, amount: 1 });
  wait(200);
  const freshPrefix = { clicks: G.cookieClicks, cursorAmount: G.Objects.Cursor.amount,
    upgrades: G.UpgradesOwned, rawCps: G.cookiesPs, frameIncrement: G.cookiesPs / G.fps,
    elapsedMs: runtime.snapshot().elapsedMs, elderWrath: G.elderWrath };
  const premises = [];
  const ladder = [];
  let spent = 15;
  for (const name of ['Grandma','Farm','Mine','Factory','Bank','Temple','Wizard tower']) {
    const building = G.Objects[name], price = building.getPrice();
    const boundary = nextPositiveFloat(price, -1), beforeCps = G.cookiesPs;
    premises.push({ kind: 'ladder-affordability-boundary', building: name, price, bank: boundary,
      description: 'Inject bank immediately below the next native price and lifetime earned equal to prior spending plus bank; the intervening passive frames and callbacks are not replayed.' });
    G.cookies = boundary; G.cookiesEarned = spent + boundary;
    wait(34);
    const before = G.cookies;
    act({ type: 'buy-building', id: building.id, amount: 1 });
    spent += price;
    wait(34);
    ladder.push({ name, price, before, after: G.cookies, beforeCps, afterCps: G.cookiesPs,
      credit: G.cookiesPs / G.fps, amount: building.amount, clicks: G.cookieClicks,
      upgrades: G.UpgradesOwned, elderWrath: G.elderWrath,
      normalOrZeroBank: G.cookies === 0 || Number.isFinite(G.cookies) && G.cookies >= 2 ** -1022 });
  }
  const boundary = nextPositiveFloat(1e9, -1);
  premises.push({ kind: 'challenge-boundary',
    description: 'Inject earned immediately below1e9 and bank net of the eight native first-purchase prices; do not simulate the full6,660,050-credit ladder.',
    earned: boundary, bank: boundary - spent, spent });
  G.cookiesEarned = boundary; G.cookies = boundary - spent;
  wait(5100);
  const challengeBoundary = { hardcore: !!G.HasAchiev('Hardcore'), neverclick: !!G.HasAchiev('Neverclick'),
    clicks: G.cookieClicks, earned: G.cookiesEarned, lumpsTotal: G.lumpsTotal,
    lumpType: G.lumpCurrentType, elderWrath: G.elderWrath };
  premises.push({ kind: 'ripe-boundary', description: 'Set current lump age to exactly23h; do not simulate the wait' });
  G.lumpT = runtime.clock.now - 23 * 3600000;
  act({ type: 'harvest-lump' });
  const ripeHarvest = { lumps: G.lumps, total: G.lumpsTotal };
  // The native purchase ladder already owns the Temple; retain exactly one.
  act({ type: 'buy-building', id: G.Objects.Cursor.id, amount: 9 });
  for (const name of ['Reinforced index finger', 'Carpal tunnel prevention cream', 'Ambidextrous'])
    act({ type: 'buy-upgrade', id: G.Upgrades[name].id });
  for (let i = 0; i < 125; i++) { wait(20); act({ type: 'click' }); }
  wait(5100);
  act({ type: 'buy-upgrade', id: G.Upgrades['Plastic mouse'].id });
  act({ type: 'level-building', id: G.Objects.Temple.id });
  if (G.promptOn) act({ type: 'prompt', option: 0 });
  wait(34);
  act({ type: 'sell-building', id: G.Objects.Cursor.id, amount: 9 });
  act({ type: 'pantheon-slot', god: 'ruin', slot: 0 });
  wait(34);
  const entry = { bank: G.cookies, templeLevel: G.Objects.Temple.level,
    templeAmount: G.Objects.Temple.amount, cursorAmount: G.Objects.Cursor.amount,
    mouseCps: G.computedMouseCps, godSlot: G.hasGod('ruin'), elderWrath: G.elderWrath };
  premises.push({ kind: 'small-burst-bank', description: 'Reduce bank to32768 to execute a bounded1024-cycle native diagnostic' });
  G.cookies = 32768;
  const cycles = Math.floor(G.cookies / 32), before = G.cookies, start = runtime.clock.now;
  for (let i = 0; i < cycles; i++) {
    act({ type: 'sell-building', id: G.Objects.Cursor.id, amount: 1 });
    act({ type: 'buy-building', id: G.Objects.Cursor.id, amount: 1 });
  }
  const afterCycles = G.cookies, multiplier = G.hasBuff('Devastation').multClick;
  wait(33);
  const clicksBefore = G.cookieClicks;
  for (let i = 0; i < 400; i++) { wait(20); act({ type: 'click' }); }
  const burst = { before, afterCycles, after: G.cookies, cycles, multiplier,
    acceptedClicks: G.cookieClicks - clicksBefore, elapsedMs: runtime.clock.now - start,
    remainingBuffFrames: G.hasBuff('Devastation')?.time ?? 0, claimedMinimumGain: 9 * cycles };
  return { schemaVersion: 1, scope: 'native-prefix-and-boundary-diagnostics-not-long-route-execution',
    sourceHashes: runtime.source.hashes, route: BOOTSTRAP_ROUTE, premises,
    freshPrefix, ladder, challengeBoundary, ripeHarvest, entry, burst };
}
