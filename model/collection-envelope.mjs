import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { createRuntime } from './runtime.mjs';
import { loadGameSource } from './game-source.mjs';

const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const acorn = require('acorn');

// A source-catalogue and arithmetic certificate for the proposed retry route.
// It does not assert that every legal policy has this envelope, or that the
// native callbacks have already been refined to the displayed algebra.
export const COLLECTION_ENVELOPE = Object.freeze({
  status: 'route-envelope-with-source-refinement-obligations',
  premises: {
    buildingAmountMaximum: 2000, buildingLevelMaximum: 12,
    soil: 'dirt', heraldMaximum: 100, noDebugUpgradesOrMods: true,
    noDragonsFortuneOrRealityBending: true,
    resetCookieCapExponent: 1000, perEpochEarnedCapExponent: 940,
    prePrestigeRawCpsCapExponent: 400,
  },
  algebra: {
    gardenEffectBoost: 'At most eight neighbors: (6/5)^8 < 8.',
    gardenPositiveEffect: '1 + 36*(4/100)*8 < 16; milk uses 2/1000 and is <2.',
    cookieFactorProduct: 'At most248 factors <=5/4; (5/4)^248 < 2^83.',
    kittenFactorProduct: 'Milk<26, milk multiplier<3, coefficient<=1/5: each factor<32;18 factors <=2^90.',
    ordinaryBuildingSum: 'base<2^49;15tiers<4;5synergies<128;fortune<2;grandma factor<32;level<2;god<2;amount<2^11;20-way sum<2^5. Upper bound2^138.',
    buildingSumBudget: 'The separate Cursor and Grandma formulas also fit2^140, including the additive egg9.',
    otherRawFactors: 'Garden4bits,Herald1,ingredients5,Santa4,fortunes2,dragon-scale1,ascetic1,ages1,Santa-legacy1,eggs14,sugar1,Radiant2:37bits, budget40.',
    unroundedRawBudget: '140+83+90+40=353 exponent bits before the prestige factor.',
    roundingObligation: 'Refine native arithmetic with total expansion <=2^47 to obtain the stated2^400 bound; the catalogue alone does not establish this.',
    resetBarrier: 'For integer0<=old<=2^1000 and0<=earned<=2^940, binary64 integer rounding(old+earned)<=2^1000.',
  },
  earningPhases: {
    golden: {
      policyConditions: ['1000 Cursors and at most700 of each other building', 'elderWrath0 and no research purchases', 'empty Garden', 'no dragon aura, no scorn god, no loans or sugar frenzy', 'golden switch off', 'click only timer-created leaders, with no big-cookie clicks or storm-drop clicks'],
      product: '101*71^19*7*2 <2^128: building buffs, Frenzy, and a conservative veil factor. Wrath and dragon buffs are absent under these conditions.',
      cpsCapExponent: 863,
      largestCredit: 'Golden-lump harvest <=86400*CpS <2^880; Lucky and chain payouts have smaller source coefficients.',
      buffDrain: {
        durationMultiplierUpperCandidate: 2.4495818395400004,
        maximumFrenzySecondsCandidate: 189,
        conservativeSecondsPerLeader: 240,
        maximumDrainLogicFrames: 7777 * 240 * 30 + 1,
        source: ['main.js:5460-5478', 'main.js:13748-13825', 'main.js:13862-14005'],
        argument: 'Native Get lucky2, Lasting fortune1.1, four1.01 factors and Decadence1.07 give the maximum duration multiplier with empty Garden and auras0. Every golden production/click effect lasts at most240 seconds per pop. Existing names add duration, not multiplicative CpS;7777 pops add at most55,994,400 integer frames. updateBuffs subtracts one each logic frame and deletes nonpositive timers.',
        open: 'Refine the finite multiplier cases, allowed effect pool and native callback/frame schedule. Sugar blessing is excluded from the drain condition because it changes frequency only and can be renewed by later lumps.',
      },
      exit: 'Wrath cookie and Eldeer have already been completed before this fresh wrath0 run. After7777 leaders, stop popping golden cookies and wait at most the stated drain-frame budget for golden-created production/click buffs to expire, then enter collection/refill. Do not wait for unrelated Sugar blessing. Reset-dependent Thick-skinned work must also precede this epoch.',
    },
    collection: {
      policyConditions: ['do not pop further golden cookies, including Fortune-generated cookies', 'Easter drops use wrinklers only', 'only Diminish Ineptitude is cast', 'no Dragon Fortune or Reality Bending', 'Godzamok click multiplier<=2^53', 'at most1000 shares per market transaction', 'only a self-addressed one-cookie gift', 'no ascension after final collection begins unless abandoning the failed epoch'],
      cpsCapExponent: 741, clickCapExponent: 800, marketCreditCapExponent: 762,
      buildingRefundCapExponent: 500,
      wrinklerStorageCandidateCapExponent: 850, wrinklerPayoutCandidateCapExponent: 854,
      gardenCreditCapExponent: 755,
      open: 'The wrinkler storage barrier and native rounding of all listed expressions require source refinement.',
    },
    counterInvariant: {
      ordinaryCreditCapExponent: 880, beforeChocolateCapExponent: 936,
      oneChocolateCreditCapExponent: 932, afterChocolateCapExponent: 938,
      argument: 'Every ordinary credit preserves the applicable binary64 barrier, irrespective of the number of inputs. Refunds use earned=max(bank,earned). The one Chocolate egg purchase changes the barrier from2^936 to2^938. The end-earned bound2^940 then follows.',
    },
  },
  retryReset: {
    source: ['main.js:3492-3618', 'minigameGarden.js:M.reset', 'minigameMarket.js:M.reset'],
    discarded: ['current non-prestige upgrade ownership except selected permanent slots', 'cookies and cookiesEarned', 'building amounts and highest counts', 'cookiesPsRawHighest', 'seasonUses', 'research and pledge state', 'dragon and Santa levels', 'market holdings and profit'],
    retained: ['normal achievements', 'building levels', 'heavenly upgrades', 'previously unlocked Garden seed knowledge', 'historical access union'],
    program: 'Leave permanent slots empty for this route. On a failed fixed-deadline epoch, ordinarily ascend and reincarnate, clear controller ownership caches, and rebuild current ownership from the new public snapshot. Test completion only against current ownership plus the separately defined historical-access union.',
    open: ['Prove the complete reset/rebuild source transition preserves the route entry invariant', 'Do not count a discarded owned upgrade as completed after reset'],
  },
  open: [
    'Prove the native production expressions are bounded by the extracted catalogue algebra, including all binary64 rounding.',
    'Bound every Earn, direct bank addition and earned=max(bank,earned) path during an epoch by2^940; a raw-CpS bound alone does not do this.',
    'Prove a uniform funded rebuild reaches the chosen board without exceeding the epoch/frame bounds.',
    'Compose the source reset and completion projection; current-upgrade ownership is not persistent.',
  ],
});

export function auditCollectionEnvelopeCatalog(options = {}) {
  const runtime = createRuntime({ ...options, diagnosticMode: true, recordAudit: false });
  const G = runtime.Game;
  const digest = value => createHash('sha256').update(String(value)).digest('hex');
  const cookieUpgrades = Array.from(G.cookieUpgrades);
  const functionalCookies = cookieUpgrades.filter(u => typeof u.power === 'function').map(u => ({
    name: u.name, functionSha256: digest(u.power),
    upperPower: u.name === 'Sugar crystal cookies' ? 25 : 3.9,
    justification: u.name === 'Sugar crystal cookies' ? '5 plus at most20 building types' : '3 from Starlove, multiplied by at most1.3 from Selebrak',
  }));
  const ordinaryCookiePowers = cookieUpgrades.filter(u => typeof u.power !== 'function').map(u => u.power);
  const buildings = Array.from(G.ObjectsById).map(b => ({
    id: b.id, name: b.name, baseCps: Number.isFinite(b.baseCps) ? b.baseCps : null,
    ordinaryTierCount: Object.values(b.tieredUpgrades).filter(u => !G.Tiers[u.tier].special).length,
    synergyCount: b.synergies.length, cpsFunctionSha256: digest(b.cps),
  }));
  const facts = {
    buildingTypes: buildings.length, cookieFactors: G.cookieUpgrades.length,
    maximumFixedCookiePower: Math.max(...ordinaryCookiePowers),
    functionalCookieFactors: functionalCookies.length,
    achievementDefinitions: Object.keys(G.Achievements).length,
    kittenPoolEntries: G.UpgradesByPool.kitten.length,
    grandmaSynergies: G.GrandmaSynergies.length,
    maximumOrdinaryTiers: Math.max(...buildings.map(b => b.ordinaryTierCount)),
    maximumBuildingSynergies: Math.max(...buildings.map(b => b.synergyCount)),
    maximumOrdinaryBaseCps: Math.max(...buildings.filter(b => b.id >= 2).map(b => b.baseCps)),
  };
  const checks = {
    cookieProduct: 5n ** 248n < (2n ** 83n) * (4n ** 248n),
    gardenBoost: 6n ** 8n < 8n * (5n ** 8n),
    gardenPositiveEffect: 100 + 36 * 4 * 8 < 1600,
    gardenMilk: 1000 + 36 * 2 * 8 < 2000,
    kittenSingle: 1 + 26 * 0.2 * 3 < 32,
    ordinarySumBits: 49 + 30 + 35 + 1 + 5 + 1 + 1 + 11 + 5 === 138,
    rawBudget: 140 + 83 + 90 + 40 === 353,
    resetCapNativeAddition: 2 ** 1000 + 2 ** 940 === 2 ** 1000,
    resetCapFinite: Number.isFinite(2 ** 1000),
    epochClockRoom: (231 + 1 + 122445 * 1032) * 60 + 4925 * 300 < 2 ** 50,
  };
  if (Object.values(checks).some(value => !value)) throw new Error('Collection envelope arithmetic failed');
  if (facts.cookieFactors !== 248 || facts.achievementDefinitions !== 643 || facts.kittenPoolEntries !== 18 ||
      facts.grandmaSynergies !== 18 || facts.maximumOrdinaryTiers !== 15 || facts.maximumBuildingSynergies !== 5 ||
      facts.maximumFixedCookiePower !== 13 || !Number.isFinite(facts.maximumOrdinaryBaseCps) ||
      facts.maximumOrdinaryBaseCps >= 2 ** 49 || functionalCookies.length !== 8)
    throw new Error('Pinned production catalogue changed');
  return { schemaVersion: 1, ...COLLECTION_ENVELOPE, sourceHashes: runtime.source.hashes,
    facts, functionalCookies, buildings, arithmeticChecks: checks,
    sourceFunctions: Object.fromEntries(['CalculateGains', 'GetTieredCpsMult', 'GetHeavenlyMultiplier', 'ComputeCps', 'Reset', 'gainBuff', 'updateBuffs']
      .map(name => [name, digest(G[name])])) };
}

/** A reset implication probe from an explicitly funded/seeded entry fixture.
 * All purchases, levels, ascension and reincarnation below use the legal action
 * adapter. Entry resources and the novel seed are premises, not earned here.
 */
export function probeCollectionReset(options = {}) {
  const runtime = createRuntime({ ...options, diagnosticMode: true, recordAudit: false });
  const G = runtime.Game, actions = [];
  const act = action => { actions.push(action); return runtime.act(action, { observe: false }); };
  const wait = milliseconds => act({ type: 'wait', milliseconds });
  wait(200);
  G.cookies = G.cookiesEarned = 2 ** 90;
  wait(5100);
  G.lumps = 136;
  for (const [name, level] of [['Cursor', 12], ['Farm', 10], ['Temple', 1], ['Wizard tower', 1], ['Bank', 1]]) {
    act({ type: 'buy-building', id: G.Objects[name].id, amount: 1 });
    for (let i = 0; i < level; i++) {
      act({ type: 'level-building', id: G.Objects[name].id });
      if (G.promptOn) act({ type: 'prompt', option: 0 });
    }
  }
  wait(100);
  const garden = G.Objects.Farm.minigame;
  garden.plants.thumbcorn.unlocked = 1;
  garden.computeMatures();
  act({ type: 'buy-upgrade', id: G.Upgrades['Reinforced index finger'].id });
  const project = () => ({
    currentOwned: !!G.Has('Reinforced index finger'), legacyOwned: !!G.Has('Legacy'),
    clickAchievement: !!G.HasAchiev('Click'),
    levels: Object.fromEntries(['Cursor', 'Farm', 'Temple', 'Wizard tower', 'Bank'].map(name => [name, G.Objects[name].level])),
    amounts: Object.fromEntries(['Cursor', 'Farm', 'Temple', 'Wizard tower', 'Bank'].map(name => [name, G.Objects[name].amount])),
    thumbcornUnlocked: !!garden.plants.thumbcorn.unlocked,
    seasonUses: G.seasonUses, santaLevel: G.santaLevel, dragonLevel: G.dragonLevel,
    rawCpsHighest: G.cookiesPsRawHighest, cookiesReset: G.cookiesReset,
    lumps: G.lumps, onAscend: !!G.OnAscend,
  });
  const before = project();
  act({ type: 'ascend' }); wait(5100);
  act({ type: 'buy-upgrade', id: G.Upgrades.Legacy.id });
  act({ type: 'reincarnate', mode: 0 }); wait(5100);
  const after = project();
  // A controller must rebuild from this current snapshot. Deliberately retain
  // only achievements and access history, never the earlier ownership list.
  const postResetSnapshot = runtime.snapshot();
  const rebuiltOwnership = Object.fromEntries(Object.entries(postResetSnapshot.upgrades).map(([name, u]) => [name, !!u.bought]));
  return { scope: 'native-reset-implication-from-explicit-entry-premises', sourceHashes: runtime.source.hashes,
    premises: ['bank and earned2^90 after normal startup', '136 spendable lumps after lump activation', 'Thumbcorn seed unlocked before reset'],
    before, after, rebuiltOwnership: { 'Reinforced index finger': rebuiltOwnership['Reinforced index finger'], Legacy: rebuiltOwnership.Legacy },
    actionCount: actions.length, actionsSha256: createHash('sha256').update(JSON.stringify(actions)).digest('hex') };
}

/** Synthetic source/DOM implication probe, not a reachable-trajectory claim.
 * It isolates the retained display style across native market reset when drawT
 * can no longer advance to a multiple of ten.
 */
export function probeMarketOfficeResetTail(options = {}) {
  const runtime = createRuntime({ ...options, diagnosticMode: true, recordAudit: false });
  const G = runtime.Game;
  const act = action => runtime.act(action, { observe: false });
  act({ type: 'wait', milliseconds: 200 });
  G.cookies = G.cookiesEarned = 2 ** 90;
  act({ type: 'wait', milliseconds: 5100 });
  G.lumps = 1;
  act({ type: 'buy-building', id: G.Objects.Bank.id, amount: 1 });
  act({ type: 'level-building', id: G.Objects.Bank.id });
  if (G.promptOn) act({ type: 'prompt', option: 0 });
  act({ type: 'wait', milliseconds: 100 });
  const M = G.Objects.Bank.minigame, button = runtime.context.l('bankOfficeUpgrade');
  const cases = [];
  for (const officeLevel of [5, 4]) {
    M.officeLevel = officeLevel;
    G.drawT = 10;
    M.draw();
    const before = { officeLevel: M.officeLevel, display: button.style.display ?? null };
    G.drawT = 2 ** 53;
    M.reset();
    M.draw();
    cases.push({ before, after: { officeLevel: M.officeLevel, display: button.style.display ?? null,
      drawT: G.drawT, drawTModulo10: G.drawT % 10 } });
  }
  return { scope: 'synthetic-native-market-DOM-reset-implication', sourceHashes: runtime.source.hashes,
    premises: ['bank and earned2^90 after normal startup', 'one lump to open the Bank minigame',
      'office level5 or4 is an assigned entry condition', 'drawT2^53 is an assigned saturation condition'],
    cases,
    doesNotProve: ['new-save reachability of the assigned states', 'a browser hit-test', 'global nonattainment'],
    routeRepair: 'Use office4 and750 highest of each goods building for storage>=1000. Defer office5 until the final deterministic completion step, so failed epochs never hide the office upgrade button.' };
}

const EARN_TREATMENTS = Object.freeze({
  'main.js:3369': 'offline save-load reward: absent after the empty new-save startup; no reload in this route',
  'main.js:4496': 'golden lump: reward <=86400*currentCpS; no more than one natural harvest per second',
  'main.js:4780': 'big-cookie click: only during the bounded refill phase after golden buffs expire',
  'main.js:5537': 'Lucky: <=900*currentCpS*effectMultiplier+13, at most7777 leader pops',
  'main.js:5591': 'chain: <=max(7,21600*currentCpS*effectMultiplier), included in7777 leader pops',
  'main.js:5600': 'storm drop: ignored by this route; only timer-created leaders are clicked',
  'main.js:5793': 'reindeer: <=max(25,60*currentCpS)*2*GardenReindeerGain; the frosting and Garden factors multiply the25-cookie floor too; at most200 per successful epoch',
  'main.js:7646': 'fortune CpS: <=3600*currentCpS; consumed at most once per epoch',
  'main.js:10402': 'Chocolate egg: one multiplicative bank increment<=0.05*bank after purchase',
  'main.js:12036': 'gift: only the displayed self-addressed one-cookie gift is redeemed',
  'main.js:14513': 'wrinkler: stored counter receives <=currentCpS/30 per frame, rounds below its candidate2^850 barrier, and is multiplied by digestive factors with product<8 before payout; source refinement remains open',
  'main.js:15894': 'debug reward: unavailable under the no-debug route premise',
  'main.js:16275': 'passive income: one currentCpS/30 addition per native logic frame',
  'main.js:16487': 'You win a cookie: one cookie, only once for the persistent achievement',
  'minigameGarden.js:148': 'Bakeberry harvest: <=1800*currentCpS',
  'minigameGarden.js:174': 'Chocoroot harvest: <=180*currentCpS',
  'minigameGarden.js:199': 'White chocoroot harvest: <=180*currentCpS',
  'minigameGarden.js:350': 'Queenbeet harvest: <=3600*currentCpS',
  'minigameGarden.js:397': 'Duketater harvest: <=7200*currentCpS',
  'minigameGarden.js:424': 'Crumbspore death: <=60*currentCpS; at most36 deaths per Garden tick',
  'minigameGarden.js:449': 'Doughshroom death: <=300*currentCpS; at most36 deaths per Garden tick',
  'minigameGrimoire.js:23': 'Conjure baked goods: not cast; this route uses only Diminish Ineptitude',
});

/** Inventory direct AST sites, excluding comments and generated-handler text.
 * This is a syntactic audit, not a proof that no alias/dynamic call can earn.
 */
export function auditEpochEarnSites(sourceDirectory) {
  const source = loadGameSource(sourceDirectory), sites = [];
  const member = node => node?.type === 'MemberExpression' && node.object?.type === 'Identifier' && node.object.name === 'Game'
    ? (node.computed ? node.property?.value : node.property?.name) : undefined;
  for (const filename of ['main.js', 'minigameGarden.js', 'minigameMarket.js', 'minigameGrimoire.js', 'minigamePantheon.js']) {
    const code = source.sources[filename], ast = acorn.parse(code, { ecmaVersion: 2020, locations: true });
    const pending = [ast];
    while (pending.length) {
      const node = pending.pop();
      const earn = node.type === 'CallExpression' && member(node.callee) === 'Earn';
      const field = node.type === 'AssignmentExpression' ? member(node.left) : node.type === 'UpdateExpression' ? member(node.argument) : undefined;
      if (earn || ['cookies', 'cookiesEarned'].includes(field)) {
        const key = `${filename}:${node.loc.start.line}`, expression = code.slice(node.start, node.end);
        const treatment = earn ? EARN_TREATMENTS[key] :
          ['main.js:7873', 'main.js:7874'].includes(key) ? 'building sale: every refund<=2^500 under the route board bound, followed by earned=max(bank,earned); native counter barriers handle any finite number of Godzamok cycles' :
          ['minigameMarket.js:252', 'minigameMarket.js:253'].includes(key) ? 'market sale: <=rawCpSHighest*250180*1000 per trade, followed by earned=max(bank,earned)' :
          ['main.js:4657', 'main.js:4658'].includes(key) ? 'Game.Earn primitive: each classified credit must preserve the active native counter barrier; do not replace repeated rounded addition by an exact aggregate sum' :
          ['main.js:4662', 'main.js:4666', 'main.js:4667', 'main.js:4668', 'main.js:4669'].includes(key) ? 'spend/dissolve: no positive increment for nonnegative amounts' :
          ['main.js:3009', 'main.js:3010'].includes(key) ? 'save parsing: only empty new-save startup; no load/reload retry' :
          ['main.js:2022', 'main.js:2023', 'main.js:3497', 'main.js:3498', 'main.js:16317'].includes(key) ? 'zero initialization/reset or NaN recovery; adds no positive cookies' : undefined;
        if (!treatment) throw new Error(`Unclassified native income site ${key}: ${expression}`);
        sites.push({ filename, line: node.loc.start.line, sourceStart: node.start, sourceEnd: node.end,
          kind: earn ? 'Earn-call' : 'counter-write', expression,
          expressionSha256: createHash('sha256').update(expression).digest('hex'), treatment });
      }
      for (const [key, value] of Object.entries(node)) {
        if (key === 'loc') continue;
        if (Array.isArray(value)) {
          for (const child of value) if (child?.type) pending.push(child);
        } else if (value?.type) pending.push(value);
      }
    }
  }
  sites.sort((a, b) => a.filename.localeCompare(b.filename) || a.line - b.line);
  const earnCalls = sites.filter(site => site.kind === 'Earn-call');
  if (earnCalls.length !== Object.keys(EARN_TREATMENTS).length) throw new Error('Native Earn inventory count changed');
  return { scope: 'direct-AST-income-site-inventory-not-callback-bound-proof', sourceHashes: source.hashes,
    earnCalls: earnCalls.length, counterWrites: sites.length - earnCalls.length, sites,
    open: ['Refine every listed callback bound and prove the route control guards that exclude unused callbacks', 'Cover generated handlers and alias/dynamic dispatch through the full source interpreter', 'Compose native rounded counter barriers and the one Chocolate phase change to prove earned<=2^940'] };
}
