import { createRuntime } from './runtime.mjs';

// These probes test implications from stated resource premises. They do not
// supply those resources through a new-save policy or prove an expected time.
export const INCOME_LADDER = Object.freeze([
  { bankExponent: 90, count: 0, cursorCount: 10, targetExponent: 140, ascend: false },
  { bankExponent: 140, count: 200, cursorCount: 200, targetExponent: 190, ascend: true },
  { bankExponent: 190, count: 450, cursorCount: 450, targetExponent: 220, ascend: true },
  { bankExponent: 220, count: 600, cursorCount: 1000, targetExponent: 240, ascend: false },
  { bankExponent: 240, count: 700, cursorCount: 1000, targetExponent: 270, ascend: true },
  { bankExponent: 270, count: 700, cursorCount: 1000, targetExponent: 280, ascend: true },
  { bankExponent: 280, count: 700, cursorCount: 1000, targetExponent: 286, ascend: true },
  { bankExponent: 286, count: 700, cursorCount: 1000, targetExponent: 286, ascend: true },
]);

export function nextPositiveFloat(value, direction = 1) {
  if (!(value > 0 && Number.isFinite(value)) || ![-1, 1].includes(direction))
    throw new Error('A finite positive value and a direction of -1 or 1 are required');
  const data = new DataView(new ArrayBuffer(8));
  data.setFloat64(0, value);
  data.setBigUint64(0, data.getBigUint64(0) + BigInt(direction));
  return data.getFloat64(0);
}

/** Native probes; every non-native resource or macro premise is in the result. */
export function probeFundedIncomeLadder({ sourceDirectory, randomSeed = 1 } = {}) {
  const runtime = createRuntime({ sourceDirectory, randomSeed, diagnosticMode: true, recordAudit: false });
  const G = runtime.Game, rows = [], premises = [];
  const act = action => runtime.act(action, { observe: false });
  const wait = milliseconds => act({ type: 'wait', milliseconds });
  const funding = (exponent, reason) => {
    premises.push({ kind: 'funding', exponent, reason, priorBank: G.cookies, priorEarned: G.cookiesEarned });
    G.cookies = 2 ** exponent;
    G.cookiesEarned = Math.max(G.cookiesEarned, G.cookies);
  };
  let ledger;
  const buyBuilding = (building, amount) => {
    const price = building.getSumPrice(amount), before = G.cookies;
    act({ type: 'buy-building', id: building.id, amount });
    ledger.push({ kind: 'building', id: building.id, name: building.name, amount, price, bankBefore: before, bankAfter: G.cookies, nativeDebit: before - G.cookies });
  };
  const buyUpgrade = upgrade => {
    const price = upgrade.getPrice(), before = G.cookies;
    act({ type: 'buy-upgrade', id: upgrade.id });
    ledger.push({ kind: 'upgrade', id: upgrade.id, name: upgrade.name, price, bankBefore: before, bankAfter: G.cookies, nativeDebit: before - G.cookies });
  };
  const fill = (building, count) => {
    while (building.amount < count) buyBuilding(building, Math.min(100, count - building.amount));
  };
  const buyOrdinary = () => {
    for (let pass = 0; pass < 30; pass++) {
      // These unlock conditions run every five seconds in the pinned source.
      wait(5100);
      let bought = 0;
      for (const u of Object.values(G.UpgradesById)) {
        if (u.bought || !u.unlocked || !['', 'cookie'].includes(u.pool) || u.name === 'Bingo center/Research facility') continue;
        if (u.canBuy() && G.cookies - u.getPrice() >= 2 ** 88) { buyUpgrade(u); bought++; }
      }
      if (!bought) return;
    }
    throw new Error('Native ordinary purchases did not settle within the diagnostic limit');
  };
  const macroEndpoint = () => {
    const temple = G.Objects.Temple;
    if (!temple.level) {
      premises.push({ kind: 'lump', amount: 1, reason: 'One previously harvested lump for Temple level 1' });
      G.lumps = 1;
      act({ type: 'level-building', id: temple.id });
      wait(34);
    }
    const pantheon = temple.minigame;
    if (!pantheon || !temple.minigameLoaded) throw new Error('Native Temple minigame is unavailable');
    if (pantheon.slot[0] !== pantheon.gods.ruin.id) act({ type: 'pantheon-slot', god: 'ruin', slot: 0 });
    fill(G.Objects.Mine, 101);
    const bankBeforeCycle = G.cookies;
    act({ type: 'sell-building', id: G.Objects.Mine.id, amount: 100 });
    buyBuilding(G.Objects.Mine, 100);
    const buff = G.buffs.Devastation;
    if (!buff) throw new Error('The native Godzamok sale did not create Devastation');
    if (G.cookies !== bankBeforeCycle) throw new Error('The native sell/rebuy cycle changed the bank');
    premises.push({ kind: 'macro-endpoint', multiplier: 2 ** 53, bankBeforeCycle, bankAfterCycle: G.cookies,
      reason: 'Endpoint of a finite unit-increment Godzamok loop; its iterations are not executed by this diagnostic' });
    buff.multClick = 2 ** 53;
    G.CalculateGains();
  };
  const clickAtBoundary = exponent => {
    wait(80);
    const saved = { cookies: G.cookies, cookiesEarned: G.cookiesEarned, handmadeCookies: G.handmadeCookies };
    const target = 2 ** exponent, before = nextPositiveFloat(target, -1);
    const amount = G.computedMouseCps;
    for (const name of Object.keys(saved)) G[name] = before;
    const priorClicks = G.cookieClicks;
    act({ type: 'click' });
    const result = { target, before, targetUlp: nextPositiveFloat(target) - target, amount,
      amountOverTargetUlp: amount / (nextPositiveFloat(target) - target),
      accepted: G.cookieClicks === priorClicks + 1,
      counters: Object.fromEntries(Object.keys(saved).map(name => [name, { after: G[name], increment: G[name] - before, crossed: G[name] >= target }])) };
    Object.assign(G, saved);
    return result;
  };
  const ascend = () => {
    const earned = G.cookiesEarned, resetCookies = G.cookiesReset;
    act({ type: 'ascend' });
    wait(5100);
    const prestige = G.prestige;
    if (!G.OnAscend || G.AscendTimer) throw new Error('Native ascension did not finish');
    const legacy = G.Upgrades.Legacy;
    if (!legacy.bought) act({ type: 'buy-upgrade', id: legacy.id });
    act({ type: 'reincarnate', mode: 0 });
    wait(5100);
    return { earned, resetCookies, prestige, expectedNativePrestige: Math.floor(G.HowMuchPrestige(resetCookies + earned)), bankAfterReincarnate: G.cookies };
  };

  for (const stage of INCOME_LADDER) {
    ledger = [];
    funding(stage.bankExponent, stage.ascend ? 'Income endpoint assumed before native ascension' : 'Income endpoint assumed before purchases');
    const ascension = stage.ascend ? ascend() : null;
    if (stage.ascend) funding(stage.bankExponent, 'Rebuild funding after native reset is an independent premise');
    wait(5100);
    if (!stage.count) {
      fill(G.Objects.You, 1); fill(G.Objects.Mine, 101); fill(G.Objects.Temple, 1);
    } else for (const building of G.ObjectsById) fill(building, stage.count);
    fill(G.Objects.Cursor, stage.cursorCount);
    // A fresh run has no handmade cookies. These ordinary accepted clicks
    // unlock Plastic mouse without writing upgrade or achievement flags.
    for (let click = 0; G.handmadeCookies < 1000 && click < 1000; click++) { wait(20); act({ type: 'click' }); }
    if (G.handmadeCookies < 1000) throw new Error('Plastic mouse prerequisite was not earned');
    buyOrdinary();
    macroEndpoint();
    wait(80);
    const bankBeforeIncomeClick = G.cookies, earnedBeforeIncomeClick = G.cookiesEarned;
    act({ type: 'click' });
    const incomeClick = { amount: G.computedMouseCps, bankBefore: bankBeforeIncomeClick,
      bankAfter: G.cookies, earnedBefore: earnedBeforeIncomeClick, earnedAfter: G.cookiesEarned };
    // The preceding native click unlocks higher mouse tiers on the next check.
    buyOrdinary();
    macroEndpoint();
    const clickProbe = clickAtBoundary(stage.targetExponent);
    const production = G.ObjectsById.map(building => {
      const threshold = Math.max(...building.productionAchievs.map(goal => goal.pow));
      const increment = building.storedTotalCps * G.globalCpsMult / G.fps;
      const thresholdUlp = nextPositiveFloat(threshold) - threshold;
      return { building: building.name, amount: building.amount, threshold, increment,
        thresholdUlp, incrementOverUlp: increment / thresholdUlp };
    });
    rows.push({ ...stage, ascension, prestige: G.prestige, remainingBank: G.cookies,
      ordinaryUpgrades: G.UpgradesOwned, normalAchievements: G.AchievementsOwned,
      heavenlyPower: G.GetHeavenlyMultiplier(), rawCps: G.cookiesPsRaw, cps: G.cookiesPs,
      nativeClick: G.computedMouseCps, incomeClick, clickProbe, production, purchases: ledger,
      quotedPurchaseCost: ledger.reduce((sum, purchase) => sum + purchase.price, 0),
      nativePurchaseDebit: ledger.reduce((sum, purchase) => sum + purchase.nativeDebit, 0) });
  }

  // This terminal diagnostic cannot influence a later purchase stage. It tests
  // the actual Logic update at each building's highest production threshold.
  const boundaryCounters = G.ObjectsById.map(building => {
    const threshold = Math.max(...building.productionAchievs.map(goal => goal.pow));
    const before = nextPositiveFloat(threshold, -1);
    building.totalCookies = before;
    return { building: building.name, threshold, before };
  });
  const beforeTick = G.T;
  wait(34);
  const productionProbe = { nativeTicks: G.T - beforeTick,
    counters: boundaryCounters.map((entry, id) => ({ ...entry, after: G.ObjectsById[id].totalCookies,
      crossed: G.ObjectsById[id].totalCookies >= entry.threshold })) };
  return { schemaVersion: 1, scope: 'funded-native-implications-only',
    doesNotProve: ['new-save reachability', 'funding or rebuild income', 'execution of the large Godzamok loops', 'stochastic completion', 'optimality'],
    sourceHashes: runtime.source.hashes, randomSeed, premises, rows, productionProbe,
    maxRawCpsGoal: G.CpsAchievements.at(-1).threshold };
}
