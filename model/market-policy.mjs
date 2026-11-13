/** A constructive Stock Market baseline. It does not claim optimal timing. */
export const MARKET_ACHIEVEMENTS = Object.freeze([
  'Initial public offering', 'Rookie numbers', 'No nobility in poverty',
  'Full warehouses', 'Make my day', 'Buy buy buy', 'Pyramid scheme', 'Liquid assets',
]);
export const MARKET_ASCENSION_ACHIEVEMENT = 'Debt evasion';

/** Invert the native integer storage threshold, including its final ceiling. */
export function requiredMarketBuildingHighest(capacity, officeLevel, buildingLevel) {
  if (!Number.isSafeInteger(capacity) || capacity < 0 || !Number.isInteger(officeLevel) || officeLevel < 0 || officeLevel > 5
    || !Number.isSafeInteger(buildingLevel) || buildingLevel < 0) throw new Error('Invalid market storage requirement');
  const bonus = [0, 25, 75, 150, 250, 250][officeLevel];
  const factor = officeLevel === 5 ? 1.5 : 1;
  let highest = Math.max(0, Math.floor((capacity - bonus - buildingLevel * 10 - 1) / factor) + 1);
  const nativeCapacity = amount => Math.ceil(amount * factor + bonus + buildingLevel * 10);
  // Preserve the native binary64 boundary if a large integer quote rounds.
  while (nativeCapacity(highest) < capacity) highest++;
  while (highest > 0 && nativeCapacity(highest - 1) >= capacity) highest--;
  return highest;
}

function marketDecision(observation, availableActions, memory, achievements, requiredHighest) {
  memory ||= {};
  const config = { brokerTarget: 50, buyFactor: 0.65, sellFactor: 1.05,
    maxWaitMs: 1000, maxDecisions: null, prepareDebtEvasion: false, collectTrades: true,
    maximumOffice: 5, maximumHolding: null, maximumTransaction: null, ...(memory.config || {}) };
  // A policy must remain available on long random waiting paths. Finite caps
  // are opt-in diagnostics; the evaluator owns the experiment's work budget.
  const nextMemory = { ...memory, config,
    decisions: config.maxDecisions === null ? null : (memory.decisions || 0) + 1 };
  const result = (status, goal, reason, action = null, extra = {}) =>
    ({ status, goal, reason, action, memory: nextMemory, ...extra });
  if (!Number.isInteger(config.maximumOffice) || config.maximumOffice < 2 || config.maximumOffice > 5
    || [config.maximumHolding, config.maximumTransaction].some(x => x !== null && (!Number.isSafeInteger(x) || x < 1000 || x >= 10000))
    || !Number.isSafeInteger(config.brokerTarget) || config.brokerTarget < 0 || config.brokerTarget > 500
    || !(config.buyFactor > 0 && config.sellFactor > config.buyFactor * 1.2)
    || !Number.isFinite(config.sellFactor) || typeof config.collectTrades !== 'boolean' || !(config.maxWaitMs > 0 && Number.isFinite(config.maxWaitMs))
    || config.maxDecisions !== null && (!Number.isSafeInteger(config.maxDecisions) || config.maxDecisions < 1)) {
    return result('blocked', 'Market configuration', 'Use finite limits and a sale threshold above the maximum purchase overhead.');
  }
  if (config.maxDecisions !== null && nextMemory.decisions > config.maxDecisions) return result('budget-exhausted', 'Market controller', 'The configured diagnostic decision limit was reached.');
  const M = observation.market;
  if (!M?.ready) return result('needs-resources', 'Stock Market access', 'Bank level 1 and the loaded Stock Market are required.', null, { building: 'Bank', level: 1 });
  if (observation.progression?.onAscend || observation.progression?.ascensionMode !== 0
    || observation.progression?.ascendTimer > 0 || observation.progression?.reincarnateTimer > 0) {
    return result('blocked', 'Active Stock Market', 'The controller requires an active normal run.');
  }
  if (observation.controls?.promptOn) return result('blocked', 'Market control', 'Resolve the current unrelated prompt first.');
  if (M.goods?.length !== 18 || new Set(M.goods.map(g => g.id)).size !== 18
    || M.goods.some(g => !Number.isInteger(g.id) || g.id < 0 || g.id > 17
      || !(g.price > 0 && Number.isFinite(g.price)) || !(g.stock >= 0 && Number.isSafeInteger(g.stock))
      || !(g.maxStock >= 0 && Number.isSafeInteger(g.maxStock))
      || !(g.buyCookiePrice > 0 && Number.isFinite(g.buyCookiePrice)))) {
    return result('blocked', 'Pinned market catalogue', 'The observed prices, storage, or goods do not match the supported market.');
  }
  const won = name => !!observation.achievements?.[name];
  const officeTarget = config.collectTrades ? config.maximumOffice : 2;
  const missing = achievements.filter(name => !won(name) && (name !== 'Pyramid scheme' || officeTarget === 5));
  const complete = () => result(officeTarget === 5 ? 'complete' : 'prepared', 'Market trading and offices',
    officeTarget === 5 ? 'All eight trading and office achievements are won, and the current office is fully upgraded.'
      : 'The configured trades are complete. Keep the final office upgrade for the release phase.');
  // A closed panel needs opening only when this controller will use it.
  // Completed market work must not delay unrelated completion purchases.
  if (!missing.length && M.officeLevel >= officeTarget && (!config.prepareDebtEvasion || won('Debt evasion'))) {
    return complete();
  }
  if (!config.collectTrades && M.officeLevel >= 2) return result('prepared', 'Loan access',
    'The first loan is unlocked. Defer further market purchases until the final collection run.');
  if (M.open === false) return result('acting', 'Market control', 'Open the native market panel before its controls are used.', { type: 'minigame-open', id: M.buildingId ?? 5 });
  const wait = (goal, reason) => result('waiting', goal, reason, { type: 'wait',
    milliseconds: Math.max(1, Math.min(config.maxWaitMs, M.nextTickMs > 0 ? M.nextTickMs : 1000 / 30)) },
  { wakeAfterMs: M.nextTickMs });
  const buy = (good, amount, goal, reason) => result('acting', goal, reason,
    { type: 'market-buy', id: good.id, amount });
  const sell = (good, goal, reason) => result('acting', goal, reason,
    { type: 'market-sell', id: good.id, amount: config.maximumTransaction === null ? 10000 : Math.min(config.maximumTransaction, good.stock) }); // Native All only in the unrestricted baseline.
  const canBuy = good => good.active && good.visible !== false && good.canBuy !== false;
  const canSell = good => good.active && good.visible !== false && good.canSell !== false && good.stock > 0;
  const enoughCookies = (good, n) => observation.cookies >= good.buyCookiePrice * n;
  const exactBuyFits = (good, n) => n > 0 && n < 10000 && canBuy(good)
    && good.stock + n <= Math.min(good.maxStock, config.maximumHolding ?? Infinity)
    && n <= (config.maximumTransaction ?? Infinity) && enoughCookies(good, n);
  // Guard against a rounded-down product at the native >= 86400 boundary.
  const dayUnits = price => { const n = Math.ceil(86400 / price); return price * n >= 86400 ? n : n + 1; };
  const goods = [...M.goods].sort((a, b) => b.price - a.price || a.id - b.id);
  const storageRequest = (good, capacity) => {
    const buildingId = good.buildingId ?? good.id + 2;
    const building = observation.shop?.buildings?.find(b => b.id === buildingId);
    const level = building?.level ?? good.buildingLevel ?? 0;
    // One highest-owned building is also needed to unlock the good, even if
    // office and level bonuses alone provide the requested storage capacity.
    const highest = Math.max(1, requiredHighest(capacity, M.officeLevel, level));
    return { good: good.id, buildingId, ...(building ? { building: building.name } : {}),
      amount: highest, requiredCapacity: capacity, requiredBuildingHighest: highest };
  };

  let officeNeed = null;
  // The second office unlocks the first loan. Further offices, brokers and
  // holdings are lost on ascension, so the composed controller can defer them.
  if (M.officeLevel < officeTarget) {
    const office = M.offices?.[M.officeLevel];
    if (!office || !(office.cursorAmount > 0 && office.cursorLevel > 0)) return result('blocked', 'Market offices', 'The next office cost is absent.');
    const cursorLevel = observation.progression?.buildingLevels?.Cursor || 0;
    const cursorAmount = observation.progression?.buildingAmounts?.Cursor || 0;
    if (cursorLevel >= office.cursorLevel && cursorAmount >= office.cursorAmount) {
      if (M.officeUpgradeVisible === false) return wait('Market offices', 'Wait for the native office control to become visible.');
      return result('acting', config.collectTrades ? 'Pyramid scheme' : 'Loan access', 'Sacrifice the required cursors to upgrade the office.', { type: 'market-office' });
    }
    officeNeed = cursorLevel < office.cursorLevel
      ? result('needs-level', 'Market offices', 'The next office requires a higher Cursor level.', null, { building: 'Cursor', level: office.cursorLevel })
      : result('needs-resources', 'Market offices', 'The next office requires more current cursors.', null, { building: 'Cursor', amount: office.cursorAmount });
  }

  if (!config.collectTrades) return officeNeed || result('prepared', 'Loan access',
    'The first loan is unlocked. Defer further market purchases until the final collection run.');

  if (!missing.length && M.officeLevel >= officeTarget) {
    if (config.prepareDebtEvasion && !won('Debt evasion')) {
      if (M.loans?.some(loan => loan.activeFrames > 0)) {
        return result('needs-ascension', 'Debt evasion', 'Ascend before the active loan enters its interest period. Coordinate this with the other run goals.');
      }
      const loan = M.loans?.find(loan => loan.unlocked && !loan.activeFrames && !loan.interestFrames);
      if (!loan) return wait('Debt evasion', 'Wait for a loan to leave its interest period.');
      if (loan.visible === false) return wait('Debt evasion', 'Wait for the native loan control to become visible.');
      return result('acting', 'Debt evasion', 'Start an available loan for the planned ascension.', { type: 'market-loan', id: loan.id });
    }
    return complete();
  }

  // Brokers cost cookies but do not subtract from the displayed market profit.
  if (!won('Liquid assets') && M.brokers < Math.min(config.brokerTarget, M.maxBrokers)
    && M.brokerVisible !== false && Number.isFinite(M.brokerPrice) && observation.cookies >= M.brokerPrice) {
    return result('acting', 'Trading overhead', 'Hire a broker within the configured limit.', { type: 'market-broker' });
  }

  if (!won('Buy buy buy')) {
    for (const good of goods) {
      const n = dayUnits(good.price * M.overheadMultiplier);
      if (exactBuyFits(good, n)) return buy(good, n, 'Buy buy buy', 'Buy at least 86400 market dollars of stock in one transaction.');
    }
  }

  // Keep these holdings together until the native all-goods checks award them.
  if (!won('No nobility in poverty') || !won('Rookie numbers')) {
    const deficient = goods.filter(good => good.stock < 500);
    for (const good of deficient) {
      if (exactBuyFits(good, 500 - good.stock)) return buy(good, 500 - good.stock, 'No nobility in poverty', 'Bring this holding to 500 units without selling the other holdings.');
    }
    if (!deficient.length) {
      const trigger = goods.find(good => exactBuyFits(good, 1));
      if (trigger) return buy(trigger, 1, 'No nobility in poverty', 'Let the native purchase callback check all holdings.');
    }
    const locked = deficient.find(good => !good.active || good.maxStock < 500);
    if (locked) return officeNeed || result('needs-resources', 'Market warehouses', 'This good must be unlocked with storage for 500 units.', null,
      storageRequest(locked, 500));
    const unaffordable = deficient.find(good => !enoughCookies(good, 500 - good.stock));
    if (unaffordable) return result('needs-resources', 'No nobility in poverty', 'The next holding requires more cookies.', null,
      { requiredCookies: unaffordable.buyCookiePrice * (500 - unaffordable.stock), good: unaffordable.id });
    return wait('No nobility in poverty', 'Wait for the restriction on buying after a sale to end.');
  }

  if (!won('Full warehouses')) {
    const good = goods.find(g => exactBuyFits(g, Math.max(1, 1000 - g.stock)));
    if (good) return buy(good, Math.max(1, 1000 - good.stock), 'Full warehouses', 'Hold at least 1000 units of one stock.');
    if (!goods.some(g => g.active && g.maxStock >= 1000)) {
      // Choose the cheapest next building. This ensures an explicit resource
      // request; it does not claim to minimize the full acquisition cost.
      const candidate = [...goods].sort((a, b) => {
        const price = g => observation.shop?.buildings?.find(x => x.id === (g.buildingId ?? g.id + 2))?.buy1price ?? Infinity;
        return price(a) - price(b) || a.id - b.id;
      })[0];
      return officeNeed || result('needs-resources', 'Full warehouses', 'At least one good requires storage for 1000 units.', null, storageRequest(candidate, 1000));
    }
    const fill = goods.filter(g => canBuy(g) && g.maxStock >= 1000 && g.stock < 1000)
      .sort((a,b) => a.buyCookiePrice * (1000-a.stock) - b.buyCookiePrice * (1000-b.stock) || a.id-b.id)[0];
    if (fill) return result('needs-resources', 'Full warehouses', 'Reserve the cookies needed to fill one warehouse to 1000 units.', null,
      { good: fill.id, requiredCookies: fill.buyCookiePrice * (1000-fill.stock) });
    return wait('Full warehouses', 'Wait for the restriction on buying after a sale to end.');
  }

  if (!won('Make my day')) {
    const sale = goods.find(g => canSell(g) && g.price * g.stock >= 86400);
    if (sale) return sell(sale, 'Make my day', 'Sell at least 86400 market dollars of stock in one transaction.');
    // One startup trade may lose overhead. Later threshold trades recover it.
    const purchase = goods.find(g => exactBuyFits(g, dayUnits(g.price) - g.stock));
    if (purchase) return buy(purchase, dayUnits(purchase.price) - purchase.stock, 'Make my day', 'Build a holding large enough for the required single sale.');
    // Selling below the achievement threshold could repeat a losing startup
    // trade forever. Keep these holdings until one sale can win the goal.
    // Each good can receive at most its finite storage capacity before then.
    return wait('Make my day', 'Keep the startup holdings until one sale is worth at least 86400 market dollars.');
  }

  // The fixed thresholds use only a displayed price and the known Bank level.
  // A new round trip buys at <= 0.65*r, including <=20% overhead, and sells at
  // >= 1.05*r. This is a positive margin, not a bound on the waiting time.
  for (const good of goods) {
    const resting = 10 + 10 * good.id + M.bankLevel - 1;
    if (canSell(good) && good.price >= config.sellFactor * resting) return sell(good, 'Liquid assets', 'Sell above the fixed sale threshold.');
  }
  if (!won('Liquid assets')) {
    for (const good of goods) {
      const resting = 10 + 10 * good.id + M.bankLevel - 1;
      if (canBuy(good) && good.stock < Math.min(good.maxStock, config.maximumHolding ?? Infinity) && good.price <= config.buyFactor * resting
        && enoughCookies(good, 1)) {
        const amount = config.maximumHolding === null && config.maximumTransaction === null ? 10000
          : Math.min(config.maximumTransaction ?? 9999, Math.min(good.maxStock, config.maximumHolding ?? Infinity) - good.stock, Math.floor(observation.cookies / good.buyCookiePrice));
        if (amount > 0) return buy(good, amount, 'Liquid assets', 'Buy below the fixed purchase threshold within the configured holding and transaction limits.');
      }
    }
  }
  if (officeNeed) return officeNeed;
  return wait(missing[0] || 'Market goals', 'Wait for the next visible market prices or trade permission.');
}

export function decideMarketAction(observation, memory = {}, options = {}) {
  return marketDecision(observation, [], { ...memory, config: { ...(memory.config || {}), ...options } }, MARKET_ACHIEVEMENTS, requiredMarketBuildingHighest);
}

/** Self-contained source for the observation-only policy evaluator. */
export function marketPolicySource(options = {}) {
  return `(function(observation, availableActions, memory) {
    const decision = ${marketDecision.toString()};
    return decision(observation, availableActions, {...(memory || {}), config: {...${JSON.stringify(options)}, ...((memory || {}).config || {})}},
      ${JSON.stringify(MARKET_ACHIEVEMENTS)}, ${requiredMarketBuildingHighest.toString()});
  })`;
}
