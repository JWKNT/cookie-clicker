/** Native ascension milestones. This constructive schedule is not an optimum. */
export const ASCENSION_DIGIT_GATES = Object.freeze([
  { name: 'Lucky digit', sevens: 1 },
  { name: 'Lucky number', sevens: 2 },
  { name: 'Lucky payout', sevens: 4 },
]);

function nextSevenPrestige(start, count) {
  if (!Number.isFinite(start) || !Number.isInteger(start) || start < 0 || !Number.isInteger(count) || count < 1 || count > 4) return null;
  const text = String(start);
  for (let length = text.length; Number.isSafeInteger(start) && length <= 16; length++) {
    const floor = text.padStart(length, '0');
    const dead = new Set();
    function fill(position, found, tight) {
      if (position === length) return found >= count ? '' : null;
      if (found + length - position < count) return null;
      const key = `${position},${Math.min(found, count)},${tight}`;
      if (dead.has(key)) return null;
      const minimum = Math.max(position === 0 && length > 1 ? 1 : 0, tight ? Number(floor[position]) : 0);
      for (let digit = minimum; digit <= 9; digit++) {
        const tail = fill(position + 1, found + Number(digit === 7), tight && digit === Number(floor[position]));
        if (tail !== null) return String(digit) + tail;
      }
      dead.add(key); return null;
    }
    const digits = fill(0, 0, true);
    if (digits !== null) {
      const value = Number(digits);
      if (Number.isSafeInteger(value)) return value;
      break;
    }
  }
  // Large native prestige levels have a finite binary64 spacing. Request a
  // wide leading-7 interval instead of an unrepresentable next integer. The
  // buffer survives the cube/cube-root rounding used by the pinned engine.
  // This supplies a concrete candidate, not the nearest large-number target.
  // At these magnitudes all three gate costs are small relative to the target;
  // keep four leading sevens so one visit can collect all of them.
  const base = 7777;
  const exponent = Math.floor(Math.log10(Math.max(1, start))) - 3;
  for (let shift = 0; shift < 5; shift++) {
    const nominal = base * 10 ** (exponent + shift);
    const cookies = nominal ** 3 * 1e12 * (1 + 1e-10);
    if (!Number.isFinite(cookies)) continue;
    const nativePrestige = Math.floor(Math.pow(cookies / 1e12, 1 / 3));
    if (nativePrestige >= start && (String(nativePrestige).match(/7/g) || []).length >= count) return nativePrestige;
  }
  return null;
}

export const nextPrestigeWithSevens = nextSevenPrestige;

function ascensionDecision(o, availableActions, memory, gates, nextSevens) {
  memory ||= {};
  const config = { allowReset: false, preserveChallengeAchievements: true, growthFactor: 4,
    assignPermanentSlots: true, finalRunCookies: 1e72, continueGrowthAfterMilestones: true, earlyCountResets: false, earlyResetCookieTarget: null,
    finalGrowthAchievements: ['And a little extra', "Speed's the name of the game (no it's not it's called Cookie Clicker)", "What's not clicking"], ...memory.config };
  const m = { ...memory, config };
  const result = (status, goal, reason, action = null, extra = {}) => ({ status, goal, reason, action, memory: m, ...extra });
  const wait = (goal, reason, milliseconds = 34) => result('waiting', goal, reason, { type: 'wait', milliseconds });
  if (!(Number.isFinite(config.growthFactor) && config.growthFactor > 1) || typeof config.allowReset !== 'boolean'
    || !(Number.isFinite(config.finalRunCookies) && config.finalRunCookies >= 1e57)
    || !(config.earlyResetCookieTarget === null || Number.isFinite(config.earlyResetCookieTarget) && config.earlyResetCookieTarget >= 1e12)
    || !Array.isArray(config.finalGrowthAchievements) || config.finalGrowthAchievements.some(name => typeof name !== 'string')) {
    return result('blocked', 'Ascension configuration', 'Use a finite growth factor above one and an explicit reset permission.');
  }
  const A = o.ascension;
  const P = o.progression;
  if (!A || !P || A.heavenlyUpgrades?.length !== 129) return result('blocked', 'Ascension observation', 'The complete pinned heavenly inventory is required.');
  const heavenly = A.heavenlyUpgrades;
  const byId = new Map(heavenly.map(u => [u.id, u]));
  const byName = new Map(heavenly.map(u => [u.name, u]));
  const won = name => !!o.achievements?.[name];
  const missing = heavenly.filter(u => !u.bought);
  const gate = gates.find(g => !byName.get(g.name)?.bought);
  const countSevens = value => (String(value).match(/7/g) || []).length;
  const parentsMet = u => u.parents.every(id => byId.get(id)?.bought);
  function closure(upgrade) {
    const done = new Set(); const visiting = new Set(); const list = [];
    function visit(u) {
      if (!u || visiting.has(u.id)) throw new Error('Invalid heavenly dependency graph');
      if (u.bought || done.has(u.id)) return;
      visiting.add(u.id);
      for (const id of u.parents) visit(byId.get(id));
      visiting.delete(u.id); done.add(u.id); list.push(u);
    }
    visit(upgrade); return list;
  }
  const slotNames = ['I', 'II', 'III', 'IV', 'V'].map(n => `Permanent upgrade slot ${n}`);
  const candidate = () => [...(A.permanentCandidates || [])].sort((a, b) =>
    Number(/kitten/i.test(b.name)) - Number(/kitten/i.test(a.name)) || b.price - a.price || a.id - b.id)[0];
  if (o.controls?.promptOn) {
    if (m.pendingSlot !== undefined && P.onAscend) {
      const slot = m.pendingSlot; delete m.pendingSlot;
      const chosen = config.assignPermanentSlots ? candidate() : null;
      if (chosen) return result('acting', 'Permanent upgrade', 'Assign a legal owned upgrade in this controller’s slot prompt.', { type: 'permanent-slot', slot, id: chosen.id });
      return result('acting', 'Permanent upgrade', 'Close this controller’s empty assignment prompt.', { type: 'close-prompt' });
    }
    return result('blocked', 'Ascension prompt', 'Resolve the unrelated prompt before changing runs.');
  }
  delete m.pendingSlot;
  if (P.ascendTimer > 0) {
    if (!m.escapeSent) {
      m.escapeSent = true;
      return result('acting', 'Ascension transition', 'Use the native Escape release to finish the ascension animation.', { type: 'key', code: 27, down: false });
    }
    return wait('Ascension transition', 'Allow the next native frame to enter the ascension screen.');
  }
  delete m.escapeSent;
  if (P.reincarnateTimer > 0) return wait('Reincarnation transition', 'Wait for the native reincarnation animation.', 100);
  if (P.onAscend) {
    let eligible = heavenly.filter(u => !u.bought && u.visible && parentsMet(u) && u.price <= o.heavenlyChips);
    // Reserve an affordable visible digit-gated ancestor closure before buying
    // unrelated upgrades. Checking only individual affordability loses the gate.
    if (gate && byName.get(gate.name).visible) {
      const needed = closure(byName.get(gate.name));
      if (needed.reduce((sum, u) => sum + u.price, 0) <= o.heavenlyChips) {
        const ids = new Set(needed.map(u => u.id)); eligible = eligible.filter(u => ids.has(u.id));
      }
    }
    eligible.sort((a, b) => a.price - b.price || a.id - b.id);
    if (eligible.length) {
      const upgrade = eligible[0];
      const slot = slotNames.indexOf(upgrade.name);
      if (slot >= 0) m.pendingSlot = slot;
      return result('acting', 'Heavenly upgrades', `Buy ${upgrade.name} after its parents.`, { type: 'buy-upgrade', id: upgrade.id });
    }
    if (config.assignPermanentSlots) {
      const slot = slotNames.findIndex((name, i) => byName.get(name)?.bought && A.permanentSlots?.[i] === -1);
      const chosen = candidate();
      if (slot >= 0 && chosen) return result('acting', 'Permanent upgrade', 'Fill an unlocked empty slot with a legal owned upgrade.', { type: 'permanent-slot', slot, id: chosen.id });
    }
    m.completedCycles = (m.completedCycles || 0) + 1;
    return result('acting', 'Normal reincarnation', 'Return to a normal run after buying the available heavenly upgrades.', { type: 'reincarnate', mode: 0 });
  }
  if (P.ascensionMode !== 0) return result('blocked', 'Normal run', 'This schedule requires normal mode.');
  if (config.preserveChallengeAchievements && (!won('Hardcore') || !won('Neverclick'))) {
    return result('needs-achievement', 'First-run achievements', 'Win Hardcore and Neverclick before the first reset.');
  }
  // The constructive early-count phase precedes digit gates and growth resets.
  // It uses actual earned cookies and positive native prestige, not a counter
  // assigned by the scheduler. Later zero-profit resets cannot satisfy it.
  if (config.earlyCountResets && config.earlyResetCookieTarget !== null && o.ascensions < 100) {
    if (!config.allowReset) return result('deferred', 'Early profitable ascensions',
      'The scheduler has not permitted the early-count reset phase.');
    if (o.cookiesEarned < config.earlyResetCookieTarget) return result('needs-resources', 'Early profitable ascensions',
      'Earn the fixed current-run target before this ordinary ascension.', null,
      { requiredCookiesEarned: config.earlyResetCookieTarget, completedProfitableResets: o.ascensions });
    if (!(A.gainedIfAscend > 0 && Number.isFinite(A.gainedIfAscend))) return result('needs-prestige', 'Early profitable ascensions',
      'Continue native growth until prestige gain is positive; a zero-profit reset would not advance the required count.', null,
      {requiredCookiesEarned: config.earlyResetCookieTarget, targetPrestige: o.prestige + Math.max(1, o.prestige * Number.EPSILON)});
    return result('acting', 'Early profitable ascensions', 'Ascend after the fixed earned-cookie target and positive native gain.', {type:'ascend'});
  }
  const allResetGoals = ['Rebirth', 'Resurrection', 'Reincarnation', 'All the stars in heaven', 'No more room in hell', 'Debt evasion'];
  const resetMilestonesDone = !missing.length && allResetGoals.every(won) && o.ascensions >= 100;
  // The default baked-cookie target is a persistent native achievement. A
  // later seasonal retry must not force the same growth milestone again.
  // Larger custom targets have no such native history certificate here.
  const runGoalReached = o.cookiesEarned >= config.finalRunCookies
    || config.finalRunCookies <= 1e72 && won('And a little extra');
  if (resetMilestonesDone && (!config.continueGrowthAfterMilestones
    || runGoalReached && config.finalGrowthAchievements.every(won))) {
    return result('complete', 'Ascension goals', 'Remain in this normal run to finish its ordinary upgrades and other current-state goals.');
  }
  const future = A.prestigeIfAscend;
  const gain = A.gainedIfAscend;
  if (!Number.isFinite(future) || !Number.isFinite(gain) || gain < 0) return result('blocked', 'Prestige arithmetic', 'The observed native prestige gain is invalid.');
  let gatePlan = null;
  if (gate) {
    const needed = closure(byName.get(gate.name));
    const cost = needed.reduce((sum, u) => sum + u.price, 0);
    const required = Math.max(future, o.prestige + Math.max(1, Math.ceil(cost - o.heavenlyChips)));
    const target = nextSevens(required, gate.sevens);
    gatePlan = { upgrade: gate.name, sevens: gate.sevens, requiredChips: cost, targetPrestige: target,
      targetLifetimeCookies: target === null ? null : target ** 3 * 1e12 };
    if (countSevens(future) >= gate.sevens && o.heavenlyChips + gain >= cost) gatePlan.ready = true;
    if (!gatePlan.ready && target === null) return result('blocked-range', gate.name,
      'No finite cookie target was found within this planner’s numeric range. This does not prove the native upgrade unreachable.', null, { gatePlan });
  }
  const newlyAffordable = missing.some(u => parentsMet(u) && u.price > o.heavenlyChips && u.price <= o.heavenlyChips + gain
    && (!gates.some(g => g.name === u.name) || countSevens(future) >= gates.find(g => g.name === u.name).sevens));
  let goal = null;
  if (gatePlan?.ready) goal = gatePlan.upgrade;
  else if (!won('No more room in hell') && o.cookiesEarned >= 1e57) goal = 'No more room in hell';
  else if (!won('All the stars in heaven') && heavenly.filter(u => u.bought).length >= 100) goal = 'All the stars in heaven';
  else if ((missing.length || (resetMilestonesDone && config.continueGrowthAfterMilestones))
    && gain > 0 && (newlyAffordable || gain >= Math.max(1, Math.ceil(o.prestige * (config.growthFactor - 1))))) goal = 'Heavenly growth';
  else if ((!missing.length || config.earlyCountResets) && o.ascensions < 100 && gain > 0) goal = 'Reincarnation';
  else if (!won('Debt evasion') && o.market?.loans?.some(l => l.unlocked)) goal = 'Debt evasion';
  if (goal) {
    if (!config.allowReset) return result('deferred', goal, 'The scheduler must release the current Garden and market work before a reset.', null, { gatePlan });
    if (!won('Debt evasion')) {
      const activeLoan = o.market?.loans?.some(l => l.activeFrames > 0);
      const loan = o.market?.loans?.find(l => l.unlocked && l.activeFrames === 0 && l.interestFrames === 0);
      if (!activeLoan && loan && o.market?.open === false) return result('acting', 'Debt evasion', 'Open the market panel before starting the loan.', { type: 'minigame-open', id: o.market.buildingId ?? 5 }, { gatePlan });
      if (!activeLoan && loan?.visible === false) return wait('Debt evasion', 'Wait for the native loan control to become visible before this ascension.', 1000);
      if (!activeLoan && loan) return result('acting', 'Debt evasion', 'Take an available loan immediately before this planned ascension.', { type: 'market-loan', id: loan.id }, { gatePlan });
      if (goal === 'Debt evasion' && !activeLoan) return wait('Debt evasion', 'Wait for an available loan; an interest period does not qualify.', 1000);
    }
    return result('acting', goal, 'Ascend after the scheduler has released the current run.', { type: 'ascend' }, { gatePlan });
  }
  if (gatePlan) return result('needs-prestige', gatePlan.upgrade, 'Grow toward the next observable prestige value with the required sevens. Stop and recheck the native value before ascending.', null, { gatePlan });
  if (missing.length) {
    const cheapest = missing.filter(parentsMet).sort((a,b) => a.price - b.price || a.id - b.id)[0];
    return result('needs-prestige', 'Heavenly upgrades', 'Earn more heavenly chips for the remaining upgrades.', null,
      { requiredChips: cheapest?.price ?? null, targetPrestige: o.prestige + Math.max(1, (cheapest?.price || 1) - o.heavenlyChips) });
  }
  if (!won('No more room in hell')) return result('needs-resources', 'No more room in hell', 'Bake at least 1e57 cookies within one run before its reset.', null, { requiredCookiesEarned: 1e57 });
  if (o.ascensions < 100) return result('needs-prestige', 'Reincarnation', 'Each counted reset needs a positive native prestige gain.', null,
    { targetPrestige: o.prestige + Math.max(1, o.prestige * Number.EPSILON) });
  if (!won('Debt evasion')) return result('needs-resources', 'Debt evasion', 'Unlock a Stock Market loan before the final required reset.', null, { officeLevel: 2 });
  if (resetMilestonesDone) return result('needs-resources', 'Final run growth', 'Grow this run, with further resets only after scheduler permission.', null,
    { requiredCookiesEarned: config.finalRunCookies, missingGrowthAchievements: config.finalGrowthAchievements.filter(name => !won(name)), targetPrestige: o.prestige * config.growthFactor });
  return result('blocked', 'Ascension achievements', 'A required native reset achievement is still absent.');
}

export function decideAscensionAction(observation, memory = {}, options = {}) {
  return ascensionDecision(observation, [], { ...memory, config: { ...memory.config, ...options } }, ASCENSION_DIGIT_GATES, nextSevenPrestige);
}

export function ascensionPolicySource(options = {}) {
  return `(function(observation, availableActions, memory) {
    const decision = ${ascensionDecision.toString()};
    const nextSevens = ${nextSevenPrestige.toString()};
    return decision(observation, availableActions, {...(memory || {}), config: {...${JSON.stringify(options)}, ...((memory || {}).config || {})}},
      ${JSON.stringify(ASCENSION_DIGIT_GATES)}, nextSevens);
  })`;
}
