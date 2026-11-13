import { readFileSync } from 'node:fs';

const catalogue = JSON.parse(readFileSync(new URL('./catalogue.json', import.meta.url)));
export const COMBO_IDENTITIES = Object.freeze({
  gods: Object.fromEntries(catalogue.pantheon.gods.map(g => [g.key, g.id])),
  auras: Object.fromEntries(catalogue.dragon.auras.map(a => [a.name, a.id])),
});

/** Observation-only growth choices. Estimates are local, not optimality certificates. */
function comboDecision(o, availableActions, memory, identities) {
  const config = { clickRate: 20, preserveChallengeAchievements: true, configurePantheon: true,
    configureAuras: true, castHandOfFate: true, godzamok: true, reserveCookies: 0,
    cycleIntervalMs: 100, minimumBuffSeconds: 1, profitMargin: 2, maximumCycleBankShare: 0.05,
    auraPaybackSeconds: 1800, deferredShimmerIds: [], ...memory?.config };
  let m = { ...memory, config };
  const result = (status, goal, reason, action = null, extra = {}) => ({ status, goal, reason, action,
    memory: m, exclusive: false, reserveCookies: 0, reserveMagic: 0, optimalityCertified: false, ...extra });
  const valid = Number.isFinite(config.clickRate) && config.clickRate >= 0 && config.clickRate <= 50
    && Number.isFinite(config.cycleIntervalMs) && config.cycleIntervalMs >= 20
    && Number.isFinite(config.minimumBuffSeconds) && config.minimumBuffSeconds > 0
    && Number.isFinite(config.profitMargin) && config.profitMargin >= 1
    && Number.isFinite(config.maximumCycleBankShare) && config.maximumCycleBankShare > 0 && config.maximumCycleBankShare <= 1
    && Number.isFinite(config.reserveCookies) && config.reserveCookies >= 0
    && Number.isFinite(config.auraPaybackSeconds) && config.auraPaybackSeconds > 0
    && Array.isArray(config.deferredShimmerIds);
  if (!valid) return result('blocked', 'Combo configuration', 'Use finite rates, reserves, and positive cost limits.');
  const p = o.progression;
  if (!p || !o.controls || !o.shop?.buildings) return result('blocked', 'Combo observation', 'The native public control and building observations are required.');
  if (![o.cookies, o.cookiesPs, o.elapsedMs].every(Number.isFinite) || o.cookies < 0 || o.elapsedMs < 0) {
    return result('blocked', 'Combo arithmetic', 'Finite bank, production, and clock values are required.');
  }
  if (m.run !== undefined && m.run !== o.ascensions) m = { config, run: o.ascensions };
  m.run = o.ascensions;
  if (p.onAscend || p.ascendTimer || p.reincarnateTimer || p.ascensionMode !== 0) {
    return result('deferred', 'Normal run', 'Wait for an active normal run before combo controls.');
  }
  const bank = Math.max(0, o.cookies - config.reserveCookies);
  const buildings = o.shop.buildings;
  const byId = id => buildings.find(b => b.id === id);
  const priceSignature = () => JSON.stringify([o.dragon?.aura, o.dragon?.aura2,
    o.controls.pantheon?.slots, Object.entries(o.upgrades || {}).filter(([, u]) => u.bought).map(([name]) => name),
    ['Everything must go', 'Crafty pixies', 'Nasty goblins'].map(name => !!o.buffs?.[name]),
    o.garden?.plot, o.garden?.soil, o.garden?.freeze]);
  // A sale is a two-action transaction. The scheduler must restore it before other controls.
  if (m.rebuy) {
    const pending = m.rebuy;
    const b = byId(pending.id);
    if (!b) return result('blocked', 'Restore sold buildings', 'The recorded building is absent.', null, { exclusive: true });
    const missing = Math.max(0, pending.targetAmount - b.amount);
    if (!missing) delete m.rebuy;
    else {
      if (!Number.isInteger(missing) || missing > 1000) return result('blocked', 'Restore sold buildings', 'The recorded purchase exceeds the native batch limit.', null, { exclusive: true });
      const unchanged = missing === pending.amount && o.elapsedMs === pending.time && priceSignature() === pending.priceSignature;
      // An interrupted pair is restored one currently quoted copy at a time.
      // Do not extrapolate a bulk buyback through changed discounts or rounding.
      const purchaseAmount = unchanged ? missing : 1;
      const required = unchanged ? pending.rebuy : b.buy1price;
      if (!Number.isFinite(required) || bank < required) return result('needs-resources', 'Restore sold buildings',
        'Keep this transaction reserved until its current native purchase is funded.', null,
        { exclusive: true, reserveCookies: required, requiredCookies: required });
      return result('acting', 'Restore sold buildings', 'Buy back the recorded copies before another action changes prices.',
        { type: 'buy-building', id: b.id, amount: purchaseAmount }, { exclusive: true, reserveCookies: required });
    }
  }
  if (m.confirmAura) {
    const pending = m.confirmAura;
    if (o.controls.promptOn) {
      if (o.elapsedMs !== pending.time || o.dragon?.level !== pending.level ||
          (pending.buildingId !== null && byId(pending.buildingId)?.amount !== pending.beforeAmount)) {
        return result('blocked', 'Owned dragon prompt', 'The aura prompt state changed; do not confirm it automatically.', null, { exclusive: true });
      }
      delete m.confirmAura;
      if (pending.buildingId !== null) m.auraRestore = { id: pending.buildingId, targetAmount: pending.beforeAmount };
      return result('acting', 'Dragon aura', 'Confirm only the aura prompt requested by this controller.',
        { type: 'prompt', option: 0 }, { exclusive: true, reserveCookies: pending.reserve });
    }
    delete m.confirmAura;
  }
  if (m.auraRestore) {
    const b = byId(m.auraRestore.id);
    if (!b || b.amount >= m.auraRestore.targetAmount) delete m.auraRestore;
    else {
      if (bank < b.buy1price) return result('needs-resources', 'Restore aura sacrifice', 'Fund the current native replacement price.', null,
        { exclusive: true, reserveCookies: b.buy1price, requiredCookies: b.buy1price });
      return result('acting', 'Restore aura sacrifice', 'Restore the highest building sacrificed by the aura prompt.',
        { type: 'buy-building', id: b.id, amount: 1 }, { exclusive: true, reserveCookies: b.buy1price });
    }
  }
  if (o.controls.promptOn) return result('deferred', 'Unowned prompt', 'This controller does not confirm another controller’s prompt.');
  if (config.preserveChallengeAchievements && (!o.achievements?.Hardcore || !o.achievements?.Neverclick)) {
    return result('needs-achievement', 'First-run challenges', 'Preserve the challenge conditions before setting up active combos.');
  }
  const P = o.controls.pantheon;
  if (config.configurePantheon && config.clickRate > 0 && p.minigames?.Temple && P?.swaps > 0) {
    const desired = ['ruin', 'labor', 'mother'];
    const slot = desired.findIndex((key, i) => P.slots[i] !== identities.gods[key]);
    if (slot !== -1) return result('acting', 'Active Pantheon', 'Use Godzamok, Muridal, and Mokalsium for this active-click schedule.',
      { type: 'pantheon-slot', god: desired[slot], slot });
  }
  // Fill empty slots only. Existing sugar, Garden, or other deliberately chosen auras stay in place.
  if (config.configureAuras && o.upgrades?.['A crumbly egg']?.bought && o.dragon?.auras) {
    const D = o.dragon;
    const ownedKitten = Object.entries(o.upgrades || {}).some(([name, u]) => /^Kitten /i.test(name) && u.bought);
    const targets = ['Radiant Appetite', ...(ownedKitten ? ['Breath of Milk'] : [])];
    const current = [D.aura, D.aura2];
    const slot = current.findIndex((id, i) => id === 0 && (i === 0 || D.level === 27));
    const aura = slot === -1 ? null : targets.map(name => D.auras.find(a => a.name === name && a.unlocked && !current.includes(a.id))).find(Boolean);
    if (aura) {
      const highest = [...buildings].reverse().find(b => b.amount > 0);
      const reserve = highest ? highest.buy1price * 1.05 : 0;
      const estimatedGain = aura.name === 'Radiant Appetite' ? o.cookiesPs : o.cookiesPs * 0.01;
      if (Number.isFinite(reserve) && bank >= reserve && estimatedGain * config.auraPaybackSeconds >= reserve) {
        m.confirmAura = { id: aura.id, slot, time: o.elapsedMs, level: D.level,
          buildingId: highest?.id ?? null, beforeAmount: highest?.amount ?? 0, reserve };
        return result('acting', 'Dragon aura', 'Fill an empty aura slot after funding its building replacement.',
          { type: 'dragon-aura', id: aura.id, slot }, { exclusive: true, reserveCookies: reserve });
      }
    }
  }
  const buffs = Object.values(o.buffs || {});
  const fps = Number.isFinite(o.fps) && o.fps > 0 ? o.fps : 30;
  const positive = buffs.filter(b => b.time / fps >= config.minimumBuffSeconds && (b.multCpS > 1 || b.multClick > 1));
  const shimmer = o.shimmers?.find(s => s.type === 'golden' && !config.deferredShimmerIds.includes(s.id));
  if (shimmer && (m.awaitingSpell || positive.length)) {
    delete m.awaitingSpell;
    return result('acting', 'Observed golden cookie', 'Click the visible cookie without predicting its effect.', { type: 'click-shimmer', id: shimmer.id });
  }
  if (m.awaitingSpell && !o.shimmers?.some(s => s.type === 'golden')) delete m.awaitingSpell;
  const M = o.controls.grimoire;
  const fate = M?.spells?.['hand of fate'];
  const reserveMagic = config.castHandOfFate && fate ? fate.cost : 0;
  if (config.castHandOfFate && positive.length && p.minigames?.['Wizard tower'] && fate && M.magic >= fate.cost
      && !o.shimmers?.some(s => s.type === 'golden') && o.elapsedMs >= (m.nextCastAt || 0)) {
    m.awaitingSpell = true; m.nextCastAt = o.elapsedMs + 1000;
    return result('acting', 'Observed-buff spell', 'Cast Force the Hand of Fate during an observed positive buff, with no golden cookie already present.',
      { type: 'cast-spell', spell: 'hand of fate' }, { reserveMagic });
  }
  const ruinSlot = P?.slots?.indexOf(identities.gods.ruin) ?? -1;
  const bonus = [0.01, 0.005, 0.0025][ruinSlot] || 0;
  const devastation = o.buffs?.Devastation;
  const seconds = devastation ? devastation.time / fps : 10;
  const basePerClick = o.cookiesPerClick / (devastation?.multClick || 1);
  if (config.godzamok && config.clickRate > 0 && bonus && seconds >= config.minimumBuffSeconds
      && Number.isFinite(basePerClick) && basePerClick > 0 && o.elapsedMs >= (m.nextCycleAt || 0)) {
    const protectedNames = ['Cursor', 'Grandma', 'Farm', 'Bank', 'Temple', 'Wizard tower', 'You'];
    const choices = buildings.filter(b => !protectedNames.includes(b.name) && !b.locked).map(b => {
      const q = b.godzamokCycle;
      if (!q || !Number.isInteger(q.amount) || q.amount < 1 || q.amount > 100 || b.amount - q.amount < 1
        || ![q.rebuy, q.refund, q.net].every(Number.isFinite) || q.rebuy < 0 || q.net < 0) return null;
      // Do not assume another observed positive buff lasts for the whole Devastation window.
      const stableSeconds = Math.min(seconds, ...buffs.filter(buff => buff.time > 0).map(buff => buff.time / fps));
      if (stableSeconds < config.minimumBuffSeconds) return null;
      const additional = bonus * q.amount * config.clickRate * basePerClick * stableSeconds;
      if (q.rebuy > bank * config.maximumCycleBankShare || additional <= config.profitMargin * q.net) return null;
      return { b, q, additional, ratio: additional / Math.max(q.net, 1) };
    }).filter(Boolean).sort((a, b) => b.ratio - a.ratio || a.b.id - b.b.id);
    if (choices.length) {
      const { b, q, additional } = choices[0];
      m.rebuy = { id: b.id, amount: q.amount, targetAmount: b.amount, rebuy: q.rebuy,
        time: o.elapsedMs, priceSignature: priceSignature() };
      m.nextCycleAt = o.elapsedMs + config.cycleIntervalMs;
      return result('acting', 'Funded Godzamok cycle', 'Sell only a funded batch whose estimated extra clicks exceed its round-trip cost margin.',
        { type: 'sell-building', id: b.id, amount: q.amount },
        { exclusive: true, reserveCookies: q.rebuy, reserveMagic, estimatedAdditionalCookies: additional, roundTripCost: q.net });
    }
  }
  if (positive.length && config.clickRate > 0 && o.elapsedMs >= (m.nextClickAt ?? 100)) {
    m.nextClickAt = o.elapsedMs + 1000 / config.clickRate;
    return result('acting', 'Observed-buff clicks', 'Use the configured native-safe click cadence during the observed buff.', { type: 'click' }, { reserveMagic });
  }
  return result('idle', 'Combo growth', 'Wait for an observed opportunity while other controllers continue.', null, { reserveMagic });
}

export function decideComboAction(observation, memory = {}, options = {}) {
  return comboDecision(observation, [], { ...memory, config: { ...memory?.config, ...options } }, COMBO_IDENTITIES);
}

export function comboPolicySource(options = {}) {
  return `(function(observation,availableActions,memory){return (${comboDecision.toString()})(observation,availableActions,{...(memory||{}),config:{...${JSON.stringify(options)},...((memory||{}).config||{})}},${JSON.stringify(COMBO_IDENTITIES)});})`;
}
