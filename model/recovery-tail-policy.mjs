import { readFileSync } from 'node:fs';
import { assessCompletion } from './completion.mjs';
import { decideSeasonAction, seasonPolicySource, SEASON_ACHIEVEMENTS } from './season-policy.mjs';
import { decideGardenAction, gardenPolicySource } from './garden-policy.mjs';
import { decideMarketAction, marketPolicySource, MARKET_ACHIEVEMENTS } from './market-policy.mjs';
import { decideProductionAction, productionPolicySource } from './production-policy.mjs';
import { decideMiscAction, miscPolicySource } from './misc-policy.mjs';

const catalogue = JSON.parse(readFileSync(new URL('./catalogue.json', import.meta.url)));
const contract = JSON.parse(readFileSync(new URL('./completion-requirements.json', import.meta.url)));
export const NATURAL_TAIL_MAINTENANCE = Object.freeze({ firstMs: 86400000, everyMs: 86400000 });
export const NATURAL_TAIL_OPTIONS = Object.freeze({
  heavenlyUpgradeCount: catalogue.upgrades.filter(u => u.pool === 'prestige' && u.vanilla).length,
  forbiddenUpgrades: catalogue.upgrades.filter(u => ['debug','unused','dungeon','shadow'].includes(u.pool)).map(u => u.name),
  season: { naturalSeasons: true, popGoldenCookies: false, helperGrandma: false, eldeer: false,
    suppressWrathForCookieCount: false, maxWaitMs: 1000 },
  garden: { fixedSoil: 'dirt', boostNovelGrowth: false, naturalCookieFarm: false,
    sacrificesRequired: 1, farmDrops: true, harvestTarget: 1000, requireFullPlot: true, maxWaitMs: 1000 },
  market: { maximumOffice: 4, maximumHolding: 1000, maximumTransaction: 1000,
    prepareDebtEvasion: false, collectTrades: true, maxWaitMs: 1000 },
  production: { finalCollection: true, clickRate: 20, maxWaitMs: 1000 },
});
// Native Logic derives these from final current holdings/ownership (main.js
// 16388–16505). They must remain eligible for the tail's own purchases.
export const NATURAL_TAIL_OWNERSHIP_ACHIEVEMENTS = Object.freeze([
  'Wholesome', 'You win a cookie', 'One with everything', 'Mathematician', 'Base 10',
  'Centennial', 'Centennial and a half', 'Bicentennial', 'Bicentennial and a half',
  'Tricentennial', 'Tricentennial and a half', 'Quadricentennial', 'Quadricentennial and a half',
  'Quincentennial', 'Quincentennial and a half', 'Sexcentennial', 'Sexcentennial and a half',
  'Builder', 'Architect', 'Engineer', 'Lord of Constructs', 'Grand design', 'Ecumenopolis', 'Myriad',
  'Enhancer', 'Augmenter', 'Upgrader', 'Lord of Progress', 'The full picture',
  "When there's nothing left to add", 'Kaizen', 'Beyond quality', "Oft we mar what's well",
  'Polymath', 'Renaissance baker', 'Jellicles', 'Elder', 'Veteran', 'The elder scrolls',
]);
const tailAchievements = [...SEASON_ACHIEVEMENTS, ...MARKET_ACHIEVEMENTS, ...NATURAL_TAIL_OWNERSHIP_ACHIEVEMENTS,
  'Botany enthusiast', 'Green, aching thumb', 'In the garden of Eden (baby)',
  'Keeper of the conservatory', 'Seedless to nay', 'Hand-picked', 'No time like the present', 'Septcentennial'];
const prefixAchievements = ['Hardcore', 'Neverclick', 'A wizard is you', 'Thick-skinned', 'Eldeer',
  'Wrath cookie', 'Early bird', 'Fading luck', "Black cat's paw", "Baby it's old outside"];
const tailAccess = ['Elder Pledge', 'Elder Covenant', 'Revoke Elder Covenant', 'Golden switch [on]', 'Golden switch [off]'];
export const NATURAL_TAIL_ACHIEVEMENTS = Object.freeze([...tailAchievements]);
export const NATURAL_TAIL_PREFIX_ACHIEVEMENTS = Object.freeze([...prefixAchievements]);

/** This is a separate final-run tail, not a new-save policy or a properness theorem.
 * Its host must commit to NATURAL_TAIL_MAINTENANCE before creating the new save.
 * The release flag is a prefix handoff, not a substitute for the checked entry.
 */
function tailDecision(o, actions, memory, options, requirements, tailNames, prefixNames, accessNames, controllers, assess) {
  const m = { ...(memory || {}) };
  const answer = (status, stage, action = null, extra = {}) => ({ status, stage, action, memory: m, ...extra });
  const wait = (stage, ms = 1000) => answer('waiting', stage, { type: 'wait', milliseconds: Math.max(1, Math.min(1000, ms)) });
  const won = name => o.achievements?.[name] === true;
  const p = o.progression;
  if (!m.released) return answer('deferred', 'prefix-handoff', null, { reason: 'Finish the independently planned prefix before releasing this final-run tail.' });
  // A scheduled current-save reload temporarily shows a fresh realm. Keep all
  // controller memories and do not act on its pre-restoration store or prompt.
  if (m.entry && (o.ascensions < m.entry.ascensions || prefixNames.some(name => !won(name))
    || p?.buildingLevels?.Farm < 10 || p?.buildingLevels?.Cursor < 12 || !o.garden?.ready || !o.market?.ready)) {
    return wait('maintenance-restoration');
  }
  if (!p || p.onAscend || p.ascendTimer || p.reincarnateTimer || p.ascensionMode !== 0) return answer('needs-entry', 'active-final-run');
  if (!m.entry) {
    const produced = [...(o.production?.bankAchievements || []), ...(o.production?.cpsAchievements || []),
      ...(o.production?.handmadeAchievements || []), ...(o.shop?.buildings || []).flatMap(b => [...b.countAchievements, ...b.productionAchievements])].map(a => a.name);
    const covered = new Set([...tailNames, ...produced]);
    const missing = [...new Set([...prefixNames, ...requirements.requiredAchievements.filter(a => !covered.has(a.name)).map(a => a.name)])].filter(name => !won(name));
    const missingHeavenly = (o.ascension?.heavenlyUpgrades || []).filter(u => !u.bought).map(u => u.name);
    const accessed = new Set(o.history?.accessedUpgrades || []);
    const missingAccess = requirements.accessUpgrades.filter(u => !accessNames.includes(u.name)
      && !o.upgrades?.[u.name]?.bought && !o.upgrades?.[u.name]?.unlocked && !accessed.has(u.name)).map(u => u.name);
    const levels = { Cursor: 12, Farm: 10, Temple: 1, 'Wizard tower': 1, Bank: 1 };
    const missingLevels = Object.entries(levels).filter(([name, value]) => !(p.buildingLevels[name] >= value));
    if (o.ascensions < 100 || missing.length || missingHeavenly.length || missingAccess.length || missingLevels.length
      || o.ascension?.heavenlyUpgrades?.length !== options.heavenlyUpgradeCount
      || o.dragon?.level !== requirements.dragonLevel || !o.garden?.ready || !o.market?.ready
      || o.market.officeLevel > 4 || !(o.seasonal?.remainingMs === null || o.seasonal?.remainingMs === 0)) {
      return answer('needs-entry', 'bounded-tail-entry', null, { missing, missingHeavenly, missingAccess, missingLevels,
        reason: 'The prefix must supply all reset-sensitive goals, heavenly ownership, level costs, finite access, max dragon, and an expired season timer. Office 5 is deferred.' });
    }
    if (o.controls?.promptOn) return answer('needs-entry', 'unrelated-entry-prompt');
    m.entry = { ascensions: o.ascensions, seasonUses: o.seasonal.uses };
    if (m.season) { m.season = { ...m.season }; delete m.season.confirm; }
    if (m.garden) { m.garden = { ...m.garden }; delete m.garden.confirmSacrifice; }
    if (m.misc) { m.misc = { ...m.misc }; delete m.misc.giftPending; }
    delete m.prompt;
  }
  if (o.ascensions !== m.entry.ascensions || o.seasonal.uses !== m.entry.seasonUses) return answer('blocked', 'tail-invariant', null,
    { reason: 'The tail does not reset or buy a paid season switch.' });
  const buildings = o.shop?.buildings;
  const currentBankCap = o.upgrades['Chocolate egg']?.bought ? 2 ** 938 : 2 ** 936;
  const allNumbers = [o.cookies, o.cookiesEarned, o.cookiesReset, o.cookiesPs, o.cookiesPerClick, o.cookiesPsRawHighest];
  if (buildings?.length !== 20 || allNumbers.some(x => !Number.isFinite(x) || x < 0)
    || buildings.some(b => !Number.isSafeInteger(b.amount) || b.amount < 0 || b.amount > 2000 || !Number.isInteger(b.level) || b.level < 0 || b.level > 12)
    || o.dragon.aura !== 0 || o.dragon.aura2 !== 0 || o.market.goods.some(g => g.stock > 1000)
    || options.forbiddenUpgrades.some(name => o.upgrades[name]?.bought)
    || o.cookiesReset > 2 ** 1000 || o.cookiesEarned > 2 ** 940 || o.cookies > currentBankCap
    || o.cookiesPsRawHighest > 2 ** 741) {
    return answer('blocked', 'tail-envelope', null, { reason: 'Use the finite collection board, auras 0, and at most 1000 shares per good.' });
  }
  // Drain production/click buffs from the counted-cookie prefix. Sugar blessing
  // changes frequency only and can be renewed by later natural lump harvests.
  const activeBuff = Object.entries(o.buffs || {}).find(([name, buff]) => name !== 'Sugar blessing' && name !== 'Gifted out' && buff.time > 0);
  if (activeBuff) return wait('drain-prefix-buffs', Math.max(1, activeBuff[1].time * 1000 / (o.fps || 30)));
  if (o.cookiesPs > 2 ** 741 || o.cookiesPerClick > 2 ** 800) return answer('blocked', 'drained-production-envelope');
  const goal = assess(o, requirements);
  if (goal.complete) return answer('complete', 'native-completion-predicate');
  if (!goal.valid) return answer('blocked', 'completion-observation', null, { issues: goal.issues });

  const emit = (action, stage) => {
    // This checks emitted controls; it is not a proof that every callback
    // preserves the source envelope or that its target is physically reachable.
    if (['ascend','reincarnate','cast-spell','market-loan','dragon-aura','pantheon-slot'].includes(action.type)) throw new Error('Forbidden recovery-tail action');
    if (action.type === 'click-shimmer' && o.shimmers.find(s => s.id === action.id)?.type !== 'reindeer') throw new Error('Recovery tail must not pop golden cookies');
    if (action.type === 'garden-soil' && action.soil !== 'dirt') throw new Error('Recovery tail requires dirt');
    if (action.type === 'buy-building' && o.shop.buildings.find(b => b.id === action.id).amount + action.amount > 2000) throw new Error('Recovery-tail building cap');
    if (['market-buy','market-sell'].includes(action.type) && !(action.amount > 0 && action.amount <= 1000)) throw new Error('Recovery-tail transaction cap');
    if (action.type === 'buy-upgrade') {
      const upgrade = o.shop.upgrades.find(u => u.id === action.id);
      if (!upgrade || ['Lovesick biscuit','Festive biscuit','Ghostly biscuit','Bunny biscuit','Fool\'s biscuit','Sugar frenzy'].includes(upgrade.name)) throw new Error('Recovery-tail paid season or frenzy');
    }
    const promptOwner = action.type === 'garden-sacrifice' ? 'garden' : action.type === 'gift-send' ? 'misc'
      : action.type === 'buy-upgrade' && o.shop.upgrades.find(u => u.id === action.id)?.name === 'One mind' ? 'season' : null;
    if (promptOwner) m.prompt = { owner: promptOwner, elapsedMs: o.elapsedMs, menu: o.controls.menu };
    else if (action.type === 'prompt' || action.type === 'close-prompt') delete m.prompt;
    return answer('acting', stage, action);
  };
  // Force this tail's options even when the prefix passes earlier controller
  // memory. Retain workflow ownership but never a paid-season or soil override.
  for (const name of ['season','garden','production']) m[name] = { ...(m[name] || {}),
    config: { ...(m[name]?.config || {}), ...options[name] } };
  // Only a controller that requested a native prompt may confirm it. Scheduled
  // maintenance prompts are left alone until the adapter restores the save.
  if (m.prompt && (!o.controls.promptOn || m.prompt.elapsedMs !== o.elapsedMs || m.prompt.menu !== o.controls.menu)) {
    // Native scheduled maintenance closes this prompt and opens Options. It
    // cannot inherit authority to confirm the newly displayed prompt.
    if (m.season) delete m.season.confirm;
    if (m.garden) delete m.garden.confirmSacrifice;
    if (m.misc) delete m.misc.giftPending;
    delete m.prompt;
  }
  const ownsPrompt = m.prompt?.owner || null;
  if (o.controls.promptOn && !ownsPrompt) return wait('unowned-prompt');
  if (ownsPrompt) {
    const d = controllers[ownsPrompt](o, actions, m[ownsPrompt]); m[ownsPrompt] = d.memory;
    return d.action ? emit(d.action, ownsPrompt) : wait('owned-prompt');
  }
  if (o.controls.menu) return emit({ type: 'open-menu', menu: '' }, 'collection-view');
  if (o.lump?.available && o.lump.ageMs >= (won('Hand-picked') ? o.lump.ripeAge : o.lump.matureAge) && o.lump.ageMs < o.lump.overripeAge) {
    return emit({ type: 'harvest-lump' }, 'natural-lump');
  }
  const season = controllers.season(o, actions, m.season); m.season = season.memory;
  if (season.action && season.action.type !== 'wait') return emit(season.action, 'natural-season');
  const garden = controllers.garden(o, actions, m.garden); m.garden = garden.memory;
  if (garden.action && garden.action.type !== 'wait') return emit(garden.action, 'dirt-garden');
  // The final office is released only after the seasonal and Garden random
  // goals, Hand-picked, and seven other market goals are actually recorded.
  const finalOffice = season.status === 'complete' && garden.status === 'complete' && won('Hand-picked')
    && ['Initial public offering','Rookie numbers','No nobility in poverty','Full warehouses','Make my day','Buy buy buy','Liquid assets'].every(won);
  const reserve = Math.max(0, ...[season, garden].map(d => d.status === 'needs-resources' ? d.requiredCookies || 0 : 0));
  const spendable = { ...o, cookies: Math.max(0, o.cookies - reserve) };
  m.market = { ...(m.market || {}), config: { ...options.market, maximumOffice: finalOffice ? 5 : 4 } };
  const market = controllers.market(spendable, actions, m.market); m.market = market.memory;
  if (market.action && market.action.type !== 'wait') return emit(market.action, 'bounded-market');
  const request = [season, garden, market].find(d => d.building && d.amount > p.buildingAmounts[d.building]);
  if (request) {
    const b = buildings.find(b => b.name === request.building);
    if (b && b.amount < 2000 && b.buy1price <= spendable.cookies) return emit({ type: 'buy-building', id: b.id, amount: 1 }, 'bounded-resource-building');
  }
  const misc = controllers.misc(o, actions, { ...(m.misc || {}), deferVeilToPreparation: true }); m.misc = misc.memory;
  if (misc.action) return emit(misc.action, 'finite-access');
  const production = controllers.production(spendable, actions, m.production); m.production = production.memory;
  if (production.action && production.action.type !== 'wait') return emit(production.action, 'bounded-production');
  const decisions = [season, garden, market, misc, production];
  const blocked = decisions.find(d => d.status === 'blocked' || d.status === 'needs-ascension');
  if (blocked) return answer('blocked', 'subcontroller-boundary', null, { goal: blocked.goal, reason: blocked.reason });
  return wait('natural-recovery', Math.min(...decisions.map(d => d.action?.type === 'wait' ? d.action.milliseconds : 1000)));
}

const controllers = {
  season: (o, a, m) => decideSeasonAction(o, m, NATURAL_TAIL_OPTIONS.season),
  garden: (o, a, m) => decideGardenAction(o, m, NATURAL_TAIL_OPTIONS.garden),
  market: (o, a, m) => decideMarketAction(o, m),
  production: (o, a, m) => decideProductionAction(o, m, NATURAL_TAIL_OPTIONS.production),
  misc: (o, a, m) => decideMiscAction(o, m),
};
export function decideRecoveryTail(observation, memory = {}) {
  return tailDecision(observation, [], memory, NATURAL_TAIL_OPTIONS, contract, tailAchievements,
    prefixAchievements, tailAccess, controllers, assessCompletion);
}
export function recoveryTailPolicySource() {
  return `(function(){
    const isRecord = value => value !== null && typeof value === 'object' && !Array.isArray(value);
    const isCount = value => Number.isInteger(value) && value >= 0;
    const controllers = {season:(${seasonPolicySource(NATURAL_TAIL_OPTIONS.season)}),
      garden:(${gardenPolicySource(NATURAL_TAIL_OPTIONS.garden)}), market:(${marketPolicySource(NATURAL_TAIL_OPTIONS.market)}),
      production:(${productionPolicySource(NATURAL_TAIL_OPTIONS.production)}), misc:(${miscPolicySource()})};
    return (o,a,m) => (${tailDecision.toString()})(o,a,m,${JSON.stringify(NATURAL_TAIL_OPTIONS)},${JSON.stringify(contract)},
      ${JSON.stringify(tailAchievements)},${JSON.stringify(prefixAchievements)},${JSON.stringify(tailAccess)},controllers,(${assessCompletion.toString()}));
  })()`;
}

/** Clock-only configuration for a prefix/tail composition. The caller must use
 * this schedule from the original new save, not install it after a bad outcome. */
export function naturalRecoveryTailPlan() {
  return { maintenanceReload: { ...NATURAL_TAIL_MAINTENANCE }, policySource: recoveryTailPolicySource(),
    initialMemory: { released: false }, scope: 'conditional-final-run-tail-awaiting-prefix-handoff' };
}
