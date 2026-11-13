/** Section: Which heavenly upgrades to buy with heavenly chips, and in which order */

import { GoldenShares, MilkMultiplier } from '../PP/AutoplayValue.js';
import { CacheLucky } from '../VariablesAndData.js';

/** "Lucky ..." heavenly upgrades: +1% prestige effect on CpS and +1% golden cookie effect duration */
const luckyUpgrade = (ctx) => 1.01 * (1 + 0.01 * ctx.golden.frenzy);

/** Click multiplier of "Aura gloves": +5% for each cursor level up to `cap` */
const auraGloves = (cap) => 1 + 0.05 * Math.min(Game.Objects.Cursor.level, cap);

/** Kitten upgrades owned, which "Cat ladies" counts */
const kittensOwned = () =>
  ((Game.UpgradesByPool && Game.UpgradesByPool.kitten) || []).filter((me) => me.bought).length;

/**
 * Estimated production multiplier of each heavenly upgrade worth chips under autoplay, given
 * ctx = {clickShare, golden: {frenzy, lucky, total}, autoplay, grandmaShare} (income shares of clicks and
 * golden cookies, which autoplay systems are on, and the share of CpS from grandmas).
 * The "Unshackled" upgrades act together and are valued by UnshackledValue().
 * Upgrades not listed are only bought as parents of listed ones: cosmetics, the golden switch and the
 * shimmering veil (they turn off or break on golden cookies), offline production, gifts and the sugar
 * frenzy. Autoplay spends lumps on the sugar frenzy once Sugar craving is owned, before the cursor levels
 * for loans and before "Sugar baking" can keep them, so Sugar craving and Sugar aging process (its child)
 * are not bought.
 */
export const HeavenlyUpgradeValues = {
  'Heavenly cookies': () => 1.1,
  'Wrinkly cookies': () => 1.1,
  'Sugar crystal cookies': () => 1.05,
  Heralds: () => 1 + 0.01 * Game.heralds,
  'Kitten angels': () => 1 + 0.1 * Game.milkProgress,
  'Halo gloves': (ctx) => 1 + 0.1 * ctx.clickShare,
  'Aura gloves': (ctx) => 1 + ctx.clickShare * (auraGloves(10) - 1),
  'Luminous gloves': (ctx) => 1 + ctx.clickShare * (auraGloves(20) / auraGloves(10) - 1),
  'Heavenly luck': (ctx) => 1 + 0.05 * ctx.golden.total,
  'Lasting fortune': (ctx) => 1 + 0.1 * ctx.golden.frenzy,
  'Lucky digit': luckyUpgrade,
  'Lucky number': luckyUpgrade,
  'Lucky payout': luckyUpgrade,
  'Distilled essence of redoubled luck': (ctx) => 1 + 0.01 * ctx.golden.total,
  'Sugar baking': () => 1 + 0.01 * Math.min(Game.lumps, 100),
  // Grandmas: x1.29 for each kitten upgrade owned, and +5% for each rank of milk
  'Cat ladies': (ctx) => 1 + (ctx.grandmaShare || 0) * (1.29 ** kittensOwned() - 1),
  'Milkhelp&reg; lactose intolerance relief tablets': (ctx) =>
    1 + (ctx.grandmaShare || 0) * 0.05 * Game.milkProgress * MilkMultiplier(),
  // Estimates for upgrades that work through cheaper or extra store upgrades
  'Divine discount': () => 1.01,
  'Divine sales': () => 1.005,
  'Divine bakeries': () => 1.03,
  'Synergies Vol. I': () => 1.05,
  'Synergies Vol. II': () => 1.05,
  'Tin of british tea biscuits': () => 1.02,
  'Box of macarons': () => 1.02,
  'Box of brand biscuits': () => 1.02,
  'Tin of butter cookies': () => 1.02,
  'Box of maybe cookies': () => 1.02,
  'Box of not cookies': () => 1.02,
  'Box of pastries': () => 1.02,
  'Starter kit': () => 1.005,
  'Starter kitchen': () => 1.005,
  'Persistent memory': () => 1.01,
  // Kitten upgrades 10% cheaper; synergy upgrades 2% cheaper (Chimera's other effects are offline)
  'Kitten wages': () => 1.01,
  Chimera: () => 1.002,
  // About 3% more sugar lumps: bifurcated lumps are more common and drop two lumps more often
  'Sucralosia Inutilis': () => 1.003,
  // Systems that autoplay runs every ascension (estimates)
  // The dragon reaches Radiant Appetite (x2) once 100 of the first 14 buildings can be sacrificed
  'How to bake your dragon': (ctx) => (ctx.autoplay.dragon ? 1.8 : 1),
  // Christmas (Santa's levels and gifts), Easter eggs, Valentine's and Halloween cookies every run
  'Season switcher': (ctx) => (ctx.autoplay.seasons ? 1.3 : 1),
  // A kitten kept from the start of every run; later slots hold weaker upgrades
  'Permanent upgrade slot I': () => 1.12,
  'Permanent upgrade slot II': () => 1.08,
  'Permanent upgrade slot III': () => 1.06,
  'Permanent upgrade slot IV': () => 1.04,
  'Permanent upgrade slot V': () => 1.03,
  // Wrinklers: respawn five times as fast, two more of them (about 1.4x their income), +5% returns
  'Unholy bait': (ctx) => (ctx.autoplay.elder ? 1.05 : 1),
  'Elder spice': (ctx) => (ctx.autoplay.elder ? 1.25 : 1),
  'Sacrilegious corruption': (ctx) => (ctx.autoplay.elder ? 1.04 : 1),
  'Five-finger discount': () => 1.01,
  Starspawn: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Starsnow: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Starterror: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Starlove: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Startrade: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Keepsakes: (ctx) => (ctx.autoplay.seasons ? 1.02 : 1),
  // Sending yourself a gift and redeeming it earns "No time like the present": one more achievement
  'Wrapping paper': (ctx) => (ctx.autoplay.achievements ? 1.02 : 1),
  // Fortunes, clicked when the ticker shows one: about two a run, mostly +7% for one building
  'Fortune cookies': (ctx) => (ctx.autoplay.achievements ? 1.02 : 1),
  // Petting drops one +3% upgrade in each new quarter-hour of a run, and drops last one run
  'Pet the dragon': (ctx) => (ctx.autoplay.dragon ? 1.03 : 1),
};

/** Upgrades that multiply the Thousand fingers gain, as in the game's cursor code */
const FINGERS = [
  ['Million fingers', 5],
  ['Billion fingers', 10],
  ['Trillion fingers', 20],
  ['Quadrillion fingers', 20],
  ['Quintillion fingers', 20],
  ['Sextillion fingers', 20],
  ['Septillion fingers', 20],
  ['Octillion fingers', 20],
  ['Nonillion fingers', 20],
  ['Decillion fingers', 20],
  ['Undecillion fingers', 20],
];

/**
 * Factor by which "Unshackled cursors" multiplies cursor CpS: it multiplies the Thousand fingers gain
 * (per building that is not a cursor) by 25, and leaves the base production of a cursor as it is
 * @returns	{number}
 */
function CursorUnshackleGain() {
  if (!Game.Has('Thousand fingers')) return 1;
  const others =
    Game.ObjectsById.reduce((sum, me) => sum + me.amount, 0) - Game.Objects.Cursor.amount;
  const fingers =
    FINGERS.reduce((gain, [name, mult]) => (Game.Has(name) ? gain * mult : gain), 0.1) * others;
  const doublings =
    Game.Has('Reinforced index finger') +
    Game.Has('Carpal tunnel prevention cream') +
    Game.Has('Ambidextrous');
  const base = 0.1 * 2 ** doublings;
  return (base + 25 * fingers) / (base + fingers);
}

/** Last shares from a normal run, for use while heavenly upgrades have no effect (Born again) */
let LastShares = [];

/**
 * What the "Unshackled" heavenly upgrades act on now. A tiered upgrade of an unshackled building gives
 * 2 + 0.1 (20 - id) (grandmas 2.5) instead of 2 when its tier is unshackled too. "Unshackled cursors"
 * multiplies the Thousand fingers gain of cursors by 25 instead; cursors have no such tiers.
 * @returns	{{upgrade: string, share: number, base: number, gain: number, tiers: string[]}[]}	For each
 * building: its unshackle upgrade, its share of CpS, the factor that upgrade gives alone, the factor of
 * each unshackled tier, and the unshackle upgrades of the tiers whose tiered upgrade it owns
 */
export function UnshackleShares() {
  if (Game.ascensionMode === 1) return LastShares;
  const total = Game.ObjectsById.reduce((sum, me) => sum + me.storedTotalCps, 0);
  if (!(total > 0)) return LastShares;
  LastShares = Game.ObjectsById.filter((me) => Game.Upgrades[me.unshackleUpgrade]).map((me) => ({
    upgrade: me.unshackleUpgrade,
    share: me.storedTotalCps / total,
    base: me.name === 'Cursor' ? CursorUnshackleGain() : 1,
    gain: (2 + (me.id === 1 ? 0.5 : (20 - me.id) * 0.1)) / 2,
    tiers: Object.keys(me.tieredUpgrades)
      .map((key) => me.tieredUpgrades[key])
      .filter(
        (it) =>
          !Game.Tiers[it.tier].special && Game.Has(it.name) && Game.Tiers[it.tier].unshackleUpgrade,
      )
      .map((it) => Game.Tiers[it.tier].unshackleUpgrade),
  }));
  return LastShares;
}

/**
 * Production multiplier of a set of "Unshackled" upgrades over those owned now: the sum over buildings
 * of share x (factor with the set) / (factor now). These upgrades are not independent: a building gains
 * only for the tiers that are unshackled too
 * @param	{object[]}	shares	From UnshackleShares()
 * @returns	{function}	has => multiplier, where has(name) tells whether an upgrade is owned or planned
 */
export function UnshackledValue(shares) {
  const owned = (name) => !!(Game.Upgrades[name] && Game.Upgrades[name].bought);
  const factor = (it, has) =>
    has(it.upgrade) ? it.tiers.reduce((f, tier) => (has(tier) ? f * it.gain : f), it.base) : 1;
  const weights = shares.map((it) => it.share / factor(it, owned));
  return (has) =>
    shares.length ? shares.reduce((sum, it, i) => sum + weights[i] * factor(it, has), 0) : 1;
}

/**
 * Shares of income from clicks and golden cookies that value the heavenly upgrades. "Lucky!" is
 * counted at its maximum, as autoplay keeps the bank for it when that pays
 * @param	{number}	income		Cookies per second
 * @param	{number}	clickIncome	Cookies per second from auto-click
 * @returns	{{clickShare: number, golden: object, autoplay: object, unshackle: object[], grandmaShare: number}}
 */
export function HeavenlyContext(income, clickIncome) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const unshackle = UnshackleShares();
  const grandma = Game.Objects.Grandma;
  const grandmas = grandma && unshackle.find((it) => it.upgrade === grandma.unshackleUpgrade);
  return {
    clickShare: income > 0 ? clickIncome / income : 0,
    golden: GoldenShares(income, CacheLucky),
    autoplay: {
      dragon: !!settings.AutoDragon,
      seasons: !!settings.AutoSeasons,
      elder: !!settings.AutoElder,
      achievements: !!settings.AutoAchievements,
    },
    unshackle,
    grandmaShare: grandmas ? grandmas.share : 0,
  };
}

/**
 * The unowned upgrades needed to own `upgrade`, parents first (the ascension screen only sells an
 * upgrade once all its parents are owned)
 * @param	{object}	upgrade	A heavenly upgrade
 * @param	{object}	planned	Names already owned or planned
 * @returns	{object[]|null}	The upgrades to buy in order, or null if one of them is unavailable
 */
function Bundle(upgrade, planned) {
  const bundle = [];
  const seen = {};
  const visit = (me) => {
    if (!me || me === -1 || me.bought || planned[me.name] || seen[me.name]) return true;
    if (me.showIf && !me.showIf()) return false;
    seen[me.name] = true;
    for (let i = 0; i < me.parents.length; i++) {
      if (!visit(me.parents[i])) return false;
    }
    bundle.push(me);
    return true;
  };
  return visit(upgrade) ? bundle : null;
}

/**
 * Orders the valued heavenly upgrades by time saved per chip: repeatedly picks the upgrade whose
 * bundle (the upgrade plus the parents it still needs, valued together) has the largest
 * (1 - 1/multiplier) / effectiveCost. The effective cost discounts each later price by earlier
 * multipliers in that bundle. This exchange rule is exact for independent fixed blocks in the
 * proportional earning model. Searching only ancestor bundles is a heuristic for general prerequisites.
 * The multiplier of an "Unshackled" upgrade is its gain given the upgrades planned before it.
 * Legacy is left out. It costs one chip and is always bought first.
 * The ascension planner assumes chips are spent along this order, saving up for the next item, and
 * auto-ascend spends them exactly that way.
 * @param	{object}	ctx	From HeavenlyContext()
 * @returns	{{name: string, bundle: object[], cost: number, mult: number}[]}
 */
export default function HeavenlyPurchaseOrder(ctx) {
  const planned = { Legacy: true };
  const shares = ctx.unshackle || [];
  const unshackledValue = UnshackledValue(shares);
  const unshackled = {};
  shares.forEach((it) => {
    unshackled[it.upgrade] = true;
    it.tiers.forEach((tier) => {
      unshackled[tier] = true;
    });
  });
  const valueOf = (me) =>
    HeavenlyUpgradeValues[me.name] ? HeavenlyUpgradeValues[me.name](ctx) : 1;
  const bought = (name) => !!(Game.Upgrades[name] && Game.Upgrades[name].bought);
  const candidates = Object.keys(HeavenlyUpgradeValues)
    .concat(Object.keys(unshackled))
    .map((name) => Game.Upgrades[name])
    .filter((me) => me && !me.bought);
  const order = [];
  for (;;) {
    const level = unshackledValue((name) => !!planned[name] || bought(name));
    let best = null;
    candidates.forEach((me) => {
      if (planned[me.name]) return;
      const bundle = Bundle(me, planned);
      if (bundle === null) return;
      const added = {};
      const has = (name) => !!added[name] || !!planned[name] || bought(name);
      let reached = level;
      const steps = bundle.map((it) => {
        added[it.name] = true;
        let mult = valueOf(it);
        if (unshackled[it.name]) {
          const next = unshackledValue(has);
          mult = reached > 0 ? next / reached : 1;
          reached = next;
        }
        return { cost: it.getPrice(), mult };
      });
      let mult = 1;
      let effectiveCost = 0;
      steps.forEach((step) => {
        effectiveCost += step.cost / mult;
        mult *= step.mult;
      });
      if (!(mult > 1)) return;
      const cost = bundle.reduce((sum, it) => sum + it.getPrice(), 0);
      const density = effectiveCost > 0 ? (1 - 1 / mult) / effectiveCost : Infinity;
      if (best === null || density > best.density)
        best = { name: me.dname || me.name, bundle, steps, cost, effectiveCost, mult, density };
    });
    if (best === null) return order;
    best.bundle.forEach((it) => {
      planned[it.name] = true;
    });
    order.push(best);
  }
}
