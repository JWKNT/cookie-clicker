/** Section: Which heavenly upgrades to buy with heavenly chips, and in which order */

import { GoldenShares } from '../PP/AutoplayValue.js';
import { CacheLucky } from '../VariablesAndData.js';

/** "Lucky ..." heavenly upgrades: +1% prestige effect on CpS and +1% golden cookie effect duration */
const luckyUpgrade = (ctx) => 1.01 * (1 + 0.01 * ctx.golden.frenzy);

/**
 * Estimated production multiplier of each heavenly upgrade worth chips under autoplay, given
 * ctx = {clickShare, golden: {frenzy, lucky, total}, autoplay} (income shares of clicks and golden
 * cookies, and which autoplay systems are on).
 * Upgrades not listed are only bought as parents of listed ones: cosmetics, the golden switch and the
 * shimmering veil (they turn off or break on golden cookies), offline production, fortunes, gifts,
 * petting the dragon and the sugar frenzy.
 */
export const HeavenlyUpgradeValues = {
  'Heavenly cookies': () => 1.1,
  'Wrinkly cookies': () => 1.1,
  'Sugar crystal cookies': () => 1.05,
  Heralds: () => 1 + 0.01 * Game.heralds,
  'Kitten angels': () => 1 + 0.1 * Game.milkProgress,
  'Halo gloves': (ctx) => 1 + 0.1 * ctx.clickShare,
  'Heavenly luck': (ctx) => 1 + 0.05 * ctx.golden.total,
  'Lasting fortune': (ctx) => 1 + 0.1 * ctx.golden.frenzy,
  'Lucky digit': luckyUpgrade,
  'Lucky number': luckyUpgrade,
  'Lucky payout': luckyUpgrade,
  'Distilled essence of redoubled luck': (ctx) => 1 + 0.01 * ctx.golden.total,
  'Sugar baking': () => 1 + 0.01 * Math.min(Game.lumps, 100),
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
};

/**
 * Shares of income from clicks and golden cookies that value the heavenly upgrades. "Lucky!" is
 * counted at its maximum, as autoplay keeps the bank for it when that pays
 * @param	{number}	income		Cookies per second
 * @param	{number}	clickIncome	Cookies per second from auto-click
 * @returns	{{clickShare: number, golden: object, autoplay: object}}
 */
export function HeavenlyContext(income, clickIncome) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  return {
    clickShare: income > 0 ? clickIncome / income : 0,
    golden: GoldenShares(income, CacheLucky),
    autoplay: {
      dragon: !!settings.AutoDragon,
      seasons: !!settings.AutoSeasons,
      elder: !!settings.AutoElder,
      achievements: !!settings.AutoAchievements,
    },
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
 * (1 - 1/multiplier) / cost. When earning chips takes time inversely proportional to the speed, swapping
 * two adjacent purchases changes the total time by exactly the difference of this index, so sorting by
 * it is optimal (Smith's rule for multiplicative speed-ups). Legacy is left out; it costs one chip and
 * is always bought first.
 * The ascension planner assumes chips are spent along this order, saving up for the next item, and
 * auto-ascend spends them exactly that way.
 * @param	{object}	ctx	From HeavenlyContext()
 * @returns	{{name: string, bundle: object[], cost: number, mult: number}[]}
 */
export default function HeavenlyPurchaseOrder(ctx) {
  const planned = { Legacy: true };
  const valueOf = (me) =>
    HeavenlyUpgradeValues[me.name] ? HeavenlyUpgradeValues[me.name](ctx) : 1;
  const candidates = Object.keys(HeavenlyUpgradeValues)
    .map((name) => Game.Upgrades[name])
    .filter((me) => me && !me.bought);
  const order = [];
  for (;;) {
    let best = null;
    candidates.forEach((me) => {
      if (planned[me.name]) return;
      const bundle = Bundle(me, planned);
      if (bundle === null) return;
      const mult = bundle.reduce((product, it) => product * valueOf(it), 1);
      if (!(mult > 1)) return;
      const cost = bundle.reduce((sum, it) => sum + it.getPrice(), 0);
      const density = (1 - 1 / mult) / Math.max(cost, 1);
      if (best === null || density > best.density)
        best = { name: me.dname || me.name, bundle, cost, mult, density };
    });
    if (best === null) return order;
    best.bundle.forEach((it) => {
      planned[it.name] = true;
    });
    order.push(best);
  }
}
