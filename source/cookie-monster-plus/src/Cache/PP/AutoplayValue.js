/**
 * Section: What upgrades are worth when autoplay clicks the cookie and golden cookies
 *
 * Cookie Monster's CpS simulation values click upgrades and golden cookie upgrades at zero, so they
 * show up gray. With auto-click a click upgrade is worth its extra cookies per click times the click
 * rate, and with auto golden cookies an upgrade that makes golden cookies more frequent or longer is
 * worth the share of income golden cookies bring in.
 */

import GetCPSBuffMult from '../CPS/GetCPSBuffMult.js';
import { CacheGoldenCookiesMult } from '../VariablesAndData.js';
import { GodzamokMultiplier } from './Godzamok.js';

/** Rough share of golden cookies that turn out "Lucky!" and "Frenzy" respectively */
const LUCKY_SHARE = 0.42;
const FRENZY_SHARE = 0.42;
/** A Frenzy multiplies CpS by 7 for 77 seconds */
const FRENZY_EXTRA_SECONDS = 6 * 77;
/** "Lucky!" pays at most 900 seconds of CpS, when the bank holds at least 6000 seconds */
const LUCKY_MAX_SECONDS = 900;
/** Seconds between golden cookies when the game has not computed its spawn window yet */
const DEFAULT_GOLDEN_INTERVAL = 462;
/**
 * Shares of golden cookie outcomes by Grandmapocalypse stage, when each cookie is a wrath cookie with
 * chance 0, 1/3, 2/3 or 1. Simulated from the game's choice rule (at least 10 buildings, no dragon
 * auras, an 80% chance to avoid repeating the last outcome). Wrath cookies give up Frenzies for clots
 * and ruin, but bring cookie storms and Elder frenzies far more often
 */
const OUTCOME_SHARES = [
  {
    frenzy: 0.4215,
    lucky: 0.4218,
    special: 0.1002,
    clickFrenzy: 0.0397,
    storm: 0.0084,
    chain: 0.0084,
  },
  {
    frenzy: 0.2936,
    lucky: 0.3407,
    special: 0.076,
    debuff: 0.0055,
    clickFrenzy: 0.0324,
    storm: 0.0235,
    chain: 0.0234,
    blood: 0.0167,
    clot: 0.0903,
    ruin: 0.0902,
    cursed: 0.0075,
  },
  {
    frenzy: 0.1565,
    lucky: 0.2801,
    special: 0.0563,
    debuff: 0.0113,
    clickFrenzy: 0.0269,
    storm: 0.039,
    chain: 0.0388,
    blood: 0.0339,
    clot: 0.171,
    ruin: 0.1708,
    cursed: 0.0154,
  },
  {
    lucky: 0.2447,
    special: 0.0411,
    debuff: 0.0176,
    clickFrenzy: 0.0231,
    storm: 0.055,
    chain: 0.0553,
    blood: 0.051,
    clot: 0.2446,
    ruin: 0.2442,
    cursed: 0.0234,
  },
];
/** Gamma(7/6), for the mean golden cookie interval */
const GAMMA_7_6 = 0.927719;

/**
 * Clicks per second of auto-click, 0 when it is off
 * @returns	{number}
 */
export function AutoClickRate() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  return settings.AutoClick ? Math.min(Math.max(Number(settings.AutoClickRate) || 0, 0), 50) : 0;
}

/**
 * Average seconds between golden cookies. The spawn chance per frame grows like (k / W)^5 for the k-th
 * frame of a window of W frames, so a cookie survives to fraction x of the window with probability
 * about exp(-W x^6 / 6) and arrives on average at x = Gamma(7/6) (6 / W)^(1/6) of the way in: 24% of the
 * base window, 31% with both frequency upgrades
 * @returns	{number}
 */
export function GoldenCookieInterval() {
  const { golden } = Game.shimmerTypes;
  const window = golden.maxTime - golden.minTime;
  const share = window > 0 ? Math.min(GAMMA_7_6 * (6 / window) ** (1 / 6), 1) : 0;
  const interval = (golden.minTime + share * window) / Game.fps;
  return Number.isFinite(interval) && interval > 0 ? interval : DEFAULT_GOLDEN_INTERVAL;
}

/**
 * Grandmapocalypse stage that decides how many golden cookies are wrath cookies (0 while a pledge or
 * the covenant holds; Skruuia makes them all wrath)
 * @returns	{number}	0 to 3
 */
export function GrandmapocalypseStage() {
  if (Game.hasGod && Game.hasGod('scorn')) return 3;
  return Math.min(Math.max(Math.round(Number(Game.elderWrath) || 0), 0), 3);
}

/**
 * Extra production from Frenzies as a share of production. A Frenzy multiplies CpS, and the click
 * power that comes from CpS, by 7 for 77 seconds (154 with "Get lucky")
 * @returns	{number}
 */
function FrenzyShare() {
  return (
    (FRENZY_SHARE * FRENZY_EXTRA_SECONDS * (Game.Has('Get lucky') ? 2 : 1)) / GoldenCookieInterval()
  );
}

/**
 * Income from golden cookies as a share of other income, 0 when auto golden cookies is off
 * @param	{number}	income	Cookies per second without golden cookies
 * @param	{number}	bank	Cookies in the bank, which caps "Lucky!" rewards
 * @returns	{{frenzy: number, lucky: number, total: number}}
 */
export function GoldenShares(income, bank) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGolden) return { frenzy: 0, lucky: 0, total: 0 };
  const interval = GoldenCookieInterval();
  const frenzy = FrenzyShare();
  const lucky =
    (LUCKY_SHARE *
      Math.min(LUCKY_MAX_SECONDS, (0.15 * bank) / Math.max(income, 1e-9)) *
      CacheGoldenCookiesMult) /
    interval;
  return { frenzy, lucky, total: frenzy + lucky };
}

/**
 * Seconds for a banked cookie, below the "Lucky!" bank, to pay itself back through golden cookies:
 * "Lucky!" pays 15% of the bank and a cookie chain about a fifth of it, while a wrath "Ruin" takes 5%
 * @returns	{number}
 */
export function LuckyBankPayback() {
  const shares = OUTCOME_SHARES[GrandmapocalypseStage()];
  const g = CacheGoldenCookiesMult;
  const perCookie =
    (shares.lucky || 0) * 0.15 * g + (shares.chain || 0) * 0.215 * g - (shares.ruin || 0) * 0.05;
  return perCookie > 0 ? GoldenCookieInterval() / perCookie : Infinity;
}

/**
 * Extra income from a store upgrade about golden cookies
 * @param	{string}	name	Upgrade name
 * @param	{number}	income	Cookies per second
 * @param	{number}	bank	Cookies in the bank
 * @returns	{number}	Cookies per second
 */
export function GoldenUpgradeValue(name, income, bank) {
  const shares = GoldenShares(income, bank);
  // "Golden cookies appear twice as often", so golden cookie income doubles
  if (name === 'Lucky day' || name === 'Serendipity') return income * shares.total;
  // "Golden cookie effects last twice as long": Frenzies double, "Lucky!" does not
  if (name === 'Get lucky') return income * shares.frenzy;
  if (name === 'Golden goose egg') return 0.05 * income * shares.total;
  return 0;
}

/**
 * Value of a store upgrade under autoplay: its CpS, its click power at the auto-click rate and its
 * golden cookie effect
 * @param	{string}	name	Upgrade name
 * @param	{object}	cached	The upgrade's entry in CM.Cache.Upgrades ({bonus, bonusMouse})
 * @param	{number}	income	Cookies per second
 * @param	{number}	bank	Cookies in the bank
 * @returns	{number}	Cookies per second
 */
export function AutoplayUpgradeValue(name, cached, income, bank) {
  return (
    (cached.bonus || 0) +
    AutoClickRate() * Math.max(cached.bonusMouse || 0, 0) +
    GoldenUpgradeValue(name, income, bank)
  );
}

/**
 * Income used by autoplay: CpS (without wrinkler losses) plus auto-click income
 * @returns	{number}	Cookies per second
 */
export function AutoplayIncome() {
  return Math.max(
    Game.cookiesPs * (1 - Game.cpsSucked) + AutoClickRate() * Game.computedMouseCps,
    1e-9,
  );
}

/**
 * Product of the current buffs' multipliers on click power (Click frenzy, Dragonflight, ...)
 * @returns	{number}
 */
function ClickBuffMult() {
  let mult = 1;
  Object.keys(Game.buffs).forEach((i) => {
    if (typeof Game.buffs[i].multClick !== 'undefined') mult *= Game.buffs[i].multClick;
  });
  return mult;
}

/**
 * How much longer golden cookie effects last, as the game computes it when one is clicked
 * @returns	{number}
 */
export function EffectDuration() {
  let d = 1;
  if (Game.Has('Get lucky')) d *= 2;
  if (Game.Has('Lasting fortune')) d *= 1.1;
  ['Lucky digit', 'Lucky number', 'Green yeast digestives', 'Lucky payout'].forEach((name) => {
    if (Game.Has(name)) d *= 1.01;
  });
  if (Game.auraMult) d *= 1 + Game.auraMult('Epoch Manipulator') * 0.05;
  if (Game.eff) d *= Game.eff('goldenCookieEffDur');
  if (Game.hasGod) d *= [1, 1.07, 1.05, 1.02][Game.hasGod('decadence') || 0];
  return d;
}

/**
 * Wrinklers autoplay expects to keep: the most the game allows once the Grandmapocalypse has started,
 * otherwise those already there
 * @returns	{number}
 */
export function ExpectedWrinklers() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (settings.AutoElder && Game.elderWrath > 0 && Game.getWrinklersMax)
    return Game.getWrinklersMax();
  return (Game.wrinklers || []).filter((me) => me.phase === 2).length;
}

/**
 * Long-run multiplier n wrinklers put on CpS. Each one digests the whole withered share s = n / 20 of
 * CpS and returns it x1.1 (plus bonuses) when popped, so they turn 1 into 1 - s + s * n * 1.1: about 6
 * with 10 wrinklers
 * @param	{number}	n	Wrinklers
 * @returns	{number}
 */
export function WrinklerFactor(n) {
  if (!(n > 0)) return 1;
  const guts = Game.auraMult ? Game.auraMult('Dragon Guts') : 0;
  const s = Math.min(1, n * 0.05 * (Game.eff ? Game.eff('wrinklerEat') : 1) * (1 + guts * 0.2));
  let back = 1.1 * (1 + guts * 0.2);
  if (Game.Has('Sacrilegious corruption')) back *= 1.05;
  if (Game.Has('Wrinklerspawn')) back *= 1.05;
  if (Game.hasGod) back *= [1, 1.15, 1.1, 1.05][Game.hasGod('scorn') || 0];
  return 1 - s + s * n * back;
}

/**
 * Average extra seconds of CpS, of click income and of direct payout each golden cookie outcome brings
 * (d: effect duration, n: mean count of building types with at least 10, r: clicks per second, g: golden
 * cookie gains). Buffs multiply CpS and the click power that comes from it; wrinklers digest buffed CpS
 * too, so buff seconds are worth W each, while payouts arrive directly
 * @returns	{object}	{outcome: {buff, click, direct}}
 */
function OutcomeEffects(d, n, r, g) {
  const debuff = -30 * d * (1 - 10 / (10 + n));
  return {
    frenzy: { buff: 6 * 77 * d, click: 6 * 77 * d, direct: 0 },
    special: { buff: 3 * n * d, click: 3 * n * d, direct: 0 },
    debuff: { buff: debuff, click: debuff, direct: 0 },
    blood: { buff: 665 * 6 * d, click: 665 * 6 * d, direct: 0 },
    clot: { buff: -0.5 * 66 * d, click: -0.5 * 66 * d, direct: 0 },
    clickFrenzy: { buff: 0, click: 776 * 13 * d, direct: 0 },
    // Cookie storms drop about 15 golden cookies a second, each worth 1 to 7 minutes of CpS
    storm: { buff: 0, click: 0, direct: 105 * d * 240 * g },
    // A cursed finger halts production; each click pays 10 seconds of CpS instead
    cursed: { buff: -10 * d, click: -10 * d, direct: r * (10 * d) ** 2 },
  };
}

/**
 * Golden cookie model for the auto-buyer: the long-run multipliers golden cookies put on one cookie per
 * second of CpS and of click income (below the "Lucky!" bank, where "Lucky!", chains and ruin depend on
 * the bank rather than on production), and the golden cookie income in all
 * @param	{number}	bank	Cookies in the bank
 * @param	{number}	cps	CpS without buffs
 * @param	{number}	clicks	Auto-click income without buffs
 * @param	{number}	W	Wrinkler factor
 * @param	{number}	intervalMult	Factor on the golden cookie interval (to try out other gods)
 * @param	{number}	stage	Grandmapocalypse stage, which sets the mix of outcomes
 * @returns	{{growth: {cps: number, click: number}, golden: number, lasting: number}}
 */
function GoldenModel(bank, cps, clicks, W, intervalMult, stage) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGolden) return { growth: { cps: W, click: 1 }, golden: 0, lasting: 0 };
  const tall = Object.keys(Game.Objects)
    .map((name) => Game.Objects[name].amount)
    .filter((amount) => amount >= 10);
  const n = tall.length ? tall.reduce((sum, amount) => sum + amount, 0) / tall.length : 0;
  const g = CacheGoldenCookiesMult;
  const effects = OutcomeEffects(EffectDuration(), n, AutoClickRate(), g);
  const shares = OUTCOME_SHARES[stage];
  const interval = GoldenCookieInterval() * intervalMult;
  let cpsGain = 0;
  let clickGain = 0;
  Object.keys(effects).forEach((outcome) => {
    const share = shares[outcome] || 0;
    cpsGain += (share * (effects[outcome].buff * W + effects[outcome].direct)) / interval;
    clickGain += (share * effects[outcome].click) / interval;
  });
  const lasting = cpsGain * cps + clickGain * clicks;
  const bankGain =
    ((shares.lucky || 0) * Math.min(0.15 * bank, 900 * cps) * g +
      (shares.chain || 0) * 0.43 * Math.min(21600 * cps, 0.5 * bank) * g -
      (shares.ruin || 0) * Math.min(0.05 * bank, 600 * cps)) /
    interval;
  return {
    growth: { cps: W + cpsGain, click: 1 + clickGain },
    golden: lasting + bankGain,
    lasting,
  };
}

/**
 * The economy the auto-buyer judges purchases by, with current buffs taken out (otherwise a Frenzy
 * would make every purchase look seven times better for 77 seconds): CpS, auto-click income, the
 * long-run multipliers golden cookies and wrinklers put on each, the golden cookie income and the
 * expected total income, which fills the bank. Click income includes the average "Devastation" buff
 * that selling and buying back buildings keeps up when Godzamok is slotted
 * @param	{number}	bank	Cookies in the bank
 * @param	{number}	[intervalMult]	Factor on the golden cookie interval (to try out other gods)
 * @param	{{stage: number, W: number}}	[assume]	Grandmapocalypse stage and wrinkler factor to assume
 * instead of the current ones (to compare stages)
 * @returns	{{cpsBuff: number, clickBuff: number, devastation: number, cps: number, clicks: number, W: number, growth: {cps: number, click: number}, golden: number, lasting: number, income: number}}
 */
export function AutoplayEconomy(bank, intervalMult = 1, assume = {}) {
  const cpsBuff = GetCPSBuffMult() || 1;
  const clickBuff = ClickBuffMult() || 1;
  const cps = Game.cookiesPs / cpsBuff;
  const baseClicks = (AutoClickRate() * Game.computedMouseCps) / (cpsBuff * clickBuff);
  const devastation = GodzamokMultiplier(baseClicks, bank);
  const clicks = baseClicks * devastation;
  const W = assume.W !== undefined ? assume.W : WrinklerFactor(ExpectedWrinklers());
  const stage = assume.stage !== undefined ? assume.stage : GrandmapocalypseStage();
  const model = GoldenModel(bank, cps, clicks, W, intervalMult, stage);
  return {
    cpsBuff,
    clickBuff,
    devastation,
    cps,
    clicks,
    W,
    growth: model.growth,
    golden: model.golden,
    lasting: model.lasting,
    income: Math.max(cps * W + clicks + model.golden, 1e-9),
  };
}

/**
 * What a golden cookie upgrade adds to income under autoplay: twice as frequent doubles golden cookie
 * income, twice as long doubles every effect but "Lucky!", chains and ruin
 * @param	{string}	name	Upgrade name
 * @param	{object}	economy	From AutoplayEconomy()
 * @returns	{number}	Cookies per second
 */
function GoldenEffectValue(name, economy) {
  if (name === 'Lucky day' || name === 'Serendipity') return economy.golden;
  if (name === 'Golden goose egg') return 0.05 * economy.golden;
  if (name === 'Get lucky') return economy.lasting;
  return 0;
}

/**
 * What a purchase adds to long-run income under autoplay, in cookies per second: its CpS and its click
 * power at the auto-click rate, without current buffs and multiplied by what golden cookies and
 * wrinklers make of each, plus its effect on golden cookies. This is the gain to compare with the
 * "Lucky!" return of keeping the cookies in the bank
 * @param	{string}	name	Building or upgrade name
 * @param	{object}	cached	Its entry in CM.Cache ({bonus, bonusMouse})
 * @param	{object}	economy	From AutoplayEconomy()
 * @returns	{number}	Cookies per second
 */
export function LongRunValue(name, cached, economy) {
  const cps = (cached.bonus || 0) / economy.cpsBuff;
  const clicks =
    (AutoClickRate() * Math.max(cached.bonusMouse || 0, 0) * (economy.devastation || 1)) /
    (economy.cpsBuff * economy.clickBuff);
  return (
    cps * economy.growth.cps + clicks * economy.growth.click + GoldenEffectValue(name, economy)
  );
}

/** Kitten upgrades and how much of the milk each turns into CpS, from the game's CpS formula */
const KITTENS = {
  'Kitten helpers': 0.1,
  'Kitten workers': 0.125,
  'Kitten engineers': 0.15,
  'Kitten overseers': 0.175,
  'Kitten managers': 0.2,
  'Kitten accountants': 0.2,
  'Kitten specialists': 0.2,
  'Kitten experts': 0.2,
  'Kitten consultants': 0.2,
  'Kitten assistants to the regional manager': 0.175,
  'Kitten marketeers': 0.15,
  'Kitten analysts': 0.125,
  'Kitten executives': 0.115,
  'Kitten admins': 0.11,
  'Kitten strategists': 0.105,
  'Kitten angels': 0.1,
  'Fortune #103': 0.05,
};

/**
 * How strongly milk counts, as in the game's CpS formula (Santa's milk and cookies, Breath of Milk,
 * Mokalsium and the milk effect of garden plants)
 * @returns	{number}
 */
export function MilkMultiplier() {
  let m = 1;
  if (Game.Has("Santa's milk and cookies")) m *= 1.05;
  if (Game.auraMult) m *= 1 + Game.auraMult('Breath of Milk') * 0.05;
  if (Game.hasGod) m *= [1, 1.1, 1.05, 1.03][Game.hasGod('mother') || 0];
  if (Game.eff) m *= Game.eff('milk');
  return m;
}

/**
 * Share of CpS one more achievement adds: it raises milk by 0.04, and each owned kitten multiplies CpS
 * by 1 + k * milk * m, so CpS grows by the factor prod (1 + k m (milk + 0.04)) / (1 + k m milk)
 * @returns	{number}
 */
export function AchievementValue() {
  const m = MilkMultiplier();
  const milk = Game.milkProgress || 0;
  let ratio = 1;
  Object.keys(KITTENS).forEach((name) => {
    if (Game.Has(name))
      ratio *= (1 + KITTENS[name] * m * (milk + 0.04)) / (1 + KITTENS[name] * m * milk);
  });
  return ratio - 1;
}

/**
 * Seconds of play still to come, for valuing permanent gains: as long again as the save has been played
 * so far (with no other information, the median remaining lifetime of something equals its age), and at
 * least an hour
 * @returns	{number}
 */
export function PlayHorizon() {
  const played = (Date.now() - (Number(Game.fullDate) || Date.now())) / 1000;
  return Math.max(played, 3600);
}

/**
 * What achievements are worth in seconds of play. A run at speed S retraces the same trajectory S times
 * faster, so a permanent gain of a share x of income makes all future play x faster: over a horizon H it
 * is worth x H seconds, to be weighed against seconds of delay (cookies spent at income I cost
 * cookies / I seconds)
 * @param	{number}	[count]	Achievements
 * @returns	{number}	Seconds
 */
export function AchievementWorth(count = 1) {
  return count * AchievementValue() * PlayHorizon();
}

/**
 * Factor of milk a kitten upgrade turns into CpS (0 for anything else)
 * @param	{string}	name	Upgrade name
 * @returns	{number}
 */
export function KittenMilkFactor(name) {
  return KITTENS[name] || 0;
}
