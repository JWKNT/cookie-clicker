import { AutoplayEconomy, LongRunValue, LuckyBankPayback } from '../../Cache/PP/AutoplayValue.js';
import {
  CacheLucky,
  CacheObjects1,
  CacheUpgrades,
  CookiesDiff,
} from '../../Cache/VariablesAndData.js';
import { SimDoSims } from '../../Sim/VariablesAndData.js';
import { RESERVE_SECONDS, SeasonState } from './AutoSeasons.js';
import { UpgradesAllowed } from './Challenge.js';

/** Upgrade pools the buyer never touches: switches, heavenly upgrades and unused content */
const SkippedPools = ['toggle', 'prestige', 'debug', 'dungeon', 'shadow', 'unused'];
/** The Chocolate egg is worth most right before ascending, which the ascension routine handles */
const SkippedUpgrades = ['Chocolate egg'];
/** Seconds of measured income behind the countdown, and the least history it needs */
const ETA_WINDOW = 600;
const ETA_MIN_HISTORY = 60;
/** Milliseconds of purchases per frame */
export const BURST_MS = 4;
/** Most copies of one building in one purchase */
export const MAX_COPIES = 1000;
/** Frames between plan updates while the buyer saves up */
const WAIT_FRAMES = 10;

/**
 * The purchase the buyer is saving for, shown in the timer bar
 * @item	{object|null}	next	{name, price, payback, reserve, reason, spendable, eta} or null when nothing is planned;
 * reserve is what is kept back from this purchase (0 when none): the "Lucky!" bank (reason 'lucky') or
 * cookies for the next seasonal action (reason 'season'); spendable is the bank above it
 */
export const AutoBuyState = { next: null };

let NextPlan = 0;

/**
 * Whether the buyer keeps its plan this frame: while it saves up it checks the plan a few times a
 * second, or at once when the planned purchase is affordable
 * Game.T restarts at 0 when the game resets for an ascension, so a check scheduled more than
 * WAIT_FRAMES ahead belongs to an earlier run and is ignored
 * @param	{number}	now	The current frame (Game.T)
 * @param	{number}	nextPlan	The frame of the next scheduled check
 * @param	{object|null}	next	The plan (AutoBuyState.next)
 * @param	{number}	bank	Cookies in the bank
 * @returns	{boolean}	Whether to skip planning this frame
 */
export function KeepPlan(now, nextPlan, next, bank) {
  if (!(now < nextPlan) || nextPlan - now > WAIT_FRAMES) return false;
  return !(next && bank - next.reserve >= next.price);
}

/**
 * The cookies kept back from a purchase with this payback period
 * @param	{number}	payback	Seconds for the purchase to pay for itself
 * @param	{{keepLucky: boolean, bankPayback: number, luckyBank: number, seasonReserve: number, seasonPayback: number}}	rules
 * Reserve rules of this frame: whether to keep a "Lucky!" bank, the payback period above which it
 * applies and its size at the start of the frame; the cookies kept for the next seasonal action and the
 * payback period above which they are kept
 * @returns	{{reserve: number, reason: string}}	The reserve and its reason ('lucky', 'season' or '')
 */
function Reserve(payback, rules) {
  const lucky = rules.keepLucky && payback > rules.bankPayback ? rules.luckyBank : 0;
  const season = payback > rules.seasonPayback ? rules.seasonReserve : 0;
  const reserve = Math.max(lucky, season);
  if (!(reserve > 0)) return { reserve: 0, reason: '' };
  return { reserve, reason: lucky >= season ? 'lucky' : 'season' };
}

/**
 * The buildings and upgrades the buyer may buy, with what each adds to long-run income
 * The values come from Cookie Monster's caches, which are current at the start of the frame
 * @param	{object}	economy	From AutoplayEconomy()
 * @returns	{{name: string, me: object, building: boolean, value: number}[]}	Candidates with a positive value
 */
function Candidates(economy) {
  const list = [];
  Object.keys(Game.Objects).forEach((name) => {
    const me = Game.Objects[name];
    if (me.locked || !CacheObjects1[name]) return;
    list.push({ name, me, building: true, value: LongRunValue(name, CacheObjects1[name], economy) });
  });
  if (UpgradesAllowed())
    Game.UpgradesInStore.forEach((me) => {
      if (
        SkippedPools.includes(me.pool) ||
        SkippedUpgrades.includes(me.name) ||
        me.clickFunction ||
        me.priceLumps > 0
      )
        return;
      const value = LongRunValue(me.name, CacheUpgrades[me.name] || {}, economy);
      list.push({ name: me.dname || me.name, me, building: false, value });
    });
  return list.filter((c) => c.value > 0);
}

/**
 * Ranks the candidates by payback period at the current bank: the time to save for each one plus the
 * time it takes to pay for itself
 * @param	{object[]}	candidates	From Candidates()
 * @param	{number}	bank	Cookies in the bank
 * @param	{number}	income	Expected income, which fills the bank
 * @param	{object}	rules	Reserve rules of this frame (see Reserve())
 * @returns	{{best: object|null, second: object|null}}	The best candidate and the runner-up, each
 * {c, price, payback, pp, reserve, reason}
 */
export function Rank(candidates, bank, income, rules) {
  let best = null;
  let second = null;
  candidates.forEach((c) => {
    if (!c.building && c.me.bought) return;
    const price = c.me.getPrice();
    if (!Number.isFinite(price)) return;
    const payback = price / c.value;
    const { reserve, reason } = Reserve(payback, rules);
    const pp = Math.max(price - (bank - reserve), 0) / income + payback;
    const entry = { c, price, payback, pp, reserve, reason };
    if (best === null || pp < best.pp) {
      second = best;
      best = entry;
    } else if (second === null || pp < second.pp) second = entry;
  });
  return { best, second };
}

/**
 * How many copies of the best building to buy before the runner-up: every copy must be affordable,
 * pay back no slower than the runner-up and need the same reserve as the first copy
 * Copies cost 1.15 times the copy before them and add the same income
 * @param	{object}	best	The best candidate, a building (from Rank())
 * @param	{object|null}	second	The runner-up (from Rank())
 * @param	{number}	bank	Cookies in the bank
 * @param	{object}	rules	Reserve rules of this frame (see Reserve())
 * @returns	{number}	Copies to buy, at least 1
 */
export function Copies(best, second, bank, rules) {
  const { me, value } = best.c;
  const factor = Game.modifyBuildingPrice(me, 1);
  const limit = second ? second.pp : Infinity;
  let cost = 0;
  let n = 0;
  while (n < MAX_COPIES) {
    const price =
      n === 0
        ? best.price
        : Math.ceil(me.basePrice * Game.priceIncrease ** Math.max(0, me.amount + n - me.free) * factor);
    const payback = price / value;
    if (n > 0 && (payback > limit || Reserve(payback, rules).reserve !== best.reserve)) break;
    if (cost + price > bank - best.reserve) break;
    cost += price;
    n += 1;
  }
  return Math.max(n, 1);
}

/**
 * Buys buildings and upgrades in order of payback period as soon as they are affordable
 * Purchases are valued by what they add to long-run income under autoplay: CpS and click power at the
 * auto-click rate, without current buffs and grown by Frenzies, plus golden cookie effects. Cookies are
 * kept for a maximum "Lucky!" reward whenever a banked cookie pays itself back through "Lucky!" faster
 * than the purchase would
 * Each frame buys as much as BURST_MS allows, with the values from the start of the frame. More copies
 * of a building only raise the value of other purchases, so these values never overrate a purchase.
 * The frame stops after an upgrade and before a second purchase that needs a reserve, because an
 * upgrade can change many values and the "Lucky!" bank grows with CpS
 */
export default function AutoBuy() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  // Cookie Monster recomputes its values after autoplay runs. They are stale on the frame after CpS
  // changes, and when CpS changed earlier in this frame
  if (settings.AutoBuy && (SimDoSims || Game.recalculateGains)) return;
  if (!settings.AutoBuy || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0) {
    AutoBuyState.next = null;
    return;
  }
  if (Game.buyMode !== 1) {
    AutoBuyState.next = null; // The store is in sell mode
    return;
  }
  if (KeepPlan(Game.T, NextPlan, AutoBuyState.next, Game.cookies)) return;

  const economy = AutoplayEconomy(Game.cookies);
  const rules = {
    keepLucky: settings.AutoGolden && settings.AutoBuyLuckyBank,
    bankPayback: LuckyBankPayback(),
    luckyBank: CacheLucky,
    seasonReserve: settings.AutoSeasons ? SeasonState.reserve : 0,
    seasonPayback: RESERVE_SECONDS,
  };
  if (rules.keepLucky && !(CacheLucky > 0) && Game.cookiesPs > 0) {
    AutoBuyState.next = null; // "Lucky!" bank not known yet
    return;
  }

  const candidates = Candidates(economy);
  const start = performance.now();
  const { volume } = Game;
  let purchases = 0;
  let upgradeBought = false;
  let plan = null;
  let affordable = false;
  try {
    for (;;) {
      const bank = Game.cookies;
      const { best, second } = Rank(candidates, bank, economy.income, rules);
      plan = best;
      affordable = best !== null && best.price <= bank - best.reserve;
      if (!affordable) break;
      if (purchases > 0) {
        if (upgradeBought || best.reserve > 0 || performance.now() - start >= BURST_MS) break;
        Game.volume = 0; // One purchase sound per frame
      }
      const { me } = best.c;
      if (best.c.building) {
        const owned = me.amount;
        me.buy(Copies(best, second, bank, rules));
        if (me.amount === owned) break;
      } else {
        me.buy();
        if (!me.bought) break;
        upgradeBought = true;
      }
      purchases += 1;
    }
  } finally {
    Game.volume = volume;
  }
  NextPlan = affordable ? 0 : Game.T + WAIT_FRAMES;
  if (plan === null) {
    AutoBuyState.next = null;
    return;
  }

  // The countdown uses income measured in this run: the expected income counts rare jackpots (cookie
  // storms, Click frenzies) that seldom land within a few minutes
  const history = Math.min(ETA_WINDOW, Math.floor((Date.now() - Game.startDate) / 1000));
  const measured =
    CookiesDiff && history >= ETA_MIN_HISTORY && CookiesDiff.queue.length >= history
      ? CookiesDiff.calcAverage(history)
      : 0;
  const etaIncome = Math.max(measured, economy.cps + economy.clicks, 1e-9);
  const spendable = Game.cookies - plan.reserve;
  AutoBuyState.next = {
    name: plan.c.name,
    price: plan.price,
    payback: plan.payback,
    reserve: plan.reserve,
    reason: plan.reason,
    spendable,
    eta: Math.max(plan.price - spendable, 0) / etaIncome,
  };
}
