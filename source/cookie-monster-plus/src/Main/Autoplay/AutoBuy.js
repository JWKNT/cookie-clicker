import { AutoplayEconomy, LongRunValue, LuckyBankPayback } from '../../Cache/PP/AutoplayValue.js';
import {
  CacheLucky,
  CacheObjects1,
  CacheUpgrades,
  CookiesDiff,
} from '../../Cache/VariablesAndData.js';
import { SimDoSims } from '../../Sim/VariablesAndData.js';
import { SeasonState } from './AutoSeasons.js';
import { UpgradesAllowed } from './Challenge.js';

/** Upgrade pools the buyer never touches: switches, heavenly upgrades and unused content */
const SkippedPools = ['toggle', 'prestige', 'debug', 'dungeon', 'shadow', 'unused'];
/** The Chocolate egg is worth most right before ascending, which the ascension routine handles */
const SkippedUpgrades = ['Chocolate egg'];
/** Seconds of measured income behind the countdown, and the least history it needs */
const ETA_WINDOW = 600;
const ETA_MIN_HISTORY = 60;

/**
 * The purchase the buyer is saving for, shown in the timer bar
 * @item	{object|null}	next	{name, price, payback, reserve, reason, spendable, eta} or null when nothing is planned;
 * reserve is what is kept back from this purchase (0 when none): the "Lucky!" bank (reason 'lucky') or
 * cookies for the next seasonal action (reason 'season'); spendable is the bank above it
 */
export const AutoBuyState = { next: null };

/**
 * Buys the building or upgrade with the best payback period as soon as it is affordable
 * Purchases are valued by what they add to long-run income under autoplay: CpS and click power at the
 * auto-click rate, without current buffs and grown by Frenzies, plus golden cookie effects. Cookies are
 * kept for a maximum "Lucky!" reward whenever a banked cookie pays itself back through "Lucky!" faster
 * than the purchase would
 */
export default function AutoBuy() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  // CpS changed this frame and Cookie Monster recomputes its values after autoplay runs, so values
  // and the "Lucky!" bank are stale until the next tick
  if (SimDoSims && settings.AutoBuy) return;
  AutoBuyState.next = null;
  if (!settings.AutoBuy || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  if (Game.buyMode !== 1) return; // The store is in sell mode

  const bank = Game.cookies;
  const economy = AutoplayEconomy(bank);
  const bankPayback = LuckyBankPayback();
  const keepLucky = settings.AutoGolden && settings.AutoBuyLuckyBank;
  const seasonReserve = settings.AutoSeasons ? SeasonState.reserve : 0;
  if (keepLucky && !(CacheLucky > 0) && Game.cookiesPs > 0) return; // "Lucky!" bank not known yet

  let best = null;
  const consider = (name, price, value, buy) => {
    if (!(value > 0) || !Number.isFinite(price)) return;
    const payback = price / value;
    const lucky = keepLucky && payback > bankPayback ? CacheLucky : 0;
    const reserve = Math.max(lucky, seasonReserve);
    let reason = '';
    if (reserve > 0) reason = lucky >= seasonReserve ? 'lucky' : 'season';
    const pp = Math.max(price - (bank - reserve), 0) / economy.income + payback;
    if (best === null || pp < best.pp) best = { name, price, payback, pp, reserve, reason, buy };
  };

  Object.keys(Game.Objects).forEach((name) => {
    const me = Game.Objects[name];
    if (me.locked || !CacheObjects1[name]) return;
    consider(name, me.getPrice(), LongRunValue(name, CacheObjects1[name], economy), () =>
      me.buy(1),
    );
  });
  Game.UpgradesInStore.forEach((me) => {
    if (
      !UpgradesAllowed() ||
      SkippedPools.includes(me.pool) ||
      SkippedUpgrades.includes(me.name) ||
      me.clickFunction ||
      me.priceLumps > 0
    )
      return;
    const value = LongRunValue(me.name, CacheUpgrades[me.name] || {}, economy);
    consider(me.dname || me.name, me.getPrice(), value, () => me.buy());
  });
  if (best === null) return;

  // The countdown uses income measured in this run: the expected income counts rare jackpots (cookie
  // storms, Click frenzies) that seldom land within a few minutes
  const history = Math.min(ETA_WINDOW, Math.floor((Date.now() - Game.startDate) / 1000));
  const measured =
    CookiesDiff && history >= ETA_MIN_HISTORY && CookiesDiff.queue.length >= history
      ? CookiesDiff.calcAverage(history)
      : 0;
  const etaIncome = Math.max(measured, economy.cps + economy.clicks, 1e-9);
  const spendable = bank - best.reserve;
  AutoBuyState.next = {
    name: best.name,
    price: best.price,
    payback: best.payback,
    reserve: best.reserve,
    reason: best.reason,
    spendable,
    eta: Math.max(best.price - spendable, 0) / etaIncome,
  };
  if (best.price <= spendable) best.buy();
}
