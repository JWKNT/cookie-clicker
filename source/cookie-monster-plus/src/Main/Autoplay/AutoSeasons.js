/**
 * Section: seasons under autoplay
 *
 * Seasonal upgrades are lost at every ascension, so each run collects them again:
 * - Christmas: A festive hat, then Santa's 14 levels (each unlocks a gift such as Santa's legacy, +3% CpS
 *   per level; the last one unlocks Santa's dominion, +20%)
 * - Valentine's day: the 7 heart biscuits (+2% CpS each), each unlocked by buying the previous one, in one
 *   short visit once they are cheap
 * - Easter: eggs drop from 10% of golden cookies; the run stays until 7 eggs while "Egging on" is missing
 * The rest of the run is spent in Christmas: reindeer pay one or two minutes of CpS each and drop
 * Christmas cookies, more than any other season brings. Switching costs a minute of CpS (x1.5 per switch in
 * a run). These actions are worth far more than they cost, so the auto-buyer keeps back the cookies for the
 * next one whenever it costs at most RESERVE_SECONDS of income. Without the Season switcher only the natural
 * season is used.
 */

import { AutoplayEconomy } from '../../Cache/PP/AutoplayValue.js';

/** Eggs to collect in a run while "Egging on" (7 eggs) is missing */
const EGG_GOAL = 7;
/**
 * Seconds of income the auto-buyer keeps back for the next seasonal action: early in a run purchases pay
 * back within minutes, so a longer pause would cost more than the season brings
 */
const RESERVE_SECONDS = 60;

/**
 * Cookies the auto-buyer should keep for the next seasonal action (0 when there is none or it is not cheap)
 * @item	{number}	reserve
 */
export const SeasonState = { reserve: 0 };

/**
 * Upgrades in a list that are unlocked or owned this run
 * @param	{string[]}	names	Upgrade names
 * @returns	{number}
 */
function CountUnlocked(names) {
  return (names || []).filter((name) => Game.HasUnlocked(name) || Game.Has(name)).length;
}

/**
 * Cookies to buy every heart biscuit not owned yet
 * @returns	{number}
 */
function HeartsCost() {
  return (Game.heartDrops || [])
    .filter((name) => !Game.Has(name))
    .reduce((sum, name) => sum + Game.Upgrades[name].getPrice(), 0);
}

/**
 * Price of switching to a season (0 if already in it, Infinity if it cannot be triggered)
 * @param	{string}	season	Season key
 * @returns	{number}
 */
function SwitchCost(season) {
  if (Game.season === season) return 0;
  if (!Game.Has('Season switcher') || !Game.seasons[season]) return Infinity;
  const trigger = Game.Upgrades[Game.seasons[season].trigger];
  return trigger && trigger.unlocked && !trigger.bought ? trigger.getPrice() : Infinity;
}

/**
 * The season the run should be in and the cookies its next action needs
 * @param	{number}	cheap	Cookies counted as cheap (RESERVE_SECONDS of income)
 * @returns	{{season: string, cost: number}}
 */
function SeasonPlan(cheap) {
  if (!Game.Has('A festive hat') || Game.santaLevel < 14) {
    const switching = SwitchCost('christmas');
    if (switching > 0) return { season: 'christmas', cost: switching };
    if (!Game.Has('A festive hat')) return { season: 'christmas', cost: 25 };
    return { season: 'christmas', cost: (Game.santaLevel + 1) ** (Game.santaLevel + 1) };
  }
  const hearts = HeartsCost();
  if (hearts > 0 && hearts + SwitchCost('valentines') <= cheap)
    return { season: 'valentines', cost: hearts + SwitchCost('valentines') };
  const eggs = CountUnlocked(Game.eggDrops) + CountUnlocked(Game.rareEggDrops);
  if (!Game.HasAchiev('Egging on') && eggs < EGG_GOAL)
    return { season: 'easter', cost: SwitchCost('easter') };
  return { season: 'christmas', cost: SwitchCost('christmas') };
}

/**
 * Buys what the current season offers: the festive hat and Santa's levels at Christmas, the heart
 * biscuits on Valentine's day (other seasonal cookies and eggs are left to the auto-buyer)
 * @returns	{boolean}	Whether something was bought
 */
function SeasonPurchases() {
  if (Game.season === 'christmas') {
    const hat = Game.Upgrades['A festive hat'];
    if (hat && hat.unlocked && !hat.bought && Game.cookies >= hat.getPrice()) {
      hat.buy();
      return true;
    }
    if (Game.Has('A festive hat') && Game.santaLevel < 14) {
      const level = Game.santaLevel;
      Game.UpgradeSanta();
      if (Game.specialTab) Game.ToggleSpecialMenu(0);
      return Game.santaLevel !== level;
    }
  }
  if (Game.season === 'valentines') {
    const heart = (Game.heartDrops || [])
      .map((name) => Game.Upgrades[name])
      .find((me) => me.unlocked && !me.bought);
    if (heart && Game.cookies >= heart.getPrice()) {
      heart.buy();
      return true;
    }
  }
  return false;
}

/**
 * Switches seasons, buys seasonal upgrades and sets the reserve the auto-buyer keeps for them
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoSeasons() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  SeasonState.reserve = 0;
  if (!settings.AutoSeasons || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  // Production without golden cookies: the expected income counts rare jackpots, too much early in a run
  const economy = AutoplayEconomy(Game.cookies);
  const cheap = (economy.cps * economy.W + economy.clicks) * RESERVE_SECONDS;
  const plan = SeasonPlan(cheap);
  if (Number.isFinite(plan.cost) && plan.cost <= cheap) SeasonState.reserve = plan.cost;
  if (SeasonPurchases() || !Game.Has('Season switcher') || plan.season === Game.season) return;
  const trigger = Game.Upgrades[Game.seasons[plan.season].trigger];
  if (trigger && trigger.unlocked && !trigger.bought && Game.cookies >= trigger.getPrice())
    trigger.buy();
}
