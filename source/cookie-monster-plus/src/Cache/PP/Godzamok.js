/**
 * Section: Godzamok's "Devastation" buff under autoplay
 *
 * With Godzamok slotted, selling buildings starts a ten-second buff worth +1% click power per building
 * sold (+0.5% in the ruby slot, +0.25% in the jade one), and every sale while it runs adds to it, without
 * limit and without extending it. Selling a building type and buying it straight back in the same frame
 * costs only the gap between the prices: a sale returns a quarter of what the next copy would cost, so
 * selling the top n copies refunds 1.15 x 25% of what buying them back costs. Each building sold adds a
 * hundredth of the auto-clicker's income for the rest of the buff, so cycling pays for every type whose
 * copies are worth less than that, which late in a run is everything but the newest tiers. With the
 * mouse upgrades a click is worth 15% of CpS, so at 20 clicks a second clicking alone earns three times
 * CpS before the buff multiplies it.
 */

/** Click power each building sold adds, by Godzamok's slot (none, diamond, ruby, jade) */
const PER_BUILDING = [0, 0.01, 0.005, 0.0025];
/** Seconds the buff lasts from the first sale */
export const BUFF_SECONDS = 10;
/** Milliseconds of each frame autoplay may spend selling and buying back */
export const BUDGET_MS = 3;
/** Most passes over the same building types in one frame */
export const MAX_PASSES = 4;
/** A cycle must bring in this many times what it costs */
const MARGIN = 2;
/**
 * Never sold: selling the last grandma ends the Elder Pledge and pops every wrinkler (the game's sell
 * hook for grandmas), and "You" is a single copy worth hours of CpS
 */
const NEVER_SELL = ['Grandma', 'You'];

/** Milliseconds one building takes to sell and buy back, measured as autoplay goes */
export const GodzamokState = { msPerUnit: 0.0035 };

/**
 * Click power per building sold with Godzamok where it sits now; 0 without him or with the setting off
 * @returns	{number}
 */
export function DevastationBonus() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGodzamok || !Game.hasGod || !Game.Objects.Temple.minigameLoaded) return 0;
  return PER_BUILDING[Game.hasGod('ruin') || 0] || 0;
}

/**
 * Cookies to buy back every copy of a building after selling them all, and what the round trip costs
 * once the sale's refund is counted
 * @param	{object}	me	Building
 * @returns	{{rebuy: number, net: number}}
 */
export function CycleCost(me) {
  const rebuy = (me.getPrice() * (1 - 1.15 ** -me.amount)) / 0.15;
  return { rebuy, net: rebuy * (1 - 1.15 * me.getSellMultiplier()) };
}

/**
 * Building types worth selling and buying back now: each copy adds bonus x click income for the rest of
 * the buff, which must beat the round trip's cost; the bank must cover buying them back
 * @param	{number}	clickIncome	Auto-click income per second without the buff
 * @param	{number}	seconds	Seconds of buff the sale feeds
 * @param	{number}	bank	Cookies at hand
 * @returns	{object[]}	Buildings
 */
export function CycleTypes(clickIncome, seconds, bank) {
  const bonus = DevastationBonus();
  if (!bonus || !(clickIncome > 0) || !(seconds > 0)) return [];
  return Object.keys(Game.Objects)
    .map((name) => Game.Objects[name])
    .filter((me) => {
      if (me.amount < 1 || NEVER_SELL.includes(me.name)) return false;
      const { rebuy, net } = CycleCost(me);
      return bonus * me.amount * clickIncome * seconds > MARGIN * net && rebuy <= bank;
    });
}

/**
 * Average click power multiplier the cycling keeps up. Each frame sells as many buildings as the time
 * budget allows (U), so the buff grows by bonus x U a frame and averages half its final size over its
 * ten seconds
 * @param	{number}	clickIncome	Auto-click income per second without buffs
 * @param	{number}	bank	Cookies at hand
 * @returns	{number}
 */
export function GodzamokMultiplier(clickIncome, bank) {
  const bonus = DevastationBonus();
  if (!bonus) return 1;
  const units = CycleTypes(clickIncome, BUFF_SECONDS / 2, bank).reduce(
    (sum, me) => sum + me.amount,
    0,
  );
  if (!units) return 1;
  const perFrame = Math.min(BUDGET_MS / GodzamokState.msPerUnit, MAX_PASSES * units);
  return 1 + (bonus * perFrame * BUFF_SECONDS * Game.fps) / 2;
}
