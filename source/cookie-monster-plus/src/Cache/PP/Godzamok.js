/**
 * Section: Godzamok's "Devastation" buff under autoplay
 *
 * With Godzamok slotted, selling buildings starts a ten-second buff worth +1% click power per building
 * sold (+0.5% in the ruby slot, +0.25% in the jade one). Further sales do not extend its duration.
 * The source has no explicit multiplier cap, but binary64 rounding can absorb small increments.
 * Selling a building type and buying it straight back in the same frame
 * has native per-copy credits and debits. Their effect on the bank can differ from their price sum
 * because each binary64 bank update rounds separately. The immediate estimate uses the actual rounded
 * multiplier increase and the remaining buff duration. With the
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
 * Sum of per-copy buy prices and their nominal difference from sale refunds.
 * These quotes do not include rounding of each payment against the current bank.
 * @param	{object}	me	Building
 * @returns	{{rebuy: number, net: number}}
 */
export function CycleCost(me) {
  // Match getPrice(), sell() and buy() in game 2.053, including free copies and rounding.
  // The geometric estimate is unsafe near the free-building floor.
  let rebuy = 0;
  let refund = 0;
  const priceAt = (amount) =>
    Math.ceil(
      Game.modifyBuildingPrice(
        me,
        me.basePrice * Game.priceIncrease ** Math.max(0, amount - me.free),
      ),
    );
  const sellMultiplier = me.getSellMultiplier();
  for (let amount = 0; amount < me.amount; amount++) {
    rebuy += priceAt(amount);
    refund += Math.floor(priceAt(amount + 1) * sellMultiplier);
  }
  return { rebuy, net: rebuy - refund };
}

/**
 * Project the native bank updates when all current copies are sold and bought back.
 * Prices and sale modifiers must stay unchanged through the cycle. No game state is changed.
 * @param {object} me Building
 * @param {number} bank Cookies before the sale
 * @returns {{afterSale: number, afterBuyback: number, net: number, bought: number, canRebuy: boolean}}
 */
export function ProjectCycle(me, bank) {
  const { amount: count } = me;
  const projection = {
    afterSale: bank,
    afterBuyback: bank,
    net: 0,
    bought: 0,
    canRebuy: false,
  };
  if (!Number.isFinite(bank) || bank < 0 || !Number.isSafeInteger(count) || count < 0)
    return projection;
  const priceAt = (amount) =>
    Math.ceil(
      Game.modifyBuildingPrice(
        me,
        me.basePrice * Game.priceIncrease ** Math.max(0, amount - me.free),
      ),
    );
  const sellMultiplier = me.getSellMultiplier();
  if (!Number.isFinite(sellMultiplier) || sellMultiplier < 0) return projection;
  // Native sell() starts at the current count, credits that rounded refund,
  // and then decrements holdings. Aggregating the refunds changes rounding.
  for (let amount = count; amount > 0; amount--) {
    const refund = Math.floor(priceAt(amount) * sellMultiplier);
    if (!Number.isFinite(refund) || refund < 0) return projection;
    projection.afterSale += refund;
    if (!Number.isFinite(projection.afterSale)) return projection;
  }
  projection.afterBuyback = projection.afterSale;
  for (let amount = 0; amount < count; amount++) {
    const price = priceAt(amount);
    if (!Number.isFinite(price) || price < 0 || projection.afterBuyback < price) break;
    // Game.Spend(price) subtracts directly from the bank on each successful copy.
    projection.afterBuyback -= price;
    projection.bought += 1;
  }
  projection.net = bank - projection.afterBuyback;
  projection.canRebuy = projection.bought === count;
  return projection;
}

/** Check benefit and full buyback with the current bank and native update order. */
export function CycleWorth(
  me, clickIncome, seconds, bank,
  multiplier = Game.hasBuff('Devastation')?.multClick ?? 1,
) {
  const bonus = DevastationBonus();
  if (!bonus || !(clickIncome > 0) || !(seconds > 0)
    || me.amount < 1 || NEVER_SELL.includes(me.name)) return false;
  const { net, canRebuy } = ProjectCycle(me, bank);
  // Match native sold * bonus followed by addition to the existing buff.
  // A rounded-away increase has no click benefit; a bank gain can still pay.
  const increase = multiplier + me.amount * bonus - multiplier;
  // Zero gain stays zero even when the estimated income has overflowed.
  const benefit = increase === 0 ? 0 : increase * clickIncome * seconds;
  return canRebuy && benefit > MARGIN * net;
}

/**
 * Building types worth selling and buying back now: each copy adds bonus x click income for the rest of
 * the buff, which must beat the round trip's cost; the bank must cover buying them back
 * @param	{number}	clickIncome	Auto-click income per second without the buff
 * @param	{number}	seconds	Seconds of buff the sale feeds
 * @param	{number}	bank	Cookies at hand
 * @param {number} multiplier Current buff multiplier; 1 for a fresh-buff forecast
 * @returns	{object[]}	Buildings
 */
export function CycleTypes(
  clickIncome, seconds, bank,
  multiplier = Game.hasBuff('Devastation')?.multClick ?? 1,
) {
  const bonus = DevastationBonus();
  if (!bonus || !(clickIncome > 0) || !(seconds > 0)) return [];
  return Object.keys(Game.Objects)
    .map((name) => Game.Objects[name])
    .filter((me) => CycleWorth(me, clickIncome, seconds, bank, multiplier));
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
  // This forecast spans future buff windows, each starting at multiplier 1.
  const units = CycleTypes(clickIncome, BUFF_SECONDS / 2, bank, 1).reduce(
    (sum, me) => sum + me.amount,
    0,
  );
  if (!units) return 1;
  const perFrame = Math.min(BUDGET_MS / GodzamokState.msPerUnit, MAX_PASSES * units);
  return 1 + (bonus * perFrame * BUFF_SECONDS * Game.fps) / 2;
}
