/** Conservative bounds for the pinned native market tick, not a trading oracle.
 * Source refinement and funded execution are separate proof obligations.
 */
export const MARKET_RECURRENCE = Object.freeze({
  maximumDragonBoost: 1.1,
  maximumVelocity: 300,
  priceAboveRestingBound: 250000,
  maximumRestingPrice: 180, // Bank level1, the18 native goods.
  velocityContraction: 0.981,
  velocityForcingMargin: 0.184,
  priceContraction: 0.99,
  priceForcingMargin: 7.9,
  alignmentTicks: 1,
  velocityTicks: 200,
  fallingPriceTicks: 600,
  risingPriceTicks: 30,
  fallingBlockTicks: 801,
  risingBlockTicks: 231,
  maximumDrawsPerForcedTick: 327,
  // Before the single-sale achievement, each top-up targets ceil86400/price.
  // Native price is at least1; the extra unit covers the product guard.
  maximumStartupHolding: 86401,
});

/** Exact-decimal margins rounded only for this diagnostic calculation. */
export function marketRecurrenceMargins() {
  const c = MARKET_RECURRENCE;
  // A fast-rise event can switch to fast-fall and run that event too.
  const worstVelocity = c.velocityContraction * c.maximumVelocity + 0.15 + 5 + 0.05 + 0.26 + 0.1;
  const worstPriceAddition = 4.95 + 2109 + 3 + 1.5 + 10.5 + 10 + c.maximumVelocity;
  const velocityAfterBlock = c.velocityContraction ** c.velocityTicks * c.maximumVelocity
    - c.velocityForcingMargin * (1 - c.velocityContraction ** c.velocityTicks) / (1 - c.velocityContraction);
  const fallingPriceAfterBlock = c.maximumRestingPrice + c.priceContraction ** c.fallingPriceTicks * c.priceAboveRestingBound
    - c.priceForcingMargin * (1 - c.priceContraction ** c.fallingPriceTicks) / (1 - c.priceContraction);
  const minimumRiseBelowSaleBand = c.priceForcingMargin - 0.0005 * c.maximumRestingPrice;
  const sumRestingPrices = 1710;
  const initialDebitBound = 2 * 1.2 * c.maximumStartupHolding
    * (18 * c.priceAboveRestingBound + sumRestingPrices);
  return {
    worstVelocity,
    velocityInvariantMargin: c.maximumVelocity - worstVelocity,
    worstPriceAddition,
    priceInvariantMargin: 0.01 * c.priceAboveRestingBound - worstPriceAddition,
    velocityAfterBlock,
    fallingPriceAfterBlock,
    minimumRiseBelowSaleBand,
    risingTicksSuffice: 1 + c.risingPriceTicks * minimumRiseBelowSaleBand > 1.05 * c.maximumRestingPrice,
    forcingBlockDrawBound: (c.fallingBlockTicks + c.risingBlockTicks) * c.maximumDrawsPerForcedTick,
    // The factor2 also covers a delayed BuyBuy purchase after MakeMyDay.
    // This excludes pre-existing losses, broker cookies, and ordinary later
    // inventory. It assumes the default thresholds and Bank level1.
    initialDebitBound,
  };
}
