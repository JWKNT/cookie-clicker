/**
 * This function calculates a stock's next expected value
 * @param	{number}	value		        The stock's current value
 * @param	{number}	delta			    The stock's current delta
 * @param	{number}	restingValue		The stock's resting value
 * @param	{number}	mode		        The stock's current mode
 * @param	{number}	bankLevel		    The bank building level
 * @param	{number}	dragonBoost		    The current aura multiplier from Supreme Intellect and Reality Bending
 * @returns	{number}	value + delta       The stock's next expected value
 */
export default function CalculateStockNextExpectedValue(
  pValue,
  pDelta,
  restingValue,
  mode,
  bankLevel,
  dragonBoost,
) {
  let value = pValue;
  let delta = pDelta;
  delta *= 0.97 + 0.01 * dragonBoost;
  switch (mode) {
    case 0:
      delta *= 0.95;
      break;
    case 1:
      delta *= 0.99;
      delta += 0.02;
      break;
    case 2:
      delta *= 0.99;
      delta -= 0.02;
      break;
    case 3:
      delta += 0.06;
      value += 2.5;
      break;
    case 4:
      delta -= 0.06;
      value -= 2.5;
      break;
    default:
      break;
  }
  value += (restingValue - value) * 0.01;
  if (mode === 3) value -= 0.582;
  if (mode === 4) value += 0.6;
  if (value > 100 + (bankLevel - 1) * 3 && delta > 0) delta *= 0.9;
  if (value < 5) value += (5 - value) * 0.5;
  if (value < 5 && delta < 0) delta *= 0.95;
  return Math.max(value + delta, 1);
}
