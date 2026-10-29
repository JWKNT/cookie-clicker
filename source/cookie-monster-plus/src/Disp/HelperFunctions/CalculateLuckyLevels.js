const SPECIAL_DIGIT = 7;

/**
 * Count the number of 7s in any number
 * @param	{number}	number	The number to count sevens for
 * @returns	{number}	The number of 7s in the provided number
 */
export function CountSevens(number) {
  return String(number).split(String(SPECIAL_DIGIT)).length - 1;
}

/**
 * Calculate the delta for the next number where the given digit is a 7
 * @param	{number}	number			The starting number to calculate the delta for
 * @param	{number}	digitPlace	1 for ones place, 10 for tens place, 100 for hundreds place, etc
 * @returns	{number}	The calculated delta
 */
export function CalculateSevenDelta(number, digitPlace) {
  const target = SPECIAL_DIGIT * digitPlace;
  const modulus = digitPlace * 10;

  let delta = target - (number % modulus) + (number % digitPlace);
  if (delta < 0) delta += modulus;

  return delta;
}

/**
 * This function calculates each of the next "lucky" prestige levels
 * @param	{number}	currentLevel	The user's prestige level, including levels earned since the last ascension
 * @returns	{{number}, {number}, {number}}	luckyDigit, luckyNumber, luckyPayout	The next eligible level for each upgrade
 */
export default function CalculateLuckyLevels(currentLevel) {
  const result = {};
  let sevenCount = CountSevens(currentLevel);
  const numberOfDigits = Math.max(Math.floor(Math.log10(Math.abs(currentLevel))), 0) + 1;

  if (sevenCount >= 1) {
    result.luckyDigit = currentLevel;
    if (sevenCount >= 2) {
      result.luckyNumber = currentLevel;
      if (sevenCount >= 4) {
        result.luckyPayout = currentLevel;
        return result;
      }
    }
  }

  // Consider only top 15 digits if it is big number
  let localLevel;
  if (numberOfDigits >= 16) {
    localLevel = Math.ceil(currentLevel / 10 ** (numberOfDigits - 15));
  } else {
    localLevel = currentLevel;
  }
  sevenCount = CountSevens(localLevel);

  if (result.luckyDigit === undefined) {
    if (sevenCount < 1) {
      const delta = CalculateSevenDelta(localLevel, 1);

      localLevel += delta;
      sevenCount = CountSevens(localLevel);
    }

    result.luckyDigit = localLevel;
    if (numberOfDigits >= 16) {
      result.luckyDigit *= 10 ** Number(numberOfDigits - 15);
    }
  }

  if (result.luckyNumber === undefined) {
    while (sevenCount < 2) {
      let delta = CalculateSevenDelta(localLevel, 1);
      if (delta === 0) delta = CalculateSevenDelta(localLevel, 10);

      localLevel += delta;
      sevenCount = CountSevens(localLevel);
    }

    result.luckyNumber = localLevel;
    if (numberOfDigits >= 16) {
      result.luckyNumber *= 10 ** Number(numberOfDigits - 15);
    }
  }

  let digitPlace = 1;
  while (sevenCount < 4) {
    const delta = CalculateSevenDelta(localLevel, digitPlace);
    if (delta === 0) {
      digitPlace *= 10;
    } else {
      localLevel += delta;
      sevenCount = CountSevens(localLevel);
    }
  }

  result.luckyPayout = localLevel;
  if (numberOfDigits >= 16) {
    result.luckyPayout *= 10 ** Number(numberOfDigits - 15);
  }

  return result;
}
