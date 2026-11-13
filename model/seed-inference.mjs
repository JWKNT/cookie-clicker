/** Public-history seed inference for the pinned 2.053 source.
 *
 * Inputs are visible Fortune numbers and a candidate domain. This module has no
 * game handle, save reader, or access to Game.seed. A posterior over a supplied
 * subset is conditional on that subset; only exhaustive coverage gives the
 * posterior over all startup seeds. Later observations can further restrict it.
 */
export const SEED_ALPHABET = 'abcdefghijklmnopqrstuvwxyz';
export const STARTUP_SEED_COUNT = 26 ** 5;
export const IID53_SIZE = 2n ** 53n;

function nativeLetter(index) {
  return Math.floor((Number(index) / 2 ** 53) * 26);
}

/** First IID53 index whose native binary64 product selects this letter. */
function firstLetterIndex(letterIndex) {
  let low = 0n, high = IID53_SIZE;
  while (low < high) {
    const middle = (low + high) / 2n;
    if (nativeLetter(middle) < letterIndex) low = middle + 1n;
    else high = middle;
  }
  return low;
}

export const LETTER_BUCKETS = Object.freeze(Array.from(SEED_ALPHABET, (letter, index) => {
  const lower = firstLetterIndex(index);
  const upperExclusive = firstLetterIndex(index + 1);
  return Object.freeze({ letter, lower, upperExclusive, count: upperExclusive - lower });
}));
export const STARTUP_SEED_PRIOR_DENOMINATOR = IID53_SIZE ** 5n;

function checkSeed(seed) {
  if (typeof seed !== 'string' || !/^[a-z]{5}$/.test(seed))
    throw new TypeError('A startup seed must contain exactly five lowercase ASCII letters.');
}

/** Exact numerator under five independent IID53 calls to native choose(letters). */
export function startupSeedPriorNumerator(seed) {
  checkSeed(seed);
  return [...seed].reduce((weight, letter) => weight * LETTER_BUCKETS[letter.charCodeAt(0) - 97].count, 1n);
}

/**
 * Explicit short-ASCII path of main.js:702 seedrandom. The native flatten/mixkey
 * path stores each character in a fresh key slot for these seeds. KSA, the
 * 256-byte discard, and output normalization use the native arithmetic order.
 * This is a pure local generator, not a replacement for the game's Math.random.
 */
export function shortAsciiSeededRandom(seed) {
  if (typeof seed !== 'string' || seed.length < 1 || seed.length > 255 || /[^\x00-\x7f]/.test(seed))
    throw new TypeError('The explicit seed must contain 1 to 255 ASCII characters.');
  const key = Array.from(seed, character => character.charCodeAt(0));
  const state = Uint8Array.from({ length: 256 }, (_, index) => index);
  let shuffleIndex = 0;
  for (let index = 0; index < 256; index++) {
    const previous = state[index];
    shuffleIndex = (shuffleIndex + key[index % key.length] + previous) & 255;
    state[index] = state[shuffleIndex];
    state[shuffleIndex] = previous;
  }
  let i = 0, j = 0;
  const read = count => {
    let result = 0;
    while (count-- > 0) {
      i = (i + 1) & 255;
      const previous = state[i];
      j = (j + previous) & 255;
      state[i] = state[j];
      state[j] = previous;
      result = result * 256 + state[(state[i] + state[j]) & 255];
    }
    return result;
  };
  read(256);
  return () => {
    let numerator = read(6), denominator = 256 ** 6, extra = 0;
    while (numerator < 2 ** 52) {
      numerator = (numerator + extra) * 256;
      denominator *= 256;
      extra = read(1);
    }
    while (numerator >= 2 ** 53) {
      numerator /= 2;
      denominator /= 2;
      extra >>>= 1;
    }
    return (numerator + extra) / denominator;
  };
}

/** Predict the four visible numbers for a candidate, not for a hidden game seed. */
export function candidateFortuneNumbers(candidateSeed) {
  checkSeed(candidateSeed);
  const random = shortAsciiSeededRandom(`${candidateSeed}-fortune`);
  return Array.from({ length: 4 }, () => Math.floor(random() * 100));
}

/** The visible English Mice clicking mice quote for one candidate seed. */
export function candidateMiceSpelling(candidateSeed) {
  checkSeed(candidateSeed);
  return shortAsciiSeededRandom(`${candidateSeed}-blasphemouse`)() < 0.3 ? 'blasphemouse' : 'blasphemous';
}

export function parseVisibleMiceSpelling(renderedHtml) {
  if (typeof renderedHtml !== 'string') throw new TypeError('Expected visible upgrade text.');
  const matches = [...renderedHtml.replace(/<[^>]*>/g, ' ').matchAll(/Absolutely (blasphemouse|blasphemous)!/g)];
  if (matches.length !== 1) throw new TypeError('Expected one visible English Mice clicking mice quote.');
  return matches[0][1];
}

function checkNumbers(numbers) {
  if (!Array.isArray(numbers) || numbers.length !== 4 || numbers.some(value => !Number.isInteger(value) || value < 0 || value > 99))
    throw new TypeError('A Fortune observation must contain four integer numbers from 0 to 99.');
}

/** Read the English Fortune text from an already visible ticker observation. */
export function parseVisibleFortuneNumbers(renderedHtml) {
  if (typeof renderedHtml !== 'string') throw new TypeError('Expected visible ticker text.');
  const text = renderedHtml.replace(/<[^>]*>/g, ' ').replace(/&nbsp;/g, ' ');
  const match = text.match(/Your lucky numbers are:\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)(?!\d)/);
  if (!match) throw new TypeError('The visible ticker does not contain an English four-number Fortune.');
  const numbers = match.slice(1).map(Number);
  checkNumbers(numbers);
  return numbers;
}

/** Enumerate every supported startup seed once, in alphabetic order. */
export function* startupSeeds() {
  for (let index = 0; index < STARTUP_SEED_COUNT; index++) {
    let remainder = index, seed = '';
    for (let position = 0; position < 5; position++) {
      seed = SEED_ALPHABET[remainder % 26] + seed;
      remainder = Math.floor(remainder / 26);
    }
    yield seed;
  }
}

/**
 * Bayes conditioning on public numbers. Omitting candidates runs an exhaustive
 * scan of all 26^5 seeds. This operation can take minutes. Duplicate supplied
 * candidates are rejected so that they cannot change the posterior weights.
 * No independence of different seeded observations or future spells is assumed.
 */
export function inferSeedFromFortune({ numbers, candidates } = {}) {
  checkNumbers(numbers);
  if (candidates !== undefined && (candidates === null || typeof candidates[Symbol.iterator] !== 'function'))
    throw new TypeError('Candidates must be an iterable of distinct startup seeds.');
  const exhaustive = candidates === undefined;
  const seen = exhaustive ? null : new Set();
  const matches = [];
  let inspected = 0, posteriorDenominator = 0n;
  for (const seed of candidates ?? startupSeeds()) {
    checkSeed(seed);
    if (seen?.has(seed)) throw new TypeError(`Duplicate candidate seed: ${seed}`);
    seen?.add(seed);
    inspected++;
    if (candidateFortuneNumbers(seed).every((value, index) => value === numbers[index])) {
      const priorNumerator = startupSeedPriorNumerator(seed);
      posteriorDenominator += priorNumerator;
      matches.push({ seed, priorNumerator });
    }
  }
  const completeStartupDomain = exhaustive || inspected === STARTUP_SEED_COUNT;
  return {
    observation: [...numbers], inspected, completeStartupDomain,
    posteriorScope: completeStartupDomain ? 'all-startup-seeds' : 'conditional-on-supplied-candidates',
    priorDenominator: STARTUP_SEED_PRIOR_DENOMINATOR,
    posteriorDenominator,
    candidates: matches.map(match => ({
      ...match,
      posteriorNumerator: match.priorNumerator,
    })),
    consistent: matches.length > 0,
  };
}

/**
 * Add a visible Mice clicking mice quote from the same run to an existing
 * Fortune result. Retain its coverage scope and recompute exact weights. A seed
 * change at ascension requires a new inference; observations cannot cross it.
 */
export function refineFortunePosteriorWithMice(posterior, spelling) {
  if (spelling !== 'blasphemouse' && spelling !== 'blasphemous')
    throw new TypeError('Expected the visible spelling blasphemouse or blasphemous.');
  if (!posterior || !Array.isArray(posterior.candidates)) throw new TypeError('Expected a Fortune posterior.');
  const checked = inferSeedFromFortune({ numbers: posterior.observation, candidates: posterior.candidates.map(candidate => candidate.seed) });
  if (checked.candidates.length !== posterior.candidates.length)
    throw new TypeError('A supplied candidate is inconsistent with the Fortune observation.');
  const candidates = checked.candidates.filter(candidate => candidateMiceSpelling(candidate.seed) === spelling);
  return {
    ...posterior,
    additionalObservation: { kind: 'mice-clicking-mice-spelling', spelling },
    priorDenominator: STARTUP_SEED_PRIOR_DENOMINATOR,
    posteriorDenominator: candidates.reduce((sum, candidate) => sum + candidate.posteriorNumerator, 0n),
    candidates,
    consistent: candidates.length > 0,
  };
}
