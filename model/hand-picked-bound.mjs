/** Necessary timing bound, not a complete-game optimality certificate. */
export const HAND_PICKED_BOUND = Object.freeze({
  gameVersion: '2.053',
  achievement: 'Hand-picked',
  achievementId: 269,
  mainSourceSha256: 'a8813ec2ee97edf5ebff6a3ce2037dcb65c08abd13c123bb92efda89b06ef4f7',
  exactMinimumMatureMilliseconds: { numerator: 13_596_000_000, denominator: 211 },
  binary64MinimumMatureMilliseconds: (20 * 3_600_000 - 3_600_000 - 420_000) / (1 + 1.1 * 0.05),
  minimumFirstAttemptClockMilliseconds: 64_436_019,
  conditionalFairExpectedClockMilliseconds: 128_872_038,
  userPolicy: {
    saveRollbackRetries: 'forbidden',
    nativeUiRngManipulation: 'forbidden',
    conditionalFairness: 'Additional mathematical assumption, not established by the source audit or by those two restrictions alone.',
  },
  firstAttemptAssumptions: [
    'A fresh vanilla save starts without the achievement or an older imported sugar lump.',
    'The game clock is monotone; no clock manipulation, debug upgrades, or save edits occur.',
    'Native initialization and event callbacks run to completion without injected reentrant actions.',
    'Loading a save cannot introduce progress or a lump timestamp from before this new-save run.',
  ],
  clockMeaning: 'The integer difference between Date.now() at the attempt and the initial new-save timestamp. Continuous wall time can differ by less than one millisecond from timestamp quantization.',
  expectedBoundStatus: 'No unconditional two-attempt expected bound is established. The user excludes native UI RNG manipulation and save rollback retries. A conditional success probability of at most one half at every attempt remains an explicit mathematical assumption.',
  sourceReferences: {
    newSaveTimer: 'main.js:2050,3691',
    savedTimer: 'main.js:3050',
    threshold: 'main.js:4412-4431',
    offlineTimer: 'main.js:4441-4450',
    attemptAndReset: 'main.js:4465-4488',
    typeRngRestoration: 'main.js:4522-4538',
    firstLumpTimer: 'main.js:4591-4605',
    auraMultiplier: 'main.js:14873-14878',
    duplicateAuraUi: 'main.js:14890-14896',
    cloneRngLeak: 'main.js:8421-8466',
  },
  timerWriteAudit: [
    { line: 2050, operation: 'Initialize to now.' },
    { line: 3050, operation: 'Restore the saved timestamp. A rolled-back save can undo a failed attempt.' },
    { line: 3691, operation: 'Hard reset sets the timestamp to now.' },
    { line: 4441, operation: 'Clamp a future timestamp to now. This cannot predate the start of a monotone-clock run.' },
    { line: 4450, operation: 'Offline remainder equals the prior timestamp plus a nonnegative number of overripe intervals.' },
    { line: 4488, operation: 'Every harvest, including a failed unripe harvest, resets to now.' },
    { line: 4601, operation: 'First ordinary lump activation resets to now.' },
  ],
});

/** Match the maturity branch of computeLumpTimes for legal, non-debug states. */
export function handPickedMatureMilliseconds({ diabetica = false, ichor = false, curveMultiplier = 0 } = {}) {
  if (typeof diabetica !== 'boolean' || typeof ichor !== 'boolean'
      || ![0, 0.1, 1, 1.1].includes(curveMultiplier)) throw new Error('Invalid vanilla lump modifiers');
  let age = 20 * 3_600_000;
  if (diabetica) age -= 3_600_000;
  if (ichor) age -= 420_000;
  return age / (1 + curveMultiplier * 0.05);
}

/**
 * Conditional finite-tail calculation only. If each attempted harvest has
 * conditional success probability at most p, the first attempt and every retry
 * take at least d milliseconds, and attempts cannot be rolled back, then the
 * first n survival terms give a lower bound on expected completion time. This
 * function returns its floating-point approximation, not an interval bound.
 * Those probability and rollback assumptions are not established for the game.
 */
export function conditionalHandPickedTailMilliseconds(attempts, maximumSuccessProbability = 0.5) {
  if (!Number.isSafeInteger(attempts) || attempts < 0
      || !Number.isFinite(maximumSuccessProbability)
      || maximumSuccessProbability < 0 || maximumSuccessProbability > 1) {
    throw new Error('Expected a nonnegative attempt count and a probability in [0,1]');
  }
  const failure = 1 - maximumSuccessProbability;
  const terms = maximumSuccessProbability === 0 ? attempts
    : (1 - failure ** attempts) / maximumSuccessProbability;
  return HAND_PICKED_BOUND.minimumFirstAttemptClockMilliseconds * terms;
}
