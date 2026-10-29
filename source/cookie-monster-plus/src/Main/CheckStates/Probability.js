/**
 * The probability that a GC or reindeer has NOT spawned
 */
let chanceTotal = 1.0;
let chanceTotalDeer = 1.0;

/**
 * Clamps a per-frame spawn chance to [0, 1]. Before the game has set a spawn window (minTime equal to
 * maxTime) the chance is NaN, which would otherwise stick in the running product until the next spawn
 * @param {number} chanceToSpawn The probablity that a shimmer appears this frame
 * @returns {number}
 */
function ValidChance(chanceToSpawn) {
  return Number.isNaN(chanceToSpawn) ? 0 : Math.min(Math.max(chanceToSpawn, 0), 1);
}

export function resetChanceTotal() {
  chanceTotal = 1.0;
}

export function resetChanceTotalDeer() {
  chanceTotalDeer = 1.0;
}

/**
 * Update the probability that a cookie has not spawned
 * @param {number} chanceToSpawn The probablity that a GC appears
 * @returns the cumulative probability that a GC has appeared from beginning to now
 */
export function updateChanceTotal(chanceToSpawn) {
  chanceTotal *= 1 - ValidChance(chanceToSpawn);
  return 1 - chanceTotal;
}

/**
 * Update the probability that a reindeer has not spawned
 * @param {number} chanceToSpawn The probablity that a reindeer appears
 * @returns the cumulative probability that a reindeer has appeared from beginning to now
 */
export function updateChanceTotalDeer(chanceToSpawn) {
  chanceTotalDeer *= 1 - ValidChance(chanceToSpawn);
  return 1 - chanceTotalDeer;
}
