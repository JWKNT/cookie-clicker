/**
 * Section: Pure functions for optimal ascension timing
 *
 * Model
 * -----
 * Prestige is P = cbrt(cookiesAllTime / 1e12). Every run benefits from a production speed S(P) that
 * depends on the prestige at its start: S = (heavenly upgrade multipliers) × (1 + 0.01·h·floor(P)),
 * where h is the prestige power (it needs the Legacy heavenly upgrade, after which the "Heavenly ..."
 * store upgrades restore it every run). Heavenly chips accumulate over ascensions, so one ascension
 * can buy several heavenly upgrades at once; S(P) assumes the chips available at P are spent along a
 * fixed purchase order (best production gain per chip first), saving up for the next item.
 *
 * Because S multiplies every source of income, a run at speed S retraces the same trajectory S times
 * faster: cookiesBaked(t; S) = F(S·t). F follows the current run: a fresh run rebuilds to the cookies
 * baked so far (convexly, exponent at least 1.5), then grows like the current run does now, as a power
 * law with exponent β = cps × run time / cookies baked this run.
 *
 * Optimal stopping
 * ----------------
 * Ascending is a trade: it restarts the run in exchange for a faster speed in every later run. The best
 * moment minimises the total time to reach a distant prestige goal, which is solved exactly with a
 * dynamic program over the prestige at which each future ascension happens:
 *
 *     V(P) = min over P' > P of [ runTime(P → P') + τ + V(P') ]
 *
 * and the current run continues to whichever target P* minimises remainingTime(P*) + τ + V(P*).
 * Ascending now is optimal when that target is the current prestige. In the late game (S ∝ P) this
 * reproduces the closed-form optimum of multiplying all-time cookies by v per run, with
 * (β/3)(v−1)/v = (1 − v^(−γ/3))/γ and γ = 3/β − 1 (β = 2 → v ≈ 7.9, β = 3 → v ≈ 16.8); in the early game,
 * where prestige barely changes production, it correctly keeps baking.
 */

const COOKIES_PER_PRESTIGE_CUBED = 1e12;
const BETA_MIN = 0.3;
const BETA_MAX = 12;
/**
 * Lowest growth exponent assumed while a fresh run rebuilds to the current run's cookies: every run
 * starts from zero CpS and grows convexly, even when the current run's income has stalled
 */
const BETA_REBUILD_MIN = 1.5;
/**
 * Smallest speed gain worth an ascension. Guards against a stalled run (for example while nothing is
 * being bought) making a restart for a percent or two look worthwhile
 */
const MIN_SPEED_GAIN = 0.1;

/**
 * Prestige gained by baking `cookiesRun` on top of `cookiesReset`, without catastrophic cancellation
 * when the run is tiny compared to the all-time total.
 * @param	{number}	cookiesReset	All-time cookies before this run
 * @param	{number}	cookiesRun		Cookies baked this run
 * @returns	{number}					Continuous (unfloored) prestige gain
 */
export function PrestigeGain(cookiesReset, cookiesRun) {
  if (!(cookiesRun > 0)) return 0;
  if (!(cookiesReset > 0)) return Math.cbrt(cookiesRun / COOKIES_PER_PRESTIGE_CUBED);
  const prestigeBefore = Math.cbrt(cookiesReset / COOKIES_PER_PRESTIGE_CUBED);
  return prestigeBefore * Math.expm1(Math.log1p(cookiesRun / cookiesReset) / 3);
}

/**
 * Builds the speed of a run as a function of the total prestige at its start
 * @param	{object}	heavenly
 * @param	{number}	heavenly.levels			Prestige levels owned now (Game.prestige)
 * @param	{number}	heavenly.chips			Unspent heavenly chips now
 * @param	{boolean}	heavenly.hasLegacy		Whether Legacy is owned
 * @param	{number}	heavenly.power			Prestige power h once Legacy is owned
 * @param	{number}	heavenly.ownedMult		Product of the modelled heavenly multipliers already owned
 * @param	{{cost: number, mult: number}[]}	heavenly.upgrades	Purchase order of upgrades not owned yet; cost includes the parents they still need
 * @returns	{{speedAt: function, currentSpeed: number}}	speedAt(P) for a run starting at prestige P, and the speed of the current run
 */
export function SpeedModel(heavenly) {
  const { upgrades } = heavenly;
  const speedAt = (prestige) => {
    const levels = Math.max(Math.floor(prestige), heavenly.levels);
    let chips = heavenly.chips + levels - heavenly.levels;
    let { hasLegacy } = heavenly;
    if (!hasLegacy && chips >= 1) {
      hasLegacy = true;
      chips -= 1;
    }
    let mult = heavenly.ownedMult;
    if (hasLegacy) {
      for (let i = 0; i < upgrades.length && upgrades[i].cost <= chips; i++) {
        chips -= upgrades[i].cost;
        mult *= upgrades[i].mult;
      }
    }
    return mult * (1 + 0.01 * (hasLegacy ? heavenly.power : 0) * levels);
  };
  const currentSpeed =
    heavenly.ownedMult * (1 + 0.01 * (heavenly.hasLegacy ? heavenly.power : 0) * heavenly.levels);
  return { speedAt, currentSpeed };
}

/** Future runs considered by the planner span this many times the current run's length */
const HORIZON_RUN_LENGTHS = 1e4;
/** Phase-shifted goals whose decisions are combined, to cancel end-of-horizon effects */
const GOAL_PHASES = 5;

/**
 * Solves the dynamic program for one goal
 * @param	{object}	run		Precomputed run quantities (see PlanAscension)
 * @param	{number}	goalFactor	All-time cookies at the goal, relative to now
 * @returns	{{index: number, factors: number[], speeds: number[], remaining: number, total: number, ascendNowTotal: number}}
 */
function SolveForGoal(run, goalFactor) {
  const { allTime, cookiesRun, runTime, overhead, beta, betaRebuild, speed, gridSize } = run;
  const prestigeAt = (factor) => Math.cbrt((allTime * factor) / COOKIES_PER_PRESTIGE_CUBED);

  // Grid of all-time cookies relative to now: log-spaced, plus every whole prestige level while levels
  // are coarse enough to matter (each one is +1% of prestige power)
  const factors = [];
  for (let i = 0; i <= gridSize; i++) factors.push(goalFactor ** (i / gridSize));
  const prestigeGoal = prestigeAt(goalFactor);
  for (let level = Math.floor(prestigeAt(1)) + 1; level < Math.min(prestigeGoal, 400); level++) {
    factors.push((level ** 3 * COOKIES_PER_PRESTIGE_CUBED) / allTime);
  }
  factors.sort((a, b) => a - b);
  const n = factors.length;
  const speeds = factors.map((factor) => speed.speedAt(prestigeAt(factor)));

  // Time from the start of a run at the current speed until it has baked `cookies`: rebuilding to the
  // current run's cookies, then growing like the current run
  const timeToBake = (cookies) =>
    runTime * (cookies / cookiesRun) ** (1 / (cookies <= cookiesRun ? betaRebuild : beta));
  const runDuration = (cookies, s) => timeToBake(cookies) * (speed.currentSpeed / s);
  const remainingAt = (j) =>
    j === 0 ? 0 : timeToBake(cookiesRun + allTime * (factors[j] - 1)) - runTime;

  // value[i]: shortest time from a fresh run at factors[i] to the goal
  const value = new Array(n).fill(0);
  for (let i = n - 2; i >= 0; i--) {
    let best = Infinity;
    for (let j = i + 1; j < n; j++) {
      const t =
        runDuration(allTime * (factors[j] - factors[i]), speeds[i]) +
        (j === n - 1 ? 0 : overhead) +
        value[j];
      if (t < best) best = t;
    }
    value[i] = best;
  }

  // The current run: keep baking until factors[j], then ascend (-1: no worthwhile ascension in sight)
  let index = -1;
  let total = Infinity;
  for (let j = 0; j < n - 1; j++) {
    if (speeds[j] / speed.currentSpeed - 1 >= MIN_SPEED_GAIN) {
      const t = remainingAt(j) + overhead + value[j];
      if (t < total) {
        total = t;
        index = j;
      }
    }
  }
  return {
    index,
    factors,
    speeds,
    remaining: index === -1 ? Infinity : remainingAt(index),
    total,
    ascendNowTotal: overhead + value[0],
  };
}

/**
 * Plans the current run's ascension
 * @param	{object}	state
 * @param	{number}	state.cookiesReset	All-time cookies before this run
 * @param	{number}	state.cookiesRun	Cookies this run would convert into prestige
 * @param	{number}	state.income		Effective income (cookies per second)
 * @param	{number}	state.runTime		Seconds since the run started
 * @param	{number}	state.overhead		Seconds lost per ascension (τ)
 * @param	{{speedAt: function, currentSpeed: number}}	speed	From SpeedModel()
 * @param	{object}	[options]
 * @param	{number}	[options.gridSize]	Log-spaced grid points of the dynamic program
 * @returns	{object}	plan
 */
export function PlanAscension(state, speed, options = {}) {
  const { cookiesReset, cookiesRun, income, runTime, overhead } = state;
  if (!(cookiesRun > 0) || !(income > 0) || !(runTime > 0)) return { applicable: false };

  const beta = Math.min(Math.max((income * runTime) / cookiesRun, BETA_MIN), BETA_MAX);
  const allTime = cookiesReset + cookiesRun;
  const run = {
    allTime,
    cookiesRun,
    runTime,
    overhead,
    beta,
    betaRebuild: Math.max(beta, BETA_REBUILD_MIN),
    speed,
    gridSize: options.gridSize || 400,
  };

  // The horizon covers what the current run's growth could bake in HORIZON_RUN_LENGTHS run lengths,
  // which keeps every duration within a range where the hour-scale decision is not lost to rounding
  const horizon = 1 + (cookiesRun / allTime) * HORIZON_RUN_LENGTHS ** beta;
  const solutions = [];
  for (let k = 0; k < GOAL_PHASES; k++) {
    solutions.push(SolveForGoal(run, horizon * 10 ** (k / GOAL_PHASES)));
  }
  const targetOf = (solution) =>
    solution.index === -1 ? Infinity : solution.factors[solution.index];
  solutions.sort((a, b) => targetOf(a) - targetOf(b));
  const solution = solutions[Math.floor(GOAL_PHASES / 2)];
  const { index, factors, speeds, remaining } = solution;

  const prestigeAt = (factor) => Math.cbrt((allTime * factor) / COOKIES_PER_PRESTIGE_CUBED);
  const levelsBefore = Math.floor(Math.cbrt(cookiesReset / COOKIES_PER_PRESTIGE_CUBED));
  const prestigeNow = prestigeAt(1);
  const found = index !== -1;
  const targetPrestige = found ? prestigeAt(factors[index]) : Infinity;

  // Remaining time to the same target if the growth exponent is 25% lower or higher than measured
  const ratio = found ? (cookiesRun + allTime * (factors[index] - 1)) / cookiesRun : Infinity;
  const remainingWithBeta = (b) => {
    if (!found) return Infinity;
    return index === 0 ? 0 : runTime * (ratio ** (1 / b) - 1);
  };

  let costOfAscendingNow = null;
  if (index === 0) costOfAscendingNow = 0;
  else if (found) costOfAscendingNow = Math.max(0, solution.ascendNowTotal - solution.total);
  return {
    applicable: true,
    ascendNow: index === 0,
    targetFound: found,
    beta,
    prestigeNow,
    targetPrestige,
    remaining,
    remainingSlow: remainingWithBeta(beta * 0.8),
    remainingFast: remainingWithBeta(beta * 1.25),
    levelsNow: Math.floor(prestigeNow) - levelsBefore,
    levelsAtTarget: found ? Math.floor(targetPrestige) - levelsBefore : Infinity,
    speedGainNow: speeds[0] / speed.currentSpeed - 1,
    speedGainAtTarget: found ? speeds[index] / speed.currentSpeed - 1 : 0,
    // Extra time to the goal if you ascended now instead of at the target (null: not worth it at all)
    costOfAscendingNow,
    readiness: found ? runTime / (runTime + remaining) : 0,
  };
}

/**
 * The all-time-cookies multiplier per run that is optimal in a pure power-law late game (S ∝ P).
 * Used to validate the dynamic program.
 * @param	{number}	beta	Growth exponent of cookies baked versus run time
 * @returns	{number}	v such that ascending when all-time cookies grew v-fold is optimal
 */
export function OptimalRunMultiplier(beta) {
  const b = Math.min(Math.max(beta, 0.5), 20);
  const g = 3 / b - 1;
  const f = (v) =>
    (b * (v - 1)) / (3 * v) -
    (Math.abs(g) < 1e-9 ? Math.log(v) / 3 : -Math.expm1((-g / 3) * Math.log(v)) / g);
  let lo = 1 + 1e-6;
  let hi = 2;
  while (f(hi) > 0 && hi < 1e12) {
    lo = hi;
    hi *= 2;
  }
  for (let i = 0; i < 100; i++) {
    const mid = Math.sqrt(lo * hi);
    if (f(mid) > 0) lo = mid;
    else hi = mid;
  }
  return Math.sqrt(lo * hi);
}
