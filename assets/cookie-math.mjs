// The numbers of the guide and of the paper. The build of the page and the tests use these
// functions, so each number on the page is calculated.

// ---------- exact fractions (BigInt) ----------
const gcd = (a, b) => {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b) [a, b] = [b, a % b];
  return a;
};
/** The fraction n / d in lowest terms */
export function fraction(n, d = 1) {
  let top = BigInt(n);
  let bottom = BigInt(d);
  if (bottom === 0n) throw new RangeError('A fraction needs a denominator that is not 0');
  if (bottom < 0n) [top, bottom] = [-top, -bottom];
  const g = gcd(top, bottom) || 1n;
  return { n: top / g, d: bottom / g };
}
const add = (x, y) => fraction(x.n * y.d + y.n * x.d, x.d * y.d);
const subtract = (x, y) => fraction(x.n * y.d - y.n * x.d, x.d * y.d);
const divide = (x, y) => fraction(x.n * y.d, x.d * y.n);
const compare = (x, y) => (x.n * y.d < y.n * x.d ? -1 : x.n * y.d > y.n * x.d ? 1 : 0);
export const fractionText = (x) => (x.d === 1n ? `${x.n}` : `${x.n}/${x.d}`);
export const fractionValue = (x) => Number(x.n) / Number(x.d);

// ---------- 1. The order of purchases ----------
/** Index of a purchase: the time to save for it plus its payback time */
export function exchangeIndex(price, gain, income) {
  return price / income + price / gain;
}

/** Seconds until both purchases are made, in each order, from an empty bank */
export function orderTimes(a, b, income) {
  return {
    ab: a.price / income + b.price / (income + a.gain),
    ba: b.price / income + a.price / (income + b.gain),
  };
}

/**
 * Exact time of the earliest schedule that buys the items in the given order. Prices, gains,
 * income and bank are whole numbers
 */
export function scheduleTime(items, income = 1, bank = 0) {
  let rate = fraction(income);
  let held = fraction(bank);
  let time = fraction(0);
  for (const { price, gain } of items) {
    const cost = fraction(price);
    if (compare(held, cost) >= 0) held = subtract(held, cost);
    else {
      time = add(time, divide(subtract(cost, held), rate));
      held = fraction(0);
    }
    rate = add(rate, fraction(gain));
  }
  return time;
}

/** The order of the index rule: the smallest index first, calculated again after each purchase */
export function indexRuleOrder(items, income = 1) {
  const left = items.map((item, at) => ({ ...item, at }));
  const order = [];
  let rate = income;
  while (left.length) {
    left.sort((x, y) => exchangeIndex(x.price, x.gain, rate) - exchangeIndex(y.price, y.gain, rate) || x.at - y.at);
    const [first] = left.splice(0, 1);
    order.push(first.at);
    rate += first.gain;
  }
  return order;
}

/**
 * The least time for a fixed list of items, by the recursion over the sets of bought items
 * (Theorem 2.4 of the paper). Returns the exact time and one fastest order
 */
export function fastestSchedule(items, income = 1, bank = 0) {
  const all = (1 << items.length) - 1;
  const memo = new Map();
  const state = (done) => {
    let spent = 0;
    let rate = income;
    items.forEach((item, at) => {
      if (done >> at & 1) {
        spent += item.price;
        rate += item.gain;
      }
    });
    return { held: Math.max(bank - spent, 0), rate };
  };
  const solve = (done) => {
    if (done === all) return { time: fraction(0), order: [] };
    if (memo.has(done)) return memo.get(done);
    const { held, rate } = state(done);
    let best = null;
    items.forEach((item, at) => {
      if (done >> at & 1) return;
      const wait = fraction(Math.max(item.price - held, 0), rate);
      const rest = solve(done | (1 << at));
      const time = add(wait, rest.time);
      if (!best || compare(time, best.time) < 0) best = { time, order: [at, ...rest.order] };
    });
    memo.set(done, best);
    return best;
  };
  return solve(0);
}

/** All orders of 0, 1, ..., n - 1 */
export function permutations(n) {
  if (n === 0) return [[]];
  const out = [];
  for (const rest of permutations(n - 1)) {
    for (let at = 0; at <= rest.length; at++) out.push([...rest.slice(0, at), n - 1, ...rest.slice(at)]);
  }
  return out.sort((x, y) => x.join('').localeCompare(y.join('')));
}

/** The three items of Example 2.2 of the paper */
export const THREE_ITEMS = [
  { name: 'A', price: 3, gain: 1 },
  { name: 'B', price: 5, gain: 4 },
  { name: 'C', price: 6, gain: 6 },
];

// ---------- 2. Golden cookies and the bank ----------
/** Gamma(7/6) */
export const GAMMA_7_6 = 0.9277193336;

/**
 * The wait for a golden cookie. After t_min frames, a golden cookie appears in frame j of the
 * next W frames with chance (j / W)^5. Returns the exact mean number of frames, the upper
 * limit 1 + Gamma(7/6) (6 W^5)^(1/6), and the mean wait in seconds
 */
export function goldenInterval({ luckyDay = false, serendipity = false, fps = 30 } = {}) {
  const factor = (luckyDay ? 0.5 : 1) * (serendipity ? 0.5 : 1);
  const min = 5 * 60 * fps * factor;
  const window = 10 * 60 * fps * factor;
  let frames = 0;
  let none = 1;
  for (let k = 0; k < window; k++) {
    frames += none;
    none *= 1 - ((k + 1) / window) ** 5;
  }
  return {
    min,
    window,
    frames,
    limit: 1 + GAMMA_7_6 * (6 * window ** 5) ** (1 / 6),
    mean: (min + frames) / fps,
  };
}

/**
 * Long-run shares of the effects of a golden cookie without wrath, for a player with at least
 * ten buildings. The game makes a list with Frenzy and Lucky. It adds Cookie chain and Cookie
 * storm together with chance 0.03, Click frenzy with chance 0.1 and a building effect with
 * chance 0.25. With chance 0.8 it removes the effect of the last golden cookie. It then takes
 * one effect of the list
 */
export function effectShares() {
  const effects = ['frenzy', 'lucky', 'chain', 'storm', 'click', 'building'];
  const extras = [[['chain', 'storm'], 0.03], [['click'], 0.1], [['building'], 0.25]];
  const next = (last) => {
    const row = Object.fromEntries(effects.map((effect) => [effect, 0]));
    for (let mask = 0; mask < 1 << extras.length; mask++) {
      let chance = 1;
      const list = ['frenzy', 'lucky'];
      extras.forEach(([names, p], at) => {
        if (mask >> at & 1) {
          chance *= p;
          list.push(...names);
        } else chance *= 1 - p;
      });
      const without = list.filter((effect) => effect !== last);
      for (const effect of without) row[effect] += (chance * 0.8) / without.length;
      for (const effect of list) row[effect] += (chance * 0.2) / list.length;
    }
    return row;
  };
  const rows = Object.fromEntries(effects.map((effect) => [effect, next(effect)]));
  let shares = Object.fromEntries(effects.map((effect) => [effect, 1 / effects.length]));
  for (let step = 0; step < 500; step++) {
    const moved = Object.fromEntries(effects.map((effect) => [effect, 0]));
    for (const last of effects) for (const effect of effects) moved[effect] += shares[last] * rows[last][effect];
    shares = moved;
  }
  return shares;
}

/** Share of the golden cookies that give Lucky, to four places as in the paper: 0.4217 */
export const LUCKY_SHARE = Math.round(effectShares().lucky * 1e4) / 1e4;

/** Cookies that a Lucky golden cookie pays from a bank and an income */
export function luckyPayout(bank, income, gain = 1) {
  return Math.min(0.15 * bank, 900 * income) * gain + 13;
}

/** Expected income with Lucky cookies at the rate `rate` per second */
export function expectedIncome(bank, income, rate, gain = 1) {
  return income + rate * luckyPayout(bank, income, gain);
}

/** Seconds in which a banked cookie earns one cookie: theta = 1 / (0.15 g lambda) */
export function bankThreshold(meanInterval, { share = LUCKY_SHARE, gain = 1 } = {}) {
  return meanInterval / (0.15 * gain * share);
}

// ---------- 3. Heavenly chips ----------
/** Ratio of an upgrade that costs `price` chips and multiplies the speed by `factor` */
export function chipRatio(price, factor) {
  return (1 - 1 / factor) / price;
}

/** Wait for a list of upgrades in the given order, in units of the effort for one chip */
export function chipOrderTime(upgrades) {
  let speed = 1;
  let time = 0;
  for (const { price, factor } of upgrades) {
    time += price / speed;
    speed *= factor;
  }
  return time;
}

// ---------- 4. When to ascend ----------
/**
 * Factor by which each run multiplies all-time cookies in the late game: the root above 1 of
 * (beta / 3)(1 - 1 / v) = (1 - v^(-gamma / 3)) / gamma with gamma = 3 / beta - 1
 */
export function optimalRunMultiplier(beta) {
  const b = Math.min(Math.max(beta, 1.01), 20);
  const g = 3 / b - 1;
  const f = (v) => (b * (v - 1)) / (3 * v)
    - (Math.abs(g) < 1e-9 ? Math.log(v) / 3 : -Math.expm1((-g / 3) * Math.log(v)) / g);
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

/**
 * Time of a run that multiplies all-time cookies by v, for each unit of the function Phi of
 * the paper: rho(v) = (v - 1)^(1 / beta) / (Phi(v) - Phi(1)). The best factor makes it least
 */
export function runCost(v, beta) {
  const g = 3 / beta - 1;
  const phi = Math.abs(g) < 1e-9 ? Math.log(v) : (3 / g) * (v ** (g / 3) - 1);
  return (v - 1) ** (1 / beta) / phi;
}

/** Factor of the rule without the correction for later runs: the root of beta (v - 1) = v ln v */
export function marginalValueMultiplier(beta) {
  const f = (v) => beta * (v - 1) - v * Math.log(v);
  let lo = 1 + 1e-9;
  let hi = 2;
  while (f(hi) > 0 && hi < 1e15) {
    lo = hi;
    hi *= 2;
  }
  for (let i = 0; i < 200; i++) {
    const mid = Math.sqrt(lo * hi);
    if (f(mid) > 0) lo = mid;
    else hi = mid;
  }
  return Math.sqrt(lo * hi);
}

// ---------- 5. Achievements and milk ----------
/** Milk factors of the kitten upgrades, in the order in which the game unlocks them */
export const KITTEN_FACTORS = [0.1, 0.125, 0.15, 0.175, 0.2, 0.2, 0.2, 0.2, 0.2, 0.175, 0.15, 0.125, 0.115, 0.11, 0.105];

/** Share of production that `count` more achievements add through the kittens owned */
export function achievementValue(kittens, milk, multiplier = 1, count = 1) {
  let ratio = 1;
  for (const k of KITTEN_FACTORS.slice(0, kittens)) {
    ratio *= (1 + k * multiplier * (milk + 0.04 * count)) / (1 + k * multiplier * milk);
  }
  return ratio - 1;
}

/** Longest pause that a permanent gain repays when the goal is `horizon` away: H x / (1 + x) */
export function completionTimeSaved(gain, horizon) {
  return (horizon * gain) / (1 + gain);
}

/** Least distance of the goal at which a pause repays a permanent gain: D (1 + x) / x */
export function horizonForPause(gain, pause) {
  return (pause * (1 + gain)) / gain;
}

// ---------- 6. Godzamok ----------
/** Click power that each building sold adds with Godzamok in the first, second and third slot */
export const GODZAMOK_BONUS = [0.01, 0.005, 0.0025];

/** Cookies to buy back the top n copies of a building, and the cost of the round trip after the refund */
export function roundTripCost(nextPrice, n, sellShare = 0.25) {
  const rebuy = (nextPrice * (1 - 1.15 ** -n)) / 0.15;
  return { rebuy, net: rebuy * (1 - 1.15 * sellShare) };
}

/** Click power in each frame of one buff, and its mean, when U buildings are sold and bought back in each frame */
export function godzamokBuff(bonus, unitsPerFrame, frames = 300) {
  const series = Array.from({ length: frames }, (_, k) => 1 + bonus * unitsPerFrame * (k + 1));
  return { series, average: 1 + (bonus * unitsPerFrame * (frames + 1)) / 2 };
}

// ---------- 7. Wrinklers and wrath ----------
/** Factor that n wrinklers put on the income from production: each receives the whole withered share n / 20 */
export function wrinklerFactor(n, { sacrilegious = false, wrinklerspawn = false } = {}) {
  if (!(n > 0)) return 1;
  const s = Math.min(1, n * 0.05);
  let r = 1.1;
  if (sacrilegious) r *= 1.05;
  if (wrinklerspawn) r *= 1.05;
  return 1 - s + s * n * r;
}

/**
 * Estimates of the long-run income with a pledge (calm) and with wrath, in units of production,
 * for click income k times production: twelve wrinklers, doubled effect times, a golden cookie
 * every 121 seconds. The four numbers are estimates and have no proof
 */
export const STAGE_ESTIMATE = { calm: [8.7, 11.8], wrath: [62.8, 8.5] };
export function stageIncomes(clickToCps) {
  const { calm, wrath } = STAGE_ESTIMATE;
  return { calm: calm[0] + calm[1] * clickToCps, wrath: wrath[0] + wrath[1] * clickToCps };
}
/** Click income, in units of production, above which the pledge earns more */
export const STAGE_THRESHOLD = (STAGE_ESTIMATE.wrath[0] - STAGE_ESTIMATE.calm[0]) / (STAGE_ESTIMATE.calm[1] - STAGE_ESTIMATE.wrath[1]);

// ---------- 8. Minigames ----------
/**
 * Seconds for magic to fill from `from` to `to`. In each frame the game adds
 * 0.002 sqrt(m / max(cap, 100)) magic, and it has 30 frames in a second
 */
export function refillSeconds(from, to, cap = 100) {
  const kappa = 0.06 / Math.sqrt(Math.max(cap, 100));
  return (2 / kappa) * (Math.sqrt(to) - Math.sqrt(from));
}

/** Garden plot limits [x0, y0, x1, y1) for the farm levels 1 to 9, as in the game */
export const PLOT_LIMITS = [
  [2, 2, 4, 4], [2, 2, 5, 4], [2, 2, 5, 5], [1, 2, 5, 5], [1, 1, 5, 5],
  [1, 1, 6, 5], [1, 1, 6, 6], [0, 1, 6, 6], [0, 0, 6, 6],
];

/**
 * Breeding layout for the garden of a farm level: parents on the tiles with x + y even (kind A
 * in even columns, kind B in odd columns), the other tiles empty. Also checks that each empty
 * tile touches the two kinds
 */
export function checkerboard(level) {
  const [x0, y0, x1, y1] = PLOT_LIMITS[level - 1];
  const role = (x, y) => ((x + y) % 2 !== 0 ? '' : x % 2 === 0 ? 'A' : 'B');
  const rows = [];
  let touchesBoth = true;
  for (let y = y0; y < y1; y++) {
    const row = [];
    for (let x = x0; x < x1; x++) {
      const tile = role(x, y);
      row.push(tile);
      if (tile === '') {
        const kinds = new Set();
        for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
          const nx = x + dx;
          const ny = y + dy;
          if (nx >= x0 && nx < x1 && ny >= y0 && ny < y1) kinds.add(role(nx, ny));
        }
        if (!(kinds.has('A') && kinds.has('B'))) touchesBoth = false;
      }
    }
    rows.push(row);
  }
  const tiles = rows.flat();
  return {
    width: x1 - x0,
    height: y1 - y0,
    rows,
    empty: tiles.filter((tile) => tile === '').length,
    parents: tiles.filter((tile) => tile !== '').length,
    touchesBoth,
  };
}

/** Least return of one trade: buy at the share `buyShare` of the resting value with the overhead, sell at the resting value */
export function marketReturn(buyShare = 0.6, overhead = 0.2) {
  return 1 / (buyShare * (1 + overhead)) - 1;
}

/** Stock Market loans: boost, its time, the penalty after it, its time, and the down payment */
export const LOANS = [
  { boost: 1.5, boostTime: '2 h', penalty: 0.25, penaltyTime: '4 h', down: 20 },
  { boost: 2, boostTime: '40 s', penalty: 0.1, penaltyTime: '40 min', down: 40 },
  { boost: 1.2, boostTime: '48 h', penalty: 0.8, penaltyTime: '120 h', down: 50 },
];
