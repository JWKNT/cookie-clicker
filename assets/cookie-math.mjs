// Pure functions behind the page's examples. They restate the formulas of the paper and the game.

/** Gamma(7/6) */
export const GAMMA_7_6 = 0.9277193336;
/** Garden plot bounds [x0, y0, x1, y1) for farm levels 1 to 9, as in the game */
export const PLOT_LIMITS = [
  [2, 2, 4, 4], [2, 2, 5, 4], [2, 2, 5, 5], [1, 2, 5, 5], [1, 1, 5, 5],
  [1, 1, 6, 5], [1, 1, 6, 6], [0, 1, 6, 6], [0, 0, 6, 6],
];
/** Milk factors of the kitten upgrades, in the order the game unlocks them */
export const KITTEN_FACTORS = [0.1, 0.125, 0.15, 0.175, 0.2, 0.2, 0.2, 0.2, 0.2, 0.175, 0.15, 0.125, 0.115, 0.11, 0.105];
/** Click power each building sold adds with Godzamok in the first, second and third slot */
export const GODZAMOK_BONUS = [0.01, 0.005, 0.0025];

/**
 * Golden cookie spawn window and mean interval in seconds. The spawn chance in frame t of a window of W
 * frames is ((t - min) / W)^5, so the mean arrives at the fraction Gamma(7/6) (6 / W)^(1/6) of the window
 */
export function goldenInterval({ luckyDay = false, serendipity = false, goldenGooseEgg = false, fps = 30 } = {}) {
  let factor = 1;
  if (luckyDay) factor *= 0.5;
  if (serendipity) factor *= 0.5;
  if (goldenGooseEgg) factor *= 0.95;
  const min = 5 * 60 * fps * factor;
  const max = 15 * 60 * fps * factor;
  const window = max - min;
  const share = Math.min(GAMMA_7_6 * (6 / window) ** (1 / 6), 1);
  return { min: min / fps, max: max / fps, share, mean: (min + share * window) / fps };
}

/** Cookies a "Lucky!" golden cookie pays from a bank and a CpS */
export function luckyPayout(bank, cps, gain = 1) {
  return Math.min(0.15 * bank, 900 * cps) * gain + 13;
}

/**
 * Seconds a banked cookie takes to pay itself back through golden cookies: "Lucky!" pays 15% of the bank,
 * a cookie chain about a fifth of it, and a wrath "Ruin" takes 5%
 */
export function bankThreshold(meanInterval, { lucky = 0.4218, chain = 0.0084, ruin = 0, gain = 1 } = {}) {
  const perCookie = lucky * 0.15 * gain + chain * 0.215 * gain - ruin * 0.05;
  return perCookie > 0 ? meanInterval / perCookie : Infinity;
}

/** Exchange index of a purchase: time to save for it plus its payback time */
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
 * Factor by which each run multiplies all-time cookies in the late game: the root of
 * (beta / 3)(1 - 1 / v) = (1 - v^(-gamma / 3)) / gamma with gamma = 3 / beta - 1
 */
export function optimalRunMultiplier(beta) {
  const b = Math.min(Math.max(beta, 0.5), 20);
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

/** Factor the marginal value theorem gives instead: the root of beta (v - 1) = v ln v */
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

/** Share of production one more achievement adds through the kittens owned */
export function achievementValue(kittens, milk, multiplier = 1) {
  let ratio = 1;
  for (const k of KITTEN_FACTORS.slice(0, kittens)) {
    ratio *= (1 + k * multiplier * (milk + 0.04)) / (1 + k * multiplier * milk);
  }
  return ratio - 1;
}

/** Long-run multiplier n wrinklers put on CpS: each digests the whole withered share n / 20 */
export function wrinklerFactor(n, { sacrilegious = false, wrinklerspawn = false } = {}) {
  if (!(n > 0)) return 1;
  const s = Math.min(1, n * 0.05);
  let r = 1.1;
  if (sacrilegious) r *= 1.05;
  if (wrinklerspawn) r *= 1.05;
  return 1 - s + s * n * r;
}

/**
 * Long-run income per unit of CpS in calm and in wrath, for click income k times CpS (Rule 5:
 * twelve wrinklers, effect duration x2, mean golden interval 121 s)
 */
export function stageIncomes(clickToCps) {
  return { calm: 8.7 + 11.8 * clickToCps, wrath: 62.8 + 8.5 * clickToCps };
}

/** Cookies to buy back the top n copies of a building, and the round trip's cost after the sale refund */
export function roundTripCost(nextPrice, n, sellShare = 0.25) {
  const rebuy = (nextPrice * (1 - 1.15 ** -n)) / 0.15;
  return { rebuy, net: rebuy * (1 - 1.15 * sellShare) };
}

/** Click power multiplier in each frame of one buff, and its average, when U buildings are cycled per frame */
export function godzamokBuff(bonus, unitsPerFrame, frames = 300) {
  const series = Array.from({ length: frames }, (_, k) => 1 + bonus * unitsPerFrame * (k + 1));
  return { series, average: 1 + (bonus * unitsPerFrame * (frames + 1)) / 2 };
}

/**
 * Breeding layout for the garden of a farm level: parents on tiles with x + y even (kind A in even
 * columns, kind B in odd columns), the other tiles empty. Also checks that every empty tile touches
 * both kinds
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
        for (let dy = -1; dy <= 1; dy++) {
          for (let dx = -1; dx <= 1; dx++) {
            const nx = x + dx;
            const ny = y + dy;
            if ((dx || dy) && nx >= x0 && nx < x1 && ny >= y0 && ny < y1 && role(nx, ny)) kinds.add(role(nx, ny));
          }
        }
        if (kinds.size < 2) touchesBoth = false;
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
