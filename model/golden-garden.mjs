/**
 * Exact mature-plant frequency planner for a rectangular Garden on clay.
 * A bit selects a Nursetulip; every other cell contains a golden clover.
 * Native neighboring tulips multiply a mature clover's power by 5/4 each.
 * The objective is frequency at this instant, not time to game completion.
 */
export function planGoldenGarden(width = 6, height = 6) {
  if (!Number.isInteger(width) || !Number.isInteger(height)
      || width < 1 || width > 6 || height < 1 || height > 6) {
    throw new Error('Garden dimensions must be integers from 1 to 6');
  }
  const count = 2 ** width;
  const popcount = Array.from({ length: count }, (_, n) => {
    let bits = 0;
    for (; n; n &= n - 1) bits++;
    return bits;
  });
  const neighborhoods = Array.from({ length: width }, (_, x) =>
    ((1 << x) | (x ? 1 << (x - 1) : 0) | (x + 1 < width ? 1 << (x + 1) : 0)));
  // All summands have denominator 4^8. Integer scores and their sums are exact
  // binary64 integers (the largest possible sum is 36 * 5^8 < 2^24).
  const powers = Array.from({ length: 9 }, (_, k) => 5 ** k * 4 ** (8 - k));
  const weights = new Uint32Array(count ** 3);
  const rowScore = (above, row, below) => weights[(above * count + row) * count + below];
  for (let above = 0; above < count; above++) {
    for (let row = 0; row < count; row++) {
      for (let below = 0; below < count; below++) {
        let score = 0;
        for (let x = 0; x < width; x++) {
          if (row & (1 << x)) continue;
          const mask = neighborhoods[x];
          const neighbors = popcount[above & mask] + popcount[row & mask] + popcount[below & mask];
          score += powers[neighbors];
        }
        weights[(above * count + row) * count + below] = score;
      }
    }
  }
  // State stores the preceding and current rows. A transition finalizes the
  // current row when the next row becomes known. Missing exterior rows are 0.
  let scores = new Float64Array(count ** 2).fill(-Infinity);
  for (let row = 0; row < count; row++) scores[row] = 0;
  const parents = [];
  for (let y = 0; y + 1 < height; y++) {
    const next = new Float64Array(count ** 2).fill(-Infinity);
    const parent = new Uint8Array(count ** 2);
    for (let above = 0; above < count; above++) {
      for (let row = 0; row < count; row++) {
        const prefix = scores[above * count + row];
        if (prefix === -Infinity) continue;
        for (let below = 0; below < count; below++) {
          const candidate = prefix + rowScore(above, row, below);
          const state = row * count + below;
          if (candidate > next[state]) { next[state] = candidate; parent[state] = above; }
        }
      }
    }
    parents.push(parent);
    scores = next;
  }
  let best = -Infinity;
  let last = 0;
  for (let state = 0; state < count ** 2; state++) {
    const candidate = scores[state] + rowScore(Math.floor(state / count), state % count, 0);
    if (candidate > best) { best = candidate; last = state; }
  }
  const rowMasks = Array(height).fill(0);
  rowMasks[height - 1] = last % count;
  if (height > 1) rowMasks[height - 2] = Math.floor(last / count);
  for (let y = height - 2; y > 0; y--) {
    rowMasks[y - 1] = parents[y][rowMasks[y] * count + rowMasks[y + 1]];
  }
  const plot = rowMasks.map(mask => Array.from({ length: width }, (_, x) =>
    mask & (1 << x) ? 'nursetulip' : 'goldenClover'));
  return {
    width, height, rowMasks, plot,
    powerSum: { numerator: best, denominator: 4 ** 8 },
    frequency: { numerator: 80 * 4 ** 8 + 3 * best, denominator: 80 * 4 ** 8 },
    objective: 'Instantaneous golden-cookie frequency with all plants mature on clay',
    policyOptimalityCertified: false,
  };
}
