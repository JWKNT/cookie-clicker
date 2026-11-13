/** Exact IID53 payout buckets for the pinned golden and meaty lump arrays.
 * Number multiplication rounds before Math.floor. The Lean bridge proves the
 * full bucket partition; this module exposes the resulting finite kernel.
 * It does not assert that a particular callback currently uses the free RNG.
 */
export const IID53_SIZE = 2n ** 53n;

export const SUGAR_YIELD_TABLES = Object.freeze({
  golden: Object.freeze({
    values: Object.freeze([2, 3, 4, 5, 6, 7]),
    boundaries: Object.freeze([0n, 1501199875790166n, 3002399751580331n,
      4503599627370496n, 6004799503160661n, 7505999378950826n, IID53_SIZE]),
  }),
  meaty: Object.freeze({
    values: Object.freeze([0, 0, 1, 2, 2]),
    boundaries: Object.freeze([0n, 1801439850948199n, 3602879701896397n,
      5404319552844595n, 7205759403792794n, IID53_SIZE]),
  }),
});

function tableFor(kind) {
  const table = SUGAR_YIELD_TABLES[kind];
  if (!table || !Object.hasOwn(SUGAR_YIELD_TABLES, kind)) throw new RangeError('Unknown sugar lump yield.');
  return table;
}

function checkedIndex(index) {
  if (typeof index !== 'bigint' || index < 0n || index >= IID53_SIZE)
    throw new RangeError('An IID53 index must be a bigint from 0 to 2^53 - 1.');
  return index;
}

export function nativeYieldIndex(kind, index) {
  const table = tableFor(kind);
  return Math.floor((Number(checkedIndex(index)) / 2 ** 53) * table.values.length);
}

export function projectedYieldIndex(kind, index) {
  const table = tableFor(kind); checkedIndex(index);
  return table.boundaries.findIndex((upper, position) => position > 0 && index < upper) - 1;
}

export function nativeSugarYield(kind, index) {
  const table = tableFor(kind);
  return table.values[nativeYieldIndex(kind, index)];
}

export function sugarYieldBuckets(kind) {
  const table = tableFor(kind);
  return table.values.map((value, index) => ({
    index, value, lower: table.boundaries[index], upperExclusive: table.boundaries[index + 1],
    count: table.boundaries[index + 1] - table.boundaries[index],
  }));
}

export function sugarYieldDistribution(kind) {
  const counts = new Map();
  for (const { value, count } of sugarYieldBuckets(kind)) counts.set(value, (counts.get(value) || 0n) + count);
  return [...counts].map(([value, numerator]) => ({ value, numerator, denominator: IID53_SIZE }));
}

export function sugarYieldExpectation(kind) {
  const numerator = sugarYieldDistribution(kind).reduce((sum, row) => sum + BigInt(row.value) * row.numerator, 0n);
  let a = numerator, b = IID53_SIZE;
  while (b !== 0n) [a, b] = [b, a % b];
  return { numerator: numerator / a, denominator: IID53_SIZE / a };
}
