/**
 * Exact reference solver for the paper's finite completion model.
 * All offers are required once. Prices/gains are fixed and nonnegative, income is positive.
 * No resets, unlocks, random events, or recurring purchases are represented.
 * Inputs are integers, rational strings such as '3/2', or Q values. Arithmetic uses BigInt.
 */
export class Q {
  constructor(n, d = 1n) {
    n = BigInt(n);
    d = BigInt(d);
    if (d === 0n) throw new RangeError('Zero denominator');
    if (d < 0n) { n = -n; d = -d; }
    let a = n < 0n ? -n : n;
    let b = d;
    while (b) [a, b] = [b, a % b];
    this.n = n / a;
    this.d = d / a;
    Object.freeze(this);
  }
  static of(x) {
    if (x instanceof Q) return x;
    if (typeof x === 'number' && !Number.isSafeInteger(x)) throw new RangeError('Use an exact rational string');
    const [n, d = '1'] = String(x).split('/');
    return new Q(n, d);
  }
  add(x) { x = Q.of(x); return new Q(this.n * x.d + x.n * this.d, this.d * x.d); }
  sub(x) { x = Q.of(x); return new Q(this.n * x.d - x.n * this.d, this.d * x.d); }
  mul(x) { x = Q.of(x); return new Q(this.n * x.n, this.d * x.d); }
  div(x) { x = Q.of(x); return new Q(this.n * x.d, this.d * x.n); }
  lt(x) { x = Q.of(x); return this.n * x.d < x.n * this.d; }
  max(x) { x = Q.of(x); return this.lt(x) ? x : this; }
  toString() { return this.d === 1n ? String(this.n) : `${this.n}/${this.d}`; }
}

export function completionTime(offers, order, bank = 0, income = 1) {
  let b = Q.of(bank);
  let c = Q.of(income);
  let time = Q.of(0);
  if (b.lt(0) || !Q.of(0).lt(c)) throw new RangeError('Require nonnegative bank and positive income');
  if (order.length !== offers.length || new Set(order).size !== offers.length) throw new RangeError('Each offer must occur once');
  for (const i of order) {
    if (!Number.isInteger(i) || !offers[i]) throw new RangeError('Unknown offer');
    const p = Q.of(offers[i].price);
    const g = Q.of(offers[i].gain);
    if (p.lt(0) || g.lt(0)) throw new RangeError('Require nonnegative prices and gains');
    time = time.add(p.sub(b).max(0).div(c));
    b = b.sub(p).max(0);
    c = c.add(g);
  }
  return time;
}

/** O(n 2^n) exact subset recurrence. The 16-offer limit keeps this audit tool bounded. */
export function optimalCompletion(offers, { bank = 0, income = 1 } = {}) {
  if (offers.length > 16) throw new RangeError('Reference model supports at most 16 offers');
  const initialBank = Q.of(bank);
  const initialIncome = Q.of(income);
  if (initialBank.lt(0) || !Q.of(0).lt(initialIncome)) throw new RangeError('Require nonnegative bank and positive income');
  const items = offers.map(({ price, gain }) => ({ price: Q.of(price), gain: Q.of(gain) }));
  if (items.some(({ price, gain }) => price.lt(0) || gain.lt(0))) throw new RangeError('Require nonnegative prices and gains');
  const end = (1 << items.length) - 1;
  const memo = new Map();
  const visit = (mask, b, c) => {
    if (mask === end) return { time: Q.of(0), order: [] };
    if (memo.has(mask)) return memo.get(mask);
    let best;
    for (let i = 0; i < items.length; i++) {
      if (mask & (1 << i)) continue;
      const { price, gain } = items[i];
      const tail = visit(mask | (1 << i), b.sub(price).max(0), c.add(gain));
      const time = price.sub(b).max(0).div(c).add(tail.time);
      if (!best || time.lt(best.time)) best = { time, order: [i, ...tail.order] };
    }
    memo.set(mask, best);
    return best;
  };
  return { ...visit(0, initialBank, initialIncome), states: memo.size };
}
