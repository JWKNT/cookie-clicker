/**
 * An opt-in, finite source-control prefix. Each cycle is four actual store
 * inputs. The controller never writes a bank, buff, holding, or game clock.
 *
 * The default count is an upper bound from the existing binary64 cent-addition theorem.
 * The maintained cent recurrence ends the prefix at its cap before another batch.
 * Exact native buff multipliers are used by the separate tests, not this policy.
 * It is far beyond a practical CPU-time budget. That theorem does not prove
 * this controller's full source/UI correspondence or its full-game value.
 */
export const GODZAMOK_LOOP_CYCLES = '72057594037927936'; // 2^56, exact decimal.
export const GODZAMOK_LOOP_CAP = 2 ** 47;
export const GODZAMOK_LOOP_CONTRACT = Object.freeze({
  status: 'standalone-opt-in-finite-prefix-with-open-source-refinement',
  minimumBank: 2 ** 60,
  maximumBankExclusive: 2 ** 1023,
  maximumOriginalCursors: 1000,
  cyclesToCap: GODZAMOK_LOOP_CYCLES,
  cap: GODZAMOK_LOOP_CAP,
  source: ['main.js:7818-7828', 'main.js:7831-7854', 'main.js:7857-7917',
    'main.js:8516-8546', 'main.js:8598-8601'],
  scalarTheorems: [
    'CookieClicker.JavaScript.BankCycleBridge.every_finite_cycle_prefix_preserves_bank',
    'CookieClicker.JavaScript.ScaledArithmeticBridge.native_cent_cap_reached',
  ],
  entry: 'Normal run; Hardcore and Neverclick won; diamond Godzamok; ready and owned Temple; no dragon auras; finite bank in [2^60,2^1023); at most 1000 Cursors. After setup, native Cursor sale price<=18 and rebuy quote<=15.',
  post: 'One Cursor. Native sale proceeds and later setup-time production are retained. The original Cursor count is recorded, not restored. Each confirmed cycle preserves the observed bank, earned counter, other holdings, prices, elapsed time and buff deadline in the checked prefix.',
  open: [
    'The mapping from the diagnostic snapshot to native public observations is not proved for exact frame, buff durations and Garden fields. Removing the exact multiplier read does not certify the full information interface.',
    'Prove the whole native buy/sell, refresh, audio, free-draw and source-control composition for every iteration, including finite host-resource limits.',
    'Refine semantic store controls to legal physical inputs and reconcile enormous real CPU time with the selected zero-input-latency mathematical model.',
    'Prove a later native gains update, click schedule and resource use reach 2^90; account for the lower Cursor production and any restoration cost.',
    'Prove new-save reachability of every entry condition and compose all remaining completion phases; no expected-time or global-optimality claim is made.',
  ],
});

function finiteLoopDecision(o, _availableActions, memory, options) {
  const config = { cycles: '72057594037927936', batchCycles: 128, ...options };
  let m = { ...(memory || {}) };
  const answer = (status, reason, action = null) => ({ status, reason, action, memory: m,
    exclusive: !!m.phase && m.phase !== 'complete', optimalityCertified: false });
  if (typeof config.cycles !== 'string' || !/^[1-9][0-9]{0,16}$/.test(config.cycles)
    || BigInt(config.cycles) > 72057594037927936n
    || !Number.isSafeInteger(config.batchCycles) || config.batchCycles < 1 || config.batchCycles > 249) {
    return answer('blocked', 'Use an exact decimal cycle count from 1 through 2^56 and a batch size from 1 through 249.');
  }
  const fail = reason => answer(m.phase ? 'blocked' : 'deferred', reason);
  const p = o.progression, c = o.controls, cursor = o.shop?.buildings?.find(b => b.id === 0 && b.name === 'Cursor');
  if (!p || !c || !cursor) return fail('Public progression, controls and Cursor quotes are required.');
  if (p.onAscend || p.ascendTimer || p.reincarnateTimer || p.ascensionMode !== 0 || c.promptOn || c.menu) {
    return fail('Use this prefix only in a normal run with no prompt or open menu.');
  }
  if (!o.achievements?.Hardcore || !o.achievements?.Neverclick) return fail('Complete Hardcore and Neverclick before this prefix.');
  const temple = o.shop.buildings.find(b => b.name === 'Temple');
  // The native catalogue gives Godzamok id2. No seed or future outcome is read.
  if (!p.minigames?.Temple || !temple || temple.amount < 1 || c.pantheon?.slots?.[0] !== 2) {
    return fail('An owned, ready Temple and diamond Godzamok are required.');
  }
  if (o.dragon?.aura !== 0 || o.dragon?.aura2 !== 0) return fail('This prefix requires empty dragon aura slots, including no sell-refund aura.');
  if (o.fps !== 30 || !Number.isSafeInteger(o.elapsedMs) || o.elapsedMs < 0
    || ![o.cookies, o.cookiesEarned].every(Number.isFinite) || o.cookies < 2 ** 60
    || o.cookies >= 2 ** 1023 || o.cookiesEarned < o.cookies) {
    return fail('The fixed 30fps profile, safe elapsed clock and finite bank/earned premises are required.');
  }
  if (!Number.isSafeInteger(cursor.amount) || cursor.amount < 0 || cursor.amount > 1000) {
    return fail('This setup admits at most 1000 original Cursors.');
  }
  if (m.run !== undefined && m.run !== o.ascensions) return answer('blocked', 'A reset interrupted the committed prefix.');
  if (m.totalCycles !== undefined && (m.totalCycles !== config.cycles || m.batchCycles !== config.batchCycles)) {
    return answer('blocked', 'Do not change the committed cycle count or batch size.');
  }
  const seq = actions => ({ type: 'sequence', actions });
  const product = { type: 'click-product', id: 0 };
  const bulk = id => ({ type: 'store-bulk', id });
  const signature = () => JSON.stringify({
    price: cursor.price, rebuy: cursor.rebuyOnePrice,
    otherHoldings: o.shop.buildings.filter(b => b.id !== 0).map(b => [b.id, b.amount, b.level]),
    owned: Object.entries(o.upgrades || {}).filter(([,u]) => u.bought).map(([name]) => name).sort(),
    slots: c.pantheon.slots, auras: [o.dragon.aura, o.dragon.aura2],
    otherBuffs: Object.keys(o.buffs || {}).filter(name => name !== 'Devastation').sort(),
    garden: o.garden ? [o.garden.plot, o.garden.soil, o.garden.freeze] : null,
  });
  if (!m.phase) {
    m = { run: o.ascensions, phase: 'prepared', totalCycles: config.cycles,
      batchCycles: config.batchCycles, completedCycles: '0', remainingCycles: config.cycles,
      originalCursors: cursor.amount, beforeSetupBank: o.cookies, beforeSetupEarned: o.cookiesEarned,
      beforeSetupElapsedMs: o.elapsedMs };
    if (cursor.amount !== 1) {
      const inputs = cursor.amount ? [bulk(1), bulk(5), product] : [];
      inputs.push(bulk(0), bulk(2), product);
      return answer('acting', 'Sell the original Cursors and buy one with ordinary store controls; retain all native bank effects.', seq(inputs));
    }
  }
  if (cursor.amount !== 1) return answer('blocked', 'The committed prefix must have exactly one Cursor after setup.');
  if (!Number.isInteger(cursor.price) || cursor.price < 0 || cursor.price > 18
    || !Number.isInteger(cursor.rebuyOnePrice) || cursor.rebuyOnePrice < 0 || cursor.rebuyOnePrice > 15) {
    return answer('blocked', 'The current native Cursor prices do not meet the refund<=4 and debit<=15 arithmetic premises.');
  }
  if (m.phase === 'waiting-expiry') {
    if (o.elapsedMs < m.waitUntil || o.buffs?.Devastation) return answer('blocked', 'The one committed expiry wait did not clear the old buff.');
    m.phase = 'prepared';
  }
  if (m.phase === 'prepared') {
    if (m.afterSetupBank === undefined) { m.afterSetupBank = o.cookies; m.afterSetupEarned = o.cookiesEarned; }
    const old = o.buffs?.Devastation;
    if (old) {
      if (!Number.isSafeInteger(old.time) || old.time < 1 || old.time > 30 * 3600) return answer('blocked', 'The old buff duration is outside this expiry profile.');
      const milliseconds = Math.ceil(old.time * 1000 / 30) + 100;
      if (!Number.isSafeInteger(o.elapsedMs + milliseconds)) return answer('blocked', 'The expiry wait exceeds the safe diagnostic clock.');
      m.phase = 'waiting-expiry'; m.waitUntil = o.elapsedMs + milliseconds;
      return answer('acting', 'Let the old resource buff expire once before the fixed same-time prefix.', { type: 'wait', milliseconds });
    }
    m.phase = 'counting'; m.startBank = o.cookies; m.startEarned = o.cookiesEarned;
    m.startElapsedMs = o.elapsedMs; m.startFrame = o.frame; m.signature = signature(); m.multiplier = 1;
  }
  if (m.phase === 'complete') return answer('complete', 'The selected finite prefix is confirmed. One Cursor remains; funding and restoration are separate obligations.');
  if (m.phase !== 'counting' || !/^(0|[1-9][0-9]*)$/.test(m.completedCycles)
    || BigInt(m.completedCycles) > BigInt(m.totalCycles)) return answer('blocked', 'The exact finite-loop memory is invalid.');
  if (o.cookies !== m.startBank || o.cookiesEarned !== m.startEarned || o.elapsedMs !== m.startElapsedMs
    || o.frame !== m.startFrame || signature() !== m.signature) {
    return answer('blocked', 'A native bank, earned, price, holding, buff, frame or time premise changed during the prefix.');
  }
  if (m.pending) {
    const buff = o.buffs?.Devastation;
    if (!buff || buff.time !== 300
      || c.buyMode !== 1 || c.buyBulk !== 1) return answer('blocked', 'The last native batch did not match its buff duration and store-control postcondition.');
    m.completedCycles = (BigInt(m.completedCycles) + BigInt(m.pending.cycles)).toString();
    m.multiplier = m.pending.multiplier; delete m.pending;
  } else if (m.completedCycles !== '0') {
    return answer('blocked', 'A continuing prefix needs a confirmed native batch receipt.');
  }
  const left = BigInt(m.totalCycles) - BigInt(m.completedCycles);
  m.remainingCycles = left.toString();
  if (left === 0n || m.multiplier === 2 ** 47) {
    m.phase = 'complete'; m.capReached = m.multiplier === 2 ** 47;
    m.stopReason = m.capReached ? 'recurrence-cap' : 'finite-count';
    return answer('complete', 'The selected finite prefix is confirmed. One Cursor remains; no bank or buff endpoint was assigned.');
  }
  const count = Number(left < BigInt(config.batchCycles) ? left : BigInt(config.batchCycles));
  let multiplier = m.multiplier;
  const inputs = [bulk(2)];
  for (let i = 0; i < count; i++) {
    inputs.push(bulk(1), product, bulk(0), product);
    multiplier += 0.01;
  }
  m.pending = { cycles: count, multiplier };
  return answer('acting', 'Execute the next finite batch of native sell-one/buy-one inputs at the same mathematical time.', seq(inputs));
}

export function decideGodzamokLoop(observation, memory = {}, options = {}) {
  return finiteLoopDecision(observation, [], memory, options);
}
export function godzamokLoopPolicySource(options = {}) {
  return `(function(observation,actions,memory){return (${finiteLoopDecision.toString()})(observation,actions,memory,${JSON.stringify(options)});})`;
}
