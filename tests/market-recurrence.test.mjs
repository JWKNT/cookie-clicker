import test from 'node:test';
import assert from 'node:assert/strict';
import { createRuntime } from '../model/runtime.mjs';
import { hasGameSource } from '../model/game-source.mjs';
import { MARKET_RECURRENCE as B, marketRecurrenceMargins } from '../model/market-recurrence.mjs';
import { decideMarketAction, MARKET_ACHIEVEMENTS } from '../model/market-policy.mjs';

const skip = !hasGameSource() && 'Pinned Steam source is unavailable';
const top = 1 - 2 ** -53;

function marketFixture() {
  const r = createRuntime({ recordAudit: false });
  const bank = r.Game.Objects.Bank;
  bank.level = 1; bank.amount = bank.highest = 700;
  r.evaluate(r.source.sources['minigameMarket.js'], 'minigameMarket.js');
  bank.minigame.launch(); bank.minigameLoaded = true;
  return r;
}

// The funded kernel fixture does not need unrelated shop quotations. Keep
// exactly the public fields read by this controller on its funded path, and
// compare them with the full adapter at regular checkpoints and action types.
function marketKernelObservation(runtime) {
  const G = runtime.Game, M = G.Objects.Bank.minigame;
  const visible = id => { const element = runtime.context.l(id); return !!element && element.style.display !== 'none'; };
  const overhead = 1 + 0.01 * (20 * Math.pow(0.95, M.brokers));
  return {
    cookies: G.cookies,
    progression: { onAscend: !!G.OnAscend, ascensionMode: G.ascensionMode,
      ascendTimer: G.AscendTimer, reincarnateTimer: G.ReincarnateTimer,
      buildingLevels: Object.fromEntries(Object.values(G.Objects).map(x => [x.name, x.level])),
      buildingAmounts: Object.fromEntries(Object.values(G.Objects).map(x => [x.name, x.amount])) },
    controls: { promptOn: !!G.promptOn },
    achievements: Object.fromEntries(Object.values(G.Achievements).map(x => [x.name, !!x.won])),
    market: {
      ready: !!G.isMinigameReady(G.Objects.Bank), bankLevel: G.Objects.Bank.level, officeLevel: M.officeLevel,
      open: !!G.Objects.Bank.onMinigame, buildingId: G.Objects.Bank.id, officeUpgradeVisible: visible('bankOfficeUpgrade'),
      offices: Array.from(M.offices, (o, id) => ({ id, cursorAmount: o.cost?.[0] ?? null, cursorLevel: o.cost?.[1] ?? null })),
      brokers: M.brokers, maxBrokers: M.getMaxBrokers(), brokerPrice: M.getBrokerPrice(), overheadMultiplier: overhead,
      brokerVisible: visible('bankBrokersBuy'),
      goods: Array.from(M.goodsById, g => ({ id: g.id, key: g.key, buildingId: g.building.id, buildingLevel: g.building.level,
        active: g.building.highest > 0, visible: !!g.l && g.l.style.display !== 'none', price: M.getGoodPrice(g), restingPrice: M.getRestingVal(g.id), last: g.last,
        stock: g.stock, maxStock: M.getGoodMaxStock(g), buyCookiePrice: G.cookiesPsRawHighest * M.getGoodPrice(g) * overhead,
        sellCookiePrice: G.cookiesPsRawHighest * M.getGoodPrice(g), canBuy: g.last !== 2, canSell: g.last !== 1 })),
      profit: M.profit, nextTickMs: Math.max(0, (G.fps * M.secondsPerTick - M.tickT) * 1000 / G.fps),
      loans: [1,2,3].map(id => ({ id, unlocked: M.officeLevel >= [2,4,5][id-1],
        visible: visible(`bankLoan${id}`),
        activeFrames: G.hasBuff(`Loan ${id}`)?.time ?? 0, interestFrames: G.hasBuff(`Loan ${id} (interest)`)?.time ?? 0 })),
    },
  };
}

function projectMarketObservation(s) {
  const p = s.progression;
  return { cookies: s.cookies, progression: { onAscend: p.onAscend, ascensionMode: p.ascensionMode,
    ascendTimer: p.ascendTimer, reincarnateTimer: p.reincarnateTimer, buildingLevels: p.buildingLevels, buildingAmounts: p.buildingAmounts },
  controls: { promptOn: s.controls.promptOn }, achievements: s.achievements, market: s.market };
}

/** A diagnostic probability-event witness, never a policy input or action.
 * Each entry is one atom of the agreed uniform53 draw law. The event may be
 * selected conditional on hidden state; the trading policy cannot select it.
 */
function forcingTick(runtime, rising) {
  const M = runtime.Game.Objects.Bank.minigame;
  const boost = runtime.Game.auraMult('Supreme Intellect');
  // A tiny nonzero global disturbance resets every mode's duration. Its
  // price/velocity effect is negligible compared with the strict margins.
  const tape = [0.5, 0, 0.5 + 2 ** -53];
  for (const good of M.goodsById) {
    tape.push(top); // Mode-specific velocity draw.
    if (good.mode === 3 || good.mode === 4) tape.push(top);
    tape.push(0, 0, 0, 0); // Apply the disturbance, with its three size draws.
    tape.push(rising ? top : 0, rising ? top : 0); // Price and velocity noise.
    tape.push(0.5, 0.5, 0.5); // Suppress the three optional perturbations.
    if (good.mode === 5) tape.push(0.5, 0.5);
    if (good.mode === 3) tape.push(0.5, 0.5);
    if (good.mode === 4) tape.push(0.5);
    tape.push(0, top); // New duration, then the dragon boost branch.
    if (top < boost) tape.push(top); // Decline the forced-chaotic mode.
    tape.push(top, rising ? 11 / 16 : 13 / 16); // Decline chaotic mode; choose3/4.
  }
  assert(tape.length <= B.maximumDrawsPerForcedTick);
  for (const draw of tape) assert(Number.isSafeInteger(draw * 2 ** 53));
  const original = runtime.context.Math.random;
  let used = 0;
  try {
    runtime.context.Math.random = () => { assert(used < tape.length); return tape[used++]; };
    M.tick();
    assert.equal(used, tape.length);
  } finally { runtime.context.Math.random = original; }
  return used;
}

test('conservative market invariant and forcing-block margins are strictly positive', () => {
  const m = marketRecurrenceMargins();
  assert(m.velocityInvariantMargin > 0.13);
  assert(m.priceInvariantMargin > 61);
  assert(m.velocityAfterBlock < 0);
  assert(m.fallingPriceAfterBlock < 5);
  assert(m.risingTicksSuffice);
  assert.equal(m.forcingBlockDrawBound, 337464);
  assert(m.initialDebitBound < 1e12);
});

test('bounded startup debt preserves a unit trade margin in native binary64 arithmetic', () => {
  for (const initialProfit of [-1e12, -1e10, -1, 0, 1e7]) {
    for (let resting = 10; resting <= 180; resting += 10) {
      const purchase = (0.65 * resting) * 1.2;
      const sale = 1.05 * resting;
      assert((initialProfit - purchase) + sale - initialProfit > 2.6);
    }
  }
  // A bounded-debt premise matters: IEEE arithmetic alone does not preserve
  // strict rational profit margins at arbitrary, unreachable initial debt.
  assert.equal((-1e100 - 7.8) + 10.5, -1e100);
});

test('native fast-fall and fast-rise blocks reach both trade bands from invariant boundary fixtures', { skip, timeout: 120000 }, () => {
  const r = marketFixture();
  const M = r.Game.Objects.Bank.minigame;
  r.Game.dragonLevel = 27;
  const aura = name => Object.values(r.Game.dragonAuras).find(a => a.name === name).id;
  for (const boosted of [false, true]) {
    r.Game.dragonAura = boosted ? aura('Supreme Intellect') : 0;
    r.Game.dragonAura2 = boosted ? aura('Reality Bending') : 0;
    assert.equal(r.Game.auraMult('Supreme Intellect'), boosted ? 1.1 : 0);
    // Covers every initial mode at both extreme velocity signs and prices.
    for (const sign of [-1, 1]) for (const highPrice of [false, true]) for (const rising of [false, true]) {
      M.goodsById.forEach((good, i) => {
        good.mode = i % 6; good.dur = 699;
        good.d = sign * B.maximumVelocity;
        good.val = highPrice ? M.getRestingVal(i) + B.priceAboveRestingBound : 1;
      });
      const ticks = rising ? B.risingBlockTicks : B.fallingBlockTicks;
      for (let tick = 0; tick < ticks; tick++) forcingTick(r, rising);
      for (const good of M.goodsById) {
        if (rising) assert(good.val >= 1.05 * M.getRestingVal(good.id), `High band ${good.id}: ${good.val}`);
        else {
          assert(good.val <= 5, `Low band ${good.id}: ${good.val}`);
          assert(good.val <= 0.65 * M.getRestingVal(good.id));
        }
        assert(good.val <= M.getRestingVal(good.id) + B.priceAboveRestingBound);
        assert(Math.abs(good.d) <= B.maximumVelocity);
      }
    }
  }
});

test('funded native trading recovers from worst-bound startup prices and completes every market goal', { skip, timeout: 240000 }, t => {
  const r = marketFixture();
  const G = r.Game, M = G.Objects.Bank.minigame;
  // Explicit funded access fixture; no claim this is a new-save trajectory.
  for (const building of Object.values(G.Objects)) building.amount = building.highest = 700;
  G.Objects.Cursor.amount = G.Objects.Cursor.highest = 2000;
  G.Objects.Cursor.level = 12;
  G.cookies = 1e100; G.cookiesPsRawHighest = 10;
  G.Objects.Bank.switchMinigame(true);
  G.T = 10; M.logic(); // Native good-row activation follows the supplied board.
  M.goodsById.forEach((good, i) => {
    good.mode = i % 6; good.dur = 699; good.d = B.maximumVelocity;
    good.val = M.getRestingVal(i) + B.priceAboveRestingBound;
  });
  let memory = {}, draws = 0, ticks = 0, complete = false, minimumProfit = 0, actions = 0;
  const seenActions = new Set();
  for (; ticks <= 200000; ticks++) {
    for (let decision = 0; decision < 1000; decision++) {
      const observation = marketKernelObservation(r);
      if (ticks % 1000 === 0 && decision === 0) assert.deepEqual(observation, projectMarketObservation(r.snapshot()));
      const d = decideMarketAction(observation, memory, { collectTrades: true }); memory = d.memory;
      minimumProfit = Math.min(minimumProfit, M.profit);
      if (d.status === 'complete') { complete = true; break; }
      assert(d.action, `${d.status}: ${d.reason}`);
      if (d.action.type === 'wait') break;
      r.act(d.action, { observe: false }); actions++;
      if (!seenActions.has(d.action.type) || actions % 1000 === 0) {
        assert.deepEqual(marketKernelObservation(r), projectMarketObservation(r.snapshot()));
        seenActions.add(d.action.type);
      }
    }
    if (complete) break;
    const index = ticks % (B.fallingBlockTicks + B.risingBlockTicks);
    draws += forcingTick(r, index >= B.fallingBlockTicks);
  }
  assert(complete, `Profit ${M.profit} after ${ticks} native market ticks`);
  for (const name of MARKET_ACHIEVEMENTS) assert.equal(G.HasAchiev(name), 1, name);
  assert.equal(M.officeLevel, 5);
  assert(M.brokers >= 50);
  assert(draws <= ticks * B.maximumDrawsPerForcedTick);
  assert(minimumProfit < -1e7); // This path actually recovers a large startup loss.
  t.diagnostic(`${ticks} native ticks; ${draws} forced53-bit draws; minimum profit ${minimumProfit}; final profit ${M.profit}.`);
});
