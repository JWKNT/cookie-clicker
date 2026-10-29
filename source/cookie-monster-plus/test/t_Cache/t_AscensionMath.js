import { describe, it } from 'mocha';
import { expect } from 'chai';

import {
  OptimalRunMultiplier,
  PlanAscension,
  PrestigeGain,
  SpeedModel,
} from '../../src/Cache/Stats/AscensionMath.js';

/** Late game: prestige 1e8 with full prestige power, so speed is proportional to prestige */
const lateGameSpeed = SpeedModel({
  levels: 1e8,
  chips: 0,
  hasLegacy: true,
  power: 1,
  ownedMult: 1,
  upgrades: [],
});
const lateGameReset = 1e12 * 1e24;

/** A run whose cookies grow like time^beta and which has baked `share` of the all-time total so far */
function lateGameState(beta, share) {
  const cookiesRun = share * lateGameReset;
  const runTime = 3600;
  return {
    cookiesReset: lateGameReset,
    cookiesRun,
    income: (beta * cookiesRun) / runTime,
    runTime,
    overhead: 0,
  };
}

/** The first run of the user's save: 4.89e12 cookies in 17.2 hours, no heavenly upgrades yet */
const firstRunSpeed = SpeedModel({
  levels: 0,
  chips: 0,
  hasLegacy: false,
  power: 1,
  ownedMult: 1,
  upgrades: [{ cost: 3, mult: 1.1 }],
});
function firstRunState(beta) {
  const cookiesRun = 4.89e12;
  const runTime = 17.2 * 3600;
  return {
    cookiesReset: 0,
    cookiesRun,
    income: (beta * cookiesRun) / runTime,
    runTime,
    overhead: 60,
  };
}

describe('PrestigeGain', () => {
  it('Matches the naive cube-root difference for comparable totals', () => {
    const naive = Math.cbrt((1e21 + 7e21) / 1e12) - Math.cbrt(1e21 / 1e12);
    expect(PrestigeGain(1e21, 7e21)).to.be.closeTo(naive, naive * 1e-12);
  });
  it('Stays accurate when the run is tiny compared to all-time cookies', () => {
    const expected = (Math.cbrt(1e40 / 1e12) / 3) * (1 / 1e40);
    expect(PrestigeGain(1e40, 1)).to.be.closeTo(expected, expected * 1e-9);
  });
  it('Handles a first run without prior prestige', () => {
    expect(PrestigeGain(0, 1e15)).to.be.closeTo(10, 1e-9);
  });
  it('Returns 0 without cookies baked', () => {
    expect(PrestigeGain(1e20, 0)).to.equal(0);
  });
});

describe('SpeedModel', () => {
  it('Gives no speed-up before Legacy can be bought', () => {
    expect(firstRunSpeed.speedAt(0.9)).to.equal(1);
    expect(firstRunSpeed.currentSpeed).to.equal(1);
  });
  it('Spends the first chip on Legacy, which turns on prestige power', () => {
    expect(firstRunSpeed.speedAt(1.7)).to.be.closeTo(1.01, 1e-12);
  });
  it('Spends several chips at once on the modelled heavenly upgrades', () => {
    // 4 chips: Legacy (1) + Heavenly cookies (3)
    expect(firstRunSpeed.speedAt(4)).to.be.closeTo(1.1 * 1.04, 1e-12);
    expect(firstRunSpeed.speedAt(3.9)).to.be.closeTo(1.03, 1e-12);
  });
  it('Saves up for the next item of the purchase order instead of skipping ahead', () => {
    const speed = SpeedModel({
      levels: 0,
      chips: 0,
      hasLegacy: true,
      power: 1,
      ownedMult: 1,
      upgrades: [
        { cost: 100, mult: 2 },
        { cost: 3, mult: 1.1 },
      ],
    });
    expect(speed.speedAt(50)).to.be.closeTo(1.5, 1e-12);
    expect(speed.speedAt(103)).to.be.closeTo(2 * 1.1 * 2.03, 1e-12);
  });
  it('Is proportional to prestige in the late game', () => {
    expect(lateGameSpeed.speedAt(3e8) / lateGameSpeed.currentSpeed).to.be.closeTo(3, 1e-5);
  });
});

describe('OptimalRunMultiplier', () => {
  const examples = [
    { beta: 2, v: 7.87 },
    { beta: 3, v: 16.8 },
    { beta: 4, v: 28.39 },
  ];
  examples.forEach((example) => {
    it(`Solves the power-law stopping condition for beta = ${example.beta}`, () => {
      expect(OptimalRunMultiplier(example.beta)).to.be.closeTo(example.v, 0.05);
    });
  });
});

describe('PlanAscension', () => {
  [2, 3, 4].forEach((beta) => {
    it(`Reproduces the late-game optimum for beta = ${beta}`, () => {
      const state = lateGameState(beta, 0.5);
      const plan = PlanAscension(state, lateGameSpeed);
      const runMultiplier = (plan.targetPrestige ** 3 * 1e12) / lateGameReset;
      expect(plan.ascendNow).to.equal(false);
      // The optimum is flat; the finite horizon and grid move the target by up to ~15%
      expect(runMultiplier).to.be.closeTo(
        OptimalRunMultiplier(beta),
        OptimalRunMultiplier(beta) * 0.15,
      );
    });
  });
  it('Says to ascend once the run is past the late-game optimum', () => {
    expect(PlanAscension(lateGameState(3, 30), lateGameSpeed).ascendNow).to.equal(true);
  });
  [1, 1.5, 2, 3, 4].forEach((beta) => {
    it(`Keeps baking on a first run worth one prestige level (beta = ${beta})`, () => {
      const plan = PlanAscension(firstRunState(beta), firstRunSpeed);
      expect(plan.ascendNow).to.equal(false);
      expect(plan.targetPrestige).to.be.at.least(4);
      expect(plan.speedGainNow).to.be.below(0.02);
    });
  });
  it('Never recommends an ascension worth less than a 10% speed-up', () => {
    // A stalled late-game run that has only grown all-time cookies by 15% (prestige +4.8%)
    const plan = PlanAscension(lateGameState(0.5, 0.15), lateGameSpeed);
    expect(plan.ascendNow).to.equal(false);
    expect(plan.speedGainAtTarget).to.be.at.least(0.1);
  });
  it('Brackets the forecast with slower and faster growth', () => {
    const plan = PlanAscension(lateGameState(2.5, 0.5), lateGameSpeed);
    expect(plan.remainingFast).to.be.below(plan.remaining);
    expect(plan.remainingSlow).to.be.above(plan.remaining);
    expect(plan.readiness).to.be.above(0);
    expect(plan.readiness).to.be.below(1);
  });
  it('Is not applicable before any cookies are baked', () => {
    const state = { ...lateGameState(3, 0.5), cookiesRun: 0 };
    expect(PlanAscension(state, lateGameSpeed).applicable).to.equal(false);
  });
});
