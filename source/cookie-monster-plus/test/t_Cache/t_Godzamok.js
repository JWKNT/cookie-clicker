import { after, before, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import { AchievementWorth, PlayHorizon } from '../../src/Cache/PP/AutoplayValue.js';
import {
  BUDGET_MS,
  CycleCost,
  CycleTypes,
  CycleWorth,
  GodzamokMultiplier,
  GodzamokState,
  ProjectCycle,
} from '../../src/Cache/PP/Godzamok.js';
import AutoGodzamok from '../../src/Main/Autoplay/AutoGodzamok.js';

/** A building whose next copy costs `price` */
const building = (name, amount, price) => ({
  name,
  amount,
  basePrice: price / 1.15 ** amount,
  free: 0,
  getPrice: () => price,
  getSellMultiplier: () => 0.25,
});

describe('Godzamok combos', () => {
  const saved = {};
  const keys = [
    'Objects', 'hasGod', 'fps', 'Has', 'milkProgress', 'fullDate', 'priceIncrease',
    'modifyBuildingPrice', 'cookies', 'hasBuff', 'computedMouseCps', 'mouseCps',
    'buyMode', 'volume', 'recalculateGains',
  ];
  before(() => {
    global.Game = Game;
    keys.forEach((key) => {
      saved[key] = Game[key];
    });
    saved.settings = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings;
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings = { AutoGodzamok: 1 };
    Game.fps = 30;
    Game.hasBuff = () => false;
    Game.priceIncrease = 1.15;
    Game.modifyBuildingPrice = (me, price) => price;
    Game.hasGod = (key) => (key === 'ruin' ? 1 : false);
    Game.Objects = {
      Temple: { ...building('Temple', 200, 1e9), minigameLoaded: true },
      Farm: building('Farm', 300, 1e6),
      Grandma: building('Grandma', 400, 1e3),
      'Cortex baker': building('Cortex baker', 40, 1e18),
    };
  });
  after(() => {
    keys.forEach((key) => {
      Game[key] = saved[key];
    });
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings = saved.settings;
  });

  it('Prices a round trip at what buying back costs minus the quarter refunded on each sale', () => {
    const { rebuy, net } = CycleCost(Game.Objects.Farm);
    expect(rebuy).to.be.closeTo((1e6 * (1 - 1.15 ** -300)) / 0.15, 300);
    // Selling the copy at amount k refunds a quarter of price(k), 1.15 times what that copy cost
    expect(net).to.be.closeTo(rebuy * (1 - 1.15 * 0.25), 300);
  });

  it('Matches individual rounded buy and sell prices when free copies flatten the price curve', () => {
    const me = { ...building('Cursor', 4, 1), basePrice: 15, free: 3 };
    // Buy at amounts 0, 1, 2, 3: 15 each. Sell at 4, 3, 2, 1: floor(18/4), then 3 each.
    expect(CycleCost(me)).to.deep.equal({ rebuy: 60, net: 47 });
  });

  it('Projects native bank updates at the free-copy floor without changing game state', () => {
    const me = Object.freeze({ ...building('Cursor', 4, 1), basePrice: 15, free: 3 });
    const bank = Game.cookies;
    expect(ProjectCycle(me, 55)).to.deep.equal({
      afterSale: 68, afterBuyback: 8, net: 47, bought: 4, canRebuy: true,
    });
    expect(me.amount).to.equal(4);
    expect(Game.cookies).to.equal(bank);
  });

  it('Recognizes a zero-loss cycle when each individual bank payment rounds away', () => {
    const objects = Game.Objects;
    const me = { ...building('Farm', 1, 115), basePrice: 100 };
    expect(CycleCost(me).net).to.equal(72);
    expect(ProjectCycle(me, 1e30)).to.deep.equal({
      afterSale: 1e30, afterBuyback: 1e30, net: 0, bought: 1, canRebuy: true,
    });
    Game.Objects = { Temple: { ...building('Temple', 0, 0), minigameLoaded: true }, Farm: me };
    expect(CycleTypes(0.000001, 1, 1e30)).to.deep.equal([me]);
    Game.Objects = objects;
  });

  it('Uses each buyback affordability check, including refund-funded and partial cases', () => {
    const me = { ...building('Farm', 1, 115), basePrice: 100 };
    expect(ProjectCycle(me, 72)).to.deep.equal({
      afterSale: 100, afterBuyback: 0, net: 72, bought: 1, canRebuy: true,
    });
    expect(ProjectCycle(me, 71)).to.deep.equal({
      afterSale: 99, afterBuyback: 99, net: -28, bought: 0, canRebuy: false,
    });
    expect(ProjectCycle({ ...me, amount: 3 }, 200)).to.deep.equal({
      afterSale: 299, afterBuyback: 84, net: 116, bought: 2, canRebuy: false,
    });
    [NaN, Infinity, -1].forEach((bank) => expect(ProjectCycle(me, bank).canRebuy).to.equal(false));
  });

  it('Preserves round-to-even behavior on both sides of a bank binade boundary', () => {
    const me = { ...building('Cursor', 4, 1), basePrice: 1, free: 4 };
    expect(ProjectCycle(me, 2 ** 53).net).to.equal(4);
    expect(ProjectCycle(me, 2 ** 53 + 2).net).to.equal(5);
    expect(ProjectCycle(me, 2 ** 53 + 4).net).to.equal(0);
    const salesCrossingBoundary = ProjectCycle({ ...me, basePrice: 4 }, 2 ** 53 - 1);
    expect(salesCrossingBoundary.afterSale).to.equal(2 ** 53);
    expect(salesCrossingBoundary.afterBuyback).to.equal(2 ** 53 - 16);
    expect(salesCrossingBoundary.net).to.equal(15);
  });

  it('Stops repeated cycles before the bank can no longer fund the buyback', () => {
    const objects = Game.Objects;
    const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings = {
      AutoGodzamok: 1, AutoClick: 1, AutoClickRate: 20,
    };
    const me = { ...building('Farm', 1, 115), basePrice: 100 };
    let sales = 0;
    me.sell = () => {
      sales += 1;
      Game.cookies += 28;
      me.amount = 0;
    };
    me.buy = () => {
      if (Game.cookies >= 100) {
        Game.cookies -= 100;
        me.amount = 1;
      }
    };
    Game.Objects = { Temple: { ...building('Temple', 0, 0), minigameLoaded: true }, Farm: me };
    Game.cookies = 100;
    Game.hasBuff = () => false;
    Game.computedMouseCps = 1e6;
    Game.mouseCps = () => 1e6;
    Game.buyMode = 1;
    Game.volume = 25;
    Game.recalculateGains = 0;
    AutoGodzamok();
    expect(sales).to.equal(1);
    expect(me.amount).to.equal(1);
    expect(Game.cookies).to.equal(28);
    expect(Game.volume).to.equal(25);
    expect(Game.buyMode).to.equal(1);
    Game.Objects = objects;
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings = settings;
  });

  it('Cycles the building types whose copies add more click income than the round trip costs', () => {
    // 1e9 clicks a second: a copy sold adds 1e7 a second for the rest of the buff
    const names = CycleTypes(1e9, 5, 1e15).map((me) => me.name);
    expect(names).to.include('Farm');
    expect(names).to.include('Temple');
    expect(names).not.to.include('Cortex baker'); // costs far more than it adds
    expect(names).not.to.include('Grandma'); // selling the last one would end the pledge
    // Buying back must be covered by the bank (6.7 million for the farms)
    expect(CycleTypes(1e9, 5, 1e6).map((me) => me.name)).to.deep.equal([]);
  });

  it('Keeps up an average buff of half what a buff window of frames adds', () => {
    const units = 500; // Temple and Farm
    const perFrame = Math.min(BUDGET_MS / GodzamokState.msPerUnit, 4 * units);
    expect(GodzamokMultiplier(1e9, 1e15)).to.be.closeTo(1 + (0.01 * perFrame * 10 * 30) / 2, 1e-9);
    Game.hasGod = () => false;
    expect(GodzamokMultiplier(1e9, 1e15)).to.equal(1);
    Game.hasGod = (key) => (key === 'ruin' ? 1 : false);
  });

  it('Rejects a cycle when the actual current multiplier absorbs its increase', () => {
    const { hasBuff } = Game;
    const me = { ...building('Farm', 1, 115), basePrice: 100 };
    Game.hasBuff = () => ({ multClick: 2 ** 53 });
    try {
      expect(ProjectCycle(me, 1e30).net).to.equal(0);
      expect(CycleWorth(me, 1e9, 5, 1e30)).to.equal(false);
      expect(CycleWorth(me, 1e9, 5, 1e30, 1)).to.equal(true);
      expect(CycleWorth(me, 1e9, 5, 100)).to.equal(false);
    } finally {
      Game.hasBuff = hasBuff;
    }
  });

  it('Uses native round-to-even at multiplier binade and halfway boundaries', () => {
    const me = { ...building('Farm', 100, 1), basePrice: 1, free: 100 };
    // A diamond sale of 100 copies adds exactly 1 before binary64 rounding.
    const cases = [[2 ** 53 - 1, true], [2 ** 53, false],
      [2 ** 53 + 2, true], [2 ** 53 + 4, false]];
    cases.forEach(([multiplier, worth]) => {
      expect(ProjectCycle(me, 1e30).net).to.equal(0);
      expect(CycleWorth(me, 1, 1, 1e30, multiplier)).to.equal(worth);
    });
    expect(CycleWorth({ ...me, amount: 200 }, 1, 1, 1e30, 2 ** 53)).to.equal(true);
  });

  it('Keeps a native bank-gain cycle when the multiplier increase rounds away', () => {
    const me = { ...building('Farm', 1, 2), basePrice: 1, getSellMultiplier: () => 0.75 };
    // The refund of 1 rounds up at the odd significand. The debit of 1 rounds to even.
    expect(ProjectCycle(me, 2 ** 53 + 2)).to.deep.equal({
      afterSale: 2 ** 53 + 4, afterBuyback: 2 ** 53 + 4,
      net: -2, bought: 1, canRebuy: true,
    });
    expect(CycleWorth(me, 1, 1, 2 ** 53 + 2, 2 ** 53)).to.equal(true);
    expect(CycleWorth(me, Infinity, 1, 2 ** 53 + 2, 2 ** 53)).to.equal(true);
  });

  it('Values future buff windows from 1 even when the current buff absorbs all sales', () => {
    const { hasBuff } = Game;
    const baseline = GodzamokMultiplier(1e9, 1e15);
    Game.hasBuff = () => ({ multClick: 2 ** 56 });
    try {
      expect(CycleTypes(1e9, 5, 1e15)).to.deep.equal([]);
      expect(baseline).to.be.greaterThan(1);
      expect(GodzamokMultiplier(1e9, 1e15)).to.equal(baseline);
    } finally {
      Game.hasBuff = hasBuff;
    }
  });

  it('Values an achievement at its share of income times the play still expected', () => {
    Game.fullDate = Date.now() - 50 * 3600 * 1000;
    expect(PlayHorizon()).to.be.closeTo(50 * 3600, 5);
    Game.Has = (name) => name === 'Kitten helpers';
    Game.milkProgress = 8;
    const value = (1 + 0.1 * 8.08) / (1 + 0.1 * 8) - 1;
    expect(AchievementWorth(2)).to.be.closeTo((value / (1 + value)) * 50 * 3600, 1);
  });
});
