import { after, before, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import {
  AchievementValue,
  AutoplayEconomy,
  GoldenCookieInterval,
  LongRunValue,
  LuckyBankPayback,
  WrinklerFactor,
} from '../../src/Cache/PP/AutoplayValue.js';

/** Golden cookies with Lucky day and Serendipity: a window of 75 to 225 seconds, 4500 frames wide */
const share = 0.927719 * (6 / 4500) ** (1 / 6);
const interval = 75 + share * 150;
/** Stage 0 outcomes; one building type with 60, so a building special adds 180 seconds of CpS */
const buffSeconds = 0.4215 * 462 + 0.1002 * 180;
const cpsGrowth = 1 + (buffSeconds + 0.0084 * 25200) / interval;
const clickGrowth = 1 + (buffSeconds + 0.0397 * 776 * 13) / interval;

describe('Autoplay purchase values', () => {
  const saved = {};
  const keys = [
    'shimmerTypes',
    'fps',
    'Has',
    'buffs',
    'Objects',
    'cookiesPs',
    'cpsSucked',
    'computedMouseCps',
    'elderWrath',
    'milkProgress',
    'wrinklers',
  ];
  before(() => {
    global.Game = Game;
    keys.forEach((key) => {
      saved[key] = Game[key];
    });
    saved.settings = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings;
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings = {
      AutoClick: 1,
      AutoClickRate: 20,
      AutoGolden: 1,
    };
    Game.shimmerTypes = { golden: { minTime: 75 * 30, maxTime: 225 * 30 } };
    Game.fps = 30;
    Game.Has = () => false;
    Game.buffs = {};
    Game.Objects = { Grandma: { amount: 60 }, Shipment: { amount: 1 } };
    Game.cookiesPs = 1e7;
    Game.cpsSucked = 0;
    Game.computedMouseCps = 3e5;
    Game.elderWrath = 0;
    Game.milkProgress = 7.88;
    Game.wrinklers = [];
  });
  after(() => {
    keys.forEach((key) => {
      Game[key] = saved[key];
    });
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings = saved.settings;
  });

  it('Uses the exact mean golden cookie interval (31% into the window with both upgrades)', () => {
    expect(GoldenCookieInterval()).to.be.closeTo(interval, 1e-9);
    expect(interval).to.be.closeTo(121.2, 0.1);
  });

  it('Multiplies CpS and clicks by what golden cookies make of them', () => {
    const economy = AutoplayEconomy(0);
    expect(economy.growth.cps).to.be.closeTo(cpsGrowth, 1e-12);
    expect(economy.growth.click).to.be.closeTo(clickGrowth, 1e-12);
    const value = LongRunValue('Farm', { bonus: 1e6, bonusMouse: 3e4 }, economy);
    expect(value).to.be.closeTo(1e6 * cpsGrowth + 20 * 3e4 * clickGrowth, 1e-6);
  });

  it('Counts expected golden cookie rewards in the income that fills the bank', () => {
    const bank = 2e10; // 15% of it is below 900 seconds of CpS
    const economy = AutoplayEconomy(bank);
    const bankGain = (0.4218 * 0.15 * bank + 0.0084 * 0.43 * 0.5 * bank) / interval;
    const expected = 1e7 * cpsGrowth + 20 * 3e5 * clickGrowth + bankGain;
    expect(economy.income).to.be.closeTo(expected, expected * 1e-12);
  });

  it('Values golden cookie upgrades by the golden cookie income they add', () => {
    const bank = 2e10;
    const economy = AutoplayEconomy(bank);
    expect(LongRunValue('Serendipity', {}, economy)).to.be.closeTo(economy.golden, 1e-6);
    // Longer effects double everything but "Lucky!" and chains
    const bankGain = (0.4218 * 0.15 * bank + 0.0084 * 0.43 * 0.5 * bank) / interval;
    expect(LongRunValue('Get lucky', {}, economy)).to.be.closeTo(economy.golden - bankGain, 1e-3);
  });

  it('Judges purchases without current buffs', () => {
    const calm = AutoplayEconomy(1e9);
    const calmValue = LongRunValue('Farm', { bonus: 1e6, bonusMouse: 3e4 }, calm);
    // A Frenzy multiplies CpS, click power from CpS and every simulated gain by 7
    Game.buffs = { Frenzy: { multCpS: 7 } };
    Game.cookiesPs = 7e7;
    Game.computedMouseCps = 2.1e6;
    const frenzy = AutoplayEconomy(1e9);
    const frenzyValue = LongRunValue('Farm', { bonus: 7e6, bonusMouse: 2.1e5 }, frenzy);
    Game.buffs = {};
    Game.cookiesPs = 1e7;
    Game.computedMouseCps = 3e5;
    expect(frenzy.income).to.be.closeTo(calm.income, calm.income * 1e-12);
    expect(frenzyValue).to.be.closeTo(calmValue, calmValue * 1e-12);
  });

  it('Buys a purchase whose long-run gain beats the "Lucky!" return of banked cookies', () => {
    // Its CpS alone pays back its price in 11800 seconds, six times the 1860 seconds a banked cookie
    // takes through "Lucky!", but golden cookies and clicks multiply its gain about eightfold
    const price = 1.18e10;
    const value = LongRunValue('Grandma', { bonus: 1e6, bonusMouse: 3e4 }, AutoplayEconomy(0));
    expect(price / 1e6).to.be.above(6 * LuckyBankPayback());
    expect(price / value).to.be.below(LuckyBankPayback());
  });

  it('Makes banked cookies worth less under the Grandmapocalypse, where wrath cookies ruin 5% of the bank', () => {
    const golden = LuckyBankPayback();
    Game.elderWrath = 3;
    const wrath = LuckyBankPayback();
    Game.elderWrath = 0;
    expect(golden).to.be.closeTo(interval / (0.4218 * 0.15 + 0.0084 * 0.215), 1e-9);
    expect(wrath).to.be.closeTo(interval / (0.2447 * 0.15 + 0.0553 * 0.215 - 0.2442 * 0.05), 1e-9);
    expect(wrath).to.be.above(1.5 * golden);
  });

  it('Turns ten wrinklers into about six times the CpS', () => {
    expect(WrinklerFactor(0)).to.equal(1);
    expect(WrinklerFactor(10)).to.be.closeTo(1 - 0.5 + 0.5 * 10 * 1.1, 1e-12);
    expect(WrinklerFactor(12)).to.be.closeTo(1 - 0.6 + 0.6 * 12 * 1.1, 1e-12);
  });

  it('Values an achievement by the milk it adds through the kittens owned', () => {
    expect(AchievementValue()).to.equal(0);
    const owned = ['Kitten helpers', 'Kitten managers'];
    Game.Has = (name) => owned.includes(name);
    const expected =
      ((1 + 0.1 * 7.92) / (1 + 0.1 * 7.88)) * ((1 + 0.2 * 7.92) / (1 + 0.2 * 7.88)) - 1;
    expect(AchievementValue()).to.be.closeTo(expected, 1e-12);
    Game.Has = () => false;
  });
});
