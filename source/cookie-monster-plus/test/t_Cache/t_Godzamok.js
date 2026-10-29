import { after, before, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import { AchievementWorth, PlayHorizon } from '../../src/Cache/PP/AutoplayValue.js';
import {
  BUDGET_MS,
  CycleCost,
  CycleTypes,
  GodzamokMultiplier,
  GodzamokState,
} from '../../src/Cache/PP/Godzamok.js';

/** A building whose next copy costs `price` */
const building = (name, amount, price) => ({
  name,
  amount,
  getPrice: () => price,
  getSellMultiplier: () => 0.25,
});

describe('Godzamok combos', () => {
  const saved = {};
  const keys = ['Objects', 'hasGod', 'fps', 'Has', 'milkProgress', 'fullDate'];
  before(() => {
    global.Game = Game;
    keys.forEach((key) => {
      saved[key] = Game[key];
    });
    saved.settings = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings;
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings = { AutoGodzamok: 1 };
    Game.fps = 30;
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
    expect(rebuy).to.be.closeTo((1e6 * (1 - 1.15 ** -300)) / 0.15, 1e-3);
    // Selling the copy at amount k refunds a quarter of price(k), 1.15 times what that copy cost
    expect(net).to.be.closeTo(rebuy * (1 - 1.15 * 0.25), 1e-3);
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

  it('Values an achievement at its share of income times the play still expected', () => {
    Game.fullDate = Date.now() - 50 * 3600 * 1000;
    expect(PlayHorizon()).to.be.closeTo(50 * 3600, 5);
    Game.Has = (name) => name === 'Kitten helpers';
    Game.milkProgress = 8;
    const value = (1 + 0.1 * 8.04) / (1 + 0.1 * 8) - 1;
    expect(AchievementWorth(2)).to.be.closeTo(2 * value * 50 * 3600, 1);
  });
});
