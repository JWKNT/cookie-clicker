import { after, before, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import { SeasonPlan } from '../../src/Main/Autoplay/AutoSeasons.js';

const Hearts = ['Pure heart biscuits', 'Ardent heart biscuits', 'Sour heart biscuits'];
const Triggers = { christmas: 'Festive biscuit', valentines: 'Lovesick biscuit', easter: 'Bunny biscuit' };

/** A run with Santa complete, the Season switcher, three hearts and no eggs */
function SetRun(season, owned) {
  Game.season = season;
  Game.santaLevel = 14;
  Game.heartDrops = Hearts;
  Game.eggDrops = ['Chicken egg'];
  Game.rareEggDrops = [];
  Game.seasons = {};
  Game.Upgrades = {};
  Object.entries(Triggers).forEach(([key, name]) => {
    Game.seasons[key] = { trigger: name };
    Game.Upgrades[name] = { unlocked: 1, bought: 0, getPrice: () => 600 };
  });
  Hearts.forEach((name, i) => {
    Game.Upgrades[name] = { unlocked: i <= owned ? 1 : 0, bought: i < owned ? 1 : 0, getPrice: () => 10 ** (i + 2) };
  });
  Game.Has = (name) => ['A festive hat', 'Season switcher'].includes(name) || !!Game.Upgrades[name]?.bought;
  Game.HasUnlocked = () => false;
  Game.HasAchiev = () => false;
}

describe('Season plan', () => {
  const saved = {};
  const keys = ['season', 'santaLevel', 'heartDrops', 'eggDrops', 'rareEggDrops', 'seasons', 'Upgrades', 'Has', 'HasUnlocked', 'HasAchiev'];
  before(() => {
    global.Game = Game;
    keys.forEach((key) => { saved[key] = Game[key]; });
  });
  after(() => keys.forEach((key) => { Game[key] = saved[key]; }));

  it('Goes to Valentine\'s day when the hearts and the switch are cheap', () => {
    SetRun('christmas', 0);
    // Hearts cost 100 + 1000 + 10000. The switch costs 600.
    expect(SeasonPlan(11700)).to.deep.equal({ season: 'valentines', cost: 11700 });
  });

  it('Waits in Christmas for cheap hearts instead of going to Easter and back', () => {
    SetRun('christmas', 0);
    expect(SeasonPlan(5000)).to.deep.equal({ season: 'christmas', cost: 0 });
  });

  it('Stays in Valentine\'s day until the last heart, even when the income estimate drops', () => {
    SetRun('valentines', 1);
    expect(SeasonPlan(10)).to.deep.equal({ season: 'valentines', cost: 1000 });
  });

  it('Goes to Easter for eggs once the hearts are bought', () => {
    SetRun('valentines', 3);
    expect(SeasonPlan(1e9)).to.deep.equal({ season: 'easter', cost: 600 });
  });
});
