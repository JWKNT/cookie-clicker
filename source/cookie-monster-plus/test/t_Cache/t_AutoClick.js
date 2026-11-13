import { afterEach, beforeEach, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';
import UpdateAutoClicker from '../../src/Main/Autoplay/AutoClick.js';

describe('Native auto-click bookkeeping', () => {
  const keys = ['mods', 'ready', 'OnAscend', 'AscendTimer', 'ReincarnateTimer', 'ascensionMode',
    'cookieClicks', 'HasAchiev', 'mouseX', 'mouseY', 'cookieOriginX', 'cookieOriginY', 'volume',
    'ClickCookie', 'playCookieClickSound'];
  let saved;
  let oldInterval;
  let oldClear;
  let click;
  let soundCalls;
  let settings;

  beforeEach(() => {
    global.Game = Game;
    saved = Object.fromEntries(keys.map((key) => [key, Game[key]]));
    oldInterval = global.setInterval;
    oldClear = global.clearInterval;
    global.setInterval = (callback) => { click = callback; return 1; };
    global.clearInterval = () => {};
    settings = { AutoClick: 1, AutoClickRate: 50 };
    soundCalls = 0;
    Object.assign(Game, {
      mods: { cookieMonsterFramework: { saveData: { cookieMonsterMod: { settings } } } },
      ready: 1, OnAscend: 0, AscendTimer: 0, ReincarnateTimer: 0, ascensionMode: 0,
      cookieClicks: 0, HasAchiev: () => false,
      mouseX: 7, mouseY: 9, cookieOriginX: 100, cookieOriginY: 200, volume: 73,
      playCookieClickSound() { soundCalls += 1; },
      ClickCookie() {
        expect(this.volume).to.equal(0);
        expect([this.mouseX, this.mouseY]).to.deep.equal([100, 200]);
        this.playCookieClickSound();
        this.cookieClicks += 1;
      },
    });
    UpdateAutoClicker();
  });

  afterEach(() => {
    settings.AutoClick = 0;
    UpdateAutoClicker();
    global.setInterval = oldInterval;
    global.clearInterval = oldClear;
    Object.assign(Game, saved);
  });

  it('Retains the native sound callback and restores volume and pointer position', () => {
    const nativeSound = Game.playCookieClickSound;
    click();
    expect(soundCalls).to.equal(1);
    expect(Game.cookieClicks).to.equal(1);
    expect(Game.playCookieClickSound).to.equal(nativeSound);
    expect([Game.volume, Game.mouseX, Game.mouseY]).to.deep.equal([73, 7, 9]);
  });

  it('Restores volume and pointer position when the native click throws', () => {
    Game.ClickCookie = () => { throw new Error('native click failure'); };
    expect(click).to.throw('native click failure');
    expect([Game.volume, Game.mouseX, Game.mouseY]).to.deep.equal([73, 7, 9]);
  });

  it('Leaves transition and challenge states unchanged', () => {
    ['OnAscend', 'AscendTimer', 'ReincarnateTimer'].forEach((key) => {
      Game[key] = 1;
      click();
      Game[key] = 0;
    });
    Game.ascensionMode = 1;
    Game.cookieClicks = 15;
    click();
    expect(soundCalls).to.equal(0);
    expect(Game.cookieClicks).to.equal(15);
    expect([Game.volume, Game.mouseX, Game.mouseY]).to.deep.equal([73, 7, 9]);
  });
});
