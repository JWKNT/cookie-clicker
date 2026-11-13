import { describe, it } from 'mocha';
import { expect } from 'chai';
import { readFileSync } from 'node:fs';
import { runInNewContext } from 'node:vm';
import { createRuntime, hasGameSource } from '../NativeEngine.js';

const DROPS = ['Dragon scale', 'Dragon claw', 'Dragon fang', 'Dragon teddy bear'];
const source = readFileSync(new URL('../../src/Main/Autoplay/AutoDragon.js', import.meta.url), 'utf8')
  .replace(/^import[\s\S]*?;\n/gm, '').replace(/export (default )?/g, '');

/** Isolate the actual controller; fixtures supply only the native functions it calls. */
function Fixture({ owned = [], specialTab = '', click = () => {} } = {}) {
  const clock = { now: Date.UTC(2026, 9, 29, 12) };
  class ClockDate extends Date {
    constructor(...args) { super(...(args.length ? args : [clock.now])); }

    static now() { return clock.now; }
  }
  const game = {
    mods: { cookieMonsterFramework: { saveData: { cookieMonsterMod: { settings: { AutoDragon: true } } } } },
    Upgrades: Object.fromEntries(DROPS.map((name) => [name, { bought: 0, unlocked: Number(owned.includes(name)) }])),
    dragonLevel: 8, dragonLevels: Array.from({ length: 28 }, () => ({ cost: () => false })),
    dragonAuras: {}, startDate: clock.now, resets: 0, volume: 37, specialTab,
    promptOn: false, OnAscend: false, AscendTimer: 0, ReincarnateTimer: 0,
    pets: 0, menus: [],
    Has(name) { return name === 'Pet the dragon' || this.Upgrades[name]?.bought; },
    HasUnlocked(name) { return this.Upgrades[name]?.unlocked; },
    ToggleSpecialMenu(on) {
      this.menus.push([on, this.specialTab]);
      if (!on) this.specialTab = '';
    },
    ClickSpecialPic() { this.pets += 1; click(this, this.pets, clock); },
  };
  game.Upgrades['A crumbly egg'] = { bought: true };
  // Controller learning must not inspect a hidden seed, even when one is available to the game.
  Object.defineProperty(game, 'seed', { get() { throw new Error('Hidden seed read'); } });
  const context = { Game: game, Date: ClockDate };
  runInNewContext(`${source}\nthis.run=AutoDragon;`, context);
  return { game, clock, run: () => context.run() };
}

describe('Dragon pet cadence', () => {
  it('Stops at the first new drop, restores the menu and volume, and skips that phase next hour', () => {
    const f = Fixture({ specialTab: 'santa', click(game, count) {
      const { Upgrades } = game;
      if (count === 3) Upgrades[DROPS[0]].unlocked = 1;
      if (count === 4) Upgrades[DROPS[1]].unlocked = 1;
    } });
    f.run();
    expect(f.game.pets).to.equal(3);
    expect(f.game.specialTab).to.equal('santa');
    expect(f.game.volume).to.equal(37);
    expect(f.game.menus).to.deep.equal([[1, 'dragon'], [1, 'santa']]);
    f.run();
    f.clock.now += 3600000;
    f.run();
    expect(f.game.pets).to.equal(3);
    f.clock.now += 900000;
    f.run();
    expect(f.game.pets).to.equal(4);
    expect(f.game.Upgrades[DROPS[1]].unlocked).to.equal(1);
  });

  it('Caps each call at twenty pets and retries a certainly missing phase without a minute wait', () => {
    const f = Fixture();
    f.run();
    expect(f.game.pets).to.equal(20);
    f.run();
    expect(f.game.pets).to.equal(40);
    expect(f.game.specialTab).to.equal('');
    expect(f.game.volume).to.equal(37);
  });

  it('Uses a positive retry cadence for unobserved partial ownership instead of inferring a silent drop', () => {
    const f = Fixture({ owned: [DROPS[0]] });
    f.run();
    expect(f.game.pets).to.equal(20);
    f.run();
    f.clock.now += 99;
    f.run();
    expect(f.game.pets).to.equal(20);
    f.clock.now += 1;
    f.run();
    expect(f.game.pets).to.equal(40);
    expect(f.game.Upgrades[DROPS[1]].unlocked).to.equal(0);
  });

  it('Clears learned phases across a zero-gain transition and a changed public run start', () => {
    ['transition', 'startDate', 'resets'].forEach((change) => {
      const f = Fixture({ click(game, count) {
        const { Upgrades } = game;
        Upgrades[DROPS[count - 1]].unlocked = 1;
      } });
      f.run();
      f.run();
      expect(f.game.pets).to.equal(1);
      if (change === 'transition') {
        f.game.OnAscend = true;
        f.run();
        f.game.OnAscend = false;
      } else f.game[change] += 1;
      // A permanent slot can retain the old drop while the new run has a different permutation.
      f.run();
      expect(f.game.pets).to.equal(2);
      expect(f.game.Upgrades[DROPS[1]].unlocked).to.equal(1);
    });
  });

  it('Restores menu and volume if a native pet callback throws, and preserves an open dragon menu', () => {
    ['', 'santa', 'dragon'].forEach((specialTab) => {
      const f = Fixture({ specialTab, click() { throw new Error('Native callback failed'); } });
      expect(f.run).to.throw('Native callback failed');
      expect(f.game.specialTab).to.equal(specialTab);
      expect(f.game.volume).to.equal(37);
      expect(f.game.pets).to.equal(1);
      if (specialTab === 'dragon') expect(f.game.menus).to.deep.equal([]);
    });
  });

  it('Leaves unrelated prompts alone and stops when all drops are accessed', () => {
    const f = Fixture();
    f.game.promptOn = true;
    f.run();
    expect(f.game.promptOn).to.equal(true);
    expect(f.game.pets).to.equal(0);
    expect(f.game.menus).to.deep.equal([]);
    f.game.promptOn = false;
    DROPS.forEach((name) => { f.game.Upgrades[name].unlocked = 1; });
    f.run();
    expect(f.game.pets).to.equal(0);
  });

  (hasGameSource() ? it : it.skip)('Obtains a native drop at one timestamp despite the growl timer, then skips the learned phase', () => {
    const runtime = createRuntime({ randomSeed: 91 });
    // Funded progression fixture only: the actual native drop callback remains unchanged.
    runtime.evaluate(`
      Game.dragonLevel=8; Game.Upgrades['Pet the dragon'].bought=1;
      Game.volume=37; Game.specialTab='santa'; Game.ToggleSpecialMenu(1);
      Game.lastClickedSpecialPic=Date.now();
      var petCalls=0; var nativePet=Game.ClickSpecialPic;
      Game.ClickSpecialPic=function(){petCalls++;return nativePet.apply(this,arguments);};
      ${source}
    `);
    const initialTime = runtime.snapshot().wallTimeMs;
    let obtained = false;
    for (let batch = 0; batch < 100 && !obtained; batch++) {
      runtime.evaluate('TrackDragonRun();PetDragon();');
      obtained = DROPS.some((name) => runtime.Game.HasUnlocked(name));
    }
    expect(obtained).to.equal(true);
    expect(runtime.snapshot().wallTimeMs).to.equal(initialTime);
    expect(runtime.Game.lastClickedSpecialPic).to.equal(initialTime);
    expect(runtime.Game.specialTab).to.equal('santa');
    expect(runtime.Game.volume).to.equal(37);
    const calls = runtime.context.petCalls;
    expect(runtime.evaluate('PetDragon()')).to.equal(false);
    expect(runtime.context.petCalls).to.equal(calls);
  });

  (hasGameSource() ? it : it.skip)('Keeps native duplicate-drop retries bounded after attaching to a partially completed run', () => {
    const runtime = createRuntime({ randomSeed: 92 });
    runtime.evaluate(`
      Game.dragonLevel=8; Game.Upgrades['Pet the dragon'].bought=1;
      Game.specialTab='dragon'; Game.ToggleSpecialMenu(1);
    `);
    // Reveal this quarter through native play before loading the controller, without revealing its seed.
    for (let pet = 0; pet < 2000 && !DROPS.some((name) => runtime.Game.HasUnlocked(name)); pet++) {
      runtime.evaluate('Game.ClickSpecialPic();');
    }
    expect(DROPS.filter((name) => runtime.Game.HasUnlocked(name))).to.have.length(1);
    runtime.evaluate(`
      var petCalls=0; var nativePet=Game.ClickSpecialPic;
      Game.ClickSpecialPic=function(){petCalls++;return nativePet.apply(this,arguments);};
      ${source}
      TrackDragonRun();PetDragon();
    `);
    expect(runtime.context.petCalls).to.equal(20);
    expect(runtime.evaluate('PetDragon()')).to.equal(false);
    runtime.advance(100);
    expect(runtime.evaluate('PetDragon()')).to.equal(true);
    expect(runtime.context.petCalls).to.equal(40);
    expect(DROPS.filter((name) => runtime.Game.HasUnlocked(name))).to.have.length(1);
  });
});
