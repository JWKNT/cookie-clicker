import { after, before, describe, it } from 'mocha';
import { expect } from 'chai';
import { Game } from '../GlobalsForTesting.js';

import { CatchUp, LAG_MS } from '../../src/Main/Autoplay/AutoBackground.js';
import { ClickSchedule } from '../../src/Main/Autoplay/AutoClick.js';

const FRAME = 1000 / 30;

/** One run of the game's own loop, as in Game.Loop: a frame, then the catch-up of at most 5 seconds */
function GameLoop(now) {
  Game.Logic();
  Game.accumulatedDelay += now - Game.time - FRAME;
  Game.accumulatedDelay = Math.min(Game.accumulatedDelay, 5000);
  Game.time = now;
  while (Game.accumulatedDelay > 0) {
    Game.Logic();
    Game.accumulatedDelay -= FRAME;
  }
  Game.loopT += 1;
}

describe('Full speed while the window is hidden', () => {
  const saved = {};
  const keys = ['ready', 'timedout', 'fps', 'loopT', 'time', 'accumulatedDelay', 'Logic', 'catchupLogic'];
  let frames = 0;
  before(() => {
    global.Game = Game;
    keys.forEach((key) => {
      saved[key] = Game[key];
    });
    Object.assign(Game, { ready: 1, timedout: 0, fps: 30, loopT: 0, time: 0, accumulatedDelay: 0 });
    Game.Logic = () => {
      frames += 1;
    };
  });
  after(() =>
    keys.forEach((key) => {
      Game[key] = saved[key];
    }),
  );

  it('Leaves the game alone while its own loop keeps running', () => {
    Game.time = 100000 - FRAME;
    frames = 0;
    for (let now = 100000; now < 101000; now += FRAME) {
      GameLoop(now);
      expect(CatchUp(now + 5)).to.equal(0);
    }
    expect(frames).to.be.closeTo(30, 1);
  });

  it('Runs the missed frames once the loop has not run for LAG_MS', () => {
    Game.loopT += 1;
    Game.time = 200000;
    Game.accumulatedDelay = 0;
    expect(CatchUp(200000)).to.equal(0); // the loop has just run
    expect(CatchUp(200000 + LAG_MS - 1)).to.equal(0);
    frames = 0;
    expect(CatchUp(201000)).to.equal(30);
    expect(frames).to.equal(30);
    expect(Game.time).to.equal(201000);
    expect(Game.accumulatedDelay).to.be.within(-FRAME, 0);
  });

  it('Makes up at most five seconds at once, like the game', () => {
    // 5000 / (1000 / 30) frames, plus at most one for the floating-point remainder, as in Game.Loop
    Game.time -= 60000;
    expect(CatchUp(Game.time + 60000)).to.be.within(150, 151);
  });

  it('Keeps game time in step with real time when the throttled loop also runs', () => {
    Game.loopT += 1;
    Game.time = 300000;
    Game.accumulatedDelay = 0;
    frames = 0;
    // Ticks every frame; the game's own loop only once a second, as in a hidden window
    for (let i = 1; i <= 300; i += 1) {
      const now = 300000 + i * FRAME;
      if (i % 30 === 0) GameLoop(now);
      CatchUp(now);
    }
    expect(frames).to.be.closeTo(300, 2);
  });

  it('Clicks at the set rate on ticks every frame, without a burst after a long gap', () => {
    let next = 0;
    let clicks = 0;
    for (let now = 1000; now < 2000; now += FRAME) {
      const result = ClickSchedule(now, next, 50);
      ({ next } = result);
      if (result.click) clicks += 1;
    }
    expect(clicks).to.be.closeTo(20, 1);
    expect(ClickSchedule(60000, next, 50)).to.deep.equal({ click: true, next: 60050 });
  });
});
