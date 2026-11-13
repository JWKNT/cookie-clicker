/**
 * Section: full speed while the window is hidden
 *
 * The browser throttles timers in a hidden window, for example one behind a full-screen app. The game's
 * loop and the auto-clicker then run a few times a minute, and the game makes up at most five seconds
 * each time, so a hidden game runs at a fraction of its speed. A worker's timer is not throttled. It
 * sends a tick every frame. When the game's own loop has not run for LAG_MS, each tick runs the logic
 * frames that the window missed, with the game's own catch-up, and the clicks that the auto-clicker
 * missed.
 */

import { ClickWhenDue } from './AutoClick.js';

/** Milliseconds without a run of the game's own loop before the ticks take over */
export const LAG_MS = 250;
/** The game's own limit on the catch-up in one run of its loop */
export const MAX_CATCHUP_MS = 5000;
/** The worker posts a message at every interval it receives, and stops on 0 */
const WORKER_SOURCE =
  'let t=0;onmessage=(e)=>{clearInterval(t);t=e.data>0?setInterval(()=>postMessage(0),e.data):0;};';

let Ticker = null;
let Unavailable = false;
let LastLoopT = -1;
let LastLoopSeen = 0;

/**
 * Whether the game's own loop has stopped keeping up: it has not run for LAG_MS
 * @param	{number}	now	Date.now()
 * @returns	{boolean}
 */
export function Behind(now) {
  if (Game.loopT !== LastLoopT) {
    LastLoopT = Game.loopT;
    LastLoopSeen = now;
  }
  return now - LastLoopSeen >= LAG_MS;
}

/**
 * Runs the logic frames that the game missed while its own loop was throttled, with the game's own
 * accounting: Game.Loop adds the elapsed time to Game.accumulatedDelay and runs one frame for every
 * 1000 / fps milliseconds of it, up to five seconds
 * @param	{number}	now	Date.now()
 * @returns	{number}	Logic frames run
 */
export function CatchUp(now) {
  if (!Game.ready || Game.timedout || !Behind(now)) return 0;
  const frame = 1000 / Game.fps;
  Game.accumulatedDelay = Math.min(Game.accumulatedDelay + (now - Game.time), MAX_CATCHUP_MS);
  Game.time = now;
  let frames = 0;
  Game.catchupLogic = 1;
  try {
    while (Game.accumulatedDelay > 0) {
      Game.Logic();
      Game.accumulatedDelay -= frame;
      frames += 1;
    }
  } finally {
    Game.catchupLogic = 0;
  }
  return frames;
}

/** Runs on each message from the worker */
function Tick() {
  const now = Date.now();
  CatchUp(now);
  if (Behind(now)) ClickWhenDue(now);
}

/**
 * Starts or stops the worker to match the settings
 * It is called once a second by Cookie Monster's loop
 */
export default function UpdateBackgroundTicks() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const on = !!settings.AutoBackground && !Unavailable && typeof Worker !== 'undefined';
  if (on && Ticker === null) {
    try {
      const url = URL.createObjectURL(new Blob([WORKER_SOURCE], { type: 'text/javascript' }));
      Ticker = new Worker(url);
      Ticker.onmessage = Tick;
      Ticker.postMessage(1000 / Game.fps);
    } catch {
      // Without workers the game runs as before
      Unavailable = true;
      Ticker = null;
    }
  } else if (!on && Ticker !== null) {
    Ticker.terminate();
    Ticker = null;
  }
}
