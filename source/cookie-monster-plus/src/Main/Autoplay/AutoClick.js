import { ClicksAllowed } from './Challenge.js';

/** The game ignores clicks less than 20 ms apart, so more than 50 per second is pointless */
const MAX_RATE = 50;

let ClickTimer = null;
let ClickInterval = 0;
let NextClickAt = 0;

/**
 * Whether a click is due on a tick at time now, and when the next one is due. Clicks keep their
 * interval on average. A schedule more than one interval behind starts again: missed clicks are not
 * made up in a burst
 * @param	{number}	now	Date.now()
 * @param	{number}	next	When the next click is due
 * @param	{number}	interval	Milliseconds between clicks
 * @returns	{{click: boolean, next: number}}
 */
export function ClickSchedule(now, next, interval) {
  const due = now - next > interval ? now : next;
  if (now < due) return { click: false, next: due };
  return { click: true, next: due + interval };
}

/**
 * Clicks the big cookie once, without the click sound and with particles drawn on the cookie rather
 * than under the player's mouse
 */
function ClickOnce() {
  if (!Game.ready || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0) return;
  if (!ClicksAllowed()) return;
  const { mouseX, mouseY, volume } = Game;
  // Keep the native sound callback's random draw and sound-index update.
  // The native audio function checks this volume before it plays a sound.
  Game.volume = 0;
  Game.mouseX = Game.cookieOriginX;
  Game.mouseY = Game.cookieOriginY;
  try {
    Game.ClickCookie();
  } finally {
    Game.volume = volume;
    Game.mouseX = mouseX;
    Game.mouseY = mouseY;
  }
}

/**
 * Clicks when a click is due, for ticks that replace the clicker's timer while the window is hidden
 * @param	{number}	now	Date.now()
 */
export function ClickWhenDue(now) {
  if (ClickTimer === null) return;
  const { click, next } = ClickSchedule(now, NextClickAt, ClickInterval);
  NextClickAt = next;
  if (click) ClickOnce();
}

/**
 * Starts, stops or retimes the clicker to match the settings
 * Clicks run on their own timer because the game limits clicks by real time, not by game frames
 */
export default function UpdateAutoClicker() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const rate = settings.AutoClick
    ? Math.min(Math.max(Number(settings.AutoClickRate) || 0, 0), MAX_RATE)
    : 0;
  const interval = rate > 0 ? Math.round(1000 / rate) : 0;
  if (interval === ClickInterval) return;
  if (ClickTimer !== null) clearInterval(ClickTimer);
  ClickTimer = interval > 0 ? setInterval(ClickOnce, interval) : null;
  ClickInterval = interval;
}
