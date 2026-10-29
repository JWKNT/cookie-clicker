import { ClicksAllowed } from './Challenge.js';

/** The game ignores clicks less than 20 ms apart, so more than 50 per second is pointless */
const MAX_RATE = 50;

let ClickTimer = null;
let ClickInterval = 0;

/**
 * Clicks the big cookie once, without the click sound and with particles drawn on the cookie rather
 * than under the player's mouse
 */
function ClickOnce() {
  if (!Game.ready || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0) return;
  if (!ClicksAllowed()) return;
  const playSound = Game.playCookieClickSound;
  const { mouseX, mouseY } = Game;
  Game.playCookieClickSound = function () {};
  Game.mouseX = Game.cookieOriginX;
  Game.mouseY = Game.cookieOriginY;
  try {
    Game.ClickCookie();
  } finally {
    Game.playCookieClickSound = playSound;
    Game.mouseX = mouseX;
    Game.mouseY = mouseY;
  }
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
