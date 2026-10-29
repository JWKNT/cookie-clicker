/**
 * Section: achievements that only take an action
 *
 * Every achievement (shadow ones aside) adds 4% milk, which the kitten upgrades turn into CpS: about +2%
 * CpS each with a dozen kittens and 800% milk. These take nothing but a click in the right place, done
 * the way a player would do them (through the game's own click handlers and menus).
 */

/** Seconds between pokes of the same wrinkler: it regains 1.2 hp per second and loses 0.75 per poke */
const POKE_SECONDS = 1.5;
/** Milliseconds between moving the mouse onto the wrinkler and clicking (it must register as hovered) */
const POKE_DELAY = 250;

/** Seconds between tries at the madeleine, in case the update log cannot show it */
const MADELEINE_RETRY_SECONDS = 600;
/** Window width to shrink to for "Stifling the press" (the game squishes the ticker below 900) */
const NARROW_WIDTH = 880;
/** Milliseconds to wait for the narrow window before giving up, and seconds before trying again */
const SQUISH_WAIT = 3000;
const SQUISH_RETRY_SECONDS = 3600;
/** A gift code stays valid for two days; use it well within that */
const GIFT_CODE_SECONDS = 36 * 3600;

let LastPoke = 0;
let LastMadeleine = 0;
let Squish = null;
let LastSquish = 0;
let Gift = null;

/** The wrinkler being poked for "Wrinkler poker" (bursting sprees spare it) */
export const PokeState = { target: null };

/**
 * Clicks the news ticker: 50 clicks for "Tabloid addiction", once in a narrow window for "Stifling the
 * press", and whenever it shows a fortune (fortune upgrades add CpS, the others pay out at once)
 * @returns	{boolean}	Whether it clicked
 */
function ClickTicker() {
  if (!Game.tickerL) return false;
  // In a window narrower than the game's limit, a click squishes the ticker: "Stifling the press"
  const narrow = Game.windowW < Game.tickerTooNarrow && !Game.HasAchiev('Stifling the press');
  const fortune = Game.TickerEffect && Game.TickerEffect.type === 'fortune';
  if (Game.HasAchiev('Tabloid addiction') && !narrow && !fortune) return false;
  Game.tickerL.click();
  return true;
}

/**
 * "Stifling the press" needs the ticker clicked in a window under 900 pixels wide. In the Steam app the
 * page can resize its own window: shrink it for a moment (the ticker click above then counts), and put
 * the size back once the achievement is in or the window did not shrink
 * @returns	{boolean}	Whether it is busy with this
 */
function SquishTicker() {
  if (Squish) {
    if (Game.HasAchiev('Stifling the press') || Date.now() - Squish.since > SQUISH_WAIT) {
      window.resizeTo(Squish.width, Squish.height);
      Squish = null;
      LastSquish = Date.now();
    }
    return true;
  }
  if (
    Game.HasAchiev('Stifling the press') ||
    !window.api || // only the Steam app's page owns its window
    window.outerWidth <= NARROW_WIDTH ||
    Date.now() - LastSquish < SQUISH_RETRY_SECONDS * 1000
  )
    return false;
  Squish = { width: window.outerWidth, height: window.outerHeight, since: Date.now() };
  window.resizeTo(NARROW_WIDTH, window.outerHeight);
  return true;
}

/**
 * "Baby it's old outside": during Christmas some grandmas in the grandma row are Santa's helpers, and
 * pressing the mouse on one counts. Points the row's mouse at a helper with the button down for one
 * redraw of the row, as hovering and pressing would
 * @returns	{boolean}	Whether it tried
 */
function ElfGrandma() {
  const me = Game.Objects.Grandma;
  if (Game.HasAchiev("Baby it's old outside") || Game.season !== 'christmas' || !me.amount)
    return false;
  const elf = me.pics.find((pic) => pic.pic === 'elfGrandma.png');
  if (!elf) {
    me.redraw(); // the pictures predate Christmas: draw them again from the season's list
    return true;
  }
  const { mouseDown } = Game;
  me.mouseOn = true;
  me.mousePos = [elf.x + 32, elf.y + 32];
  Game.mouseDown = 1;
  try {
    me.draw();
  } finally {
    me.mouseOn = false;
    me.mousePos = [-100, -100];
    Game.mouseDown = mouseDown;
  }
  return true;
}

/**
 * "No time like the present": with Wrapping paper, sends a gift of 1 cookie to keep its code, then
 * redeems the code once the hour of "Gifted out" that sending starts is over
 * @returns	{boolean}	Whether it did something
 */
function SelfGift() {
  if (
    Game.HasAchiev('No time like the present') ||
    !Game.Has('Wrapping paper') ||
    Game.ascensionMode !== 0 ||
    Game.cookies < 1e9 ||
    Game.hasBuff('Gifted out') ||
    Game.promptOn
  )
    return false;
  if (!Gift || Date.now() - Gift.time > GIFT_CODE_SECONDS * 1000) {
    Game.promptGiftSend();
    if (l('giftAmount') && l('promptOption0')) {
      l('giftAmount').value = 1;
      l('promptOption0').click();
      if (l('giftCode') && l('giftCode').value) Gift = { code: l('giftCode').value, time: Date.now() };
    }
    Game.ClosePrompt();
    return true;
  }
  Game.promptGiftRedeem();
  if (l('giftCode') && l('promptOption0')) {
    l('giftCode').value = Gift.code;
    l('giftCode').dispatchEvent(new Event('change'));
    l('promptOption0').click();
  }
  Game.ClosePrompt();
  Gift = null;
  return true;
}

/**
 * Finds the forgotten madeleine at the bottom of the update log, then goes back to the menu that was open
 * @returns	{boolean}	Whether it found it
 */
function FindMadeleine() {
  if (Game.HasAchiev('Olden days') || Date.now() - LastMadeleine < MADELEINE_RETRY_SECONDS * 1000)
    return false;
  LastMadeleine = Date.now();
  const previous = Game.onMenu;
  if (previous !== 'log') Game.ShowMenu('log');
  const madeleine = l('oldenDays');
  if (madeleine && madeleine.firstChild) madeleine.firstChild.click();
  if (previous !== 'log') Game.ShowMenu(previous);
  return true;
}

/**
 * "Wrinkler poker": pokes one wrinkler 50 times without bursting it. Moves the mouse onto the wrinkler,
 * then clicks once the game has registered it as hovered
 * @returns	{boolean}	Whether it is busy poking
 */
function PokeWrinkler() {
  if (Game.HasAchiev('Wrinkler poker') || !Game.wrinklers) return false;
  if (!PokeState.target || PokeState.target.phase !== 2 || PokeState.target.type !== 0) {
    PokeState.target = Game.wrinklers.find((me) => me.phase === 2 && me.type === 0) || null;
    if (!PokeState.target) return false;
  }
  const { target } = PokeState;
  if (target.hp < Game.wrinklerHP - 0.05 || Date.now() - LastPoke < POKE_SECONDS * 1000) return true;
  LastPoke = Date.now();
  Game.mouseX = target.x;
  Game.mouseY = target.y;
  setTimeout(() => {
    Game.mouseX = target.x;
    Game.mouseY = target.y;
    if (target.selected && l('backgroundLeftCanvas'))
      l('backgroundLeftCanvas').dispatchEvent(new MouseEvent('click', { bubbles: true }));
  }, POKE_DELAY);
  return true;
}

/**
 * Takes the next action-only achievement, one per call
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoAchievements() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (
    !settings.AutoAchievements ||
    Game.OnAscend ||
    Game.AscendTimer > 0 ||
    Game.ReincarnateTimer > 0
  )
    return;
  if (!Game.HasAchiev('Here you go')) {
    Game.Achievements['Here you go'].click();
    return;
  }
  if (!Game.HasAchiev('Tiny cookie')) {
    Game.ClickTinyCookie();
    return;
  }
  if (!Game.HasAchiev('Just wrong') && Game.Objects.Grandma.amount > 1) {
    Game.Objects.Grandma.sell(1);
    return;
  }
  if (FindMadeleine()) return;
  if (SquishTicker() && Game.windowW >= Game.tickerTooNarrow) return;
  if (ClickTicker()) return;
  if (ElfGrandma()) return;
  if (SelfGift()) return;
  PokeWrinkler();
}
