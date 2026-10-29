/**
 * Section: the "Born again" challenge run
 *
 * "Neverclick" (1 million cookies baked with at most 15 clicks) and "Hardcore" (1 billion baked without
 * buying an upgrade) only count in a Born again run, which starts from nothing: no prestige, heavenly
 * upgrades, sugar lumps or minigames. A simulation of such a run (buildings only, golden cookies
 * clicked, the 15 clicks spent on the first cursor) reaches 1 million in about 41 minutes and 1 billion
 * in about 3.8 hours. The run earns nothing worth having, so it delays all later play by its length, and
 * autoplay starts one when the achievements are worth more than that (see AchievementWorth). It then
 * plays the run within the rules (no clicks past 15 until "Neverclick", no upgrades until "Hardcore")
 * and ascends as soon as both are won, back into a normal run.
 */

import { AchievementWorth } from '../../Cache/PP/AutoplayValue.js';

/** Seconds a Born again run takes to reach each achievement, rounded up from the simulation */
const NEVERCLICK_SECONDS = 0.75 * 3600;
const HARDCORE_SECONDS = 4 * 3600;
/** Clicks "Neverclick" allows */
const NEVERCLICK_CLICKS = 15;
/** Give up on a run that takes this many times longer than expected */
const TIMEOUT_FACTOR = 2;

/**
 * Whether this is a Born again run
 * @returns	{boolean}
 */
export function ChallengeRun() {
  return Game.ascensionMode === 1;
}

/**
 * The challenge achievements not won yet
 * @returns	{string[]}
 */
function Missing() {
  return ['Neverclick', 'Hardcore'].filter((name) => !Game.HasAchiev(name));
}

/**
 * Seconds a Born again run needs for what is missing (Hardcore's billion comes after Neverclick's
 * million, so one run gets both)
 * @returns	{number}
 */
function ChallengeSeconds() {
  return Game.HasAchiev('Hardcore') ? NEVERCLICK_SECONDS : HARDCORE_SECONDS;
}

/**
 * Whether the next run should be a Born again run: the missing achievements are worth more seconds of
 * play than the run takes. Not twice in a row, in case a run timed out
 * @param	{boolean}	lastWasChallenge	Whether the run just ended was one
 * @returns	{boolean}
 */
export function ChallengeDue(lastWasChallenge) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const missing = Missing().length;
  if (!settings.AutoChallenge || !missing || lastWasChallenge) return false;
  return ChallengeSeconds() <= AchievementWorth(missing);
}

/**
 * Whether the big cookie may be clicked: in a Born again run, only 15 times until "Neverclick"
 * @returns	{boolean}
 */
export function ClicksAllowed() {
  return !(
    ChallengeRun() &&
    !Game.HasAchiev('Neverclick') &&
    Game.cookieClicks >= NEVERCLICK_CLICKS
  );
}

/**
 * Whether upgrades may be bought: in a Born again run, not until "Hardcore"
 * @returns	{boolean}
 */
export function UpgradesAllowed() {
  return !(ChallengeRun() && !Game.HasAchiev('Hardcore'));
}

/**
 * Whether the Born again run is over: both achievements won, or it took far longer than expected
 * @returns	{boolean}
 */
export function ChallengeDone() {
  if (!ChallengeRun()) return false;
  const elapsed = (Date.now() - Game.startDate) / 1000;
  return !Missing().length || elapsed > TIMEOUT_FACTOR * ChallengeSeconds();
}
