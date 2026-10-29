/**
 * Section: the Grimoire under autoplay
 *
 * Casts Force the Hand of Fate, a free golden cookie, whenever magic is full. Magic refills at a rate
 * proportional to sqrt(magic / max), faster the fuller the bar, so casting from the top of the bar uses
 * the fastest stretch of the refill: with about 70 magic a cast every 23 minutes, against 40 when casting
 * as soon as the cost is reached.
 */

/**
 * Casts Force the Hand of Fate when magic is full and no golden cookie is on screen (each one on screen
 * makes the spell 15% more likely to backfire)
 * It is called by Autoplay() with the auto-buyer's cadence
 */
export default function AutoGrimoire() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const tower = Game.Objects['Wizard tower'];
  if (!settings.AutoGrimoire || !tower.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0)
    return;
  const M = tower.minigame;
  const spell = M && M.spells['hand of fate'];
  if (!spell || Game.shimmerTypes.golden.n > 0) return;
  if (M.magic >= M.magicM - 0.5 && M.magic >= M.getSpellCost(spell)) M.castSpell(spell);
}
