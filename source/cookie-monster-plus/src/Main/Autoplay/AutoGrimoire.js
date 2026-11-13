/**
 * Section: the Grimoire under autoplay
 *
 * For a fixed magic cap and spell cost, a continuous square-root recharge model favors full-bar
 * casting over long runs. At about 70 magic, it estimates a cast every 23 minutes, against 40 when
 * casting as soon as the cost is reached. Native recharge uses discrete updates, a minimum rate and
 * rounding. This argument does not prove an optimum for a finite spell goal or the full game.
 */

/**
 * Casts Force the Hand of Fate when magic is full and no golden cookie is on screen (each one on screen
 * makes the spell 15% more likely to backfire)
 * It is called by Autoplay() once in every cycle of frames
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

/**
 * Use remaining magic just before an already committed ordinary ascension.
 * The caller has completed cash-in, loans and the Lucky prestige wait. These
 * two spells do not change cookies or lumps on either outcome. Reset clears
 * their buffs, while their spell count and achievements remain.
 * This does not request another reset or wait for magic.
 * @returns {number} Number of completed casts
 */
export function CastBeforeAscension() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const tower = Game.Objects['Wizard tower'];
  if (
    !settings.AutoGrimoire || Game.promptOn || Game.OnAscend || Game.ascensionMode === 1
    || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0
    || !tower || tower.amount <= 0 || !Game.isMinigameReady(tower)
    || Game.HasAchiev('A wizard is you')
  ) return 0;
  const M = tower.minigame;
  if (!M || !Number.isFinite(M.magicM) || M.magicM <= 0) return 0;
  let casts = 0;
  // Native costs permit fewer casts from a full bar. This limit also stops
  // altered callbacks from keeping the browser in an unbounded loop.
  while (casts < 32 && !Game.HasAchiev('A wizard is you')) {
    if (!Number.isFinite(M.magic) || M.magic < 0 || !Number.isSafeInteger(M.spellsCastTotal) || M.spellsCastTotal < 0) break;
    const choices = [M.spells["haggler's charm"], M.spells['diminish ineptitude']]
      .filter(Boolean)
      .map((spell) => ({ spell, cost: M.getSpellCost(spell) }))
      .filter(({ cost }) => Number.isFinite(cost) && Number.isInteger(cost) && cost > 0 && cost <= M.magic)
      .sort((a, b) => a.cost - b.cost);
    if (!choices.length) break;
    const before = M.spellsCastTotal;
    const { magic } = M;
    if (!M.castSpell(choices[0].spell)) break;
    casts += 1;
    if (!(M.spellsCastTotal > before) || !(M.magic < magic)) break;
  }
  return casts;
}
