/** Frames of life left at which a golden cookie is clicked for "Fading luck" (it needs under a second) */
const FADING_LUCK_FRAMES = 20;

/**
 * Clicks golden cookies and reindeer as soon as they appear
 * Wrath cookies only show up during the Grandmapocalypse and are skipped if the setting says so. Until
 * "Fading luck" is won, golden cookies are clicked in their last second instead (it costs nothing: the
 * cookie's effect does not depend on when it is clicked)
 */
export default function AutoGolden() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGolden || Game.OnAscend || Game.AscendTimer > 0) return;
  const fading = settings.AutoAchievements && !Game.HasAchiev('Fading luck');
  Game.shimmers.slice().forEach((shimmer) => {
    if (shimmer.type === 'golden' && (!shimmer.wrath || settings.AutoGoldenWrath)) {
      if (!fading || shimmer.life <= FADING_LUCK_FRAMES) shimmer.pop();
    } else if (shimmer.type === 'reindeer') shimmer.pop();
  });
}
