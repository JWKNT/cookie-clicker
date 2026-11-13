/** Fixed public input sweep. No game handle, seed, save, or sprite positions. */
export const HELPER_GRANDMAS = 24;
export const HELPER_HOLD_MILLISECONDS = 134;
export const HELPER_ART_EXCLUSIONS = Object.freeze([
  'Farmer grandmas', 'Worker grandmas', 'Miner grandmas', 'Cosmic grandmas',
  'Transmuted grandmas', 'Altered grandmas', "Grandmas' grandmas", 'Antigrandmas',
  'Rainbow grandmas', 'Banker grandmas', 'Priestess grandmas', 'Witch grandmas',
  'Lucky grandmas', 'Metagrandmas', 'Script grannies', 'Alternate grandmas',
  'Brainy grandmas', 'Clone grandmas',
]);

export function helperSweepPoint(index) {
  if (!Number.isInteger(index) || index < 0 || index >= HELPER_GRANDMAS) throw new Error('Expected a Grandma index from 0 through 23');
  return { x: Math.floor(32 * Math.floor(index / 3) + 32 * (index % 3) / 3) + 32,
    y: 56 + 16 * (index % 3) };
}

/** Preconditions: Christmas; no listed art upgrade; >=24 Grandmas; visible,
 * unmuted canvas at least 278x89; animate and fancy on; menu/prompt closed;
 * enough native Draw calls remain before drawT saturation. The initial wait
 * draws the bought sprites. A 134ms hold spans at least three 30Hz draw calls.
 * The native achievement test runs for every hit sprite, before overlap wins.
 */
export function helperSweepActions() {
  return [{ type: 'wait', milliseconds: HELPER_HOLD_MILLISECONDS },
    ...Array.from({ length: HELPER_GRANDMAS }, (_, index) => [
      { type: 'building-hover', id: 1, ...helperSweepPoint(index) },
      { type: 'building-press', id: 1, release: false },
      { type: 'wait', milliseconds: HELPER_HOLD_MILLISECONDS },
      { type: 'building-press', id: 1, release: true },
    ]).flat()];
}
