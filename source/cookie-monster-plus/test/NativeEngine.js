/**
 * The native tests run the mod against the source of the game itself. They need the model of the
 * game engine in the folder `model/` at the repository root, and an installed copy of Cookie
 * Clicker 2.053. Without the model or without the game, mocha reports the native tests as pending.
 */
const model = new URL('../../../model/', import.meta.url);

let createRuntime = null;
let hasGameSource = () => false;
try {
  // The addresses are calculated, so that the lint check does not look for the model.
  ({ createRuntime } = await import(new URL('runtime.mjs', model).href));
  ({ hasGameSource } = await import(new URL('game-source.mjs', model).href));
} catch {
  // The model is not present, for example in a copy of this folder alone. The native tests are skipped.
  createRuntime = null;
  hasGameSource = () => false;
}

export { createRuntime, hasGameSource };
