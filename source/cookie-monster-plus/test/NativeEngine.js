/**
 * The native tests run the mod against the source of the game itself. They need two things that
 * are not in this repository: a model of the game engine in the folder `model/` at the repository
 * root, and an installed copy of Cookie Clicker 2.053. Without them, mocha reports the native
 * tests as pending.
 */
const model = new URL('../../../model/', import.meta.url);

let createRuntime = null;
let hasGameSource = () => false;
try {
  // The addresses are calculated, so that the lint check does not look for the model.
  ({ createRuntime } = await import(new URL('runtime.mjs', model).href));
  ({ hasGameSource } = await import(new URL('game-source.mjs', model).href));
} catch {
  // The model is not present. hasGameSource() stays false, and the native tests are skipped.
  createRuntime = null;
  hasGameSource = () => false;
}

export { createRuntime, hasGameSource };
