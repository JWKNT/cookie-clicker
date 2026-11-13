import { existsSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { homedir } from 'node:os';
import { spawnSyncWithFileInput as spawnSync } from '../lean/process-input.mjs';

export const EXPECTED_NATIVE_ENGINE = Object.freeze({
  electron: '11.5.0', v8: '8.7.220.31-electron.0', node: '12.18.3',
  icu: '67.1', unicode: '13.0',
});

export function nativeEnginePath() {
  return process.env.COOKIE_CLICKER_ENGINE || join(homedir(),
    'Library/Application Support/Steam/steamapps/common/Cookie Clicker/Cookie Clicker.app/Contents/MacOS/Cookie Clicker');
}

export function hasNativeEngine() { return existsSync(nativeEnginePath()); }

/** The engine path with the home folder written as `~`. A witness records this form, so that
 * it does not hold the account name of the machine that made it. */
export function portableEnginePath(path = nativeEnginePath(), home = homedir()) {
  return home && path.startsWith(`${home}/`) ? `~${path.slice(home.length)}` : path;
}

/** Run a supplied audit worker, not the game entry point. The Electron Node-mode
 * flag prevents loading start.js, Steam integration, or the player's save.
 * Workers must use stdin for their case data and stdout for JSON results. */
export function runNativeEngine(script, input = null, { timeout = 120_000 } = {}) {
  const binary = resolve(nativeEnginePath());
  if (!existsSync(binary)) throw new Error(`Installed game engine not found: ${binary}`);
  const result = spawnSync(binary, ['-e', script], {
    env: { ...process.env, ELECTRON_RUN_AS_NODE: '1' },
    input: JSON.stringify(input), encoding: 'utf8', maxBuffer: 128 * 1024 * 1024, timeout,
  });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`Native engine audit worker failed (${result.status}): ${result.stderr}`);
  return JSON.parse(result.stdout);
}

export function inspectNativeEngine() {
  const identity = runNativeEngine('process.stdout.write(JSON.stringify({versions:process.versions,arch:process.arch,platform:process.platform}));');
  for (const [name, version] of Object.entries(EXPECTED_NATIVE_ENGINE)) {
    if (identity.versions[name] !== version) throw new Error(`Unsupported installed engine ${name}: ${identity.versions[name]}`);
  }
  return { binary: portableEnginePath(), ...identity, gameEntryPointExecuted: false };
}
