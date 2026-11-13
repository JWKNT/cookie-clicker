import { readFileSync, existsSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { join } from 'node:path';
import { homedir } from 'node:os';

export const GAME_VERSION = '2.053';
export const SOURCE_HASHES = Object.freeze({
  'main.js': 'a8813ec2ee97edf5ebff6a3ce2037dcb65c08abd13c123bb92efda89b06ef4f7',
  'minigameGarden.js': '184eacacd9325d493412dcda07f63d3a791939f83889b4349b6099d04be8e6c9',
  'minigameMarket.js': '78538743673f3c1cd0e870a3695c77dcacd63febbe64b88f8a8fab9ea7e2863f',
  'minigameGrimoire.js': '9efea1feb898dc9b719dd971bd27a71f083a8855b910013c524aea9b6d2a349d',
  'minigamePantheon.js': 'af08c31c4564d445cc2d1a7d101c4a63b57aa9b89991b93b8a65f4c0427573a0',
  'base64.js': '875839c3e0c174c9358ce96923adfed6a6d2c090187a32deb35152dfac2c0e47',
  'loc/EN.js': 'ce48272a5fd5ab1f309dbb8fd7bd70188984ce14235a1d3d9215f3585101f433',
  'index.html': '28488d9aef9bf31c4c023a0af01f0500a3b3e462b79bf7f2b09790025927a969',
});

export function defaultGameSourceDirectory() {
  return process.env.COOKIE_CLICKER_SOURCE || join(homedir(), 'Library/Application Support/Steam/steamapps/common/Cookie Clicker/Cookie Clicker.app/Contents/Resources/app/src');
}

export function hasGameSource(directory = defaultGameSourceDirectory()) {
  return existsSync(join(directory, 'main.js'));
}

/** Read game code only. Never read a save or write to the installation. */
export function loadGameSource(directory = defaultGameSourceDirectory()) {
  const sources = {};
  const hashes = {};
  for (const filename of Object.keys(SOURCE_HASHES)) {
    const bytes = readFileSync(join(directory, filename));
    hashes[filename] = createHash('sha256').update(bytes).digest('hex');
    if (SOURCE_HASHES[filename] && hashes[filename] !== SOURCE_HASHES[filename]) {
      throw new Error(`Unsupported game source: SHA-256 mismatch for ${filename}`);
    }
    sources[filename] = bytes.toString('utf8');
  }
  if (!/var VERSION=2\.053;/.test(sources['index.html'])) throw new Error('Expected game version 2.053');
  return { directory, version: GAME_VERSION, hashes, sources };
}
