import assert from 'node:assert/strict';
import test from 'node:test';
import { readFile, readdir } from 'node:fs/promises';
import { dirname, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { portableEnginePath } from '../model/native-engine.mjs';

// Rules for what this repository publishes. Every file here is public at jehlp.net/cookie-clicker/.
const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const skippedFolders = new Set(['.git', 'node_modules', '.lake', 'dist', '.claude', '__pycache__']);
const textFile = /\.(json|json5|mjs|cjs|js|md|txt|py|lean|log|toml|html|css|tex|cc|h|hpp|cpp|idl|patch)$/;

async function* files(folder) {
  for (const entry of await readdir(folder, { withFileTypes: true })) {
    if (entry.isDirectory()) {
      if (!skippedFolders.has(entry.name)) yield* files(join(folder, entry.name));
    } else if (entry.isFile()) yield join(folder, entry.name);
  }
}

test('no file records the home folder of a machine', async () => {
  // A witness or a script of the audit must not hold a path such as /Users/name/ or /home/name/.
  const homePath = /\/(?:Users|home)\/[A-Za-z0-9._-]+\//;
  const found = [];
  const self = fileURLToPath(import.meta.url);
  for await (const file of files(root)) {
    // This file has example paths for the test below.
    if (!textFile.test(file) || file === self) continue;
    if (homePath.test(await readFile(file, 'utf8'))) found.push(relative(root, file));
  }
  assert.deepEqual(found, []);
});

test('the engine path of a witness has ~ for the home folder', () => {
  assert.equal(portableEnginePath('/Users/somebody/Library/Game/engine', '/Users/somebody'), '~/Library/Game/engine');
  assert.equal(portableEnginePath('/opt/game/engine', '/Users/somebody'), '/opt/game/engine');
  assert.equal(portableEnginePath('/Users/somebody-else/engine', '/Users/somebody'), '/Users/somebody-else/engine');
  assert.doesNotMatch(portableEnginePath(), /^\/(?:Users|home)\//);
});

test('the two files with the complete game program stay out of the repository', async () => {
  const ignored = (await readFile(join(root, '.gitignore'), 'utf8')).split('\n');
  for (const name of ['request.json.gz', 'request-template.json']) {
    assert.ok(ignored.includes(`model/experiments/cursor-cycle-source/${name}`), name);
  }
  const notice = await readFile(join(root, 'THIRD-PARTY.md'), 'utf8');
  assert.match(notice, /please do not re-host it/);
});
