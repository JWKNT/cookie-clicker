import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import test from 'node:test';
import { spawnSyncWithFileInput } from '../lean/process-input.mjs';

test('checker transport preserves empty and large UTF-8 fixtures through EOF', () => {
  const script = 'const fs=require("fs"),crypto=require("crypto");const b=fs.readFileSync(0);process.stdout.write(JSON.stringify({bytes:b.length,sha:crypto.createHash("sha256").update(b).digest("hex")}));';
  for (const input of ['', 'lump\u0000🍪\n'.repeat(100000)]) {
    const result = spawnSyncWithFileInput(process.execPath, ['-e', script], { input, encoding: 'utf8', timeout: 5000 });
    assert.equal(result.status, 0, result.stderr || result.error?.message);
    assert.deepEqual(JSON.parse(result.stdout), {
      bytes: Buffer.byteLength(input), sha: createHash('sha256').update(input).digest('hex'),
    });
  }
});

test('checker transport preserves failure and timeout and removes its input files', () => {
  const before = new Set(readdirSync(tmpdir()).filter(name => name.startsWith('cookie-lean-input-')));
  const failed = spawnSyncWithFileInput(process.execPath, ['-e', 'process.stderr.write("failure");process.exit(7);'], { input: 'fixture', encoding: 'utf8' });
  assert.equal(failed.status, 7);
  assert.equal(failed.stderr, 'failure');
  const timed = spawnSyncWithFileInput(process.execPath, ['-e', 'setInterval(()=>{},1000);'], { input: 'fixture', encoding: 'utf8', timeout: 100 });
  assert.equal(timed.error?.code, 'ETIMEDOUT');
  assert.equal(timed.status, null);
  const after = readdirSync(tmpdir()).filter(name => name.startsWith('cookie-lean-input-') && !before.has(name));
  assert.deepEqual(after, []);
});


test('native-engine workers receive complete finite fixtures through a regular file', async t => {
  const {hasNativeEngine, runNativeEngine} = await import('../model/native-engine.mjs');
  if (!hasNativeEngine()) { t.skip('Pinned engine is not installed'); return; }
  const worker = 'const fs=require("fs"),crypto=require("crypto");const b=fs.readFileSync(0);process.stdout.write(JSON.stringify({bytes:b.length,sha:crypto.createHash("sha256").update(b).digest("hex")}));';
  for (const value of [null, {text:'lump\u0000🍪\n'.repeat(100000)}]) {
    const input = JSON.stringify(value);
    assert.deepEqual(runNativeEngine(worker, value, {timeout:10000}), {
      bytes:Buffer.byteLength(input), sha:createHash('sha256').update(input).digest('hex'),
    });
  }
});
