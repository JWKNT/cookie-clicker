import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';
import { gunzipSync } from 'node:zlib';
import { loadGameSource } from '../model/game-source.mjs';
import { runNativeEngine } from '../model/native-engine.mjs';
import { shortAsciiSeededRandom, STARTUP_SEED_COUNT } from '../model/seed-inference.mjs';

const mode = process.argv[2] || '--check';
assert(['--check', '--scan'].includes(mode), 'Use --check or --scan');
assert(process.argv.length <= 3, 'Unexpected arguments');
const root = new URL('../', import.meta.url);
const read = path => readFileSync(new URL(path, root));
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const witness = JSON.parse(read('model/veil-cover-witness.json'));
assert.equal(sha256(read(witness.portableAudit.tool)), witness.portableAudit.toolSha256);
assert.equal(sha256(read(witness.portableAudit.fixture)), witness.portableAudit.fixtureSha256);
const original = JSON.parse(read(witness.originalProvenance.checkpoint));
assert.equal(sha256(read(witness.originalProvenance.checkpoint)), witness.originalProvenance.checkpointSha256);
for (const row of witness.originalProvenance.archivedFiles) {
  assert.equal(sha256(read(row.path)), row.sha256, row.path);
  if (row.originalPath !== 'checkpoint.json') {
    const originalRow = original.files.find(file => file.path === row.originalPath);
    assert(originalRow, row.originalPath);
    assert.equal(row.sha256, originalRow.sha256, row.originalPath);
  }
}
const compressed = read(witness.certificate.path), certificate = gunzipSync(compressed);
assert.equal(compressed.length, witness.certificate.compressedBytes);
assert.equal(sha256(compressed), witness.certificate.compressedSha256);
assert.equal(certificate.length, witness.certificate.bytes);
assert.equal(sha256(certificate), witness.certificate.sha256);
assert.equal(certificate.length, STARTUP_SEED_COUNT);
const histogram = Array.from({ length: witness.maximumSufficientCounter + 1 }, () => 0);
for (const counter of certificate) {
  assert(counter <= witness.maximumSufficientCounter, 'Certificate counter outside the retained bound');
  histogram[counter]++;
}
assert.deepEqual(histogram, witness.histogram);
assert.equal(witness.unresolvedSeeds, 0);
assert.equal(witness.zeroInitialSixByteWordsThroughSelectedCounter, 0);
const ordinalSeed = ordinal => {
  let seed = '';
  for (let i = 0; i < 5; i++) {
    seed = String.fromCharCode(97 + ordinal % 26) + seed;
    ordinal = Math.floor(ordinal / 26);
  }
  return seed;
};
assert.equal(ordinalSeed(certificate.indexOf(witness.maximumSufficientCounter)), witness.firstMaximumSeed);

const samples = []; let state = 1;
for (let n = 0; n < 1000; n++) {
  state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
  for (const counter of [0, 1, 9, 10, 31, 63]) samples.push({ seed: ordinalSeed(state % STARTUP_SEED_COUNT), counter });
}
for (const seed of ['aaaaa', 'aaaab', 'zzzzz']) {
  for (let counter = 0; counter < 64; counter++) samples.push({ seed, counter });
}
const sampleText = samples.map(({ seed, counter }) => `${seed} ${counter}`).join('\n') + '\n';
assert.equal(samples.length, witness.preflight.sampleInputs);
assert.equal(sha256(sampleText), witness.preflight.sampleInputSha256);
const source = loadGameSource();
assert.deepEqual(source.hashes, witness.sourceHashes);
const require = createRequire(new URL('../source/cookie-monster-plus/package.json', import.meta.url));
const text = source.sources['main.js'];
const parsed = require('acorn').parse(text, { ecmaVersion: 5 });
const roots = parsed.body.filter(node => node.type === 'ExpressionStatement'
  && text.slice(node.start, node.end).includes('c.seedrandom=function'));
assert.equal(roots.length, 1);
const library = text.slice(roots[0].start, roots[0].end);
assert.equal(sha256(library), witness.preflight.seedrandomLibrarySha256);
const scratch = mkdtempSync(join(tmpdir(), 'cookie-veil-cover-'));
try {
  const executable = join(scratch, 'scan');
  const cpp = fileURLToPath(new URL('./veil-cover/scan.cpp', import.meta.url));
  const flags = ['-std=c++17', '-O3', '-fno-fast-math', '-ffp-contract=off', '-pthread'];
  execFileSync('clang++', [...flags, cpp, '-o', executable], { stdio: 'inherit' });
  const samplePath = join(scratch, 'samples.txt'); writeFileSync(samplePath, sampleText);
  const lines = execFileSync(executable, ['--samples', samplePath], { encoding: 'utf8', maxBuffer: 10000000 }).trim().split('\n');
  assert.equal(lines.length, samples.length);
  assert.equal(sha256(lines.join('\n')), witness.preflight.sampleOutputSha256);
  const native = runNativeEngine(`const fs=require('fs'),vm=require('vm');
    const input=JSON.parse(fs.readFileSync(0,'utf8')),context=vm.createContext({});
    vm.runInContext(input.library,context);
    const rows=input.samples.map(x=>{context.seed=x.seed+'/'+x.counter;
      const value=vm.runInContext('Math.seedrandom(seed);Math.random()',context);
      const buffer=Buffer.alloc(8);buffer.writeDoubleBE(value);return buffer.toString('hex');});
    process.stdout.write(JSON.stringify({versions:process.versions,rows}));`, { library, samples });
  const bits = value => { const buffer = Buffer.alloc(8); buffer.writeDoubleBE(value); return buffer.toString('hex'); };
  for (let i = 0; i < samples.length; i++) {
    const [seed, counter, word, output] = lines[i].split(' ');
    assert.equal(seed, samples[i].seed); assert.equal(+counter, samples[i].counter);
    assert.equal(output, native.rows[i]);
    assert.equal(output, bits(shortAsciiSeededRandom(`${seed}/${counter}`)()));
    assert(BigInt(word) > 0n);
  }
  const fixture = JSON.parse(execFileSync(process.execPath,
    [fileURLToPath(new URL('./veil-cover/free-veils-fixture.mjs', import.meta.url))],
    { encoding: 'utf8', maxBuffer: 10000000 }));
  const originalFixture = JSON.parse(read('model/experiments/veil-seed-cover/free-veils-receipt.json'));
  assert.deepEqual(fixture.sales, originalFixture.sales);
  assert.deepEqual(fixture.receipts, originalFixture.receipts);
  assert.equal(fixture.purchases, 34); assert.equal(fixture.receipts.length, 35);
  assert.equal(fixture.receipts.at(-1).won, true);
  assert.deepEqual(fixture.sourceHashes, witness.sourceHashes);
  if (mode === '--scan') {
    // This is an explicit new exhaustive native computation. It does not write
    // over the historical archive and does not invoke Lean's kernel.
    const result = join(scratch, 'first-counter.bin'), summary = join(scratch, 'scan.json');
    execFileSync(executable, [result, summary, String(STARTUP_SEED_COUNT), '2', '64'], { stdio: 'inherit' });
    assert.equal(sha256(readFileSync(result)), witness.certificate.sha256);
    const scan = JSON.parse(readFileSync(summary));
    assert.equal(scan.unresolved, 0); assert.equal(scan.zeroInitialSixByteWordsThroughSelectedCounter, 0);
    assert.equal(scan.maxSufficientCounter, witness.maximumSufficientCounter);
    assert.deepEqual(scan.histogram, histogram);
  }
  console.log(JSON.stringify({ scope: witness.scope, archiveIntegrity: true,
    certificateBytes: certificate.length, maximumSufficientCounter: witness.maximumSufficientCounter,
    pinnedNativePreflightOutputs: samples.length, preflightBitExact: true, suppliedEntryFixtureClicks: fixture.receipts.length,
    exhaustivePredicatesRecomputed: mode === '--scan', kernelChecked: false,
    engine: { electron: native.versions.electron, v8: native.versions.v8 } }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
