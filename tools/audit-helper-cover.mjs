import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { gzipSync } from 'node:zlib';
import { createRuntime } from '../model/runtime.mjs';
import { shortAsciiSeededRandom, STARTUP_SEED_COUNT } from '../model/seed-inference.mjs';
import { HELPER_GRANDMAS, helperSweepActions } from '../model/helper-cover.mjs';

const sha256 = value => createHash('sha256').update(value).digest('hex');
const ordinalSeed = ordinal => {
  let seed = '';
  for (let i = 0; i < 5; i++) { seed = String.fromCharCode(97 + ordinal % 26) + seed; ordinal = Math.floor(ordinal / 26); }
  return seed;
};
const scratch = mkdtempSync(join(tmpdir(), 'cookie-helper-cover-'));
const cppPath = fileURLToPath(new URL('./check-helper-seeds.cpp', import.meta.url));
const executable = join(scratch, 'check-helper-seeds');
const compilerFlags = ['-std=c++17', '-O3', '-fno-fast-math', '-ffp-contract=off', '-pthread'];
execFileSync('clang++', [...compilerFlags, cppPath, '-o', executable], { stdio: 'inherit' });

const samples = []; let sampleState = 1;
for (let i = 0; i < 1000; i++) {
  sampleState = (Math.imul(sampleState, 1664525) + 1013904223) >>> 0;
  for (const index of [0, 1, 2, 9, 10, 31, 99, 100, 254]) samples.push({ seed: ordinalSeed(sampleState % STARTUP_SEED_COUNT), index });
}
for (const seed of ['aaaaa', 'aaaao', 'zzzzz']) for (const index of [0, 1, 9, 10, 99, 100, 254]) samples.push({ seed, index });
const sampleText = samples.map(sample => `${sample.seed} ${sample.index}`).join('\n') + '\n';
writeFileSync(join(scratch, 'samples.txt'), sampleText);
const output = execFileSync(executable, ['--samples', join(scratch, 'samples.txt')], { encoding: 'utf8', maxBuffer: 10000000 });
const lines = output.trim().split('\n');
const native = createRuntime({ diagnosticMode: true, recordAudit: false });
const values = native.evaluate(`(${JSON.stringify(samples)}).map(({seed,index})=>{Math.seedrandom(seed+' 1 '+index);const values=[Math.random(),Math.random(),Math.random()];Math.seedrandom();return values;})`);
const bits = value => { const data = Buffer.alloc(8); data.writeDoubleBE(value); return data.toString('hex'); };
for (let n = 0; n < samples.length; n++) {
  const [seed, index, ...drawBits] = lines[n].split(' ');
  assert.equal(seed, samples[n].seed); assert.equal(+index, samples[n].index);
  const independent = shortAsciiSeededRandom(`${seed} 1 ${index}`);
  for (let draw = 0; draw < 3; draw++) {
    assert.equal(drawBits[draw], bits(values[n][draw])); assert.equal(drawBits[draw], bits(independent()));
  }
}
console.log(`Preflight: ${samples.length * 3} native binary64 draws match exactly.`);

const certificateFile = join(scratch, 'helper-first-index.bin');
const scanFile = join(scratch, 'scan.json'), verifyFile = join(scratch, 'verify.json');
execFileSync(executable, ['--scan', certificateFile, scanFile, String(STARTUP_SEED_COUNT), '4'], { stdio: 'inherit' });
execFileSync(executable, ['--verify', certificateFile, verifyFile, String(STARTUP_SEED_COUNT), '4'], { stdio: 'inherit' });
const scan = JSON.parse(readFileSync(scanFile)), verification = JSON.parse(readFileSync(verifyFile));
assert.equal(scan.unresolvedSeeds, 0); assert.equal(scan.maximumFirstHelperIndex, HELPER_GRANDMAS - 1);
assert.equal(verification.allChosenThirdLeadingBytesAtLeast128, true);

const uiFixtures = [];
for (const seed of [scan.firstMaximumSeed, 'aaaaa', 'zzzzz']) {
  const runtime = createRuntime({ diagnosticMode: true, recordAudit: false }), G = runtime.Game;
  // Explicit diagnostic entry premises. The fixed input sweep below receives
  // none of these values and never reads the private sprite list or seed.
  G.seed = seed; G.cookies = G.cookiesEarned = 1e6;
  G.season = 'christmas'; G.seasonT = G.fps * 86400;
  runtime.advance(5100);
  const price = G.Objects.Grandma.getSumPrice(HELPER_GRANDMAS);
  runtime.act({ type: 'buy-building', id: 1, amount: HELPER_GRANDMAS }, { observe: false });
  const elapsedBefore = runtime.clock.now;
  for (const action of helperSweepActions()) runtime.act(action, { observe: false });
  const won = !!G.HasAchiev("Baby it's old outside"); assert(won, seed);
  uiFixtures.push({ seed, price, canvasWidth: G.Objects.Grandma.canvas.width,
    canvasHeight: G.Objects.Grandma.canvas.height, inputCount: helperSweepActions().length,
    sweepMilliseconds: runtime.clock.now - elapsedBefore, won,
    premises: 'Isolated runtime with stated seed, bank/earned=1e6 and active Christmas timer; native purchases and the fixed public grid sweep afterward' });
}
const certificate = readFileSync(certificateFile), compressed = gzipSync(certificate, { level: 9 });
const artifact = new URL('../model/certificates/helper-first-index.bin.gz', import.meta.url);
mkdirSync(new URL('../model/certificates/', import.meta.url), { recursive: true });
writeFileSync(artifact, compressed);
const witness = { ...scan, sourceHashes: native.source.hashes,
  reproduction: 'node tools/audit-helper-cover.mjs', compiler: execFileSync('clang++', ['--version'], { encoding: 'utf8' }).trim(), compilerFlags,
  cppSourceSha256: sha256(readFileSync(cppPath)), helperSweepModuleSha256: sha256(readFileSync(new URL('../model/helper-cover.mjs', import.meta.url))),
  runtimeSha256: sha256(readFileSync(new URL('../model/runtime.mjs', import.meta.url))),
  preflight: { sampleInputs: samples.length, binary64Draws: samples.length * 3, matchesNativeAndIndependentJs: true,
    sampleInputSha256: sha256(sampleText), sampleOutputSha256: sha256(output) },
  certificate: { path: 'model/certificates/helper-first-index.bin.gz', bytes: certificate.length, sha256: sha256(certificate),
    compressedBytes: compressed.length, compressedSha256: sha256(compressed) },
  sufficientBytePredicateVerification: verification,
  uiFixtures,
  conclusion: 'Exhaustive native arithmetic evidence: 24 Grandmas suffice for every startup seed under the two-art Christmas setup. The fixed 3350ms grid sweep uses no private seed or sprite positions.',
  remainingProofObligations: ['Kernel-checked all-seed certificate checker', 'Source refinement of the short-ASCII ARC4 projection and its binary64 normalization', 'Source refinement of the held-pointer/draw schedule and legal entry setup'],
};
writeFileSync(new URL('../model/helper-seeds-witness.json', import.meta.url), JSON.stringify(witness, null, 2) + '\n');
console.log(JSON.stringify({ seeds: scan.checkedSeeds, maximumIndex: scan.maximumFirstHelperIndex,
  certificateBytes: certificate.length, compressedBytes: compressed.length, uiFixtures: uiFixtures.length, scope: scan.scope }));
