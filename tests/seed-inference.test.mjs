import assert from 'node:assert/strict';
import test from 'node:test';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import * as inference from '../model/seed-inference.mjs';
import {
  candidateFortuneNumbers, inferSeedFromFortune, LETTER_BUCKETS, IID53_SIZE,
  parseVisibleFortuneNumbers, shortAsciiSeededRandom, startupSeedPriorNumerator,
  STARTUP_SEED_PRIOR_DENOMINATOR, startupSeeds, candidateMiceSpelling,
  parseVisibleMiceSpelling, refineFortunePosteriorWithMice,
} from '../model/seed-inference.mjs';
import { hasGameSource, SOURCE_HASHES } from '../model/game-source.mjs';
import { createRuntime } from '../model/runtime.mjs';

test('IID53 letter buckets follow binary64 boundaries and cover every index', () => {
  assert.equal(LETTER_BUCKETS.reduce((total, bucket) => total + bucket.count, 0n), IID53_SIZE);
  assert.deepEqual(LETTER_BUCKETS.filter(bucket => bucket.count === 346430740566962n).map(bucket => bucket.letter), ['a', 'f', 'k', 'o', 'u', 'y']);
  for (const [index, bucket] of LETTER_BUCKETS.entries()) {
    assert(bucket.count === 346430740566961n || bucket.count === 346430740566962n);
    const actual = value => Math.floor((Number(value) / 2 ** 53) * 26);
    assert.equal(actual(bucket.lower), index);
    assert.equal(actual(bucket.upperExclusive - 1n), index);
    if (index > 0) assert.equal(actual(bucket.lower - 1n), index - 1);
    if (index < 25) assert.equal(actual(bucket.upperExclusive), index + 1);
    assert.equal(bucket.lower, index ? LETTER_BUCKETS[index - 1].upperExclusive : 0n);
  }
  assert.equal(STARTUP_SEED_PRIOR_DENOMINATOR, 2n ** 265n);
  assert.equal(startupSeedPriorNumerator('aaaaa'), 346430740566962n ** 5n);
  assert.equal(startupSeedPriorNumerator('bbbbb'), 346430740566961n ** 5n);
  assert.equal(LETTER_BUCKETS.reduce((sum, bucket) => sum + bucket.count, 0n) ** 5n, STARTUP_SEED_PRIOR_DENOMINATOR);
});

test('short ASCII generator agrees with the exact Lean helper witness', () => {
  const random = shortAsciiSeededRandom('aaaao 1 0');
  assert.deepEqual(Array.from({ length: 3 }, random), [
    7103933198431415 / 18014398509481984,
    6524103155113467 / 9007199254740992,
    8931643759593147 / 9007199254740992,
  ]);
  assert.throws(() => shortAsciiSeededRandom('é'), /ASCII/);
  assert.throws(() => shortAsciiSeededRandom('a'.repeat(256)), /ASCII/);
});

test('visible Fortune parsing retains collisions and exact unequal posterior weights', () => {
  const html = '<span class="fortune"><div class="icon" style="background-position:-1392px -384px"></div>Your lucky numbers are: 73 43 10 64</span>';
  const numbers = parseVisibleFortuneNumbers(html);
  assert.deepEqual(candidateFortuneNumbers('aaodk'), numbers);
  assert.deepEqual(candidateFortuneNumbers('abeby'), numbers);
  const posterior = inferSeedFromFortune({ numbers, candidates: ['aaaaa', 'aaodk', 'abeby', 'zzzzz'] });
  assert.equal(posterior.completeStartupDomain, false);
  assert.equal(posterior.posteriorScope, 'conditional-on-supplied-candidates');
  assert.equal(posterior.inspected, 4);
  assert.equal(posterior.consistent, true);
  assert.deepEqual(posterior.candidates.map(candidate => candidate.seed), ['aaodk', 'abeby']);
  assert(posterior.candidates[0].posteriorNumerator > posterior.candidates[1].posteriorNumerator);
  assert.equal(posterior.posteriorDenominator, posterior.candidates.reduce((sum, candidate) => sum + candidate.posteriorNumerator, 0n));
  assert.deepEqual(inferSeedFromFortune({ numbers, candidates: ['aaaaa'] }).candidates, []);
  assert.equal(inferSeedFromFortune({ numbers, candidates: ['aaaaa'] }).consistent, false);
});

test('seed inference rejects ambiguous domains and malformed observations', () => {
  assert.throws(() => inferSeedFromFortune({ numbers: [73, 43, 10, 64], candidates: ['aaodk', 'aaodk'] }), /Duplicate/);
  assert.throws(() => inferSeedFromFortune({ numbers: [73, 43, 10, 64], candidates: null }), /iterable/);
  assert.throws(() => inferSeedFromFortune({ numbers: [73, 43, 10, 100], candidates: [] }), /four integer/);
  assert.throws(() => inferSeedFromFortune({ numbers: [73, 43, 10, 64], candidates: ['Game.seed'] }), /five lowercase/);
  assert.throws(() => parseVisibleFortuneNumbers('Your lucky numbers are: 73 43 10 640'), /four integer/);
  assert.throws(() => parseVisibleFortuneNumbers('No Fortune is visible.'), /does not contain/);
  const seeds = startupSeeds();
  assert.deepEqual(Array.from({ length: 3 }, () => seeds.next().value), ['aaaaa', 'aaaab', 'aaaac']);
});

test('a second visible quote distinguishes both Fortune collision branches', () => {
  const posterior = inferSeedFromFortune({ numbers: [73, 43, 10, 64], candidates: ['aaodk', 'abeby'] });
  for (const [seed, spelling] of [['aaodk', 'blasphemouse'], ['abeby', 'blasphemous']]) {
    assert.equal(candidateMiceSpelling(seed), spelling);
    const observed = parseVisibleMiceSpelling(`<q>Absolutely ${spelling}!</q>`);
    const after = refineFortunePosteriorWithMice(posterior, observed);
    assert.deepEqual(after.candidates.map(candidate => candidate.seed), [seed]);
    assert.equal(after.posteriorDenominator, after.candidates[0].posteriorNumerator);
    assert.equal(after.completeStartupDomain, false);
  }
  assert.throws(() => refineFortunePosteriorWithMice(posterior, 'unknown'), /visible spelling/);
  assert.throws(() => parseVisibleMiceSpelling('<q>Unknown.</q>'), /one visible/);
});

test('archived exhaustive evidence pins the unchanged core and exact result', () => {
  const artifact = JSON.parse(readFileSync(new URL('../model/seed-inference-witness.json', import.meta.url), 'utf8'));
  const sha = value => createHash('sha256').update(value).digest('hex');
  for (const [name, expected] of Object.entries(artifact.scanImplementation.functions))
    assert.equal(sha(inference[name].toString()), expected, name);
  assert.equal(sha(JSON.stringify(LETTER_BUCKETS, (_, value) => typeof value === 'bigint' ? value.toString() : value)), artifact.scanImplementation.letterBucketsHash);
  assert.deepEqual(artifact.nativeSourceHashes, SOURCE_HASHES);
  assert.equal(artifact.posterior.inspected, 26 ** 5);
  assert.equal(artifact.posterior.completeStartupDomain, true);
  assert.deepEqual(artifact.posterior.candidates.map(candidate => candidate.seed), ['aaodk', 'abeby']);
  for (const branch of artifact.quoteRefinements) {
    const actual = refineFortunePosteriorWithMice(artifact.posterior, branch.additionalObservation.spelling);
    assert.deepEqual(JSON.parse(JSON.stringify(actual, (_, value) => typeof value === 'bigint' ? value.toString() : value)), branch);
  }
  // This checks an archived execution and its unchanged core. It does not repeat
  // all 11,881,376 cases; the artifact gives the full-scan reproduction command.
});

test('observation-only CLI reports its supplied-domain scope', () => {
  const result = JSON.parse(execFileSync(process.execPath, [
    new URL('../tools/infer-fortune-seed.mjs', import.meta.url).pathname,
    '73', '43', '10', '64', '--mice', 'blasphemouse', '--candidates', 'aaodk,abeby',
  ], { encoding: 'utf8' }));
  assert.equal(result.posteriorScope, 'conditional-on-supplied-candidates');
  assert.deepEqual(result.candidates.map(candidate => candidate.seed), ['aaodk']);
});

test('independent ARC4 path agrees with pinned native explicit seeding', {
  skip: !hasGameSource() && 'Pinned Steam source is unavailable',
}, () => {
  const runtime = createRuntime({ diagnosticMode: true });
  // Each tested seed is supplied by this fixture. No inference reads Game.seed.
  const seeds = ['aaaao 1 0', 'aaodk-fortune', 'abeby-fortune', 'zzzzz-fortune', 'abcde-blasphemouse', 'abcde-tombolacomputing', 'a'.repeat(255)];
  for (const seed of seeds) {
    const local = shortAsciiSeededRandom(seed);
    runtime.context.Math.seedrandom(seed);
    for (let index = 0; index < 100; index++) assert.equal(local(), runtime.context.Math.random(), `${seed} draw ${index}`);
  }
  runtime.context.Math.seedrandom();
  assert(runtime.source.sources['main.js'].includes("Math.seedrandom(Game.seed+'-fortune');me=loc(\"Your lucky numbers are:\")+' '+Math.floor(Math.random()*100)+' '+Math.floor(Math.random()*100)+' '+Math.floor(Math.random()*100)+' '+Math.floor(Math.random()*100)"));
});
